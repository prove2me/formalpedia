-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.exists_K5_pde_solution
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T23:08:50.759269+00:00
-- url     : https://prove2.me/submissions/20f6728f-1508-4441-aadc-6e9b00e76d88

import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_VerticalData
import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_RUData
import Definitions.Def_HodgeComputerSSR_RInfData
import Definitions.Def_HodgeComputerSSR_RQ5Data
import Theorems.Thm_HodgeComputer_Formal_HoldoutCover_finiteNormalizedTrace_firstOrder
import Theorems.Thm_HodgeComputer_Formal_RationalResidues_residue_sum_eq_infinity
import Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_residue_mapRatFunc
import Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_infinityCoefficient_mapRatFunc
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_vertical_K5_identity
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_regularAt_eta_L_of_notMem
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_sum_R34_eq_sheet_div
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_residue_zero_eta
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_infinityCoefficient_eta
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_sum_RQ5_eta_L
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_global_residue_cancellation

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
namespace SymmetricSexticResidual.Certificate
open SymmetricSexticResidual.K5Field
  SymmetricSexticResidual.VerticalIdentity SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverResidue SymmetricSexticResidual.LocalResidueU0
  QuadraticCovers
open scoped BigOperators Classical

/-- Global residue theorem on `CoverL`: the sum of the 34 finite residues of `eta_L` over `R34`
equals `ιL_K5 (toK5 P_horiz_5)`. -/
theorem sum_R34_eta_L :
    ∑ r ∈ R34, CrossedRationalResidue.residue r eta_L = ιL_K5 (toK5 P_horiz_5) := by
  let S_all : Finset CoverL := ({0} ∪ RQ5) ∪ R34
  have hglob : ∑ r ∈ S_all, CrossedRationalResidue.residue r eta_L =
      CrossedRationalResidue.infinityCoefficient eta_L :=
    HodgeComputer.Formal.RationalResidues.residue_sum_eq_infinity eta_L eta_L_denom_splits S_all
      (fun r hr => (HodgeComputer.SymmetricSexticResidual.Proof.regularAt_eta_L_of_notMem r hr).residue_eq_zero)
  have hdisj1 : Disjoint ({0} ∪ RQ5 : Finset CoverL) R34 := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_singleton_left.mpr zero_notMem_R34, disjoint_R34_RQ5.symm⟩
  have hdisj2 : Disjoint ({0} : Finset CoverL) RQ5 :=
    Finset.disjoint_singleton_left.mpr zero_notMem_RQ5
  have hsplit : ∑ r ∈ S_all, CrossedRationalResidue.residue r eta_L =
      CrossedRationalResidue.residue 0 eta_L +
        (∑ r ∈ RQ5, CrossedRationalResidue.residue r eta_L) +
        (∑ r ∈ R34, CrossedRationalResidue.residue r eta_L) := by
    dsimp only [S_all]
    rw [Finset.sum_union hdisj1, Finset.sum_union hdisj2, Finset.sum_singleton]
  have hres0 : CrossedRationalResidue.residue (0 : CoverL) eta_L = ιL_K5 toK5_RU := by
    have h0 := HodgeComputer.Formal.QuadraticCovers.residue_mapRatFunc ιL_K5 (0 : K5) eta
    rw [map_zero] at h0
    change CrossedRationalResidue.residue 0 eta_L = ιL_K5 (CrossedRationalResidue.residue 0 eta) at h0
    rw [h0, HodgeComputer.SymmetricSexticResidual.Proof.residue_zero_eta]
  have hinf : CrossedRationalResidue.infinityCoefficient eta_L =
      ιL_K5 (-toK5_RInf / L_K ^ 2) := by
    have hi := HodgeComputer.Formal.QuadraticCovers.infinityCoefficient_mapRatFunc ιL_K5 eta
    change CrossedRationalResidue.infinityCoefficient eta_L =
      ιL_K5 (CrossedRationalResidue.infinityCoefficient eta) at hi
    rw [hi, HodgeComputer.SymmetricSexticResidual.Proof.infinityCoefficient_eta]
  rw [hsplit, hres0, HodgeComputer.SymmetricSexticResidual.Proof.sum_RQ5_eta_L, hinf] at hglob
  have hcancel := congrArg ιL_K5 HodgeComputer.SymmetricSexticResidual.Proof.global_residue_cancellation
  simp only [map_sub] at hcancel
  linear_combination hglob - hcancel

private lemma resDivW_L_map (w : Fin 4 → K5) :
    resDivW_L (L := CoverL) (fun i => ιL_K5 (w i)) = ιL_K5 (resDivW w) := by
  simp only [resDivW_L, resDivW, map_sum, map_sub, map_mul, map_div₀, map_ofNat]
  apply Finset.sum_congr rfl; intro i _
  have h1 : δL (L := CoverL) i (ιL_K5 (w i)) = ιL_K5 (δ i (w i)) := δL_apply i (w i)
  have h2 : δL (L := CoverL) i (ιL_K5 Fx_K) = ιL_K5 (δ i Fx_K) := δL_apply i Fx_K
  have h3 : δL (L := CoverL) i (ιL_K5 W2_K) = ιL_K5 (δ i W2_K) := δL_apply i W2_K
  change δL (L := CoverL) i (ιL_K5 (w i)) -
      ιL_K5 (w i) * δL (L := CoverL) i (ιL_K5 Fx_K) / ιL_K5 Fx_K -
      ιL_K5 (w i) * δL (L := CoverL) i (ιL_K5 W2_K) / (2 * ιL_K5 W2_K) = _
  rw [h1, h2, h3]

private lemma resDivW_div_two (w : Fin 4 → K5) :
    resDivW (fun i => w i / 2) = resDivW w / 2 := by
  have h2 : (2 : K5) ≠ 0 := by norm_num
  have hδ (i : Fin 4) (x : K5) : δ i (x / 2) = δ i x / 2 := by
    have h : δ i x = δ i (x / 2) + δ i (x / 2) := by
      rw [← map_add, add_halves]
    field_simp [h2]
    linear_combination -h
  simp only [resDivW, Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _
  rw [hδ i]
  field_simp [h2]

/-- Descending the combined vertical + 34-sheet horizontal solution from `CoverL` to `K5`
produces a rational vector field `w : Fin 4 → K5` solving `srcX + resDivW w = 0`. -/
theorem exists_K5_pde_solution : ∃ w : Fin 4 → K5, srcX + resDivW w = 0 := by
  obtain ⟨w_H_L, hwH⟩ := HodgeComputer.SymmetricSexticResidual.Proof.sum_R34_eq_sheet_div
  rw [sum_R34_eta_L] at hwH
  let w_tot_L : Fin 4 → CoverL := fun i => ιL_K5 (w_V i) + w_H_L i
  have htot_mul :
      2 * ιL_K5 W2_K * ιL_K5 H0_K ^ 2 * resDivW_L (L := CoverL) w_tot_L =
        ιL_K5 (toK5 NA_Q5 * H0_K) := by
    have hV_L := congrArg ιL_K5 HodgeComputer.SymmetricSexticResidual.Proof.vertical_K5_identity
    simp only [map_add, map_mul, map_pow, map_ofNat] at hV_L
    change 2 * ιL_K5 W2_K * ιL_K5 H0_K ^ 2 * resDivW_L (L := CoverL) (fun i => ιL_K5 (w_V i) + w_H_L i) = _
    rw [resDivW_L_add, mul_add, resDivW_L_map, hwH, map_mul]
    exact hV_L
  have h2_ne : (2 : CoverL) ≠ 0 := by norm_num
  have hW2_L : ιL_K5 W2_K ≠ 0 := (map_ne_zero_iff ιL_K5 ιL_K5.injective).mpr W2_K_ne_zero
  have hH0_L : ιL_K5 H0_K ≠ 0 := (map_ne_zero_iff ιL_K5 ιL_K5.injective).mpr H0_K_ne_zero
  have hden_L : (2 * ιL_K5 W2_K * ιL_K5 H0_K ^ 2 : CoverL) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2_ne hW2_L) (pow_ne_zero 2 hH0_L)
  have htot_L : resDivW_L (L := CoverL) w_tot_L = ιL_K5 (toK5 NA_Q5 / (2 * W2_K * H0_K)) := by
    apply mul_left_cancel₀ hden_L
    rw [htot_mul]
    simp only [map_div₀, map_mul, map_ofNat]
    field_simp [h2_ne, hW2_L, hH0_L]
  -- Descend `resDivW_L w_tot_L = ιL_K5 (toK5 NA_Q5 / (2 * W2_K * H0_K))` via normalized trace!
  let coeff : Fin 4 → K5 := fun i => -(δ i Fx_K / Fx_K) - δ i W2_K / (2 * W2_K)
  have heq_firstOrder :
      ∑ i : Fin 4, (δL (L := CoverL) i (w_tot_L i) + w_tot_L i * algebraMap K5 CoverL (coeff i)) =
        algebraMap K5 CoverL (toK5 NA_Q5 / (2 * W2_K * H0_K)) := by
    rw [← htot_L, resDivW_L]
    apply Finset.sum_congr rfl; intro i _
    have hFx : δL (L := CoverL) i (ιL (L := CoverL) Fx_K) = ιL_K5 (δ i Fx_K) := δL_apply i Fx_K
    have hW2 : δL (L := CoverL) i (ιL (L := CoverL) W2_K) = ιL_K5 (δ i W2_K) := δL_apply i W2_K
    simp only [coeff, map_sub, map_neg, map_div₀, map_mul, map_ofNat]
    rw [hFx, hW2]; ring
  have hdesc := HodgeComputer.Formal.HoldoutCover.finiteNormalizedTrace_firstOrder
    δ (δL (L := CoverL)) (fun i x => δL_apply (L := CoverL) i x)
    coeff (toK5 NA_Q5 / (2 * W2_K * H0_K)) w_tot_L heq_firstOrder
  let w_tot : Fin 4 → K5 := fun i => Algebra.normalizedTrace K5 CoverL (w_tot_L i)
  have htot_K5 : resDivW w_tot = toK5 NA_Q5 / (2 * W2_K * H0_K) := by
    rw [← hdesc, resDivW]
    apply Finset.sum_congr rfl; intro i _
    simp only [w_tot, coeff]; ring
  let w_rad : Fin 4 → K5 := ![0, 0, 0, y_K * MA_K / H0_K]
  let w_final : Fin 4 → K5 := fun i => (w_tot i - w_rad i) / 2
  refine ⟨w_final, ?_⟩
  have hdiv_final : resDivW w_final = (resDivW w_tot - resDivW w_rad) / 2 := by
    dsimp only [w_final]
    rw [resDivW_div_two, K5Field.resDivW_sub]
  rw [hdiv_final, htot_K5]
  linear_combination (1 / 2 : K5) * radial_normal_chart_identity


end SymmetricSexticResidual.Certificate

theorem solution :
    ∃ w : Fin 4 → SymmetricSexticResidual.K5Field.K5,
      SymmetricSexticResidual.K5Field.srcX + SymmetricSexticResidual.K5Field.resDivW w = 0 :=
  SymmetricSexticResidual.Certificate.exists_K5_pde_solution
