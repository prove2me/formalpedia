-- Prove2me | solution 1 for GlobalTheory.ChF.sub_surjective_of_lin_leftInverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:04:34.995226+00:00
-- url     : https://prove2.me/submissions/8ce3899e-ca9a-43cb-9bb7-97ae356a096f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemSupSpanXPowIffAndIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubSurjectiveOfLinLeftInverse
import Theorems.Thm_GlobalTheory_ChF_mem_sup_span_X_pow_iff_and_isAdicComplete
import Theorems.Thm_GlobalTheory_X_mem_germIdeal
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_germIdeal_eq_span
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private theorem isAdicComplete_germIdeal (R κ : Type) [CommRing R] [Finite κ] :
    IsAdicComplete (germIdeal κ R) (MvPowerSeries κ R) := by
  have h := (mem_sup_span_X_pow_iff_and_isAdicComplete R ⊥ κ).2 inferInstance
  rwa [Ideal.map_bot, bot_sup_eq, ← germIdeal_eq_span] at h
private theorem eq_zero_or_single {κ : Type} {e : κ →₀ ℕ} (he : e.degree < 2) :
    e = 0 ∨ ∃ k, e = Finsupp.single k 1 := by
  classical
  by_cases h0 : e = 0
  · exact Or.inl h0
  · right
    obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h0
    have hle : Finsupp.single k 1 ≤ e := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 hk
    obtain ⟨c, hc⟩ := exists_add_of_le hle
    have hd : e.degree = 1 + c.degree := by rw [hc, map_add, Finsupp.degree_single]
    have : c = 0 := (Finsupp.degree_eq_zero_iff c).1 (by omega)
    exact ⟨k, by rw [hc, this, add_zero]⟩
end GlobalTheory.ChF
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d r : ℕ) (φ : Fin d → PS R 1 r) (A' : Matrix (Fin r) (Fin d) R), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → A' * lin φ = 1 → Function.Surjective (fun f : PS R 1 d => sub ![φ] f) := by
  intro R _ d r φ A' h0 hA
  classical
  set a : Fin 1 × Fin d → PS R 1 r := fun q => (![φ] : Fin 1 → Fin d → PS R 1 r) q.1 q.2 with ha
  have ha' : ∀ q : Fin 1 × Fin d, a q = φ q.2 := by
    rintro ⟨i, j⟩
    fin_cases i
    rfl
  have hs : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by rw [ha', h0]
  let f : PS R 1 d →+* PS R 1 r := (MvPowerSeries.substAlgHom (R := R) hs).toRingHom
  have hf : ∀ u, f u = sub ![φ] u := fun u => by
    change MvPowerSeries.substAlgHom hs u = MvPowerSeries.subst a u
    rw [MvPowerSeries.coe_substAlgHom]
  have hfX : ∀ q, f (MvPowerSeries.X q) = φ q.2 := fun q => by
    change MvPowerSeries.substAlgHom hs _ = _
    rw [MvPowerSeries.substAlgHom_X, ha']
  have hC1 := isAdicComplete_germIdeal R (Fin 1 × Fin d)
  have hC2 := isAdicComplete_germIdeal R (Fin 1 × Fin r)
  have hmap : (germIdeal (Fin 1 × Fin d) R).map f = germIdeal (Fin 1 × Fin r) R := by
    apply le_antisymm
    · rw [germIdeal_eq_span, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      rw [hfX]
      exact RingHom.mem_ker.2 (h0 _)
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := germIdeal (Fin 1 × Fin r) R) ?_
        (IsAdicComplete.le_jacobson_bot _) ?_
      · rw [germIdeal_eq_span]
        exact Submodule.fg_span (Set.finite_range _)
      · rw [smul_eq_mul, ← pow_two]
        conv_lhs => rw [germIdeal_eq_span]
        rw [Ideal.span_le]
        rintro _ ⟨⟨i0, i⟩, rfl⟩
        obtain rfl : i0 = 0 := Subsingleton.elim _ _
        have h1 : ∑ j, A' i j • φ j ∈ (germIdeal (Fin 1 × Fin d) R).map f := by
          refine Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ ?_
          rw [← hfX (0, j)]
          exact Ideal.mem_map_of_mem _ (X_mem_germIdeal _)
        have h2 : (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 r) - ∑ j, A' i j • φ j ∈
            germIdeal (Fin 1 × Fin r) R ^ 2 := by
          refine mem_germIdeal_pow_iff.2 fun e he => ?_
          rcases eq_zero_or_single he with rfl | ⟨⟨k0, k⟩, rfl⟩
          · simp [h0]
          · obtain rfl : k0 = 0 := Subsingleton.elim _ _
            have h3 := congrFun (congrFun hA i) k
            rw [Matrix.mul_apply, Matrix.one_apply] at h3
            simp only [lin, Matrix.of_apply] at h3
            rw [map_sub, map_sum]
            simp only [map_smul, smul_eq_mul]
            rw [h3, MvPowerSeries.coeff_X]
            simp [Finsupp.single_left_inj, eq_comm]
        have h4 := Submodule.add_mem_sup h1 h2
        rwa [add_sub_cancel] at h4
  have hsurj : Function.Surjective f := by
    have : IsHausdorff ((germIdeal (Fin 1 × Fin d) R).map f) (PS R 1 r) := by
      rw [hmap]
      exact hC2.toIsHausdorff
    refine surjective_of_mk_map_comp_surjective (I := germIdeal (Fin 1 × Fin d) R) f fun y => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPowerSeries.C (MvPowerSeries.constantCoeff y), ?_⟩
    have h5 : f (MvPowerSeries.C (MvPowerSeries.constantCoeff y)) =
        MvPowerSeries.C (MvPowerSeries.constantCoeff y) :=
      (MvPowerSeries.substAlgHom (R := R) hs).commutes _
    rw [RingHom.comp_apply, h5, Ideal.Quotient.eq, hmap]
    exact RingHom.mem_ker.2 (by simp)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, (hf x).symm.trans hx⟩
end GlobalTheory.ChF
