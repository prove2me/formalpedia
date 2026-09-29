-- Prove2me | solution 1 for ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/68220926-ae78-52ee-a883-a97ceb778c9d

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_exists_chartData_of_lineResidues
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_MultCovering_cuspInftyBar_not_mem_zeroChart_dom
import Theorems.Thm_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom
import Theorems.Thm_ModularCurve_MultCovering_mem_zeroChart_nodes_iff
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ValuationSubring.instIsAlgClosedResidueField ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ValuationSubring.reduceAt_coe"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne.ModularCurve.MultCovering"
open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar jqModC modularFunctionFieldC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar exists_chartData_of_lineResidues eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty hasPrincipalDivisors_modularFunctionFieldBar_unconditional deg_eq_one_modularFunctionFieldBar"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "hasseExp goodFamilyZero ssPolyBarZero FamCtx jBar mAnnuli ChartCtx infChart zeroChart chart ssValue ssValue_mem_ssJSet cuspInftyBar_not_mem_zeroChart_dom cuspInftyBar_mem_infChart_dom mem_zeroChart_nodes_iff"
namespace P2Mcd0
p2m_open "ModularCurve.MultCovering ModularCurve"

section LineAlgebra

variable {k : Type} [Field k] {r : ℕ} (P : Fin r → k[X]) (m : ℕ)
  (hspan : ∀ Q : k[X], Q.natDegree ≤ m → Q ∈ Submodule.span k (Set.range P))

include hspan in

theorem pos_r : 0 < r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exfalso
    subst hr
    have h1 := hspan 1 (by rw [natDegree_one]; exact Nat.zero_le _)
    have hempty : Set.range P = ∅ := Set.range_eq_empty P
    rw [hempty, Submodule.span_empty, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · exact hr

include hspan in

theorem exists_expansion (Q : k[X]) (hQ : Q.natDegree ≤ m) : ∃ c : Fin r → k, ∑ l, c l • P l = Q :=
  (Submodule.mem_span_range_iff_exists_fun k).mp (hspan Q hQ)

include hspan in

theorem exists_rootMultiplicity_eq_one (hm : 0 < m) (D : k[X]) (x₀ : k) (hDx : D.eval x₀ ≠ 0) :
    ∃ l, (P l * C (D.eval x₀) - D * C ((P l).eval x₀)).rootMultiplicity x₀ = 1 := by

  set φ : k[X] → k[X] := fun Q => Q * C (D.eval x₀) - D * C (Q.eval x₀) with hφ
  have hφsum : ∀ c : Fin r → k, φ (∑ l, c l • P l) = ∑ l, c l • φ (P l) := by
    intro c
    simp only [hφ, smul_eq_C_mul, Finset.sum_mul, eval_finset_sum, eval_C_mul, map_sum, map_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, mul_sub]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hroot : ∀ Q, (φ Q).IsRoot x₀ := by
    intro Q
    simp only [hφ, IsRoot, eval_sub, eval_mul, eval_C]
    ring
  by_contra hall
  push_neg at hall

  have hdvd : ∀ l, (X - C x₀) ^ 2 ∣ φ (P l) := by
    intro l
    by_cases h0 : φ (P l) = 0
    · rw [h0]; exact dvd_zero _
    · rw [← le_rootMultiplicity_iff h0]
      have hpos : 0 < (φ (P l)).rootMultiplicity x₀ := (rootMultiplicity_pos h0).mpr (hroot (P l))
      have hne : (φ (P l)).rootMultiplicity x₀ ≠ 1 := hall l
      omega

  obtain ⟨c, hc⟩ := exists_expansion P m hspan (X - C x₀) (by rw [natDegree_X_sub_C]; exact hm)
  have hdvd' : (X - C x₀) ^ 2 ∣ φ (X - C x₀) := by
    have h' : (X - C x₀) ^ 2 ∣ φ (∑ l, c l • P l) := by
      rw [hφsum]
      exact Finset.dvd_sum fun l _ => by rw [smul_eq_C_mul]; exact (hdvd l).mul_left _
    rwa [hc] at h'

  have hφX : φ (X - C x₀) = C (D.eval x₀) * (X - C x₀) := by
    simp only [hφ, eval_sub, eval_X, eval_C, sub_self, map_zero, mul_zero, sub_zero]
    ring
  rw [hφX] at hdvd'
  have hne0 : C (D.eval x₀) * (X - C x₀) ≠ 0 := mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_sub_C_ne_zero x₀)
  have h2 := (le_rootMultiplicity_iff hne0).mpr hdvd'
  rw [rootMultiplicity_mul hne0, rootMultiplicity_C, rootMultiplicity_X_sub_C_self] at h2
  omega

include hspan in

theorem exists_eval_minor_ne (hm : 0 < m) (l₀ : Fin r) (x₀ y₀ : k) (hDx : (P l₀).eval x₀ ≠ 0) (hxy : x₀ ≠ y₀) :
    ∃ a b, (P a).eval x₀ * (P b).eval y₀ ≠ (P b).eval x₀ * (P a).eval y₀ := by
  by_contra hall
  push_neg at hall

  have hprop : ∀ a, (P a).eval y₀ = (P a).eval x₀ * ((P l₀).eval y₀ * ((P l₀).eval x₀)⁻¹) := by
    intro a
    have h := hall a l₀
    calc (P a).eval y₀ = ((P l₀).eval x₀ * (P a).eval y₀) * ((P l₀).eval x₀)⁻¹ := by
            rw [mul_comm ((P l₀).eval x₀), mul_assoc, mul_inv_cancel₀ hDx, mul_one]
      _ = ((P a).eval x₀ * (P l₀).eval y₀) * ((P l₀).eval x₀)⁻¹ := by rw [h]
      _ = (P a).eval x₀ * ((P l₀).eval y₀ * ((P l₀).eval x₀)⁻¹) := by rw [mul_assoc]
  obtain ⟨c, hc⟩ := exists_expansion P m hspan (X - C x₀) (by rw [natDegree_X_sub_C]; exact hm)
  have hx : (∑ l, c l • P l).eval x₀ = 0 := by rw [hc]; simp
  have hy : (∑ l, c l • P l).eval y₀ = y₀ - x₀ := by rw [hc]; simp
  rw [eval_finset_sum] at hx hy
  simp only [eval_smul, smul_eq_mul] at hx hy
  have : y₀ - x₀ = 0 := by
    rw [← hy]
    calc ∑ l, c l * (P l).eval y₀
        = ∑ l, c l * (P l).eval x₀ * ((P l₀).eval y₀ * ((P l₀).eval x₀)⁻¹) := by
          refine Finset.sum_congr rfl (fun l _ => ?_); rw [hprop l]; ring
      _ = (∑ l, c l * (P l).eval x₀) * ((P l₀).eval y₀ * ((P l₀).eval x₀)⁻¹) := by rw [Finset.sum_mul]
      _ = 0 := by rw [hx, zero_mul]
  exact hxy (sub_eq_zero.mp this).symm

include hspan in

theorem exists_eval_coeff_minor_ne (hm : 0 < m) (l₀ : Fin r) (hmon : (P l₀).Monic) (hdegl₀ : (P l₀).natDegree = m)
    (x₀ : k) (hDx : (P l₀).eval x₀ ≠ 0) :
    ∃ a b, (P a).eval x₀ * ((P b).coeff (P l₀).natDegree / (P l₀).leadingCoeff)
      ≠ (P b).eval x₀ * ((P a).coeff (P l₀).natDegree / (P l₀).leadingCoeff) := by
  rw [hmon.leadingCoeff, hdegl₀]
  by_contra hall
  push_neg at hall

  have htop : (P l₀).coeff m = 1 := by rw [← hdegl₀]; exact hmon.coeff_natDegree
  have hprop : ∀ a, (P a).coeff m = (P a).eval x₀ * ((P l₀).eval x₀)⁻¹ := by
    intro a
    have h := hall a l₀
    rw [htop, div_one, div_one, mul_one] at h
    calc (P a).coeff m = ((P l₀).eval x₀ * (P a).coeff m) * ((P l₀).eval x₀)⁻¹ := by
            rw [mul_comm ((P l₀).eval x₀), mul_assoc, mul_inv_cancel₀ hDx, mul_one]
      _ = (P a).eval x₀ * ((P l₀).eval x₀)⁻¹ := by rw [← h]
  obtain ⟨c, hc⟩ := exists_expansion P m hspan 1 (by rw [natDegree_one]; exact Nat.zero_le _)
  have hx : (∑ l, c l • P l).eval x₀ = 1 := by rw [hc]; simp
  have hcoef : (∑ l, c l • P l).coeff m = 0 := by
    rw [hc, coeff_one]
    simp [Nat.pos_iff_ne_zero.mp hm]
  rw [eval_finset_sum] at hx
  rw [finset_sum_coeff] at hcoef
  simp only [eval_smul, smul_eq_mul] at hx
  simp only [coeff_smul, smul_eq_mul] at hcoef
  have : (1 : k) * ((P l₀).eval x₀)⁻¹ = 0 := by
    rw [← hx, ← hcoef, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hprop l]; ring
  rw [one_mul, inv_eq_zero] at this
  exact hDx this

include hspan in

theorem exists_nextToTop (hm : 0 < m) (hdeg : ∀ l, (P l).natDegree ≤ m) (l₀ : Fin r) (hmon : (P l₀).Monic)
    (hdegl₀ : (P l₀).natDegree = m) :
    ∃ l, (P l - C ((P l).coeff (P l₀).natDegree / (P l₀).leadingCoeff) * P l₀).natDegree + 1 = (P l₀).natDegree ∧
      P l - C ((P l).coeff (P l₀).natDegree / (P l₀).leadingCoeff) * P l₀ ≠ 0 := by
  rw [hmon.leadingCoeff, hdegl₀]
  simp only [div_one]

  set ψ : k[X] → k[X] := fun Q => Q - C (Q.coeff m) * P l₀ with hψ
  have htop : (P l₀).coeff m = 1 := by rw [← hdegl₀]; exact hmon.coeff_natDegree
  have hψdeg : ∀ Q, Q.natDegree ≤ m → (ψ Q).degree < m := by
    intro Q hQ
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    simp only [hψ, coeff_sub, coeff_C_mul]
    rcases Nat.eq_or_lt_of_le hn with h | h
    · subst h; rw [htop, mul_one, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ h),
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_eq hdegl₀) h), mul_zero, sub_self]
  have hψsum : ∀ c : Fin r → k, ψ (∑ l, c l • P l) = ∑ l, c l • ψ (P l) := by
    intro c
    simp only [hψ, smul_eq_C_mul, finset_sum_coeff, coeff_C_mul, map_sum, map_mul, Finset.sum_mul,
      ← Finset.sum_sub_distrib, mul_sub, mul_assoc]
  by_contra hall
  push_neg at hall

  have hlt : ∀ l, ψ (P l) ∈ degreeLT k (m - 1) := by
    intro l
    rw [mem_degreeLT]
    by_cases h0 : ψ (P l) = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · have hd : (ψ (P l)).degree < m := hψdeg (P l) (hdeg l)
      rw [degree_eq_natDegree h0] at hd ⊢
      have hd' : (ψ (P l)).natDegree < m := by exact_mod_cast hd
      have hne : (ψ (P l)).natDegree + 1 ≠ m := fun h => h0 (hall l h)
      exact_mod_cast (show (ψ (P l)).natDegree < m - 1 by omega)

  obtain ⟨c, hc⟩ := exists_expansion P m hspan (X ^ (m - 1)) (by rw [natDegree_X_pow]; omega)
  have hmem : ψ (X ^ (m - 1)) ∈ degreeLT k (m - 1) := by
    rw [← hc, hψsum]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hlt l)
  have hψX : ψ (X ^ (m - 1)) = X ^ (m - 1) := by
    simp only [hψ, coeff_X_pow]
    rw [if_neg (by omega), map_zero, zero_mul, sub_zero]
  rw [hψX, mem_degreeLT, degree_X_pow] at hmem
  exact lt_irrefl _ hmem

end LineAlgebra

theorem mAnnuli_pos' (p : ℕ) [hp : Fact p.Prime] : 0 < mAnnuli p := by
  have hp' := hp.out
  unfold mAnnuli
  rcases Nat.lt_or_ge p 12 with h | h
  · interval_cases p <;> first | decide | (exfalso; norm_num at hp')
  · have h1 : 1 ≤ p / 12 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
    omega

section PerA

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem redFst_eq_placeInfty_of_isCuspidal [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hW : Γ.P.IsCuspidal W) :
    Γ.P.redFst W = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) := by
  rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (IsLocalRing.ResidueField ↥A) (Γ.P.redFst W) with ⟨c, hc⟩ | h
  · exact absurd hc (Γ.supply.redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal hW c)
  · exact h

include Γ in

theorem placeInfty_ne_charLGeomPlaceOfPoint [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] (a : (IsLocalRing.ResidueField ↥A)) :
    charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) ≠ charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a := by
  intro h
  have hc : Γ.P.IsCuspidal (cuspInftyBar (1 * p)) := (Γ.supply.isInftySide_cuspInftyBar).1
  exact Γ.supply.redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal hc a
    ((redFst_eq_placeInfty_of_isCuspidal Γ _ hc).trans h)

noncomputable def cusp0 (p : ℕ) [Fact p.Prime] : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) :=
  (frickeInvolutionBar (1 * p))⁻¹ • cuspInftyBar (1 * p)

theorem smul_cusp0 : frickeInvolutionBar (1 * p) • cusp0 p = cuspInftyBar (1 * p) := smul_inv_smul _ _

theorem cusp0_mem_dom : cusp0 p ∈ (zeroChart Γ).dom := by
  show frickeInvolutionBar (1 * p) • cusp0 p ∈ (infChart Γ).dom
  rw [smul_cusp0]
  exact cuspInftyBar_mem_infChart_dom Γ

theorem placeMap_cusp0 [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] :
    (zeroChart Γ).placeMap (cusp0 p) = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) := by
  show Γ.P.redFst (frickeInvolutionBar (1 * p) • cusp0 p) = _
  rw [smul_cusp0]
  exact redFst_eq_placeInfty_of_isCuspidal Γ _ (Γ.supply.isInftySide_cuspInftyBar).1

theorem t_mem_place {r : ℕ} (Φ : FamCtx p r) (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hP : P ≠ cuspInftyBar (1 * p)) (l : Fin r) :
    Φ.t l ∈ P.toValuationSubring := by
  classical
  obtain ⟨-, hb⟩ := Φ.t_basis
  have ht : Φ.t l ∈ riemannRochSpace (embDivisor (1 * p)) := by
    rw [← hb]; exact Submodule.subset_span ⟨l, rfl⟩
  rcases (mem_riemannRochSpace_iff.mp ht) P with h0 | hord
  · rw [h0]; exact zero_mem _
  · have hD : embDivisor (1 * p) P = 0 := by
      unfold embDivisor
      rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hP), smul_zero]
    rw [hD, neg_zero] at hord
    by_cases h0 : Φ.t l = 0
    · rw [h0]; exact zero_mem _
    · exact P.mem_of_ord_nonneg h0 hord

theorem goodFamilyZero_mem_place {r : ℕ} (Φ : FamCtx p r) (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hP : P ≠ cuspInftyBar (1 * p))
    (l : Fin r) : goodFamilyZero Φ.toFamData l ∈ P.toValuationSubring := by
  unfold goodFamilyZero
  refine mul_mem ?_ (t_mem_place Φ P hP l)
  rw [← _root_.map_inv₀]
  have hne : ((p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  exact P.mem_of_ord_nonneg ((_root_.map_ne_zero _).mpr hne) (le_of_eq (Place.ord_algebraMap P _).symm)

noncomputable def ssPolZ : Polynomial (IsLocalRing.ResidueField ↥A) := ∏ e : Fin (mAnnuli p), (X - C (ssValue Γ e ^ p))

theorem ssPolZ_monic : (ssPolZ Γ).Monic := by
  unfold ssPolZ; exact monic_prod_of_monic _ _ fun e _ => monic_X_sub_C _

theorem ssPolZ_natDegree : (ssPolZ Γ).natDegree = mAnnuli p := by
  unfold ssPolZ
  rw [natDegree_prod_of_monic _ _ fun e _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem ssPolZ_eval (x : (IsLocalRing.ResidueField ↥A)) : (ssPolZ Γ).eval x = ∏ e : Fin (mAnnuli p), (x - ssValue Γ e ^ p) := by
  unfold ssPolZ; rw [eval_prod]; simp only [eval_sub, eval_X, eval_C]

theorem aeval_ssPolZ : aeval (jBar (IsLocalRing.ResidueField ↥A)) (ssPolZ Γ) = ssPolyBarZero Γ := by
  unfold ssPolZ ssPolyBarZero
  rw [_root_.map_prod]
  simp only [_root_.map_sub, aeval_X, aeval_C]

theorem eval_ne_zero_of_placeMap_eq {P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))} (hP : P ∈ (zeroChart Γ).dom) {x₀ : (IsLocalRing.ResidueField ↥A)}
    (hx : (zeroChart Γ).placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀) : (ssPolZ Γ).eval x₀ ≠ 0 := by
  rw [ssPolZ_eval, Finset.prod_ne_zero_iff]
  intro e _ he
  apply (zeroChart Γ).placeMap_not_mem_nodes P hP
  rw [hx, mem_zeroChart_nodes_iff]
  exact ⟨ssValue Γ e, ssValue_mem_ssJSet Γ e, by rw [sub_eq_zero.mp he]⟩

end PerA

theorem mapDomain_filter_apply_congr {α β M : Type*} [AddCommMonoid M] (g : α → β) (E : α →₀ M) (b : β)
    (P Q : α → Prop) {decP : DecidablePred P} {decQ : DecidablePred Q} (hPQ : ∀ a, g a = b → (P a ↔ Q a)) :
    Finsupp.mapDomain g (E.filter P) b = Finsupp.mapDomain g (E.filter Q) b := by
  classical
  refine Finsupp.induction_linear E ?_ (fun f₁ f₂ h₁ h₂ => ?_) (fun a n => ?_)
  · simp only [Finsupp.filter_zero, Finsupp.mapDomain_zero]
  · simp only [Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.add_apply, h₁, h₂]
  · have key := hPQ a
    by_cases hP : P a <;> by_cases hQ : Q a <;> by_cases hg : g a = b <;>
      simp_all [Finsupp.mapDomain_single, Finsupp.single_apply]

theorem zeroChart_chartData (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∃ (hint : ∀ i, goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers)
      (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
        → Fin r),
      (∀ P ∈ (zeroChart Γ).dom, P.IsRational ∧ ((zeroChart Γ).placeMap P).IsRational) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)), hint _⟩
          ≠ 0) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ (zeroChart Γ).integers) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ P.toValuationSubring) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        ∀ hmem : goodFamilyZero Φ.toFamData (iQ ((zeroChart Γ).placeMap P))
            * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
              ∈ (zeroChart Γ).integers,
        ((zeroChart Γ).placeMap P).ord ((zeroChart Γ).residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
              (((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (zeroChart Γ).placeMap P ≠ (zeroChart Γ).placeMap Q →
        ∀ (hmP : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
                ∈ (zeroChart Γ).integers)
          (hmQ : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap Q)))⁻¹
                ∈ (zeroChart Γ).integers),
        ∃ i j, ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP i⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ j⟩)
          ≠ ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP j⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ i⟩)) := by
  classical
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  have hFrat : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), P.IsRational := fun P =>
    (Place.isRational_iff_deg_eq_one P).mpr (deg_eq_one_modularFunctionFieldBar (1 * p) P)

  obtain ⟨hint, Pl, hdeg, hli, hspan, hP0, hR⟩ := Φ.t_zeroChart A hA Γ hw1
  have hm : 0 < mAnnuli p := mAnnuli_pos' p
  have hr : 0 < r := pos_r Pl (mAnnuli p) hspan
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : Fin r, (l₀ : ℕ) = 0 := ⟨⟨0, hr⟩, rfl⟩
  have hPl₀ : Pl l₀ = ssPolZ Γ := hP0 l₀ hl₀
  have hmon : (Pl l₀).Monic := by rw [hPl₀]; exact ssPolZ_monic Γ
  have hdegl₀ : (Pl l₀).natDegree = mAnnuli p := by rw [hPl₀, ssPolZ_natDegree]
  have hD0 : Pl l₀ ≠ 0 := hmon.ne_zero
  have hDx : ∀ P ∈ (zeroChart Γ).dom, ∀ x₀ : (IsLocalRing.ResidueField ↥A), (zeroChart Γ).placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      (Pl l₀).eval x₀ ≠ 0 := by
    intro P hP x₀ hx; rw [hPl₀]; exact eval_ne_zero_of_placeMap_eq Γ hP hx

  have hR' : ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ * aeval (jBar (IsLocalRing.ResidueField ↥A)) (Pl l₀)
      = aeval (jBar (IsLocalRing.ResidueField ↥A)) (Pl l) := by
    intro l; rw [hPl₀, aeval_ssPolZ]; exact hR l

  have hunit : ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ ≠ 0 := by
    intro l h0
    have h := hR l
    rw [h0, zero_mul] at h
    have e : aeval (jqModC (IsLocalRing.ResidueField ↥A)) (Pl l) = (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1).val (aeval (jBar (IsLocalRing.ResidueField ↥A)) (Pl l)) :=
      Polynomial.aeval_algHom_apply (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1).val (jBar (IsLocalRing.ResidueField ↥A)) (Pl l)
    rw [← h, _root_.map_zero] at e
    exact ModularCurve.transcendental_jqModC (IsLocalRing.ResidueField ↥A) ⟨Pl l, hli.ne_zero l, e⟩

  have hreg : ∀ P ∈ (zeroChart Γ).dom, ∀ l, goodFamilyZero Φ.toFamData l ∈ P.toValuationSubring :=
    fun P hP l => goodFamilyZero_mem_place Φ P
      (fun h => cuspInftyBar_not_mem_zeroChart_dom Γ (by rw [← h]; exact hP)) l
  have hnodeInf : charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) ∉ (zeroChart Γ).nodes := by
    intro h
    obtain ⟨a, -, ha⟩ := (mem_zeroChart_nodes_iff Γ _).mp h
    exact placeInfty_ne_charLGeomPlaceOfPoint Γ (a ^ p) ha.symm

  have hix_ex : ∀ x₀ : (IsLocalRing.ResidueField ↥A), ∃ l : Fin r, ((Pl l₀).eval x₀ ≠ 0 →
      (Pl l * C ((Pl l₀).eval x₀) - Pl l₀ * C ((Pl l).eval x₀)).rootMultiplicity x₀ = 1) := by
    intro x₀
    by_cases hx : (Pl l₀).eval x₀ ≠ 0
    · obtain ⟨l, hl⟩ := exists_rootMultiplicity_eq_one Pl (mAnnuli p) hspan hm (Pl l₀) x₀ hx
      exact ⟨l, fun _ => hl⟩
    · exact ⟨l₀, fun h => absurd h hx⟩
  obtain ⟨iFun, hiFun⟩ : ∃ i : (IsLocalRing.ResidueField ↥A) → Fin r, ∀ x₀, (Pl l₀).eval x₀ ≠ 0 →
      (Pl (i x₀) * C ((Pl l₀).eval x₀) - Pl l₀ * C ((Pl (i x₀)).eval x₀)).rootMultiplicity x₀ = 1 :=
    ⟨fun x₀ => (hix_ex x₀).choose, fun x₀ => (hix_ex x₀).choose_spec⟩
  obtain ⟨iInf, hiInf, hiInf0⟩ := exists_nextToTop Pl (mAnnuli p) hspan hm hdeg l₀ hmon hdegl₀
  have hcInf : ∀ l, (Pl l).natDegree ≤ (Pl l₀).natDegree := fun l => by rw [hdegl₀]; exact hdeg l
  have hpole : ∀ l, -(((Pl l₀).natDegree - (Pl l₀).natDegree : ℕ) : ℤ) ≤ (cusp0 p).ord (goodFamilyZero Φ.toFamData l) :=
    fun l => (neg_nonpos.mpr (Int.natCast_nonneg _)).trans
      (Place.ord_nonneg_of_mem _ (hreg _ (cusp0_mem_dom Γ) l))

  obtain ⟨cQ, iQ, h1, h2, h3, h4, h5, h6, -⟩ :=
    ModularCurve.exists_chartData_of_lineResidues hFrat (zeroChart Γ) (goodFamilyZero Φ.toFamData) hint hunit
      (Pl l₀) Pl hD0 hR' (cusp0 p) (cusp0_mem_dom Γ) (placeMap_cusp0 Γ)
      (fun P hP _ l => hreg P hP l)
      (by
        intro P hP
        rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (IsLocalRing.ResidueField ↥A)
            ((zeroChart Γ).placeMap P) with ⟨x₀, hx⟩ | h
        · exact Or.inl ⟨x₀, hx, hDx P hP x₀ hx⟩
        · exact Or.inr h)
      (by
        intro f hf hres E hE
        refine (mapDomain_filter_apply_congr (zeroChart Γ).placeMap E _ _ (fun W => W ∈ (zeroChart Γ).dom)
          (decQ := Classical.decPred _) (fun a ha => ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩)).trans ?_
        exact (zeroChart Γ).mapDomain_placeMap ⟨f, hf⟩ hres _
          (fun P hP => by simp only [Finsupp.filter_apply, if_pos hP, hE])
          (fun P hP => by simp only [Finsupp.filter_apply, if_neg hP]) _ hnodeInf)
      (fun _ => l₀) iFun Finset.univ
      (fun P hP x₀ hx => hDx P hP x₀ hx)
      (fun P hP x₀ hx => hiFun x₀ (hDx P hP x₀ hx))
      (fun P hP Q hQ x₀ y₀ hx hy hxy => exists_eval_minor_ne Pl (mAnnuli p) hspan hm l₀ x₀ y₀ (hDx P hP x₀ hx) hxy)
      (fun P hP x₀ hx => ⟨l₀, Finset.mem_univ _, hDx P hP x₀ hx⟩)
      l₀ iInf hcInf le_rfl (Finset.mem_univ _) hpole hiInf hiInf0
      (fun P hP x₀ hx => exists_eval_coeff_minor_ne Pl (mAnnuli p) hspan hm l₀ hmon hdegl₀ x₀ (hDx P hP x₀ hx))
  exact ⟨hint, cQ, iQ, h1, h2, h3, h4, h5, h6⟩

end ModularCurve.MultCovering.P2Mcd0

open _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne.ModularCurve.MultCovering in
theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∃ (hint : ∀ i, goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers)
      (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
        → Fin r),
      (∀ P ∈ (zeroChart Γ).dom, P.IsRational ∧ ((zeroChart Γ).placeMap P).IsRational) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)), hint _⟩
          ≠ 0) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ (zeroChart Γ).integers) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ P.toValuationSubring) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        ∀ hmem : goodFamilyZero Φ.toFamData (iQ ((zeroChart Γ).placeMap P))
            * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
              ∈ (zeroChart Γ).integers,
        ((zeroChart Γ).placeMap P).ord ((zeroChart Γ).residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
              (((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (zeroChart Γ).placeMap P ≠ (zeroChart Γ).placeMap Q →
        ∀ (hmP : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
                ∈ (zeroChart Γ).integers)
          (hmQ : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap Q)))⁻¹
                ∈ (zeroChart Γ).integers),
        ∃ i j, ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP i⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ j⟩)
          ≠ ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP j⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ i⟩)) :=
  ModularCurve.MultCovering.P2Mcd0.zeroChart_chartData p A hA Γ Φ hw1

end S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne
end P2MW
export P2MW.S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne (solution)
