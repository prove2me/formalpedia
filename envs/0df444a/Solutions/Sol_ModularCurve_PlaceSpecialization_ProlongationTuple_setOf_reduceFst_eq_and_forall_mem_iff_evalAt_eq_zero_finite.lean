-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1aa06979-2399-56d4-8bc1-d3aaa3bd6fc3

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N))
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) (h𝔮0 : 𝔮 ≠ ⊥) :
    Set.Finite {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) | (P.reduceFst V = w ∧
      ∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0)} := by
  classical

  obtain ⟨f, hf𝔮, hf0⟩ : ∃ f ∈ 𝔮, f ≠ 0 := by
    by_contra h
    push Not at h
    exact h𝔮0 ((Submodule.eq_bot_iff 𝔮).mpr h)
  have hfF : ((f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 :=
    fun h => hf0 (Subtype.ext h)

  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar ModularCurve.modularPolynomialFamily (N * q)
  obtain ⟨D, hD, -⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    ((f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) hfF
  refine (D.support.finite_toSet).subset ?_
  rintro V ⟨-, hker⟩

  have hev : V.evalAt ((f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = 0 := (hker f).mp hf𝔮
  have hrat : V.IsRational := by
    haveI := ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)
    exact (AlgebraicCurve.Place.isRational_iff_deg_eq_one V).2 (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed V)
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hD V]
  intro hord
  exact (V.evalAt_ne_zero hrat hfF hord) hev

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite (solution)
