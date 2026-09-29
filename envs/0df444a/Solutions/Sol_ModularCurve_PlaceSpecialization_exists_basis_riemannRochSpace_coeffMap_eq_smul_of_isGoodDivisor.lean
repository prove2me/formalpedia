-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_basis_riemannRochSpace_coeffMap_eq_smul_of_isGoodDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f2088729-7e39-5c18-88ed-e5edb9029c21

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
import Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidal
import Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidalSnd
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_basis_riemannRochSpace_coeffMap_eq_smul_of_isGoodDivisor
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace FltWs24
namespace Hint

theorem exists_coeffMap_subtype_eq {L : Type*} [Field L] (A : ValuationSubring L)
    (x : LaurentSeries L) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    ∃ y : LaurentSeries A, coeffMap A.subtype y = x := by
  refine ⟨⟨fun n => ⟨x.coeff n, hx n⟩, ?_⟩, ?_⟩
  · convert x.isPWO_support' using 1
    ext n
    simp only [Function.mem_support, ne_eq]
    rw [← ZeroMemClass.coe_eq_zero]
  · ext n
    rfl

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem frickeInvolutionBar_mul_self :
    frickeInvolutionBar (1 * q) * frickeInvolutionBar (1 * q) = 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  refine AlgEquiv.ext fun y => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
  exact frickeInvolutionBar_frickeInvolutionBar (1 * q) y

theorem frickeInvolutionBar_jqFun :
    frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have key : ∀ (n : ℕ) [NeZero n], n = q → IsFrickeAutFull n (frickeInvolutionFull n) := by
    rintro n _ rfl
    exact isFrickeAutFull_frickeInvolutionFull_prime _
  have hFA : IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) := key (1 * q) (one_mul q)
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) hFA (1 * q) 1 (mul_one _)
  apply Subtype.ext
  have h' : ((frickeInvolutionBar (1 * q) (jqFun (q := q)) : modularFunctionFieldBar (1 * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) :=
    congrArg Subtype.val h
  rw [qExpand_one_apply] at h'
  exact h'

theorem exists_ord_jFun_sub_pos (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))} (hgood : P.IsGoodDivisor D)
    {f : modularFunctionFieldBar (1 * q)} (hf : f ∈ riemannRochSpace D) (hf0 : f ≠ 0)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : W.ord f < 0) :
    ∃ a : A, 0 < W.ord (jFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) := by
  have h1 := ((mem_riemannRochSpace_iff.mp hf) W).resolve_left hf0
  have hDW : D W ≠ 0 := by omega
  have htype := hgood W (Finsupp.mem_support_iff.mpr hDW)
  have hnc : ¬ P.IsCuspidal W := by
    intro hc
    have h2 := not_isStrictType_of_isCuspidal P W hc
    rcases htype with h | h
    · exact h2.1 h
    · exact h2.2 h
  unfold PlaceSpecialization.IsCuspidal at hnc
  push_neg at hnc
  exact hnc

theorem exists_ord_jqFun_sub_pos (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))} (hgood : P.IsGoodDivisor D)
    {f : modularFunctionFieldBar (1 * q)} (hf : f ∈ riemannRochSpace D) (hf0 : f ≠ 0)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : W.ord f < 0) :
    ∃ a : A, 0 < W.ord (jqFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) := by
  have h1 := ((mem_riemannRochSpace_iff.mp hf) W).resolve_left hf0
  have hDW : D W ≠ 0 := by omega
  have htype := hgood W (Finsupp.mem_support_iff.mpr hDW)
  have hnc : ¬ P.IsCuspidal' W := by
    intro hc
    have h2 := not_isStrictType_of_isCuspidalSnd P W hc
    rcases htype with h | h
    · exact h2.1 h
    · exact h2.2 h
  unfold PlaceSpecialization.IsCuspidal' at hnc
  push_neg at hnc
  exact hnc

theorem main (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hgood : P.IsGoodDivisor D)
    [FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D)] :
    ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace D)) → modularFunctionFieldBar (1 * q),
      (∀ i, b i ∈ riemannRochSpace D) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((frickeInvolutionBar (1 * q) (b i) :
                modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))) := by
  classical
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  have B : Module.Basis (Fin (Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace D))) (AlgebraicClosure ℚ)
      (riemannRochSpace D) := Module.finBasis (AlgebraicClosure ℚ) (riemannRochSpace D)
  have hbli : LinearIndependent (AlgebraicClosure ℚ) ((riemannRochSpace D).subtype ∘ B) :=
    B.linearIndependent.map' _ (Submodule.ker_subtype _)
  refine ⟨(riemannRochSpace D).subtype ∘ B, fun i => (B i).2, hbli, fun i => ⟨?_, ?_⟩⟩
  ·
    have hf0 : ((riemannRochSpace D).subtype ∘ B) i ≠ 0 := fun h =>
      B.ne_zero i (Subtype.ext h)
    obtain ⟨c, hc0, hc⟩ := exists_forall_coeff_smul_mem_of_forall_ord_neg A (1 * q) _ hf0
      (fun W hW => exists_ord_jFun_sub_pos P hgood (B i).2 hf0 W hW)
    obtain ⟨y, hy⟩ := exists_coeffMap_subtype_eq A _ hc
    exact ⟨c, y, hc0, hy⟩
  ·
    have hf0 : ((riemannRochSpace D).subtype ∘ B) i ≠ 0 := fun h =>
      B.ne_zero i (Subtype.ext h)
    have hwf0 : frickeInvolutionBar (1 * q) (((riemannRochSpace D).subtype ∘ B) i) ≠ 0 := (map_ne_zero _).mpr hf0
    obtain ⟨c, hc0, hc⟩ := exists_forall_coeff_smul_mem_of_forall_ord_neg A (1 * q)
      (frickeInvolutionBar (1 * q) (((riemannRochSpace D).subtype ∘ B) i)) hwf0 (by
        intro W hW
        set W' := frickeInvolutionBar (1 * q) • W with hW'
        have hWW : frickeInvolutionBar (1 * q) • W' = W := by
          rw [hW', smul_smul, frickeInvolutionBar_mul_self, one_smul]
        have h1 : W'.ord (((riemannRochSpace D).subtype ∘ B) i) < 0 := by
          rw [← hWW, Place.ord_smul] at hW
          exact hW
        obtain ⟨a, ha⟩ := exists_ord_jqFun_sub_pos P hgood (B i).2 hf0 W' h1
        refine ⟨a, ?_⟩
        show 0 < W.ord (jFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))
        have heq : jFun (q := q)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)
            = frickeInvolutionBar (1 * q) (jqFun (q := q)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) := by
          rw [map_sub, frickeInvolutionBar_jqFun, AlgEquiv.commutes]
        rw [heq, ← hWW, Place.ord_smul]
        exact ha)
    obtain ⟨y, hy⟩ := exists_coeffMap_subtype_eq A _ hc
    exact ⟨c, y, hc0, hy⟩

end FltWs24.Hint

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hgood : P.IsGoodDivisor D)
    [FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D)] :
    ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace D)) → modularFunctionFieldBar (1 * q),
      (∀ i, b i ∈ riemannRochSpace D) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((frickeInvolutionBar (1 * q) (b i) :
                modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))) :=
  FltWs24.Hint.main P D hgood

end S_ModularCurve_PlaceSpecialization_exists_basis_riemannRochSpace_coeffMap_eq_smul_of_isGoodDivisor
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_basis_riemannRochSpace_coeffMap_eq_smul_of_isGoodDivisor (solution)
