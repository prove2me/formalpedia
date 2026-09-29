-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.hasValuation_jQFun_pow_of_isInftySide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/37bbbafb-bccc-5e38-969e-4f3eca4b0bdf

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_PlaceDepth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_pow_of_isInftySide
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace SolutionAux

private theorem hasValue_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

private theorem valuation_eq_one_of_red_eq_one {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (τ : A) (hred : red τ = 1) :
    A.valuation (τ : AlgebraicClosure ℚ) = 1 := by
  have hker : τ - 1 ∈ RingHom.ker red := by
    rw [RingHom.mem_ker, map_sub, map_one, hred, sub_self]
  have hmax : τ - 1 ∈ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) hker
  have hunit : IsUnit τ := by
    apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
    rw [← IsLocalRing.mem_maximalIdeal, ← neg_sub, Ideal.neg_mem_iff]
    exact hmax
  exact (A.valuation_eq_one_iff τ).mp hunit

end SolutionAux

open SolutionAux ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : IsInftySide P W)
    {γ : A.ValueGroup} (hj : W.HasValuation A (jFun N q) γ) :
    W.HasValuation A (jQFun N q) (γ ^ q) := by
  obtain ⟨-, τ, hred, hτ⟩ := hW
  obtain ⟨J, hJ, hJγ⟩ := hj
  have hjne : jFun N q ≠ 0 := by
    intro h
    apply jq_ne_zero
    have h' := congrArg Subtype.val h
    simpa [jFun] using h'
  have heq : jQFun N q = tInfty N q * jFun N q ^ q := by
    rw [tInfty, div_mul_cancel₀ _ (pow_ne_zero q hjne)]
  refine ⟨(τ : AlgebraicClosure ℚ) * J ^ q, ?_, ?_⟩
  · rw [heq]
    exact hτ.mul (hasValue_pow W hJ q)
  · rw [Valuation.map_mul, valuation_eq_one_of_red_eq_one red τ hred, one_mul,
      Valuation.map_pow, hJγ]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_pow_of_isInftySide
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_pow_of_isInftySide (solution)
