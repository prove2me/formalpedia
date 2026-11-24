-- Prove2me | solution 1 for GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:45:06.646036+00:00
-- url     : https://prove2.me/submissions/56e5b7ab-8b4f-4552-aebd-8d50343acc29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLZerosEqPrimitiveCharacterZeros

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open scoped Classical
namespace GlobalTheory.Lin
namespace _root_.GlobalTheory.Lin
theorem _root_.solution :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
      (LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0) ∧
        _root_.GlobalTheory.Lin.ord χ s = _root_.GlobalTheory.Lin.ord χ.primitiveCharacter s := by
  intro q _ χ s hs hχs
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set E : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z))
    with hE
  have hform : ∀ z, (χ.primitiveCharacter ≠ 1 ∨ z ≠ 1) →
      LFunction χ z = LFunction χ.primitiveCharacter z * E z := by
    intro z hz
    have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hz
    rwa [changeLevel_primitiveCharacter] at h
  have hprim : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with h | h
    · left
      intro h1
      apply h
      calc χ = changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
            (changeLevel_primitiveCharacter χ).symm
        _ = 1 := by rw [h1, map_one]
    · exact Or.inr h
  have hEne : E s ≠ 0 := by
    rw [hE]
    refine Finset.prod_ne_zero_iff.2 (fun p hp => ?_)
    have hp1 : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
    have hlt : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
      calc _ ≤ 1 * (p : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right (norm_le_one _ _) (by positivity)
        _ < 1 := by
            rw [one_mul]
            exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp1) (by linarith)
    intro h0
    rw [sub_eq_zero] at h0
    rw [← h0, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hEd : Differentiable ℂ E := by
    have h : Differentiable ℂ (∏ p ∈ q.primeFactors,
        fun z : ℂ => 1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z)) :=
      Differentiable.finset_prod (fun p hp => by
        have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
        fun_prop (disch := exact Or.inl hp0))
    rw [hE]
    convert h using 1
    ext z
    simp [Finset.prod_apply]
  have hEa : AnalyticAt ℂ E s := hEd.analyticAt s
  have hLa : AnalyticAt ℂ (LFunction χ.primitiveCharacter) s := by
    by_cases h1 : χ.primitiveCharacter = 1
    · have hs1 : s ≠ 1 := hprim.resolve_left (not_not.2 h1)
      exact DifferentiableOn.analyticAt (s := {z | z ≠ 1})
        (fun z hz => (differentiableAt_LFunction _ z (Or.inl hz)).differentiableWithinAt)
        (isOpen_ne.mem_nhds hs1)
    · exact (differentiable_LFunction h1).analyticAt s
  have hev : LFunction χ =ᶠ[𝓝 s] LFunction χ.primitiveCharacter * E := by
    rcases hprim with h1 | h1
    · exact Eventually.of_forall (fun z => hform z (Or.inl h1))
    · filter_upwards [isOpen_ne.mem_nhds h1] with z hz using hform z (Or.inr hz)
  refine ⟨?_, ?_⟩
  · rw [hform s hprim, mul_eq_zero]
    simp [hEne]
  · show (analyticOrderAt _ s).toNat = (analyticOrderAt _ s).toNat
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hLa hEa,
      analyticOrderAt_eq_zero.2 (Or.inr hEne), add_zero]
end _root_.GlobalTheory.Lin
end GlobalTheory.Lin
