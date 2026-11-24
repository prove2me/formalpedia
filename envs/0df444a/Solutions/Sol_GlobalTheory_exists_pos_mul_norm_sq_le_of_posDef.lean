-- Prove2me | solution 1 for GlobalTheory.exists_pos_mul_norm_sq_le_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:45:56.445289+00:00
-- url     : https://prove2.me/submissions/483f5b02-eb97-46c7-821b-745d1587cfcb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Module TensorProduct
namespace GlobalTheory
section SecondDifference
variable {X A : Type*} [AddCommGroup X] [AddCommGroup A]
namespace HasConstSecondDiff
variable {f : X → A}
end HasConstSecondDiff
end SecondDifference
section Definite
private theorem continuous_quadraticForm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) : Continuous Q := by
  have h : Continuous fun v => (QuadraticMap.associated Q).toContinuousBilinearMap v v := by
    fun_prop
  exact h.congr fun v => QuadraticMap.associated_eq_self_apply ℝ Q v
end Definite
section RealExtension
variable {X : Type*} [AddCommGroup X]
example : HasConstSecondDiff (fun x : ℤ => ((x : ℝ) ^ 2 + 1)) ∧
    (∀ x : ℤ, (((-x : ℤ) : ℝ) ^ 2 + 1) = (x : ℝ) ^ 2 + 1) ∧
    Tendsto (fun x : ℤ => ((x : ℝ) ^ 2 + 1)) cofinite atTop := by
  refine ⟨fun a a' μ ν => ?_, fun x => by simp, tendsto_atTop_add_const_right _ _ ?_⟩
  · simp only [secondDiff]
    push_cast
    ring
  · have h : Tendsto (fun x : ℤ => |(x : ℝ)|) cofinite atTop := by
      rw [Int.cofinite_eq, tendsto_sup]
      exact ⟨tendsto_abs_atBot_atTop.comp (tendsto_intCast_atBot_iff.2 tendsto_id),
        tendsto_abs_atTop_atTop.comp tendsto_intCast_atTop_atTop⟩
    simpa [Function.comp_def] using (tendsto_pow_atTop two_ne_zero).comp h
end RealExtension
end GlobalTheory
end

set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V} (hQ : Q.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ Q v := by
  have := FiniteDimensional.proper_real V
  obtain ⟨c, hc, h⟩ := (isCompact_sphere (0 : V) 1).exists_forall_le'
    (continuous_quadraticForm Q).continuousOn (a := 0)
    (fun v hv => hQ v (by rintro rfl; simp at hv))
  refine ⟨c, hc, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have h₁ := h (‖v‖⁻¹ • v) (by simp [norm_smul, hn])
  rw [QuadraticMap.map_smul, smul_eq_mul] at h₁
  calc c * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * ‖v‖⁻¹ * Q v * ‖v‖ ^ 2 := by gcongr
    _ = Q v := by field_simp
end GlobalTheory
