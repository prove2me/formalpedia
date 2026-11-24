-- Prove2me | solution 1 for GlobalTheory.exists_equiv_inner_eq_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:41:33.186396+00:00
-- url     : https://prove2.me/submissions/08b56d74-3872-4577-94ef-adcea2e24f0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FourierInversionHaarSymmForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory FourierTransform
open GlobalTheory
open MeasureTheory FourierTransform
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : V ≃L[ℝ] E) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (hn : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ R : V ≃L[ℝ] E, ∀ x y, B x y = inner ℝ (T x) (R y) := by
  let φ : V → StrongDual ℝ E := fun y =>
    LinearMap.toContinuousLinearMap ((B.flip y).comp (T.symm : E →L[ℝ] V).toLinearMap)
  have hφ : ∀ y e, φ y e = B (T.symm e) y := fun _ _ => rfl
  let L : V →ₗ[ℝ] E :=
    { toFun := fun y => (InnerProductSpace.toDual ℝ E).symm (φ y)
      map_add' := fun y z => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext e
        simp [hφ]
      map_smul' := fun r y => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext e
        simp [hφ] }
  have hL : ∀ x y, inner ℝ (T x) (L y) = B x y := by
    intro x y
    rw [real_inner_comm]
    change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (φ y)) (T x) = _
    rw [InnerProductSpace.toDual_symm_apply, hφ, T.symm_apply_apply]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hn y
    intro x
    rw [hs, ← hL, hy, inner_zero_right]
  have hdim : Module.finrank ℝ V = Module.finrank ℝ E := T.toLinearEquiv.finrank_eq
  refine ⟨(LinearMap.linearEquivOfInjective L hinj hdim).toContinuousLinearEquiv, fun x y => ?_⟩
  rw [← hL]
  rfl
end _root_.GlobalTheory
end GlobalTheory
