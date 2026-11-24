-- Prove2me | solution 1 for GlobalTheory.OpTrace.finRankTrace_eq_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:25.223265+00:00
-- url     : https://prove2.me/submissions/bccb3091-9d0f-491e-a371-773ddada8e24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.OpTrace
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    {T : V →ₗ[ℂ] V} {T' : W →ₗ[ℂ] W} (h : ∀ v, e (T v) = T' (e v))
    [FiniteDimensional ℂ (LinearMap.range T)] :
    FiniteDimensional ℂ (LinearMap.range T') ∧ finRankTrace T' = finRankTrace T := by
  have hm : ∀ x ∈ LinearMap.range T, (e : V →ₗ[ℂ] W) x ∈ LinearMap.range T' := by
    rintro _ ⟨v, rfl⟩; exact ⟨e v, (h v).symm⟩
  let a : LinearMap.range T →ₗ[ℂ] LinearMap.range T' := (e : V →ₗ[ℂ] W).restrict hm
  let b : LinearMap.range T' →ₗ[ℂ] LinearMap.range T :=
    T.rangeRestrict ∘ₗ (e.symm : W →ₗ[ℂ] V) ∘ₗ (LinearMap.range T').subtype
  have ha : Function.Surjective a := by
    rintro ⟨_, w, rfl⟩
    exact ⟨⟨T (e.symm w), _, rfl⟩, Subtype.ext (by simpa [a] using h (e.symm w))⟩
  have := Module.Finite.of_surjective a ha
  refine ⟨this, ?_⟩
  have h1 : T'.restrict (fun x _ => LinearMap.mem_range_self T' x) = a ∘ₗ b := by
    ext x; simp [a, b, h]
  have h2 : T.restrict (fun x _ => LinearMap.mem_range_self T x) = b ∘ₗ a := by
    ext x; simp [a, b]
  rw [finRankTrace, finRankTrace, h1, h2, LinearMap.trace_comp_comm']
end GlobalTheory.OpTrace
