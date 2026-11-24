-- Prove2me | solution 1 for GlobalTheory.CubeFace.glue_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:41:26.360499+00:00
-- url     : https://prove2.me/submissions/3801dbe7-64f7-4e66-a3c8-d8f8fb472c48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_span_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace
namespace GlobalTheory.CubeFace
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {κ : Type*} (U : κ → Set E) (f : κ → E → ℂ)
    (hU : ∀ k, IsOpen (U k)) (hcov : ∀ x, ∃ k, x ∈ U k)
    (hf : ∀ k, DifferentiableOn ℂ (f k) (U k))
    (hagree : ∀ k k' x, x ∈ U k → x ∈ U k' → f k x = f k' x)
    {S : Set E} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ k x, ∀ l ∈ S, x ∈ U k → x + l ∈ U k ∧ f k (x + l) = f k x)
    (k k' : κ) (x y : E) (hx : x ∈ U k) (hy : y ∈ U k') : f k x = f k' y := by
  choose s hs using hcov
  have hG : ∀ k x, x ∈ U k → f (s x) x = f k x := fun k x hx => hagree _ _ _ (hs x) hx
  have hd : Differentiable ℂ (fun x => f (s x) x) := by
    intro x
    have h1 : DifferentiableAt ℂ (f (s x)) x :=
      (hf _).differentiableAt ((hU _).mem_nhds (hs x))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(hU _).mem_nhds (hs x)] with y hy using hG _ _ hy
  have := entire_apply_eq_of_periodic_of_span_real hd hS (fun x l hl => by
    obtain ⟨h1, h2⟩ := hper (s x) x l hl (hs x)
    rw [hG _ _ h1, h2]) x y
  rw [← hG k x hx, ← hG k' y hy]
  exact this
end GlobalTheory.CubeFace
