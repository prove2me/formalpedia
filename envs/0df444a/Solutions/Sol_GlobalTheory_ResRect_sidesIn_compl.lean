-- Prove2me | solution 1 for GlobalTheory.ResRect.sidesIn_compl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:27.298923+00:00
-- url     : https://prove2.me/submissions/afb6ac76-55be-4be6-8f91-991d4fb8c632

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ResRect
namespace GlobalTheory.ResRect
theorem _root_.solution {a b c d : ℝ} {p : ℂ} (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im)
    (h4 : p.im < d) : SidesIn a b c d {p}ᶜ := by
  refine ⟨fun x _ hx => ?_, fun x _ hx => ?_, fun x _ hx => ?_, fun x _ hx => ?_⟩
  · have := congrArg Complex.im (Set.mem_singleton_iff.1 hx); simp at this; linarith
  · have := congrArg Complex.im (Set.mem_singleton_iff.1 hx); simp at this; linarith
  · have := congrArg Complex.re (Set.mem_singleton_iff.1 hx); simp at this; linarith
  · have := congrArg Complex.re (Set.mem_singleton_iff.1 hx); simp at this; linarith
end GlobalTheory.ResRect
