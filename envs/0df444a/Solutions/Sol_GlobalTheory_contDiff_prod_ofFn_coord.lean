-- Prove2me | solution 1 for GlobalTheory.contDiff_prod_ofFn_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:54.821307+00:00
-- url     : https://prove2.me/submissions/d6b82fd7-4333-4b69-9c4f-1b7ebe2f07ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContDiffOfContinuousOneParameterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothOfFiniteDimensionalTranslationStable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type} [NormedRing A] [NormedAlgebra ℝ A] {ι : Type}
    (R : ι → ℝ → A) (hR : ∀ i, ContDiff ℝ ∞ (R i)) (k : ℕ) (I : Fin k → ι) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun a => R (I a) (t a)).prod := by
  induction k with
  | zero => simpa using contDiff_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    refine ContDiff.mul ((hR (I 0)).comp (contDiff_apply ℝ ℝ 0)) ?_
    have h : ContDiff ℝ ∞ fun (t : Fin (k + 1) → ℝ) (a : Fin k) => t a.succ :=
      contDiff_pi.2 fun a => contDiff_apply ℝ ℝ a.succ
    exact (ih fun a => I a.succ).comp h
end GlobalTheory
