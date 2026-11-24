-- Prove2me | solution 1 for GlobalTheory.CubeCut.exactMod_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:21.996289+00:00
-- url     : https://prove2.me/submissions/46ca27c3-cef0-4520-a660-b4e9bf569210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence
import Theorems.Thm_GlobalTheory_cubeComplex_exactAt_succ_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory GlobalTheory
open GlobalTheory
open GlobalTheory.CubeCut
variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]
namespace GlobalTheory.CubeCut
theorem _root_.solution {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (hJ : ∀ s, J s = ⊥) (h : ∀ p, (cubeComplex A).ExactAt p) : ExactMod A J := by
  refine ⟨fun x hx s => ?_, fun p x hx => ?_⟩
  · have h0 : Cube.d A 0 x = 0 := funext fun s => by simpa [hJ] using hx s
    have h1 := (cubeComplex_exactAt_zero_iff' A).1 (h 0) (h0.trans (map_zero _).symm)
    simp [h1, hJ]
  · have h0 : Cube.d A (p + 1) x = 0 := funext fun s => by simpa [hJ] using hx s
    obtain ⟨y, hy⟩ := ((cubeComplex_exactAt_succ_iff A p).1 (h (p + 1)) x).1 h0
    exact ⟨y, fun s => by simp [hy, hJ]⟩
end GlobalTheory.CubeCut
