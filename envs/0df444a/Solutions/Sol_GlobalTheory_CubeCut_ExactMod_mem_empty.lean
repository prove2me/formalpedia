-- Prove2me | solution 1 for GlobalTheory.CubeCut.ExactMod.mem_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:51.158926+00:00
-- url     : https://prove2.me/submissions/581a8d8b-19f2-4e4e-8c23-e2622ab3ae7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence

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
namespace ExactMod
theorem _root_.solution {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (h : ExactMod A J) (y : A.obj ∅)
    (hy : ∀ a : I, Cube.res A (Finset.empty_subset {a}) y ∈ J {a}) : y ∈ J ∅ := by
  have h1 := h.1 ((Cube.termZeroEquiv A).symm y) (fun s => by
    rw [Cube.d_zero_apply, LinearEquiv.apply_symm_apply, Cube.aug_apply]
    obtain ⟨s, hs⟩ := s
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
    exact hy a) ⟨∅, rfl⟩
  simpa using h1
end ExactMod
end GlobalTheory.CubeCut
