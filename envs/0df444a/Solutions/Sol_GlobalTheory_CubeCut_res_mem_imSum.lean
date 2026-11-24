-- Prove2me | solution 1 for GlobalTheory.CubeCut.res_mem_imSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:41.335408+00:00
-- url     : https://prove2.me/submissions/b3e2e18d-dd51-4a25-b950-5f1fb8e92e43

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
variable {g : ℕ} {A B : Cube.{0} I K} (φ : Fin g → (A ⟶ B))
omit [LinearOrder I]
namespace GlobalTheory.CubeCut
theorem _root_.solution (k : ℕ) {s t : Finset I} (h : s ⊆ t) (x : B.obj s)
    (hx : x ∈ imSum φ k s) : Cube.res B h x ∈ imSum φ k t := by
  have key : imSum φ k s ≤ (imSum φ k t).comap (Cube.res B h) := by
    refine iSup₂_le fun j hj => ?_
    rintro _ ⟨a, rfl⟩
    rw [Submodule.mem_comap, ← Cube.app_res]
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (LinearMap.mem_range_self _ _))
  exact key hx
end GlobalTheory.CubeCut
