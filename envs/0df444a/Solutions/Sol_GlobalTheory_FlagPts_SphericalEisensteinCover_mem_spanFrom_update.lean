-- Prove2me | solution 1 for GlobalTheory.FlagPts.SphericalEisensteinCover.mem_spanFrom_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:32:27.442938+00:00
-- url     : https://prove2.me/submissions/0596f043-e74c-44f3-8f6c-a3e5a16f79e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_spanFrom_update_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
theorem _root_.solution (f : ℕ → W) (N m : ℕ) (v : W) (h : m < N) :
    v ∈ spanFrom k (Function.update f m v) N m := by
  rw [spanFrom_update_self f N m v h]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
end GlobalTheory.FlagPts.SphericalEisensteinCover
