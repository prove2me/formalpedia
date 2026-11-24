-- Prove2me | solution 1 for GlobalTheory.FlagPts.SphericalEisensteinCover.finrank_sup_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:57:37.983331+00:00
-- url     : https://prove2.me/submissions/9e7854e8-c281-4ceb-b6f6-e6edef0cd460

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell

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
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
theorem _root_.solution [FiniteDimensional k W] (G : Submodule k W) (v : W) (hv : v ∉ G) :
    finrank k (G ⊔ k ∙ v : Submodule k W) = finrank k G + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ G.zero_mem)
  have h := Submodule.finrank_sup_add_finrank_inf_eq G (k ∙ v)
  rw [((Submodule.disjoint_span_singleton' hv0).2 hv).eq_bot, finrank_bot, add_zero,
    finrank_span_singleton hv0] at h
  exact h
end GlobalTheory.FlagPts.SphericalEisensteinCover
