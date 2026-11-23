-- Prove2me | solution 1 for GlobalTheory.Mem.PosDirichlet.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:04.390444+00:00
-- url     : https://prove2.me/submissions/1173180e-7597-483c-9112-1e9c292407c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
open GlobalTheory.Mem.PosDirichlet
namespace GlobalTheory.Mem.PosDirichlet
theorem _root_.solution {F G : ℂ → ℂ} (h : PosDirichlet F) (e : ∀ s : ℂ, 1 < s.re → F s = G s) :
    PosDirichlet G := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := h
  exact ⟨ι, w, N, hw, hN, fun s hs => e s hs ▸ h s hs⟩
end GlobalTheory.Mem.PosDirichlet
