-- Prove2me | solution 1 for GroundTheory.LocalField.vle_algEquiv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:48:13.633296+00:00
-- url     : https://prove2.me/submissions/d8d39a4e-5f11-4df8-af2e-01bce2e2e875

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Topology Filter
variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution (σ : L ≃ₐ[K] L) (x y : L) : σ x ≤ᵥ σ y ↔ x ≤ᵥ y :=
  vle_map_iff σ.toAlgHom x y
end GroundTheory.LocalField
