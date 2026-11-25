-- Prove2me | solution 1 for GroundTheory.LocalField.exists_restrictNormal_eq_frobenius_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:51.455941+00:00
-- url     : https://prove2.me/submissions/65d4f25d-c671-4215-91e7-e953e216ceef

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℤ) :
    ∃ σ : Ω ≃ₐ[K] Ω,
      σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ^ n :=
  AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := maximalUnramifiedExtension K Ω) (E := Ω) _
end GroundTheory.LocalField
