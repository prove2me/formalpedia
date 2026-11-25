-- Prove2me | solution 1 for GroundTheory.LocalField.restrictNormal_eq_frobenius_zpow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:31.468994+00:00
-- url     : https://prove2.me/submissions/96d1300a-4928-4245-b2cb-17ea8c7543ce

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
variable {K Ω}
namespace GroundTheory.LocalField
theorem _root_.solution (σ : Ω ≃ₐ[K] Ω) (n : ℤ) :
    σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ^ n ↔
      unramifiedDegree K Ω σ = Multiplicative.ofAdd (n : ℤ̂) := by
  rw [← unramifiedDegree_restrictNormal, ← unramifiedDegree_maximalUnramifiedExtensionFrobenius_zpow K Ω n]
  exact unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm
end GroundTheory.LocalField
