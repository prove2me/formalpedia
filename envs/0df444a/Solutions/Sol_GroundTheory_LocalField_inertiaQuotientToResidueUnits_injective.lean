-- Prove2me | solution 1 for GroundTheory.LocalField.inertiaQuotientToResidueUnits_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:30.370614+00:00
-- url     : https://prove2.me/submissions/f26fcf0c-44c1-478f-bd85-53aaebc42af1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure

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
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ
namespace GroundTheory.LocalField
theorem _root_.solution :
    Function.Injective (inertiaQuotientToResidueUnits (K := K) hϖ) :=
  fun _ _ hab ↦ (MulEquiv.injective _) (QuotientGroup.kerLift_injective (inertiaToResidueUnits hϖ) hab)
end GroundTheory.LocalField
