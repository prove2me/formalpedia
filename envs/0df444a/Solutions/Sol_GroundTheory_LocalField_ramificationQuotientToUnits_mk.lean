-- Prove2me | solution 1 for GroundTheory.LocalField.ramificationQuotientToUnits_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:09.021099+00:00
-- url     : https://prove2.me/submissions/5ffac8e5-4d03-4402-9c7a-3912d47acc67

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits

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
theorem _root_.solution (n : ℕ) (σ : lowerRamificationGroup K L n) :
    ramificationQuotientToUnits hϖ n (QuotientGroup.mk σ) = ramificationToUnits hϖ n σ :=
  rfl
end GroundTheory.LocalField
