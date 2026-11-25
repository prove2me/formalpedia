-- Prove2me | solution 1 for GroundTheory.LocalField.minpoly_eq_map_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:21.483341+00:00
-- url     : https://prove2.me/submissions/9b6ae2fd-7992-49f6-afb1-65458b3c6b67

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein

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
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ
namespace GroundTheory.LocalField
theorem _root_.solution :
    minpoly K (ϖ : L) = (minpoly 𝒪[K] (ϖ : L)).map (algebraMap 𝒪[K] K) :=
  minpoly.isIntegrallyClosed_eq_field_fractions' K ((isIntegral_iff K L _).mpr ϖ.2)
end GroundTheory.LocalField
