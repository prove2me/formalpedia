-- Prove2me | solution 1 for GroundTheory.LocalField.valuation_algebraMap_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:22.957057+00:00
-- url     : https://prove2.me/submissions/221308e0-9702-4e98-87b6-cd0c1048aa4a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice

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
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
omit [FiniteDimensional K L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
namespace GroundTheory.LocalField
theorem _root_.solution {π : 𝒪[K]} (hπ : Irreducible π) :
    valuation L (algebraMap K L (π : K)) < 1 :=
  (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) _).mpr
    (valuation_lt_one_of_mem_maximalIdeal ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit))
end GroundTheory.LocalField
