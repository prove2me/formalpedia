-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.modulus_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:24:49.870485+00:00
-- url     : https://prove2.me/submissions/fdb892a9-078d-424d-9b1b-ed1029973d01

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F} {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (u : Fˣ) : modulus (u : F) = distribHaarChar F u := by
  rw [modulus, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_neg u.ne_zero]
  congr 1
  ext
  rfl
end GroundTheory.Automorphic.Measures
