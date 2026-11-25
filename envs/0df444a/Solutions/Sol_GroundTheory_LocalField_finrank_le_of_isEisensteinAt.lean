-- Prove2me | solution 1 for GroundTheory.LocalField.finrank_le_of_isEisensteinAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:20.435223+00:00
-- url     : https://prove2.me/submissions/f64d0c5e-e1c7-4cd0-8890-04884d230475

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_finrank_adjoin_le_of_isEisensteinAt

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
  {f : 𝒪[K][X]}
variable (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
  {α : L} (hα : aeval α f = 0)
include hf hn hα
variable (hgen : K⟮α⟯ = ⊤)
include hgen
omit hn
namespace GroundTheory.LocalField
theorem _root_.solution : Module.finrank K L ≤ f.natDegree := by
  rw [← IntermediateField.finrank_top', ← hgen]
  exact finrank_adjoin_le_of_isEisensteinAt hf hα
end GroundTheory.LocalField
