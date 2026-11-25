-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.abs_log_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:24:00.72675+00:00
-- url     : https://prove2.me/submissions/e2f225ff-19a2-43ac-b047-400695c5ea6b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {r M : ℝ} (hr : 0 < r) :
    |Real.log r| ≤ M ↔ Real.exp (-M) ≤ r ∧ r ≤ Real.exp M := by
  rw [abs_le, neg_le, ← Real.log_inv, Real.log_le_iff_le_exp (inv_pos.2 hr),
    Real.log_le_iff_le_exp hr, inv_le_comm₀ hr (Real.exp_pos _), Real.exp_neg]
end GroundTheory.Global.IdeleGroup
