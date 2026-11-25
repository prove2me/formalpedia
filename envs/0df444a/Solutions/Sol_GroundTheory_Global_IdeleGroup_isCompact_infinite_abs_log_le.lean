-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.isCompact_infinite_abs_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:23.003788+00:00
-- url     : https://prove2.me/submissions/42f6bfa2-244c-4431-a5c2-36405f1e9043

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isCompact_units_abs_log_le

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
omit [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (M : ℝ) :
    IsCompact {y : (InfiniteAdeleRing K)ˣ |
      ∀ w : InfinitePlace K, |Real.log ‖(y : InfiniteAdeleRing K) w‖| ≤ M} := by
  let p := (ContinuousMulEquiv.piUnits :
    (InfiniteAdeleRing K)ˣ ≃ₜ* ∀ w : InfinitePlace K, (w.Completion)ˣ)
  have hc : IsCompact ((p ⁻¹' Set.univ.pi fun w ↦
      {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M}) : Set (InfiniteAdeleRing K)ˣ) :=
    p.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun w ↦ isCompact_units_abs_log_le K w M)
  convert hc using 1
  ext y
  exact ⟨fun hy w _ ↦ hy w, fun hy w ↦ hy w (Set.mem_univ w)⟩
end GroundTheory.Global.IdeleGroup
