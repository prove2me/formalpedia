-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.norm_mul_le_one_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:42.892952+00:00
-- url     : https://prove2.me/submissions/a4360abf-e321-4a9b-8ae8-519c93bf1c25

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {E : Type*} [NormedField E] {a a' b : E} (h : a * a' = 1)
    (hb : ‖b‖ ≤ ‖a‖) : ‖a' * b‖ ≤ 1 := by
  have ha : ‖a‖ * ‖a'‖ = 1 := by rw [← norm_mul, h, norm_one]
  rw [norm_mul]
  calc ‖a'‖ * ‖b‖ ≤ ‖a'‖ * ‖a‖ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = 1 := by rw [mul_comm, ha]
end GroundTheory.Automorphic.Reduction
