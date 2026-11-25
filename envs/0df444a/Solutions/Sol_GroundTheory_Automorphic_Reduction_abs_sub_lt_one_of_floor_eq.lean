-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.abs_sub_lt_one_of_floor_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:42.847624+00:00
-- url     : https://prove2.me/submissions/eaf5e4df-c664-4a87-b1aa-9bac6a502a41

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : ⌊x⌋₊ = ⌊y⌋₊) :
    |x - y| < 1 := by
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one x
  have h3 := Nat.floor_le hy
  have h4 := Nat.lt_floor_add_one y
  rw [h] at h1 h2
  rw [abs_lt]
  constructor <;> linarith
end GroundTheory.Automorphic.Reduction
