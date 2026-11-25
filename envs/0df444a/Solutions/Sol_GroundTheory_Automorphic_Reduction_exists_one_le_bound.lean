-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_one_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:36:47.8039+00:00
-- url     : https://prove2.me/submissions/e5b22874-3574-482a-8319-8bd9f010187f

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
theorem _root_.solution {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsCompact C)
    {f : X → ℝ} (hf : Continuous f) : ∃ m : ℝ, 1 ≤ m ∧ ∀ x ∈ C, f x ≤ m := by
  obtain ⟨m, hm⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max m 1, le_max_right _ _, fun x hx =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hm x hx).trans (le_max_left _ _))⟩
end GroundTheory.Automorphic.Reduction
