-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.finite_setOf_ratVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:42.82248+00:00
-- url     : https://prove2.me/submissions/894de776-bac2-41e4-a6bb-50290e862f52

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finite_setOf_algebraMap_mem

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
theorem _root_.solution {D : Set (Fin n → 𝔸[K])} (hD : IsCompact D) :
    {x : Fin n → K | ratVec x ∈ D}.Finite := by
  refine (Set.Finite.pi (t := fun i => {k : K | algebraMap K 𝔸[K] k ∈ (fun y => y i) '' D})
    fun i => finite_setOf_algebraMap_mem (hD.image (continuous_apply i))).subset ?_
  intro x hx i _
  exact ⟨ratVec x, hx, rfl⟩
end GroundTheory.Automorphic.Reduction
