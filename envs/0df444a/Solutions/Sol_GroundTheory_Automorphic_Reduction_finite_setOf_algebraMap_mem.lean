-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.finite_setOf_algebraMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:53.468331+00:00
-- url     : https://prove2.me/submissions/a8b32a68-1f67-41dc-a010-41161c274c11

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Theorems.Thm_GroundTheory_Global_discreteTopology_principalSubgroup
import Theorems.Thm_GroundTheory_Global_isClosed_principalSubgroup


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
theorem _root_.solution {D : Set 𝔸[K]} (hD : IsCompact D) :
    {k : K | algebraMap K 𝔸[K] k ∈ D}.Finite := by
  have := discreteTopology_principalSubgroup K
  have hc : IsCompact ((Subtype.val : AdeleRing.principalSubgroup (𝓞 K) K → 𝔸[K]) ⁻¹' D) :=
    (isClosed_principalSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hD
  let f : K → AdeleRing.principalSubgroup (𝓞 K) K := fun k => ⟨algebraMap K 𝔸[K] k, k, rfl⟩
  have hf : Function.Injective f := fun a b h =>
    AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Subtype.val h)
  exact (hc.finite_of_discrete.preimage hf.injOn).subset fun k hk => hk
end GroundTheory.Automorphic.Reduction
