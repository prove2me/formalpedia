-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_isCompact_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:53:06.222416+00:00
-- url     : https://prove2.me/submissions/aa8a4677-dc46-4d16-91ef-9e36ac6d648f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionSiegel
import Theorems.Thm_GroundTheory_Global_exists_isCompact_forall_exists_sub_mem


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
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution :
    ∃ D : Set 𝔸[K], IsCompact D ∧ ∀ x : 𝔸[K], ∃ k : K, x + algebraMap K 𝔸[K] k ∈ D := by
  obtain ⟨C, hC, hx⟩ := exists_isCompact_forall_exists_sub_mem K
  refine ⟨C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)),
    hC.prod (isCompact_integralFiniteAdeles K), fun x => ?_⟩
  obtain ⟨k, hk⟩ := hx x
  exact ⟨-k, by rwa [map_neg, ← sub_eq_add_neg]⟩
end GroundTheory.Automorphic.Reduction
