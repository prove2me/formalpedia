-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.mem_standardOpenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:29.106068+00:00
-- url     : https://prove2.me/submissions/b1727e7c-c818-4d36-a7fc-083aad8320c0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_integralAtFinite

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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {x : IdeleGroup K} :
    x ∈ standardOpenSubgroup K ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
  rw [standardOpenSubgroup, Submonoid.mem_units_iff, mem_integralAtFinite, mem_integralAtFinite,
    ← forall_and]
end GroundTheory.Global.IdeleGroup
