-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_units_neg_iff_mem_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:15.315669+00:00
-- url     : https://prove2.me/submissions/b4bfd26c-1c79-4939-adf7-7a778ce8deb6

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalClassFormation_ExtensionEmbeddingOfIsRealAlgebraMap
import Theorems.Thm_GroundTheory_ProfCoh_exists_units_neg_iff_mem
import Theorems.Thm_GroundTheory_ProfCoh_extensionEmbeddingOfIsReal_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.ProfCoh
theorem _root_.solution (S : Set {v : InfinitePlace K // v.IsReal}) :
    ∃ a : Kˣ, ∀ v : {v : InfinitePlace K // v.IsReal},
      (Completion.extensionEmbeddingOfIsReal v.2 (algebraMap K v.1.Completion (a : K)) < 0 ↔ v ∈ S) ∧
      (0 < Completion.extensionEmbeddingOfIsReal v.2 (algebraMap K v.1.Completion (a : K)) ↔ v ∉ S) := by
  obtain ⟨a, ha⟩ := exists_units_neg_iff_mem S
  exact ⟨a, fun v => by simpa only [extensionEmbeddingOfIsReal_algebraMap] using ha v⟩
end GroundTheory.ProfCoh
