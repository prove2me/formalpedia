-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_units_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:17.83312+00:00
-- url     : https://prove2.me/submissions/7a3b7c0d-5bb1-4b08-88b4-d14451ca7817

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalClassFormation_ExtensionEmbeddingOfIsRealAlgebraMap
import Theorems.Thm_GroundTheory_ProfCoh_exists_units_neg_iff_mem

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
theorem _root_.solution (ε : {v : InfinitePlace K // v.IsReal} → ℤˣ) :
    ∃ a : Kˣ, ∀ v : {v : InfinitePlace K // v.IsReal},
      (SignType.sign (embedding_of_isReal v.2 (a : K)) : ℤ) = (ε v : ℤ) := by
  obtain ⟨a, ha⟩ := exists_units_neg_iff_mem {v | ε v = -1}
  refine ⟨a, fun v => ?_⟩
  rcases Int.units_eq_one_or (ε v) with hε | hε
  · have hpos : 0 < embedding_of_isReal v.2 (a : K) := (ha v).2.2 (by simp [hε])
    rw [sign_pos hpos, hε]
    rfl
  · have hneg : embedding_of_isReal v.2 (a : K) < 0 := (ha v).1.2 hε
    rw [sign_neg hneg, hε]
    rfl
end GroundTheory.ProfCoh
