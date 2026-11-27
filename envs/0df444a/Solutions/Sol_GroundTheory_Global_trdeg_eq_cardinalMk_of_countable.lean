-- Prove2me | solution 1 for GroundTheory.Global.trdeg_eq_cardinalMk_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:10.354584+00:00
-- url     : https://prove2.me/submissions/6853c0f1-84c8-4281-9a5b-402849766bdf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis

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
open Cardinal Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
namespace GroundTheory.Global
theorem _root_.solution (F : Type*) [Field F] [Algebra F Ω] [Countable F]
    (hΩ : ℵ₀ < #Ω) : Algebra.trdeg F Ω = #Ω := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F Ω
  rw [← hs.cardinalMk_eq_trdeg]
  simpa using (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs
    Cardinal.mk_le_aleph0 hΩ).symm
end GroundTheory.Global
