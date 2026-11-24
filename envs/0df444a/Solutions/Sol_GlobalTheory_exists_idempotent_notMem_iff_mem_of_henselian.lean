-- Prove2me | solution 1 for GlobalTheory.exists_idempotent_notMem_iff_mem_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:39.083486+00:00
-- url     : https://prove2.me/submissions/45f4bec2-1afc-481d-8314-796df8d799ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_finite_maximalSpectrum_of_finite_of_isLocalRing
import Theorems.Thm_GlobalTheory_exists_idempotent_notMem_iff_of_henselian
import Theorems.Thm_GlobalTheory_one_sub_mem_iff_notMem_of_isIdempotentElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (T : Set (MaximalSpectrum S)) :
    ∃ e : S, IsIdempotentElem e ∧ ∀ n : MaximalSpectrum S, (e ∉ n.asIdeal ↔ n ∈ T) := by
  have := finite_maximalSpectrum_of_finite_of_isLocalRing R S
  induction T, T.toFinite using Set.Finite.induction_on with
  | empty => exact ⟨0, .zero, by simp⟩
  | @insert q T hq _ ih =>
    obtain ⟨e, he, H⟩ := ih
    have := q.isMaximal
    obtain ⟨d, hd, H'⟩ := exists_idempotent_notMem_iff_of_henselian R q.asIdeal
    refine ⟨1 - (1 - d) * (1 - e), (hd.one_sub.mul he.one_sub).one_sub, fun n ↦ ?_⟩
    have := n.isMaximal
    rw [one_sub_mem_iff_notMem_of_isIdempotentElem (hd.one_sub.mul he.one_sub), not_not,
      Ideal.IsPrime.mul_mem_iff_mem_or_mem inferInstance,
      one_sub_mem_iff_notMem_of_isIdempotentElem hd, one_sub_mem_iff_notMem_of_isIdempotentElem he,
      H, H' _ this, Set.mem_insert_iff, MaximalSpectrum.ext_iff]
end GlobalTheory
