-- Prove2me | solution 1 for GlobalTheory.exists_completeOrthogonalIdempotents_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:52.637422+00:00
-- url     : https://prove2.me/submissions/01254b20-f656-4dbd-be16-5b477b1aa2f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_exists_idempotent_notMem_iff_of_henselian
import Theorems.Thm_GlobalTheory_idempotent_eq_of_forall_isMaximal

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
theorem _root_.solution (R S : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] :
    ∃ e : MaximalSpectrum S → S, CompleteOrthogonalIdempotents e ∧
      ∀ (q : MaximalSpectrum S) (n : Ideal S), n.IsMaximal → (e q ∉ n ↔ n = q.asIdeal) := by
  classical
  choose e he H using fun q : MaximalSpectrum S ↦
    have := q.isMaximal; exists_idempotent_notMem_iff_of_henselian R q.asIdeal
  have horth : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij ↦ idempotent_eq_of_forall_isMaximal ((he i).mul (he j)) .zero
      fun n hn ↦ ?_⟩
    simp only [zero_mem, iff_true, hn.isPrime.mul_mem_iff_mem_or_mem]
    by_contra! h
    exact hij (MaximalSpectrum.ext (((H i n hn).1 h.1).symm.trans ((H j n hn).1 h.2)))
  refine ⟨e, ⟨horth, idempotent_eq_of_forall_isMaximal horth.isIdempotentElem_sum .one
    fun n hn ↦ ?_⟩, H⟩
  have h1 : (1 : S) ∉ n := (Ideal.ne_top_iff_one _).1 hn.ne_top
  simp only [h1, iff_false]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨n, hn⟩), Submodule.add_mem_iff_left,
    H _ n hn]
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  by_contra h
  exact (Finset.mem_erase.1 hi).1 (MaximalSpectrum.ext ((H i n hn).1 h).symm)
end GlobalTheory
