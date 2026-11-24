-- Prove2me | solution 1 for GlobalTheory.surjective_algebraMap_localization_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:50:07.925733+00:00
-- url     : https://prove2.me/submissions/c4a0b882-7ffe-42c3-8b59-2cc4e4586088

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
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
    (q : Ideal S) [hq : q.IsMaximal] :
    Function.Surjective (algebraMap S (Localization.AtPrime q)) := by
  obtain ⟨e, he, H⟩ := exists_idempotent_notMem_iff_of_henselian R q
  have heq : e ∉ q := (H q hq).2 rfl
  have he1 : algebraMap S (Localization.AtPrime q) e = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit
      (IsLocalization.map_units _ (⟨e, heq⟩ : q.primeCompl))).1 (he.map _)
  intro y
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl y
  have hu : IsUnit (e * s + (1 - e)) := by
    by_contra h
    obtain ⟨n, hn, hmem⟩ := exists_max_ideal_of_mem_nonunits h
    by_cases hen : e ∈ n
    · rw [Submodule.add_mem_iff_right _ (Ideal.mul_mem_right _ _ hen),
        one_sub_mem_iff_notMem_of_isIdempotentElem he] at hmem
      exact hmem hen
    · rw [Submodule.add_mem_iff_left _ ((one_sub_mem_iff_notMem_of_isIdempotentElem he n).2 hen),
        (H n hn).1 hen] at hmem
      exact (hq.isPrime.mem_or_mem hmem).elim heq s.2
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  refine ⟨a * v, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have := congr(algebraMap S (Localization.AtPrime q) $hv)
  simp only [map_mul, map_add, map_sub, map_one, he1, one_mul, sub_self, add_zero] at this
  rw [map_mul, mul_assoc, this, mul_one]
end GlobalTheory
