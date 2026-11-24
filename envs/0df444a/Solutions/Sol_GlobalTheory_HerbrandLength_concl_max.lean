-- Prove2me | solution 1 for GlobalTheory.HerbrandLength.concl_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:42.755696+00:00
-- url     : https://prove2.me/submissions/6fc9b0cd-19db-4eb8-aa5a-657eba964354

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum
import Theorems.Thm_GlobalTheory_HerbrandLength_loc_zero_of_ann
import Theorems.Thm_GlobalTheory_HerbrandLength_ker_eq_coker
import Theorems.Thm_GlobalTheory_HerbrandLength_ne_max

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HerbrandLength
open IsLocalRing
variable {A : Type} [CommRing A]
namespace GlobalTheory.HerbrandLength
theorem _root_.solution [IsLocalRing A] (b : A) (P : Finset (PrimeSpectrum A))
    (hP : ∀ p ∈ P, ringKrullDim (A ⧸ p.asIdeal) = 1 ∧ b ∉ p.asIdeal) :
    Concl b P (A ⧸ maximalIdeal A) := by
  have hlen : Module.length A (A ⧸ maximalIdeal A) = 1 :=
    Module.length_eq_one_iff.2
      (isSimpleModule_iff_isCoatom.2 (inferInstance : (maximalIdeal A).IsMaximal).out)
  have hfin : Module.length A (A ⧸ maximalIdeal A) ≠ ⊤ := by rw [hlen]; exact ENat.one_ne_top
  refine ⟨ne_top_of_le_ne_top hfin
    (Module.length_le_of_injective (LinearMap.ker _).subtype (Submodule.injective_subtype _)), ?_⟩
  rw [ker_eq_coker _ hfin, Finset.sum_eq_zero, add_zero]
  intro p hp
  have hnle : ¬ maximalIdeal A ≤ p.asIdeal := fun h =>
    ne_max p (hP p hp).1 (le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) h)
  obtain ⟨s, hsm, hsp⟩ := SetLike.not_le_iff_exists.1 hnle
  rw [loc_zero_of_ann p.asIdeal _ s hsp (fun x => ?_), zero_mul]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ hsm
end GlobalTheory.HerbrandLength
