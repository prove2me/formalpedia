-- Prove2me | solution 1 for GlobalTheory.NormCompat.NormCont.pow_card_mul_prod_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:35.37437+00:00
-- url     : https://prove2.me/submissions/a1b69d95-1251-4c8b-a22c-0ca193519f37

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.NormCont
namespace GlobalTheory.NormCompat.NormCont
theorem _root_.solution {Ω : Type} [CommRing Ω] (A : Subring Ω) {ι : Type} [DecidableEq ι]
    (s : Finset ι) (a d : Ω) (ha : a ∈ A) (hd : d ∈ A) (x y : ι → Ω) (hy : ∀ i ∈ s, y i ∈ A)
    (hxy : ∀ i ∈ s, a * x i = d * y i) :
    ∃ β ∈ A, a ^ s.card * ∏ i ∈ s, (1 + x i) = a ^ s.card + d * β := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, A.zero_mem, by simp⟩
  | insert j s hj ih =>
    obtain ⟨β, hβ, h⟩ := ih (fun i hi => hy i (Finset.mem_insert_of_mem hi))
      (fun i hi => hxy i (Finset.mem_insert_of_mem hi))
    have hyj := hy j (Finset.mem_insert_self j s)
    refine ⟨y j * a ^ s.card + a * β + d * y j * β, ?_, ?_⟩
    · exact A.add_mem (A.add_mem (A.mul_mem hyj (A.pow_mem ha _)) (A.mul_mem ha hβ))
        (A.mul_mem (A.mul_mem hd hyj) hβ)
    · rw [Finset.card_insert_of_notMem hj, Finset.prod_insert hj, pow_succ]
      have e := hxy j (Finset.mem_insert_self j s)
      calc a ^ s.card * a * ((1 + x j) * ∏ i ∈ s, (1 + x i))
          = (a + a * x j) * (a ^ s.card * ∏ i ∈ s, (1 + x i)) := by ring
        _ = (a + d * y j) * (a ^ s.card + d * β) := by rw [e, h]
        _ = _ := by ring
end GlobalTheory.NormCompat.NormCont
