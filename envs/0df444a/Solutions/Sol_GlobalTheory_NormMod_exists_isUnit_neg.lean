-- Prove2me | solution 1 for GlobalTheory.NormMod.exists_isUnit_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:39.675801+00:00
-- url     : https://prove2.me/submissions/efdaa0e6-a619-483a-83ae-90ecc13900c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf
import Theorems.Thm_GlobalTheory_NormMod_exists_pow_sub_one_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormMod
variable {R : Type*} [CommRing R] [Finite R]
namespace GlobalTheory.NormMod
theorem _root_.solution (σ : R →+* R) (htop : Ideal.span {a | σ a = -a} = ⊤) :
    ∃ δ, σ δ = -δ ∧ IsUnit δ := by
  classical
  have key : ∀ s : Finset R, (∀ a ∈ s, σ a = -a) →
      ∃ δ, σ δ = -δ ∧ ∀ P : Ideal R, P.IsPrime → δ ∈ P → ∀ a ∈ s, a ∈ P := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp, by simp⟩
    | insert b s _ ih =>
      intro hs
      obtain ⟨δ, hδ, hP⟩ := ih fun a ha => hs a (Finset.mem_insert_of_mem ha)
      have hb := hs b (Finset.mem_insert_self _ _)
      obtain ⟨k, hk, hδk⟩ := exists_pow_sub_one_mem (δ ^ 2)
      refine ⟨δ + (1 - (δ ^ 2) ^ k) * b, ?_, fun P hp h => ?_⟩
      · simp only [map_add, map_mul, map_sub, map_pow, map_one, hδ, hb, neg_sq]
        ring
      · have h1 : δ ∈ P := by
          by_contra h1
          have h2 := hδk P hp fun h => h1 (hp.mem_of_pow_mem _ h)
          refine h1 ?_
          have := P.add_mem h (P.mul_mem_right b h2)
          convert this using 1
          ring
        have h2 : (δ ^ 2) ^ k ∈ P := P.pow_mem_of_mem (P.pow_mem_of_mem h1 2 two_pos) k hk
        have h3 : b ∈ P := by
          have := P.add_mem (P.sub_mem h h1) (P.mul_mem_right b h2)
          convert this using 1
          ring
        intro a ha
        rcases Finset.mem_insert.1 ha with rfl | ha
        · exact h3
        · exact hP P hp h1 a ha
  obtain ⟨δ, hδ, hP⟩ := key (Set.toFinite {a | σ a = -a}).toFinset (by simp)
  refine ⟨δ, hδ, ?_⟩
  by_contra hu
  obtain ⟨P, hmax, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  refine hmax.ne_top (top_le_iff.1 ?_)
  rw [← htop, Ideal.span_le]
  intro a ha
  exact hP P hmax.isPrime hmem a (by simpa using ha)
end GlobalTheory.NormMod
