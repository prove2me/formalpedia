-- Prove2me | solution 1 for GlobalTheory.IntClsCount.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:39.473188+00:00
-- url     : https://prove2.me/submissions/7f74371e-62da-4e43-93c1-88247774cdfc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RmulMul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.IntClsCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.IntClsCount
theorem _root_.solution (L : LocE F E) (t : E) (m : ℕ) (hm : m ≠ 0)
    (hc : Nat.card (L.O ⧸ Ideal.span {y : L.O | (y : E) = t}) = m) (N : ℕ) :
    ∃ R : Set (Matrix (Fin N) (Fin N) E), R.encard ≤ ((m ^ (N * (N - 1) / 2) : ℕ) : ℕ∞) ∧
      (∀ B ∈ R, IsUni B ∧ IsIntM L B) ∧
      ∀ B, IsUni B → IsIntM L B → ∃ B₀ ∈ R, ∀ i j, ∃ c ∈ L.O, B i j - B₀ i j = t * c := by
  set I : Ideal L.O := Ideal.span {y : L.O | (y : E) = t} with hI
  haveI : Finite (L.O ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hm)
  have hmem : ∀ y ∈ I, ∃ c ∈ L.O, (y : E) = t * c := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact ⟨1, L.O.one_mem, by rw [mul_one]; exact hx⟩
    | zero => exact ⟨0, L.O.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, e⟩ := hx
      obtain ⟨d, hd, e'⟩ := hy
      exact ⟨c + d, L.O.add_mem hc hd, by push_cast; rw [e, e', mul_add]⟩
    | smul a x _ hx =>
      obtain ⟨c, hc, e⟩ := hx
      exact ⟨a * c, L.O.mul_mem a.2 hc, by rw [smul_eq_mul]; push_cast; rw [e]; ring⟩
  let lift : ((j : Fin N) → Fin j → L.O ⧸ I) → Matrix (Fin N) (Fin N) E := fun x i j =>
    if h : i < j then ((x j ⟨i, h⟩).out : L.O) else if i = j then 1 else 0
  refine ⟨Set.range lift, ?_, ?_, ?_⟩
  · rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans (le_of_eq ?_)
    rw [Set.encard_univ, ENat.card_eq_coe_natCard]
    congr 1
    rw [Nat.card_pi]
    simp only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin, hc]
    rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun j => j) N, Finset.sum_range_id]
  · rintro _ ⟨x, rfl⟩
    refine ⟨⟨fun i j h => ?_, fun i => ?_⟩, fun i j => ?_⟩
    · simp only [lift]
      rw [dif_neg (not_lt_of_gt h), if_neg (ne_of_gt h)]
    · simp [lift]
    · simp only [lift]
      split_ifs
      · exact Subtype.property _
      · exact L.O.one_mem
      · exact L.O.zero_mem
  · intro B hB hBI
    refine ⟨_, ⟨fun j i => Ideal.Quotient.mk I ⟨B ⟨i, i.2.trans j.2⟩ j, hBI _ _⟩, rfl⟩,
      fun i j => ?_⟩
    simp only [lift]
    split_ifs with h1 h2
    · have h3 : (⟨B i j, hBI i j⟩ : L.O) - (Ideal.Quotient.mk I ⟨B i j, hBI i j⟩).out ∈ I := by
        rw [← Ideal.Quotient.eq]
        exact (Quotient.out_eq _).symm
      exact hmem _ h3
    · subst h2
      exact ⟨0, L.O.zero_mem, by rw [hB.2]; simp⟩
    · exact ⟨0, L.O.zero_mem, by rw [hB.1 i j (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))]; simp⟩
end GlobalTheory.IntClsCount
