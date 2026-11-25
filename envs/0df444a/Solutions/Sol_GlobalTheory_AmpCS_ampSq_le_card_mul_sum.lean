-- Prove2me | solution 1 for GlobalTheory.AmpCS.ampSq_le_card_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:47.642619+00:00
-- url     : https://prove2.me/submissions/45a011d3-a2fe-4ba5-b489-36c4b440c664

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AmpSqLeCardMulSum
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.AmpCS
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma norm_tsum_sq_le_card_mul_sum_sq {α ι : Type*} (s : Finset ι) (f : ι → α → ℂ)
    (g : α → ℂ) (hg : ∀ a, g a = ∑ i ∈ s, f i a) (hdom : ∀ i ∈ s, ∀ a, ‖f i a‖ ≤ ‖g a‖) :
    ‖∑' a, g a‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := by
  by_cases hs : Summable g
  · have hfi : ∀ i ∈ s, Summable (f i) := fun i hi =>
      Summable.of_norm_bounded (summable_norm_iff.mpr hs) (hdom i hi)
    have hsum : ∑' a, g a = ∑ i ∈ s, ∑' a, f i a := by
      simp_rw [hg]
      exact Summable.tsum_finsetSum hfi
    rw [hsum]
    calc ‖∑ i ∈ s, ∑' a, f i a‖ ^ 2 ≤ (∑ i ∈ s, ‖∑' a, f i a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  · rw [tsum_eq_zero_of_not_summable hs, norm_zero]
    have : (0 : ℝ) ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := by positivity
    simpa using this
end GlobalTheory.AmpCS
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.AmpCS
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.AmpCS
namespace _root_.GlobalTheory.AmpCS
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), 1 ≤ k → ∀ {ι : Type} (s : Finset ι) (P : ι → S.Datum → Submodule L.O S.V → Prop) (Q : S.Datum → Submodule L.O S.V → Prop), (∀ d Λ, S.IsTerm d Λ → (Q d Λ ↔ ∃ i ∈ s, P i d Λ)) → (∀ d Λ, S.IsTerm d Λ → ∀ i ∈ s, ∀ i' ∈ s, P i d Λ → P i' d Λ → i = i') → S.ampSq Q ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, S.ampSq (P i) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ ι s P Q hQ hdisj
  unfold _root_.GlobalTheory.HL.Frames.ampSq _root_.GlobalTheory.HL.Frames.sumData
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (s.card : ℝ≥0∞), mul_assoc]
  gcongr
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold _root_.GlobalTheory.HL.Frames.amp
  apply norm_tsum_sq_le_card_mul_sum_sq
  · intro a
    by_cases ht : S.IsTerm (Quotient.out o) (Quotient.out a)
    · by_cases hq : Q (Quotient.out o) (Quotient.out a)
      · obtain ⟨i, hi, hPi⟩ := (hQ _ _ ht).mp hq
        rw [if_pos ⟨ht, hq⟩, Finset.sum_eq_single_of_mem i hi, if_pos ⟨ht, hPi⟩]
        intro j hj hji
        rw [if_neg]
        rintro ⟨-, hPj⟩
        exact hji (hdisj _ _ ht j hj i hi hPj hPi)
      · rw [if_neg (fun h => hq h.2)]
        refine (Finset.sum_eq_zero fun i hi => ?_).symm
        rw [if_neg]
        rintro ⟨-, hPi⟩
        exact hq ((hQ _ _ ht).mpr ⟨i, hi, hPi⟩)
    · rw [if_neg (fun h => ht h.1)]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [if_neg (fun h => ht h.1)]
  · intro i hi a
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.1, (hQ _ _ h1.1).mpr ⟨i, hi, h1.2⟩⟩ h2
    · rw [norm_zero]; exact norm_nonneg _
    · simp
end _root_.GlobalTheory.AmpCS
end GlobalTheory.AmpCS
