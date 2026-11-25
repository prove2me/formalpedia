-- Prove2me | solution 1 for GlobalTheory.HL.sum_eq_sum_of_symm_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:42:16.293803+00:00
-- url     : https://prove2.me/submissions/064cd192-f8c9-456f-977d-bd2165896be5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormOrbitSumLeOfSymmKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {ι : Type*} (Z : Finset ι) (r : ι → ι → Prop)
    (hr : ∀ p q, r p q → r q p) (hne : ∀ p ∈ Z, ∃ q ∈ Z, r p q) (F H : ι → ℂ)
    (hFH : ∀ p ∈ Z, ∀ q ∈ Z, r p q →
      F p * ((Z.filter (r q)).card : ℂ) = H q * ((Z.filter (r p)).card : ℂ)) :
    ∑ p ∈ Z, F p = ∑ p ∈ Z, H p := by
  have hd : ∀ p ∈ Z, ((Z.filter (r p)).card : ℂ) ≠ 0 := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hne p hp
    exact_mod_cast (Finset.card_pos.2 ⟨q, Finset.mem_filter.2 ⟨hq, hpq⟩⟩).ne'
  have key : ∀ F : ι → ℂ, ∑ p ∈ Z, F p =
      ∑ p ∈ Z, ∑ q ∈ Z, if r p q then F p / ((Z.filter (r p)).card : ℂ) else 0 := by
    intro F
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (hd p hp)]
  rw [key F, key H, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun p hp => ?_
  by_cases h : r p q
  · rw [if_pos h, if_pos (hr _ _ h), div_eq_div_iff (hd p hp) (hd q hq), hFH p hp q hq h]
  · rw [if_neg h, if_neg (fun h' => h (hr _ _ h'))]
end GlobalTheory.HL
