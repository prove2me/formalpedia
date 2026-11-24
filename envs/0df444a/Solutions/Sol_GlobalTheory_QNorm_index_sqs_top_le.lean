-- Prove2me | solution 1 for GlobalTheory.QNorm.index_sqs_top_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:58:50.625229+00:00
-- url     : https://prove2.me/submissions/d1057cf0-8130-44f1-98eb-bfb77a63b341

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSquaresLeTwoMulUnitsSquares
import Theorems.Thm_GlobalTheory_QNorm_mem_hiUnits_sup_sqs_of_even

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K),
    w π = WithZero.exp (-1) → (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 →
    (sqs (⊤ : Subgroup Kˣ)).index ≠ 0 ∧
      (sqs (⊤ : Subgroup Kˣ)).index ≤ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
  intro K _ w π hπ h0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hdvd : (hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ)).index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨Units.mk0 π hπ0, fun b => ?_⟩
    have hb : w (b : K) ≠ 0 := by simp
    have hb' : w (b : K) = WithZero.exp (WithZero.log (w (b : K))) := (WithZero.exp_log hb).symm
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (WithZero.log (w (b : K)))
    · right
      exact mem_hiUnits_sup_sqs_of_even w (Units.mk0 π hπ0) hπ b m (by rw [hb', hm])
    · left
      refine mem_hiUnits_sup_sqs_of_even w (Units.mk0 π hπ0) hπ _ m ?_
      rw [Units.val_mul, map_mul, hb', hm, Units.val_mk0, hπ, ← WithZero.exp_add]
      congr 1
      ring
  have hmul := Subgroup.relIndex_mul_index
    (le_sup_right : sqs (⊤ : Subgroup Kˣ) ≤ hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ))
  rw [Subgroup.relIndex_sup_right] at hmul
  have hle : sqs (hiUnits w 0) ≤ sqs (⊤ : Subgroup Kˣ) := Subgroup.map_mono le_top
  have hd2 := Subgroup.relIndex_dvd_of_le_left (hiUnits w 0) hle
  have hd : (sqs (⊤ : Subgroup Kˣ)).index ∣ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
    rw [← hmul, mul_comm]
    exact Nat.mul_dvd_mul hdvd hd2
  have hpos : 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 := mul_ne_zero two_ne_zero h0
  exact ⟨ne_zero_of_dvd_ne_zero hpos hd, Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hd⟩
end GlobalTheory.QNorm
