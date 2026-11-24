-- Prove2me | solution 1 for GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:24:37.674904+00:00
-- url     : https://prove2.me/submissions/96eb4af3-0f67-45a3-9524-ec935241f8ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Theorems.Thm_GlobalTheory_LocalQuad_isSquare_of_valued_sub_one_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
namespace DeepSquares
end DeepSquares
open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exp_neg_two_mul_le_mul_of_lt {e : ℕ} {a b : ℤᵐ⁰}
    (ha : WithZero.exp (-((e : ℤ) + 1)) < a) (hb : WithZero.exp (-((e : ℤ) + 1)) < b) :
    WithZero.exp (-(2 * (e : ℤ))) ≤ a * b := by
  obtain ⟨k, rfl⟩ : ∃ k, WithZero.exp k = a := ⟨_, WithZero.exp_log (ne_bot_of_gt ha)⟩
  obtain ⟨l, rfl⟩ : ∃ l, WithZero.exp l = b := ⟨_, WithZero.exp_log (ne_bot_of_gt hb)⟩
  rw [WithZero.exp_lt_exp] at ha hb
  rw [← WithZero.exp_add, WithZero.exp_le_exp]
  omega
end GlobalTheory.QNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero
namespace GlobalTheory.QNorm
namespace _root_.GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : ℕ),
    Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) →
    _root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (2 * e + 1) ≤
      _root_.GlobalTheory.QNorm.sqs
        (_root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (e + 1)) := by
  intro F _ _ v e h2 x hx
  unfold _root_.GlobalTheory.QNorm.hiUnits at hx
  unfold _root_.GlobalTheory.QNorm.sqs _root_.GlobalTheory.QNorm.hiUnits
  obtain ⟨-, hx1⟩ := hx
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have h4 : w 4 = WithZero.exp (-(2 * e : ℤ)) := by
    have : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
    rw [this, map_mul, h2, ← WithZero.exp_add]; congr 1; ring
  have hlt : w ((x : v.adicCompletion F) - 1) < w 4 := by
    refine lt_of_le_of_lt hx1 ?_
    rw [h4, WithZero.exp_lt_exp]; push_cast; omega
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v _ hlt
  have hprod : w (r - 1) * w (r + 1) ≤ WithZero.exp (-((2 * e + 1 : ℕ) : ℤ)) := by
    rw [← map_mul, show (r - 1) * (r + 1) = r * r - 1 by ring, ← hr]; exact hx1
  obtain ⟨s, hs, hs1⟩ : ∃ s : v.adicCompletion F, s * s = x ∧
      w (s - 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ)) := by
    by_cases hm : w (r - 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ))
    · exact ⟨r, hr.symm, hm⟩
    by_cases hp : w (r + 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ))
    · refine ⟨-r, by rw [neg_mul_neg, hr], ?_⟩
      rwa [show -r - 1 = -(r + 1) by ring, Valuation.map_neg]
    exfalso
    push_cast at hm hp hprod
    have := (exp_neg_two_mul_le_mul_of_lt (not_le.mp hm) (not_le.mp hp)).trans hprod
    rw [WithZero.exp_le_exp] at this
    omega
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hs
    exact x.ne_zero hs.symm
  have hsv : w s = 1 := by
    have hlt1 : w (s - 1) < 1 :=
      hs1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using Valuation.map_one_add_of_lt w hlt1
  refine ⟨Units.mk0 s hs0, ⟨hsv, hs1⟩, ?_⟩
  ext
  simp [pow_two, hs]
end _root_.GlobalTheory.QNorm
end GlobalTheory.QNorm
