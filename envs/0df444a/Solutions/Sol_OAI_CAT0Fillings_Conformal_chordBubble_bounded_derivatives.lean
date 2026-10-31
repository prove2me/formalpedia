-- Prove2me | solution 1 for OAI.CAT0Fillings.Conformal.chordBubble_bounded_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:59:14.4827+00:00
-- url     : https://prove2.me/submissions/edf95b64-70db-47d1-8566-75f827a70b41

import Mathlib
import Definitions.Def_OAIQ29C0001

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Bubble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory

namespace CAT0Fillings.Conformal
lemma chordBubble_hasDerivAt {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) :
    HasDerivAt (chordBubble q a) (chordBubbleD q a t) t := by
  have hb := (((hasDerivAt_id t).pow 2).const_mul a).const_add 1
  simp only [Pi.pow_apply,id_eq] at hb
  have hh := hb.rpow_const (p := -q) (Or.inl (ne_of_gt (by positivity)))
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [chordBubbleD,Nat.cast_ofNat,mul_one]
  ring
lemma chordBubbleD_hasDerivAt {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) :
    HasDerivAt (chordBubbleD q a) (chordBubbleDD q a t) t := by
  have hb := (((hasDerivAt_id t).pow 2).const_mul a).const_add 1
  simp only [Pi.pow_apply,id_eq] at hb
  have hh := hb.rpow_const (p := -q-1) (Or.inl (ne_of_gt (by positivity)))
  have h := ((hasDerivAt_id t).const_mul (-2*q*a)).mul hh
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [chordBubbleDD,id_eq,Nat.cast_ofNat,mul_one]
  rw [show -q-1-1 = -q-2 by ring]
  ring
lemma chordBubble_pos {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) : 0 < chordBubble q a t :=
  Real.rpow_pos_of_pos (by positivity) _
lemma chordBubble_le_one {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (t : ℝ) : chordBubble q a t ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · nlinarith [mul_nonneg ha (sq_nonneg t)]
  · linarith
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Combined
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory

namespace CAT0Fillings.Conformal
lemma chord_rational_bounds {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |t|/(1+a*t^2) ≤ 1+a⁻¹ ∧ t^2/(1+a*t^2)^2 ≤ a⁻¹ := by
  have hb : 0 < 1+a*t^2 := by positivity
  have h1 : 1 ≤ 1+a*t^2 := by nlinarith [mul_nonneg ha.le (sq_nonneg t)]
  have ht : |t| ≤ 1+t^2 := by nlinarith [sq_nonneg (|t|-1),sq_abs t]
  have hd : t^2/(1+a*t^2) ≤ a⁻¹ := by
    rw [←one_div,div_le_div_iff₀ hb ha]
    nlinarith
  constructor
  · calc
      _ ≤ (1+t^2)/(1+a*t^2) := div_le_div_of_nonneg_right ht hb.le
      _ = 1/(1+a*t^2)+t^2/(1+a*t^2) := add_div _ _ _
      _ ≤ 1+a⁻¹ := add_le_add (div_le_one_of_le₀ h1 hb.le) hd
  · apply le_trans (div_le_div_of_nonneg_left (sq_nonneg t) hb ?_) hd
    nlinarith
lemma chordBubbleD_bound {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (t : ℝ) :
    |chordBubbleD q a t| ≤ 2*q*a*(1+a⁻¹) := by
  have hb : 0 < 1+a*t^2 := by positivity
  have hp := (chordBubble_pos ha.le q t).le
  have hp1 := chordBubble_le_one ha.le hq t
  have hid : |chordBubbleD q a t| = 2*q*a*(|t|/(1+a*t^2))*chordBubble q a t := by
    unfold chordBubbleD chordBubble
    rw [Real.rpow_sub hb,Real.rpow_one]
    simp only [abs_mul,abs_div,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hq,abs_of_pos ha,abs_of_pos hb,abs_of_pos (Real.rpow_pos_of_pos hb (-q))]
    ring
  rw [hid]
  calc
    _ ≤ 2*q*a*(1+a⁻¹)*1 := mul_le_mul (mul_le_mul_of_nonneg_left (chord_rational_bounds ha t).1 (by positivity)) hp1 hp (by positivity)
    _ = _ := mul_one _
lemma chordBubbleDD_bound {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (t : ℝ) :
    |chordBubbleDD q a t| ≤ 2*q*a+4*q*(q+1)*a := by
  have hb : 0 < 1+a*t^2 := by positivity
  have h1 : 1 ≤ 1+a*t^2 := by nlinarith [mul_nonneg ha.le (sq_nonneg t)]
  have hp := (chordBubble_pos ha.le q t).le
  have hp1 := chordBubble_le_one ha.le hq t
  have hfirst : |(-2*q*a)*(1+a*t^2)^(-q-1)| ≤ 2*q*a := by
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hb.le _)]
    have hpow : (1+a*t^2)^(-q-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have habs : |-2*q*a| = 2*q*a := by rw [abs_of_nonpos (by nlinarith)]; ring
    rw [habs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2*q*a by positivity)
  have hsecond : |4*q*(q+1)*a^2*t^2*(1+a*t^2)^(-q-2)| ≤ 4*q*(q+1)*a := by
    rw [abs_of_nonneg (by positivity)]
    have hid : 4*q*(q+1)*a^2*t^2*(1+a*t^2)^(-q-2) =
        (4*q*(q+1)*a^2)*(t^2/(1+a*t^2)^2)*chordBubble q a t := by
      rw [Real.rpow_sub hb,Real.rpow_two]
      unfold chordBubble
      ring
    rw [hid]
    calc
      _ ≤ (4*q*(q+1)*a^2)*a⁻¹*1 := mul_le_mul (mul_le_mul_of_nonneg_left (chord_rational_bounds ha t).2 (by positivity)) hp1 hp (by positivity)
      _ = _ := by field_simp
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
lemma chordBubble_bounded_derivatives_oai {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |chordBubble q a t| ≤ B ∧
      |deriv (chordBubble q a) t| ≤ B ∧ |deriv (chordBubbleD q a) t| ≤ B := by
  let B := 1+2*q*a*(1+a⁻¹)+(2*q*a+4*q*(q+1)*a)
  have hA : 0 ≤ 2*q*a*(1+a⁻¹) := by positivity
  have hC : 0 ≤ 2*q*a+4*q*(q+1)*a := by positivity
  refine ⟨B,by dsimp [B]; linarith,fun t => ?_⟩
  rw [(chordBubble_hasDerivAt ha.le q t).deriv,(chordBubbleD_hasDerivAt ha.le q t).deriv]
  have hw := chordBubble_le_one ha.le hq t
  rw [←abs_of_nonneg (chordBubble_pos ha.le q t).le] at hw
  exact ⟨hw.trans (by dsimp [B]; linarith),
    (chordBubbleD_bound ha hq t).trans (by dsimp [B]; linarith),
    (chordBubbleDD_bound ha hq t).trans (by dsimp [B]; linarith)⟩
end CAT0Fillings.Conformal
end

end OAI
end

theorem solution : type_of% @OAI.CAT0Fillings.Conformal.chordBubble_bounded_derivatives_oai := @OAI.CAT0Fillings.Conformal.chordBubble_bounded_derivatives_oai
