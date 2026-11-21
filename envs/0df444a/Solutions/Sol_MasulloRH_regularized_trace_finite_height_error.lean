-- Prove2me | solution 1 for MasulloRH.regularized_trace_finite_height_error
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:37:39.986656+00:00
-- url     : https://prove2.me/submissions/e4dc1431-4f8f-41df-b712-da713d17c33a

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Mathlib

open Filter Set Topology

open MasulloRH

private theorem height_majorant {R : ℝ} {s : ℂ} (hR : ‖s‖ ≤ R)
    (hs : (3/2:ℝ) ≤ s.re) (ρ : ZetaZerosInTraceStrip (1/2)) :
    ‖zeroResolventTerm (1/2) s ρ‖ ≤
      (2*(2*R+3)*(R+5/2)) * zeroDecayWeight (1/2) ρ := by
  let z : ℂ := ρ
  let b : ℂ := 5/2
  have hβ : z.re < 1 := ρ.property.2.2.1
  have hb : b.re = 5/2 := by norm_num [b,Complex.div_re]
  have hbim : b.im = 0 := by norm_num [b,Complex.div_im]
  have hbn : ‖b‖ = 5/2 := by norm_num [b,norm_div]
  have hA : 1/2 ≤ ‖s-z‖ := by
    have h := Complex.re_le_norm (s-z)
    rw [Complex.sub_re] at h
    linarith
  have hB : 1 ≤ ‖b-z‖ := by
    have h := Complex.re_le_norm (b-z)
    rw [Complex.sub_re,hb] at h
    linarith
  have ha0 : 0 < ‖s-z‖ := by linarith
  have hb0 : 0 < ‖b-z‖ := by linarith
  have hR0 := (norm_nonneg s).trans hR
  have himA : |z.im| ≤ R+‖s-z‖ := by
    calc |z.im| = |s.im - (s-z).im| := by rw [Complex.sub_im]; congr 1; ring
         _ ≤ |s.im|+|(s-z).im| := abs_sub _ _
         _ ≤ _ := add_le_add ((Complex.abs_im_le_norm s).trans hR) (Complex.abs_im_le_norm _)
  have himB : |z.im| ≤ ‖b-z‖ := by
    simpa [Complex.sub_im,hbim] using Complex.abs_im_le_norm (b-z)
  have h1 : 1+|z.im| ≤ (2*R+3)*‖s-z‖ := by
    nlinarith [mul_nonneg (show 0 ≤ R+1 by linarith) (show 0 ≤ ‖s-z‖ - 1/2 by linarith)]
  have h2 : 1+|z.im| ≤ 2*‖b-z‖ := by linarith
  have hw : 1+z.im^2 ≤ (2*(2*R+3))*(‖s-z‖*‖b-z‖) := by
    have h := mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith [sq_abs z.im, abs_nonneg z.im]
  have hdiff : 1/(s-z) - 1/(b-z) = (b-s)/((s-z)*(b-z)) := by
    field_simp [norm_pos_iff.mp ha0,norm_pos_iff.mp hb0]
    ring
  have hnum : ‖b-s‖ ≤ R+5/2 := by linarith [norm_sub_le b s]
  have hdiv : ‖1/(s-z) - 1/(b-z)‖ ≤ (2*(2*R+3)*(R+5/2))/(1+z.im^2) := by
    rw [hdiff,norm_div,norm_mul]
    apply (div_le_div_iff₀ (mul_pos ha0 hb0) (by positivity)).mpr
    calc ‖b-s‖ * (1+z.im^2) ≤ (R+5/2)*(1+z.im^2) := by gcongr
         _ ≤ (R+5/2)*((2*(2*R+3))*(‖s-z‖*‖b-z‖)) := by gcongr
         _ = _ := by ring
  unfold zeroResolventTerm zeroDecayWeight
  rw [norm_mul,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg (analyticOrderNatAt riemannZeta z))).trans_eq
  ring

private def stripAsSubset (α : ℝ) : ZetaZerosInTraceStrip α ≃
    {z : ZetaZerosInTraceStrip (1/2) // |z.val.re-1/2| < α} where
  toFun z := ⟨⟨z.val,z.property.1,z.property.2.1,z.property.2.2.1,
    abs_lt.mpr ⟨by linarith [z.property.2.1],by linarith [z.property.2.2.1]⟩⟩,z.property.2.2.2⟩
  invFun z := ⟨z.val.val,z.val.property.1,z.val.property.2.1,z.val.property.2.2.1,z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem solution (α T R : ℝ) (s : ℂ)
    (hR : ‖s‖ ≤ R) (hs : (3/2:ℝ) < s.re) :
    ‖(zetaLogDeriv s - regularizedTraceRHS α s) -
      (∑' z : ZetaZerosInTraceStrip (1/2),
        if α ≤ |z.val.re-1/2| ∧ |z.val.im| ≤ T then zeroResolventTerm (1/2) s z else 0)‖ ≤
      (2*(2*R+3)*(R+5/2)) * ∑' z : ZetaZerosInTraceStrip (1/2),
        if α ≤ |z.val.re-1/2| ∧ T < |z.val.im| then zeroDecayWeight (1/2) z else 0 := by
  classical
  let Z := ZetaZerosInTraceStrip (1/2)
  let f : Z → ℂ := zeroResolventTerm (1/2) s
  let w : Z → ℝ := zeroDecayWeight (1/2)
  let C := 2*(2*R+3)*(R+5/2)
  have hR0 := (norm_nonneg s).trans hR
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hw0 (z : Z) : 0 ≤ w z := by dsimp [w,zeroDecayWeight]; positivity
  have hw : Summable w := weighted_zero_summability _ (by norm_num)
  have hb (z : Z) : ‖f z‖ ≤ C*w z := height_majorant hR hs.le z
  have hf : Summable f := (hw.mul_left C).of_norm_bounded hb
  let A : Set Z := {z | |z.val.re-1/2| < α}
  let B : Set Z := {z | α ≤ |z.val.re-1/2| ∧ |z.val.im| ≤ T}
  let D : Set Z := {z | T < |z.val.im|}
  let K : Set Z := Aᶜ ∩ D
  have hsplit (z : Z) : f z - A.indicator f z - B.indicator f z = K.indicator f z := by
    simp only [A,B,K,D,Set.indicator_apply,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_compl_iff]
    split_ifs <;> simp_all <;> grind
  have hnarrow : regularizedSpectral α s = ∑' z, A.indicator f z := by
    rw [←tsum_subtype]
    exact (stripAsSubset α).tsum_eq (fun z => f z.val)
  have herr : zetaLogDeriv s - regularizedTraceRHS α s - ∑' z, B.indicator f z =
      ∑' z, K.indicator f z := by
    rw [←regularized_initial_identity_full_strip s hs]
    unfold regularizedTraceRHS
    rw [hnarrow]
    change _ + ∑' z, f z - (_ + ∑' z, A.indicator f z) - _ = _
    rw [add_sub_add_left_eq_sub,←hf.tsum_sub (hf.indicator A),
      ←(hf.sub (hf.indicator A)).tsum_sub (hf.indicator B)]
    exact tsum_congr hsplit
  suffices H : ‖zetaLogDeriv s - regularizedTraceRHS α s - ∑' z, B.indicator f z‖ ≤ C*∑' z,K.indicator w z by
    simpa only [A,B,K,D,C,f,w,Z,Set.indicator_apply,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_compl_iff,not_lt] using H
  rw [herr,←tsum_mul_left]
  have hkbound (z : Z) : ‖K.indicator f z‖ ≤ C*K.indicator w z := by
    by_cases hk : z ∈ K
    · rw [Set.indicator_of_mem hk,Set.indicator_of_mem hk]
      exact hb z
    · simp [Set.indicator_of_notMem hk]
  apply (norm_tsum_le_tsum_norm (hf.indicator K).norm).trans
  exact ((hf.indicator K).norm).tsum_le_tsum hkbound ((hw.indicator K).mul_left C)

