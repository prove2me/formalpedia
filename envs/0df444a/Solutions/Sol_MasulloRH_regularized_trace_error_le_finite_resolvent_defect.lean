-- Prove2me | solution 1 for MasulloRH.regularized_trace_error_le_finite_resolvent_defect
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:42:32.221925+00:00
-- url     : https://prove2.me/submissions/f8eb6bb7-be73-4490-9e0a-af133c47b0d0

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_trace_finite_height_error
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Mathlib

open Set Filter Topology
open MasulloRH

private theorem six_lt_ordinate (z : ZetaZerosInTraceStrip (1/2)) : 6 < |z.val.im| := by
  by_contra! h
  exact ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six z.prop.2.1 z.prop.2.2.1 h z.prop.1

private theorem kernel_dominates_weight {β γ : ℝ} (hβ : 0 < β) (h1 : β < 1) (hy : 6 < |γ|) :
    1 / (1+γ^2) ≤ 16 * ((3-β)/((3-β)^2+γ^2) - (5/2-β)/((5/2-β)^2+γ^2)) := by
  let a := 3-β
  let b := 5/2-β
  let Y := γ^2
  have hY : 36 ≤ Y := by dsimp [Y]; nlinarith [sq_abs γ,sq_nonneg (|γ|-6)]
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have ha3 : a ≤ 3 := by dsimp [a]; linarith
  have hb3 : b ≤ 3 := by dsimp [b]; linarith
  have hab : a*b ≤ 9 := by nlinarith [mul_le_mul ha3 hb3 hb (by norm_num : (0:ℝ)≤3)]
  have ha2 : a^2 ≤ 9 := by nlinarith [mul_le_mul ha3 ha3 ha (by norm_num : (0:ℝ)≤3)]
  have hb2 : b^2 ≤ 9 := by nlinarith [mul_le_mul hb3 hb3 hb (by norm_num : (0:ℝ)≤3)]
  have hA : 0 < a^2+Y := by nlinarith [sq_nonneg a]
  have hB : 0 < b^2+Y := by nlinarith [sq_nonneg b]
  have hden : (a^2+Y)*(b^2+Y) ≤ (2*Y)*(2*Y) :=
    mul_le_mul (by linarith) (by linarith) hB.le (by linarith)
  have hnum : (2*Y)*(2*Y) ≤ 8*(Y-a*b)*(1+Y) := by
    have h := mul_le_mul (show 4*Y ≤ 8*(Y-a*b) by linarith) (show Y ≤ 1+Y by linarith)
      (show 0 ≤ Y by linarith) (show 0 ≤ 8*(Y-a*b) by linarith)
    nlinarith
  change 1/(1+Y) ≤ 16*(a/(a^2+Y)-b/(b^2+Y))
  have e : 16*(a/(a^2+Y)-b/(b^2+Y)) = (8*(Y-a*b))/((a^2+Y)*(b^2+Y)) := by
    field_simp [hA.ne',hB.ne']
    dsimp [a,b]
    ring
  rw [e]
  exact (div_le_div_iff₀ (by linarith) (mul_pos hA hB)).mpr (by simpa using hden.trans hnum)

private theorem term_comparison (ρ : ZetaZerosInTraceStrip (1/2)) :
    zeroDecayWeight (1/2) ρ ≤ 16*(zeroResolventTerm (1/2) 3 ρ).re ∧
    ‖zeroResolventTerm (1/2) 3 ρ‖ ≤ zeroDecayWeight (1/2) ρ := by
  let z := ρ.val
  let m := analyticOrderNatAt riemannZeta z
  have hy : 6 < |z.im| := six_lt_ordinate ρ
  have hy2 : 1 ≤ z.im^2 := by nlinarith [sq_abs z.im,sq_nonneg (|z.im|-6)]
  constructor
  · have hk := kernel_dominates_weight ρ.prop.2.1 ρ.prop.2.2.1 hy
    have he : (1/(3-z)-1/(5/2-z)).re =
        (3-z.re)/((3-z.re)^2+z.im^2) - (5/2-z.re)/((5/2-z.re)^2+z.im^2) := by
      simp only [one_div,Complex.sub_re,Complex.inv_re,Complex.normSq_apply,Complex.sub_im]
      norm_num [pow_two,Complex.div_ofNat_re,Complex.div_ofNat_im]
    unfold zeroDecayWeight zeroResolventTerm
    change (m:ℝ)/(1+z.im^2) ≤ 16*(((m:ℂ)*(1/(3-z)-1/(5/2-z))).re)
    rw [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,he]
    calc _ = (m:ℝ)*(1/(1+z.im^2)) := by ring
         _ ≤ _ := (mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg m)).trans_eq (by ring)
  · have hx : |z.im| ≤ ‖3-z‖ := by simpa using Complex.abs_im_le_norm (3-z)
    have hb : |z.im| ≤ ‖5/2-z‖ := by simpa using Complex.abs_im_le_norm (5/2-z)
    have ha0 : 0 < ‖3-z‖ := by linarith
    have hb0 : 0 < ‖5/2-z‖ := by linarith
    have he : 1/(3-z)-1/(5/2-z) = (-1/2:ℂ)/((3-z)*(5/2-z)) := by
      have iden (a b:ℂ) (ha:a ≠ 0) (hb:b ≠ 0) : 1/a-1/b=(b-a)/(a*b) := by
        field_simp
      rw [iden _ _ (norm_pos_iff.mp ha0) (norm_pos_iff.mp hb0)]
      ring
    unfold zeroDecayWeight zeroResolventTerm
    change ‖(m:ℂ)*(1/(3-z)-1/(5/2-z))‖ ≤ (m:ℝ)/(1+z.im^2)
    rw [he,norm_mul,Complex.norm_natCast,div_eq_mul_one_div (m:ℝ)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
    rw [norm_div,norm_mul]
    have hn : ‖(-1/2:ℂ)‖ = 1/2 := by norm_num
    rw [hn,div_le_div_iff₀ (mul_pos ha0 hb0) (by positivity)]
    nlinarith [mul_le_mul hx hb (abs_nonneg z.im) ha0.le,sq_abs z.im]

theorem solution (α R : ℝ) (s : ℂ)
    (hR : ‖s‖ ≤ R) (hs : (3/2:ℝ) < s.re)
    (F : Finset (ZetaZerosInTraceStrip (1/2)))
    (hF : ∀ z ∈ F, |z.val.re-1/2| < α) :
    ‖zetaLogDeriv s - regularizedTraceRHS α s‖ ≤ (16*(2*(2*R+3)*(R+5/2))) *
      ((zetaLogDeriv 3).re - (zetaLogDeriv (5/2) + regularizedArch 3 - regularizedPolar 3).re -
        ∑ z ∈ F,(zeroResolventTerm (1/2) 3 z).re) := by
  classical
  let Z := ZetaZerosInTraceStrip (1/2)
  let w : Z → ℝ := zeroDecayWeight (1/2)
  let f : Z → ℂ := zeroResolventTerm (1/2) 3
  let k (z : Z) := (f z).re
  let base := zetaLogDeriv (5/2) + regularizedArch 3 - regularizedPolar 3
  let C := 2*(2*R+3)*(R+5/2)
  have hR0 := (norm_nonneg s).trans hR
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hw0 (z : Z) : 0 ≤ w z := by dsimp [w,zeroDecayWeight]; positivity
  have hw : Summable w := weighted_zero_summability _ (by norm_num)
  have hf : Summable f := hw.of_norm_bounded (fun z => (term_comparison z).2)
  have hk : Summable k := (Complex.hasSum_re hf.hasSum).summable
  have hkw (z : Z) : w z ≤ 16*k z := (term_comparison z).1
  have hk0 (z : Z) : 0 ≤ k z := by linarith [hkw z,hw0 z]
  have hzt (z : Z) : 0 < |z.val.im| := by linarith [six_lt_ordinate z]
  let D : Set Z := {z | α ≤ |z.val.re-1/2|}
  have hmain : ‖zetaLogDeriv s - regularizedTraceRHS α s‖ ≤ C * ∑' z,D.indicator w z := by
    have he := regularized_trace_finite_height_error α 0 R s hR hs
    simpa [D,C,w,Z,Set.indicator_apply,hzt,not_le_of_gt] using he
  have hsum : (zetaLogDeriv 3).re - base.re = ∑' z, k z := by
    rw [←regularized_initial_identity_full_strip (3:ℂ) (by norm_num)]
    change (base + ∑' z,f z).re - base.re = _
    rw [Complex.add_re,add_sub_cancel_left,Complex.re_tsum hf]
  let O : Set Z := (F : Set Z)ᶜ
  have hrest : (∑' z, k z) - ∑ z ∈ F,k z = ∑' z,O.indicator k z := by
    rw [←tsum_subtype]
    exact sub_eq_of_eq_add' (hk.sum_add_tsum_compl (s:=F)).symm
  have hbound (z : Z) : D.indicator w z ≤ 16*O.indicator k z := by
    by_cases hz : z ∈ D
    · have ho : z ∈ O := fun hin => (not_lt.mpr hz) (hF z hin)
      rw [Set.indicator_of_mem hz,Set.indicator_of_mem ho]
      exact hkw z
    · rw [Set.indicator_of_notMem hz]
      exact mul_nonneg (by norm_num) (Set.indicator_nonneg (fun z _ => hk0 z) _)
  change _ ≤ 16*C*((zetaLogDeriv 3).re-base.re-∑ z ∈ F,k z)
  rw [hsum,hrest]
  apply hmain.trans
  calc C*(∑' z,D.indicator w z) ≤ C*∑' z,16*O.indicator k z :=
         mul_le_mul_of_nonneg_left ((hw.indicator D).tsum_le_tsum hbound ((hk.indicator O).mul_left 16)) hC
       _ = _ := by rw [tsum_mul_left];ring

