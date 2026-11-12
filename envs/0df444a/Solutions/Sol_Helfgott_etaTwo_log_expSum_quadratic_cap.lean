-- Prove2me | solution 1 for Helfgott.etaTwo_log_expSum_quadratic_cap
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T18:14:39.709205+00:00
-- url     : https://prove2.me/submissions/d940ddf6-c71a-4dbf-819f-54001652fc57

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Definitions.Def_Helfgott_WeightedCounting
import Definitions.Def_Helfgott_VaughanData
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.Divisors
section

open Finset
open scoped BigOperators
namespace HelfgottQuadratic

theorem one_jump_variation_partial (g : ℕ → ℝ) (k : ℕ)
    (hg0 : ∀ n, 0 ≤ g n) (hzero : ∀ n < k, g n = 0)
    (hanti : ∀ n, k+1 ≤ n → g (n+1) ≤ g n) (N : ℕ) :
    g 0+(∑ n ∈ range N, |g (n+1)-g n|) =
      if N ≤ k then g N else g k+|g (k+1)-g k|+g (k+1)-g N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ,← add_assoc,ih]
    by_cases hNk : N < k
    · have hN : N ≤ k := by omega
      have hN1 : N+1 ≤ k := by omega
      simp only [if_pos hN,if_pos hN1,hzero N hNk,sub_zero,abs_of_nonneg (hg0 _),zero_add]
    · by_cases hNe : N = k
      · subst N
        simp only [le_refl,if_true,show ¬k+1 ≤ k by omega,if_false]
        ring
      · have hN : ¬N ≤ k := by omega
        have hN1 : ¬N+1 ≤ k := by omega
        rw [if_neg hN,if_neg hN1,abs_of_nonpos (sub_nonpos.mpr (hanti N (by omega)))]
        ring

theorem one_jump_variation (g : ℕ → ℝ) (k : ℕ) (B : ℝ)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ B) (hzero : ∀ n < k, g n = 0)
    (hanti : ∀ n, k+1 ≤ n → g (n+1) ≤ g n) :
    Summable (fun n => |g (n+1)-g n|) ∧
      g 0+(∑' n : ℕ, |g (n+1)-g n|) ≤ 2*B := by
  have hpartial : ∀ N, (∑ n ∈ range N, |g (n+1)-g n|) ≤ 2*B-g 0 := by
    intro N
    have hh := one_jump_variation_partial g k (fun n => (hg n).1) hzero hanti N
    by_cases hN : N ≤ k
    · rw [if_pos hN] at hh
      have hB : 0 ≤ B := (hg 0).1.trans (hg 0).2
      linarith [(hg N).2]
    · rw [if_neg hN] at hh
      have habs : |g (k+1)-g k| ≤ 2*B-g k-g (k+1) := by
        apply abs_le.mpr
        constructor <;> linarith [(hg k).2,(hg (k+1)).2]
      linarith [(hg N).1]
  refine ⟨summable_of_sum_range_le (fun n => abs_nonneg _) hpartial,?_⟩
  have hh := Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _) hpartial
  linarith

noncomputable def clippedLog (c t : ℝ) : ℝ := Real.log (max t c)
noncomputable def clippedLogStep (c : ℝ) (n : ℕ) : ℝ :=
  clippedLog c ((n:ℝ)+1)-clippedLog c (n:ℝ)

theorem clippedLogStep_bounds (c : ℝ) (hc : 0 < c) (n : ℕ) :
    0 ≤ clippedLogStep c n ∧ clippedLogStep c n ≤ 1/c := by
  have hlo : 0 < max (n:ℝ) c := hc.trans_le (le_max_right _ _)
  have hhi : 0 < max ((n:ℝ)+1) c := hc.trans_le (le_max_right _ _)
  have hmono : max (n:ℝ) c ≤ max ((n:ℝ)+1) c := max_le_max_right _ (by linarith)
  have hdiff : max ((n:ℝ)+1) c-max (n:ℝ) c ≤ 1 := by
    calc
      _ ≤ max (((n:ℝ)+1)-(n:ℝ)) (c-c) := max_sub_max_le_max _ _ _ _
      _ = 1 := by norm_num
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hlo hmono)
  · have hh := Real.log_le_sub_one_of_pos (div_pos hhi hlo)
    rw [Real.log_div (ne_of_gt hhi) (ne_of_gt hlo)] at hh
    change Real.log (max ((n:ℝ)+1) c)-Real.log (max (n:ℝ) c) ≤ _
    calc
      _ ≤ max ((n:ℝ)+1) c/max (n:ℝ) c-1 := hh
      _ = (max ((n:ℝ)+1) c-max (n:ℝ) c)/max (n:ℝ) c := by field_simp
      _ ≤ 1/max (n:ℝ) c := div_le_div_of_nonneg_right hdiff hlo.le
      _ ≤ 1/c := one_div_le_one_div_of_le hc (le_max_right _ _)

theorem clippedLogStep_zero (c : ℝ) (n : ℕ) (hn : n < ⌊c⌋₊) :
    clippedLogStep c n = 0 := by
  have hnf : n+1 ≤ ⌊c⌋₊ := by omega
  have hc : 0 ≤ c := by
    by_contra hc
    have hf : ⌊c⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  have hnc : (n:ℝ)+1 ≤ c := by
    have hh : ((n+1:ℕ):ℝ) ≤ (⌊c⌋₊:ℝ) := by exact_mod_cast hnf
    push_cast at hh
    exact hh.trans (Nat.floor_le hc)
  simp [clippedLogStep,clippedLog,max_eq_right hnc,max_eq_right (show (n:ℝ) ≤ c by linarith)]

theorem clippedLogStep_antitone_tail (c : ℝ) (hc : 0 < c) (n : ℕ)
    (hn : ⌊c⌋₊+1 ≤ n) : clippedLogStep c (n+1) ≤ clippedLogStep c n := by
  have hnc : c < (n:ℝ) := by
    have hh : (⌊c⌋₊:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hn
    exact (Nat.lt_floor_add_one c).trans_le hh
  have hn0 : (0:ℝ) < n := hc.trans hnc
  have hn1 : c ≤ (n:ℝ)+1 := by linarith
  have hn2 : c ≤ (n:ℝ)+1+1 := by linarith
  simp only [clippedLogStep,clippedLog,Nat.cast_add,Nat.cast_one,
    max_eq_left hnc.le,max_eq_left hn1,max_eq_left hn2]
  rw [← Real.log_div (by positivity : (n:ℝ)+1+1 ≠ 0) (by positivity : (n:ℝ)+1 ≠ 0),
    ← Real.log_div (by positivity : (n:ℝ)+1 ≠ 0) (ne_of_gt hn0)]
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ (by positivity) hn0).mpr
  nlinarith

theorem clippedLogStep_variation (c : ℝ) (hc : 0 < c) :
    Summable (fun n => |clippedLogStep c (n+1)-clippedLogStep c n|) ∧
      clippedLogStep c 0+(∑' n : ℕ, |clippedLogStep c (n+1)-clippedLogStep c n|) ≤ 2/c := by
  have hh := one_jump_variation (clippedLogStep c) ⌊c⌋₊ (1/c)
    (clippedLogStep_bounds c hc) (clippedLogStep_zero c) (clippedLogStep_antitone_tail c hc)
  simpa [div_eq_mul_inv] using hh

theorem clippedLog_second_variation (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℤ => |clippedLog c ((n:ℝ)+2)-2*clippedLog c ((n:ℝ)+1)+clippedLog c n|) ∧
      (∑' n : ℤ, |clippedLog c ((n:ℝ)+2)-2*clippedLog c ((n:ℝ)+1)+clippedLog c n|) ≤ 2/c := by
  let f : ℤ → ℝ := fun n => |clippedLog c ((n:ℝ)+2)-2*clippedLog c ((n:ℝ)+1)+clippedLog c n|
  have hnat : ∀ n : ℕ, f n = |clippedLogStep c (n+1)-clippedLogStep c n| := by
    intro n
    dsimp [f,clippedLogStep]
    push_cast
    congr 1
    rw [show (n:ℝ)+1+1 = (n:ℝ)+2 by ring]
    ring
  have hneg : ∀ n : ℕ, f (-((n:ℤ)+1)) = if n = 0 then clippedLogStep c 0 else 0 := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hc0 : max (0:ℝ) c = c := max_eq_right hc.le
      have hc1 : max (-1:ℝ) c = c := max_eq_right (by linarith)
      simp only [f,Nat.cast_zero,zero_add,Int.cast_neg,Int.cast_one,neg_add_cancel,
        show (-1:ℝ)+2 = 1 by norm_num,clippedLog,hc0,hc1,if_pos rfl,
        clippedLogStep,Nat.cast_zero,zero_add]
      rw [show Real.log (max 1 c)-2*Real.log c+Real.log c = Real.log (max 1 c)-Real.log c by ring]
      apply abs_of_nonneg
      simpa [clippedLogStep,clippedLog,hc0] using (clippedLogStep_bounds c hc 0).1
    · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have h0 : -(n:ℝ)-1 ≤ c := by linarith
      have h1 : -(n:ℝ)-1+1 ≤ c := by linarith
      have h2 : -(n:ℝ)-1+2 ≤ c := by linarith
      dsimp [f]
      push_cast
      rw [show -((n:ℝ)+1) = -(n:ℝ)-1 by ring]
      simp only [clippedLog,max_eq_right h0,max_eq_right h1,max_eq_right h2,if_neg hn]
      rw [show Real.log c-2*Real.log c+Real.log c = 0 by ring]
      exact abs_zero
  have hv := clippedLogStep_variation c hc
  have hsNat : Summable (fun n : ℕ => f n) := by simpa only [hnat] using hv.1
  have hsNeg : Summable (fun n : ℕ => f (-((n:ℤ)+1))) := by
    simp_rw [hneg]
    exact (hasSum_ite_eq (0:ℕ) (clippedLogStep c 0)).summable
  refine ⟨hsNat.of_nat_of_neg_add_one hsNeg,?_⟩
  change (∑' n : ℤ, f n) ≤ _
  rw [tsum_of_nat_of_neg_add_one hsNat hsNeg]
  simp_rw [hnat,hneg]
  simpa [add_comm] using hv.2

end HelfgottQuadratic

end

section

open scoped BigOperators
namespace HelfgottQuadratic

theorem clippedLog_eq_max_log (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    clippedLog c t = max (Real.log t) (Real.log c) := by
  by_cases htc : t ≤ c
  · simp [clippedLog,max_eq_right htc,max_eq_right (Real.log_le_log ht htc)]
  · have hct := (le_of_not_ge htc)
    simp [clippedLog,max_eq_left hct,max_eq_left (Real.log_le_log hc hct)]

theorem log_tent_identity (L Y b : ℝ) (hb : 0 ≤ b) :
    max (b-|b+L-Y|) 0 = max L (Y-2*b)-2*max L (Y-b)+max L Y := by
  by_cases h0 : L ≤ Y-2*b
  · have h1 : L ≤ Y-b := by linarith
    have h2 : L ≤ Y := by linarith
    rw [max_eq_right h0,max_eq_right h1,max_eq_right h2,
      abs_of_nonpos (show b+L-Y ≤ 0 by linarith),max_eq_right (by linarith)]
    ring
  · by_cases h1 : L ≤ Y-b
    · have h2 : L ≤ Y := by linarith
      rw [max_eq_left (by linarith : Y-2*b ≤ L),max_eq_right h1,max_eq_right h2,
        abs_of_nonpos (show b+L-Y ≤ 0 by linarith),max_eq_left (by linarith)]
      ring
    · by_cases h2 : L ≤ Y
      · rw [max_eq_left (by linarith : Y-2*b ≤ L),max_eq_left (by linarith : Y-b ≤ L),
          max_eq_right h2,abs_of_nonneg (show 0 ≤ b+L-Y by linarith),max_eq_left (by linarith)]
        ring
      · rw [max_eq_left (by linarith : Y-2*b ≤ L),max_eq_left (by linarith : Y-b ≤ L),
          max_eq_left (by linarith : Y ≤ L),abs_of_nonneg (show 0 ≤ b+L-Y by linarith),
          max_eq_right (by linarith)]
        ring

theorem etaTwo_clippedLog (y t : ℝ) (hy : 0 < y) :
    Helfgott.etaTwo (t/y) =
      4*(clippedLog (y/4) t-2*clippedLog (y/2) t+clippedLog y t) := by
  have hy2 : 0 < y/2 := by positivity
  have hy4 : 0 < y/4 := by positivity
  have hl2 : Real.log (y/2) = Real.log y-Real.log 2 := Real.log_div (ne_of_gt hy) (by norm_num)
  have hl4 : Real.log (y/4) = Real.log y-2*Real.log 2 := by
    rw [Real.log_div (ne_of_gt hy) (by norm_num),show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  by_cases ht : 0 < t
  · rw [Helfgott.etaTwo,if_pos (div_pos ht hy),clippedLog_eq_max_log _ _ hy4 ht,
      clippedLog_eq_max_log _ _ hy2 ht,clippedLog_eq_max_log _ _ hy ht,hl2,hl4]
    have hlog : Real.log (2*(t/y)) = Real.log 2+Real.log t-Real.log y := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (div_pos ht hy)),Real.log_div (ne_of_gt ht) (ne_of_gt hy)]
      ring
    rw [hlog,log_tent_identity (Real.log t) (Real.log y) (Real.log 2) (Real.log_nonneg (by norm_num))]
  · have ht0 : t ≤ 0 := le_of_not_gt ht
    rw [Helfgott.etaTwo,if_neg (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg ht0 hy.le))]
    simp only [clippedLog,max_eq_right (ht0.trans hy4.le),max_eq_right (ht0.trans hy2.le),
      max_eq_right (ht0.trans hy.le),hl2,hl4]
    ring

theorem etaTwo_second_variation (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℤ => |Helfgott.etaTwo (((n:ℝ)+2)/y)-
      2*Helfgott.etaTwo (((n:ℝ)+1)/y)+Helfgott.etaTwo ((n:ℝ)/y)|) ∧
    (∑' n : ℤ, |Helfgott.etaTwo (((n:ℝ)+2)/y)-
      2*Helfgott.etaTwo (((n:ℝ)+1)/y)+Helfgott.etaTwo ((n:ℝ)/y)|) ≤ 72/y := by
  let d : ℝ → ℤ → ℝ := fun c n => clippedLog c ((n:ℝ)+2)-2*clippedLog c ((n:ℝ)+1)+clippedLog c n
  let f : ℤ → ℝ := fun n => |Helfgott.etaTwo (((n:ℝ)+2)/y)-
      2*Helfgott.etaTwo (((n:ℝ)+1)/y)+Helfgott.etaTwo ((n:ℝ)/y)|
  have hpoint : ∀ n, f n ≤ 4*|d (y/4) n|+8*|d (y/2) n|+4*|d y n| := by
    intro n
    have heq : f n = |4*d (y/4) n-8*d (y/2) n+4*d y n| := by
      dsimp [f,d]
      simp_rw [etaTwo_clippedLog y _ hy]
      congr 1
      ring
    rw [heq]
    calc
      _ ≤ |4*d (y/4) n-8*d (y/2) n|+|4*d y n| := abs_add_le _ _
      _ ≤ (|4*d (y/4) n|+|8*d (y/2) n|)+|4*d y n| := add_le_add (abs_sub _ _) le_rfl
      _ = _ := by simp [abs_mul]
  have h4 := clippedLog_second_variation (y/4) (by positivity)
  have h2 := clippedLog_second_variation (y/2) (by positivity)
  have h1 := clippedLog_second_variation y hy
  have hmajor : Summable (fun n : ℤ => 4*|d (y/4) n|+8*|d (y/2) n|+4*|d y n|) :=
    ((h4.1.mul_left 4).add (h2.1.mul_left 8)).add (h1.1.mul_left 4)
  have hf : Summable f := Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpoint hmajor
  refine ⟨hf,?_⟩
  change (∑' n : ℤ, f n) ≤ _
  calc
    _ ≤ (∑' n : ℤ, (4*|d (y/4) n|+8*|d (y/2) n|+4*|d y n|)) := hf.tsum_le_tsum hpoint hmajor
    _ = 4*(∑' n : ℤ, |d (y/4) n|)+8*(∑' n : ℤ, |d (y/2) n|)+4*(∑' n : ℤ, |d y n|) := by
      rw [Summable.tsum_add ((h4.1.mul_left 4).add (h2.1.mul_left 8)) (h1.1.mul_left 4),
        Summable.tsum_add (h4.1.mul_left 4) (h2.1.mul_left 8)]
      simp only [tsum_mul_left,d]
    _ ≤ 4*(2/(y/4))+8*(2/(y/2))+4*(2/y) := by
      have hh4 := h4.2
      have hh2 := h2.2
      have hh1 := h1.2
      change (∑' n : ℤ, |d (y/4) n|) ≤ _ at hh4
      change (∑' n : ℤ, |d (y/2) n|) ≤ _ at hh2
      change (∑' n : ℤ, |d y n|) ≤ _ at hh1
      linarith
    _ = 72/y := by ring

end HelfgottQuadratic

end

section

open scoped BigOperators
namespace HelfgottQuadratic

theorem summable_twisted (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (z : ℂ) (hz : ‖z‖ = 1) : Summable (fun n => a n*z^n) := by
  apply ha.of_norm_bounded
  intro n
  simp [norm_mul,norm_zpow,hz]

theorem summable_backward (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    Summable (fun n => ‖a (n-1)-a n‖) := by
  have hshift : Summable (fun n : ℤ => ‖a (n-1)‖) :=
    ((Equiv.subRight (1:ℤ)).summable_iff).mpr ha
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_sub_le _ _) (hshift.add ha)

theorem backward_twisted_identity (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (z : ℂ) (hz : ‖z‖ = 1) :
    (∑' n : ℤ, (a (n-1)-a n)*z^n) = (z-1)*(∑' n : ℤ, a n*z^n) := by
  have hz0 : z ≠ 0 := by intro hh; simp [hh] at hz
  have hshift : Summable (fun n : ℤ => ‖a (n-1)‖) :=
    ((Equiv.subRight (1:ℤ)).summable_iff).mpr ha
  have hs1 := summable_twisted (fun n => a (n-1)) hshift z hz
  have hs0 := summable_twisted a ha z hz
  have heq : (∑' n : ℤ, a (n-1)*z^n) = z*(∑' n : ℤ, a n*z^n) := by
    rw [← (Equiv.addRight (1:ℤ)).tsum_eq (fun n : ℤ => a (n-1)*z^n)]
    simp only [Equiv.coe_addRight,add_sub_cancel_right,zpow_add₀ hz0,zpow_one]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  simp_rw [sub_mul]
  rw [hs1.tsum_sub hs0,heq]
  ring

theorem second_difference_twisted_identity (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (z : ℂ) (hz : ‖z‖ = 1) :
    (∑' n : ℤ, (a (n-2)-2*a (n-1)+a n)*z^n) = (z-1)^2*(∑' n : ℤ, a n*z^n) := by
  have hh := backward_twisted_identity (fun n => a (n-1)-a n) (summable_backward a ha) z hz
  rw [backward_twisted_identity a ha z hz] at hh
  have heq : ∀ n : ℤ, (a (n-1-1)-a (n-1))-(a (n-1)-a n) = a (n-2)-2*a (n-1)+a n := by
    intro n
    rw [show n-1-1 = n-2 by omega]
    ring
  simpa only [heq,pow_two,mul_assoc] using hh

theorem second_difference_twisted_bound (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z-1‖^2*‖∑' n : ℤ, a n*z^n‖ ≤ ∑' n : ℤ, ‖a (n-2)-2*a (n-1)+a n‖ := by
  have hdiff : Summable (fun n : ℤ => ‖a (n-2)-2*a (n-1)+a n‖) := by
    have hh := summable_backward (fun n => a (n-1)-a n) (summable_backward a ha)
    convert hh using 1
    ext n
    congr 1
    rw [show n-1-1 = n-2 by omega]
    ring
  have htwist : Summable (fun n : ℤ => ‖(a (n-2)-2*a (n-1)+a n)*z^n‖) := by
    simpa only [norm_mul,norm_zpow,hz,one_zpow,mul_one] using hdiff
  have hh := norm_tsum_le_tsum_norm htwist
  rw [second_difference_twisted_identity a ha z hz] at hh
  simpa only [norm_mul,norm_pow,norm_zpow,hz,one_zpow,mul_one] using hh

theorem second_difference_exponential_bound (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖)) (theta : ℝ) :
    4*(Real.sin (Real.pi*theta))^2*
      ‖∑' n : ℤ, a n*(Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n‖ ≤
        ∑' n : ℤ, ‖a (n-2)-2*a (n-1)+a n‖ := by
  have hz : ‖Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  have hnorm : ‖Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))-1‖^2 =
      4*(Real.sin (Real.pi*theta))^2 := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show 2*Real.pi*theta/2 = Real.pi*theta by ring]
    simp only [Real.norm_eq_abs,sq_abs]
    ring
  have hh := second_difference_twisted_bound a ha _ hz
  rwa [hnorm] at hh

end HelfgottQuadratic

end

section

open Finset
open scoped BigOperators
namespace HelfgottQuadratic

theorem etaTwo_zero_nonpos (t : ℝ) (ht : t ≤ 0) : Helfgott.etaTwo t = 0 := by
  simp [Helfgott.etaTwo,not_lt.mpr ht]

theorem etaTwo_zero_large (y t : ℝ) (hy : 0 < y) (ht : y ≤ t) :
    Helfgott.etaTwo (t/y) = 0 := by
  rw [etaTwo_clippedLog y t hy]
  have ht2 : y/2 ≤ t := by linarith
  have ht4 : y/4 ≤ t := by linarith
  simp only [clippedLog,max_eq_left ht,max_eq_left ht2,max_eq_left ht4]
  ring

theorem etaTwo_nonneg (t : ℝ) : 0 ≤ Helfgott.etaTwo t := by
  unfold Helfgott.etaTwo
  split_ifs
  · positivity
  · rfl

theorem etaTwo_le_log_two (t : ℝ) : Helfgott.etaTwo t ≤ 4*Real.log 2 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold Helfgott.etaTwo
  split_ifs
  · exact mul_le_mul_of_nonneg_left (max_le (sub_le_self _ (abs_nonneg _)) hl) (by norm_num)
  · positivity

theorem etaTwo_int_support (y : ℝ) (hy : 0 < y) (n : ℤ)
    (hn : n ∉ Icc (1:ℤ) ⌊y⌋) : Helfgott.etaTwo ((n:ℝ)/y) = 0 := by
  by_cases hn0 : n < 1
  · apply etaTwo_zero_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (show n ≤ 0 by omega)) hy.le
  · have hnf : ⌊y⌋ < n := by simp only [mem_Icc,not_and_or,not_le] at hn; omega
    have hny : y ≤ (n:ℝ) := by
      have hh : (⌊y⌋:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hnf
      exact (Int.lt_floor_add_one y).le.trans hh
    exact etaTwo_zero_large y n hy hny

theorem etaTwo_int_summable (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℤ => ‖((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)‖) := by
  apply summable_of_ne_finset_zero (s := Icc (1:ℤ) ⌊y⌋)
  intro n hn
  simp [etaTwo_int_support y hy n hn]

theorem etaTwo_int_energy (y : ℝ) (hy : 0 < y) :
    (∑' n : ℤ, ‖((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)‖) ≤ (4*Real.log 2)*(⌊y⌋₊:ℝ) := by
  rw [tsum_eq_sum (s := Icc (1:ℤ) ⌊y⌋) (fun n hn => by simp [etaTwo_int_support y hy n hn])]
  calc
    _ ≤ ∑ _n ∈ Icc (1:ℤ) ⌊y⌋, 4*Real.log 2 := by
      apply sum_le_sum
      intro n hn
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (etaTwo_nonneg _)] using etaTwo_le_log_two ((n:ℝ)/y)
    _ = (4*Real.log 2)*(⌊y⌋₊:ℝ) := by simp [Int.card_Icc,Int.floor_toNat,mul_comm]

theorem etaTwo_int_second_bound (y : ℝ) (hy : 0 < y) :
    (∑' n : ℤ, ‖((Helfgott.etaTwo (((n-2:ℤ):ℝ)/y)):ℂ)-
        2*((Helfgott.etaTwo (((n-1:ℤ):ℝ)/y)):ℂ)+((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)‖) ≤ 72/y := by
  let f : ℤ → ℝ := fun n => |Helfgott.etaTwo (((n:ℝ)+2)/y)-
      2*Helfgott.etaTwo (((n:ℝ)+1)/y)+Helfgott.etaTwo ((n:ℝ)/y)|
  have heq : ∀ n : ℤ, ‖((Helfgott.etaTwo (((n-2:ℤ):ℝ)/y)):ℂ)-
        2*((Helfgott.etaTwo (((n-1:ℤ):ℝ)/y)):ℂ)+((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)‖ = f (n-2) := by
    intro n
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_eq_abs]
    dsimp [f]
    push_cast
    rw [show (n:ℝ)-2+2 = (n:ℝ) by ring,show (n:ℝ)-2+1 = (n:ℝ)-1 by ring]
    congr 1
    ring
  simp_rw [heq]
  have hh := (Equiv.subRight (2:ℤ)).tsum_eq f
  change (∑' n : ℤ, f (n-2)) = (∑' n : ℤ, f n) at hh
  rw [hh]
  exact (etaTwo_second_variation y hy).2

theorem etaTwo_int_sum_eq_expSum (y theta : ℝ) (hy : 0 < y) :
    (∑' n : ℤ, ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*
      (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n) =
        Helfgott.expSum (fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ)) := by
  let z := Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))
  let f : ℤ → ℂ := fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*z^n
  have hz : ‖z‖ = 1 := by simp [z,Complex.norm_exp]
  have hs : Summable f := summable_twisted _ (etaTwo_int_summable y hy) z hz
  have hneg : ∀ n : ℕ, f (-((n:ℤ)+1)) = 0 := by
    intro n
    have hn : ((-((n:ℤ)+1):ℤ):ℝ)/y ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hy.le
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    simp only [f,etaTwo_zero_nonpos _ hn,Complex.ofReal_zero,zero_mul]
  change (∑' n : ℤ, f n) = _
  rw [tsum_of_nat_of_neg_add_one (hs.comp_injective Nat.cast_injective)
    (hs.comp_injective (by
      intro n m h
      apply Nat.cast_injective (R:=ℤ)
      linarith : Function.Injective (fun n:ℕ => -((n:ℤ)+1))))]
  simp_rw [hneg]
  rw [tsum_zero,add_zero]
  unfold Helfgott.expSum
  apply tsum_congr
  intro n
  change ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*z^(n:ℤ) =
    ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*fourier (n:ℤ) (theta:AddCircle (1:ℝ))
  apply congrArg (fun w : ℂ => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*w)
  change (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^(n:ℤ) =
    fourier (n:ℤ) (theta:AddCircle (1:ℝ))
  rw [fourier_coe_apply,← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem etaTwo_expSum_quadratic (y theta : ℝ) (hy : 0 < y) :
    4*(Real.sin (Real.pi*theta))^2*
      ‖Helfgott.expSum (fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤ 72/y := by
  have hh := second_difference_exponential_bound _ (etaTwo_int_summable y hy) theta
  rw [etaTwo_int_sum_eq_expSum y theta hy] at hh
  exact hh.trans (etaTwo_int_second_bound y hy)

theorem etaTwo_expSum_trivial (y theta : ℝ) (hy : 0 < y) :
    ‖Helfgott.expSum (fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      (4*Real.log 2)*(⌊y⌋₊:ℝ) := by
  rw [← etaTwo_int_sum_eq_expSum y theta hy]
  have hs := etaTwo_int_summable y hy
  have hz : ‖Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))‖ = 1 := by simp [Complex.norm_exp]
  have hnorm : ∀ n : ℤ, ‖((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*
      (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n‖ = ‖((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)‖ := by
    intro n
    simp only [norm_mul,norm_zpow,hz,one_zpow,mul_one]
  have hh := norm_tsum_le_tsum_norm (show Summable (fun n : ℤ => ‖((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*
      (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n‖) by simpa only [hnorm] using hs)
  simp_rw [hnorm] at hh
  exact hh.trans (etaTwo_int_energy y hy)

theorem etaTwo_expSum_quadratic_cap (y theta : ℝ) (hy : 0 < y) :
    ‖Helfgott.expSum (fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      if Real.sin (Real.pi*theta) = 0 then (4*Real.log 2)*(⌊y⌋₊:ℝ)
      else min ((4*Real.log 2)*(⌊y⌋₊:ℝ)) (18/(y*(Real.sin (Real.pi*theta))^2)) := by
  by_cases hsin : Real.sin (Real.pi*theta) = 0
  · rw [if_pos hsin]
    exact etaTwo_expSum_trivial y theta hy
  · rw [if_neg hsin]
    refine le_min (etaTwo_expSum_trivial y theta hy) ?_
    apply (le_div_iff₀ (mul_pos hy (sq_pos_of_ne_zero hsin))).mpr
    have hh := (le_div_iff₀ hy).mp (etaTwo_expSum_quadratic y theta hy)
    nlinarith

end HelfgottQuadratic

end

section
/- Arithmetic and finite-convolution infrastructure retained from accepted
Prove2Me submission 63b25d14-2999-434f-b84f-5af50fbd02fa by raresbuhai,
published October 6, 2026. Apache 2.0. The analytic cancellation proof is omitted;
the new quadratic estimate is supplied separately. -/

open Finset
open scoped BigOperators
namespace Helfgott

lemma etaTwo_eq_zero_of_not_mem (t : ℝ) (ht : t ∉ Set.Icc (1/4 : ℝ) 1) :
    etaTwo t = 0 := by
  by_cases hpos : 0 < t
  · unfold etaTwo
    rw [if_pos hpos]
    have htwopos : 0 < 2*t := by positivity
    have hm : Real.log 2 - |Real.log (2*t)| ≤ 0 := by
      rcases (not_and_or.mp ht) with hlo | hhi
      · have hlt : 2*t ≤ (1/2 : ℝ) := by push_neg at hlo; linarith
        have hlog := Real.log_le_log htwopos hlt
        have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        rw [hhalf] at hlog
        linarith [neg_le_abs (Real.log (2*t))]
      · have hlt : (2 : ℝ) ≤ 2*t := by push_neg at hhi; linarith
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlt
        linarith [le_abs_self (Real.log (2*t))]
    rw [max_eq_right hm, mul_zero]
  · simp [etaTwo,hpos]


lemma etaTwo_arithmetic_eq_zero (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 (Nat.floor y)) : f n*etaTwo ((n : ℝ)/y) = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hfloor : Nat.floor y < n := by simpa [Finset.mem_Ioc,hnpos] using hn
    have hlarge : y < (n : ℝ) := Nat.lt_of_floor_lt hfloor
    have hz : etaTwo ((n : ℝ)/y) = 0 := by
      apply etaTwo_eq_zero_of_not_mem
      intro hm
      have hh := (div_le_iff₀ hy).mp hm.2
      linarith
    rw [hz,mul_zero]

lemma etaTwo_arithmetic_summable (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) := by
  apply summable_of_ne_finset_zero (s := Finset.Ioc 0 (Nat.floor y))
  intro n hn
  rw [etaTwo_arithmetic_eq_zero f y hy n hn]
  simp

lemma etaTwo_arithmetic_expSum_finite (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ n ∈ Finset.Ioc 0 (Nat.floor y), ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α := by
  unfold expSum
  apply tsum_eq_sum
  intro n hn
  dsimp only
  rw [etaTwo_arithmetic_eq_zero f y hy n hn]
  simp


theorem truncated_divisor_sum_complex (B : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

lemma etaTwo_convolution_expSum_hyperbola (f g : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => (((f*g) n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc 1 (Nat.floor y), ∑ m ∈ Finset.Icc 1 (Nat.floor (y/(d : ℝ))),
        ((f d*g m*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α := by
  have hindex : Finset.Ioc 0 (Nat.floor y) = Finset.Icc 1 (Nat.floor y) := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  let F (d m : ℕ) : ℂ :=
    ((f d*g m*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α
  rw [etaTwo_arithmetic_expSum_finite _ y hy α,hindex]
  have hinner (k : ℕ) :
      (((f*g) k*etaTwo ((k : ℝ)/y) : ℝ) : ℂ)*fourier (k : ℤ) α =
      ∑ d ∈ k.divisors, F d (k/d) := by
    rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b => f a*g b)]
    rw [Complex.ofReal_mul,Complex.ofReal_sum,Finset.sum_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have he : d*(k/d) = k := Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
    simp only [F,he,Complex.ofReal_mul]
  simp_rw [hinner]
  rw [truncated_divisor_sum_complex]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.floor_div_natCast]


lemma sum_Icc_of_high_zero (F : ℕ → ℂ) (U B : ℕ) (hF : ∀ n, U < n → F n = 0) :
    (∑ n ∈ Finset.Icc 1 B, F n) = ∑ n ∈ Finset.Icc 1 (min U B), F n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    exact Finset.mem_Icc.mpr ⟨h1,h2.trans (min_le_right _ _)⟩
  · intro n hn hnot
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    have hnU : U < n := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨h1,le_min (le_of_not_gt h) h2⟩)
    exact hF n hnU


lemma arithmeticCutoff_convolution_zero_above (U V n : ℕ) (f g : ArithmeticFunction ℝ)
    (hn : U*V < n) : (arithmeticCutoff U f*arithmeticCutoff V g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod : p.1*p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases hU : p.1 ≤ U
  · have hV : ¬p.2 ≤ V := by
      intro h
      have hh := Nat.mul_le_mul hU h
      rw [hprod] at hh
      omega
    simp [arithmeticCutoff,hV]
  · simp [arithmeticCutoff,hU]

lemma vaughan_correction_expSum (U V : ℕ) (y : ℝ) (hy : 0 < y) (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc 1 (min (U*V) (Nat.floor y)),
        (((arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
          arithmeticCutoff V ArithmeticFunction.vonMangoldt) d : ℝ) : ℂ)*
        (∑ m ∈ Finset.Icc 1 (Nat.floor (y/(d : ℝ))),
          ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α) := by
  rw [vaughanCorrection,etaTwo_convolution_expSum_hyperbola _ _ y hy α]
  rw [sum_Icc_of_high_zero (U := U*V)]
  · apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1;omega
    simp only [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hm0,Nat.cast_one,mul_one,
      Complex.ofReal_mul,mul_assoc]
  · intro d hd
    rw [arithmeticCutoff_convolution_zero_above U V d _ _ hd]
    simp


lemma fourier_product_frequency (d m : ℕ) (α : AddCircle (1 : ℝ)) :
    fourier ((d*m : ℕ) : ℤ) α = fourier (m : ℤ) ((d : ℤ) • α) := by
  simp only [fourier_apply,Nat.cast_mul,smul_smul,mul_comm]

lemma etaTwo_product_scale (d m : ℕ) (hd : 0 < d) (y : ℝ) (hy : 0 < y) :
    etaTwo (((d*m : ℕ) : ℝ)/y) = etaTwo ((m : ℝ)/(y/(d : ℝ))) := by
  congr 1
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp


lemma arithmeticCutoff_moebius_abs_le (U n : ℕ) :
    |arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ) n| ≤ 1 := by
  change |if n ≤ U then ((ArithmeticFunction.moebius n : ℤ) : ℝ) else 0| ≤ 1
  by_cases hn : n ≤ U
  · rw [if_pos hn]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · simp [hn]

lemma arithmeticCutoff_vonMangoldt_bounds (V n : ℕ) :
    0 ≤ arithmeticCutoff V ArithmeticFunction.vonMangoldt n ∧
      arithmeticCutoff V ArithmeticFunction.vonMangoldt n ≤ ArithmeticFunction.vonMangoldt n := by
  change (0 ≤ if n ≤ V then ArithmeticFunction.vonMangoldt n else 0) ∧
    (if n ≤ V then ArithmeticFunction.vonMangoldt n else 0) ≤ ArithmeticFunction.vonMangoldt n
  by_cases hn : n ≤ V
  · simp only [if_pos hn]
    exact ⟨ArithmeticFunction.vonMangoldt_nonneg,le_rfl⟩
  · simp only [if_neg hn]
    exact ⟨le_rfl,ArithmeticFunction.vonMangoldt_nonneg⟩

lemma vaughan_correction_coefficient_abs_le (U V d : ℕ) :
    |(arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      arithmeticCutoff V ArithmeticFunction.vonMangoldt) d| ≤ Real.log (d : ℝ) := by
  have he : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)*ArithmeticFunction.vonMangoldt) d =
      Real.log (d : ℝ) := by
    rw [mul_comm,ArithmeticFunction.vonMangoldt_mul_zeta,ArithmeticFunction.log_apply]
  rw [← he,ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hd : d ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hp).2
  have hprod : p.1*p.2 = d := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hp1 : p.1 ≠ 0 := by intro h;rw [h,zero_mul] at hprod;exact hd hprod.symm
  rw [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hp1,Nat.cast_one,one_mul,
    abs_mul,abs_of_nonneg (arithmeticCutoff_vonMangoldt_bounds V p.2).1]
  calc
    _ ≤ 1*arithmeticCutoff V ArithmeticFunction.vonMangoldt p.2 :=
      mul_le_mul_of_nonneg_right (arithmeticCutoff_moebius_abs_le U p.1)
        (arithmeticCutoff_vonMangoldt_bounds V p.2).1
    _ ≤ _ := by simpa only [one_mul] using (arithmeticCutoff_vonMangoldt_bounds V p.2).2


end Helfgott

end

section
/- Piecewise etaTwo formulas and monotonicity below are retained from accepted
Prove2Me submission 63b25d14-2999-434f-b84f-5af50fbd02fa by raresbuhai,
Apache 2.0, with the local namespace changed. The discrete variation proof
will be added separately. -/

open Helfgott Finset
open scoped BigOperators
namespace HelfgottQuadratic

lemma etaTwo_eq_lower (t : ℝ) (ht : t ∈ Set.Icc (1/4 : ℝ) (1/2)) :
    etaTwo t = 4 * Real.log (4*t) := by
  have hpos : 0 < t := by linarith [ht.1]
  have hprod : 0 < 2*t := by positivity
  have hlogneg : Real.log (2*t) ≤ 0 := Real.log_nonpos (le_of_lt hprod) (by linarith [ht.2])
  have hsum : Real.log 2 + Real.log (2*t) = Real.log (4*t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hprod)]
    congr 1; ring
  have hn : 0 ≤ Real.log (4*t) := Real.log_nonneg (by linarith [ht.1])
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonpos hlogneg, sub_neg_eq_add, hsum, max_eq_left hn]

lemma etaTwo_eq_upper (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    etaTwo t = -4 * Real.log t := by
  have hpos : 0 < t := by linarith [ht.1]
  have hlogpos : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith [ht.1])
  have hlogneg : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt hpos) ht.2
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt hpos)
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonneg hlogpos, hlog]
  have hm : Real.log 2 - (Real.log 2 + Real.log t) = -Real.log t := by ring
  rw [hm, max_eq_left (neg_nonneg.mpr hlogneg)]
  ring


lemma etaTwo_monotone_lower (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 1/2) :
    etaTwo s ≤ etaTwo t := by
  by_cases hs : 0 < s
  · have ht0 : 0 < t := hs.trans_le hst
    have hls : Real.log (2*s) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    have hlt : Real.log (2*t) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    have hlog : Real.log (2*s) ≤ Real.log (2*t) := Real.log_le_log (by positivity) (by linarith)
    simp only [etaTwo,if_pos hs,if_pos ht0,abs_of_nonpos hls,abs_of_nonpos hlt]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply max_le_max_right
    linarith
  · simpa [etaTwo,hs] using etaTwo_nonneg t

lemma etaTwo_antitone_upper (s t : ℝ) (hst : s ≤ t) (hs : 1/2 ≤ s) :
    etaTwo t ≤ etaTwo s := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := hs0.trans_le hst
  have hls : 0 ≤ Real.log (2*s) := Real.log_nonneg (by linarith)
  have hlt : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2*s) ≤ Real.log (2*t) := Real.log_le_log (by positivity) (by linarith)
  simp only [etaTwo,if_pos hs0,if_pos ht0,abs_of_nonneg hls,abs_of_nonneg hlt]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply max_le_max_right
  linarith


theorem single_peak_variation_partial (g : ℕ → ℝ) (k : ℕ)
    (hmono : ∀ n, n < k → g n ≤ g (n+1))
    (hanti : ∀ n, k+1 ≤ n → g (n+1) ≤ g n) (N : ℕ) :
    g 0+(∑ n ∈ range N, |g (n+1)-g n|) =
      if N ≤ k then g N else g k+|g (k+1)-g k|+g (k+1)-g N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ,← add_assoc,ih]
    by_cases hNk : N < k
    · have hN : N ≤ k := by omega
      have hN1 : N+1 ≤ k := by omega
      rw [if_pos hN,if_pos hN1,abs_of_nonneg (sub_nonneg.mpr (hmono N hNk))]
      ring
    · by_cases hNe : N = k
      · subst N
        simp only [le_refl,if_true,show ¬k+1 ≤ k by omega,if_false]
        ring
      · have hN : ¬N ≤ k := by omega
        have hN1 : ¬N+1 ≤ k := by omega
        rw [if_neg hN,if_neg hN1,abs_of_nonpos (sub_nonpos.mpr (hanti N (by omega)))]
        ring

theorem single_peak_variation (g : ℕ → ℝ) (k : ℕ) (B : ℝ)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ B) (hmono : ∀ n, n < k → g n ≤ g (n+1))
    (hanti : ∀ n, k+1 ≤ n → g (n+1) ≤ g n) :
    Summable (fun n => |g (n+1)-g n|) ∧
      g 0+(∑' n : ℕ, |g (n+1)-g n|) ≤ 2*B := by
  have hpartial : ∀ N, (∑ n ∈ range N, |g (n+1)-g n|) ≤ 2*B-g 0 := by
    intro N
    have hh := single_peak_variation_partial g k hmono hanti N
    by_cases hN : N ≤ k
    · rw [if_pos hN] at hh
      have hB : 0 ≤ B := (hg 0).1.trans (hg 0).2
      linarith [(hg N).2]
    · rw [if_neg hN] at hh
      have habs : |g (k+1)-g k| ≤ 2*B-g k-g (k+1) := by
        apply abs_le.mpr
        constructor <;> linarith [(hg k).2,(hg (k+1)).2]
      linarith [(hg N).1]
  refine ⟨summable_of_sum_range_le (fun n => abs_nonneg _) hpartial,?_⟩
  have hh := Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _) hpartial
  linarith

theorem etaTwo_first_variation_nat (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|) ∧
      (∑' n : ℕ, |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|) ≤ 8*Real.log 2 := by
  let g : ℕ → ℝ := fun n => etaTwo ((n:ℝ)/y)
  have hmono : ∀ n, n < ⌊y/2⌋₊ → g n ≤ g (n+1) := by
    intro n hn
    apply etaTwo_monotone_lower
    · apply div_le_div_of_nonneg_right _ hy.le
      push_cast
      linarith
    · apply (div_le_iff₀ hy).mpr
      have hnf : ((n+1:ℕ):ℝ) ≤ (⌊y/2⌋₊:ℝ) := by exact_mod_cast (show n+1 ≤ ⌊y/2⌋₊ by omega)
      have hfl := Nat.floor_le (show 0 ≤ y/2 by positivity)
      linarith
  have hanti : ∀ n, ⌊y/2⌋₊+1 ≤ n → g (n+1) ≤ g n := by
    intro n hn
    apply etaTwo_antitone_upper
    · apply div_le_div_of_nonneg_right _ hy.le
      push_cast
      linarith
    · apply (le_div_iff₀ hy).mpr
      have hnf : (⌊y/2⌋₊:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hn
      have hfl := Nat.lt_floor_add_one (y/2)
      linarith
  have hh := single_peak_variation g ⌊y/2⌋₊ (4*Real.log 2)
    (fun n => ⟨etaTwo_nonneg _,etaTwo_le_log_two _⟩) hmono hanti
  simpa only [g,Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_div,Helfgott.etaTwo,
    lt_self_iff_false,if_false,zero_add,show (2:ℝ)*(4*Real.log 2) = 8*Real.log 2 by ring] using hh

theorem etaTwo_first_variation (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℤ => |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|) ∧
      (∑' n : ℤ, |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|) ≤ 8*Real.log 2 := by
  let f : ℤ → ℝ := fun n => |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|
  have hsNat : Summable (fun n : ℕ => f n) := by simpa only [f,Int.cast_natCast] using (etaTwo_first_variation_nat y hy).1
  have hneg : ∀ n : ℕ, f (-((n:ℤ)+1)) = 0 := by
    intro n
    have h0 : ((-((n:ℤ)+1):ℤ):ℝ)/y ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hy.le
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    have h1 : (((-((n:ℤ)+1):ℤ):ℝ)+1)/y ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hy.le
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    simp only [f,etaTwo_zero_nonpos _ h0,etaTwo_zero_nonpos _ h1,sub_self,abs_zero]
  have hsNeg : Summable (fun n : ℕ => f (-((n:ℤ)+1))) := by simp only [hneg]; exact summable_zero
  refine ⟨hsNat.of_nat_of_neg_add_one hsNeg,?_⟩
  change (∑' n : ℤ, f n) ≤ _
  rw [tsum_of_nat_of_neg_add_one hsNat hsNeg]
  simp only [hneg,tsum_zero,add_zero]
  exact (etaTwo_first_variation_nat y hy).2

end HelfgottQuadratic

end

section

open Helfgott
open scoped BigOperators
namespace HelfgottQuadratic

theorem clippedLog_increment_bounds (c t : ℝ) (hc : 0 < c) :
    0 ≤ clippedLog c (t+1)-clippedLog c t ∧
      clippedLog c (t+1)-clippedLog c t ≤ 1/c := by
  have hlo : 0 < max t c := hc.trans_le (le_max_right _ _)
  have hhi : 0 < max (t+1) c := hc.trans_le (le_max_right _ _)
  have hmono : max t c ≤ max (t+1) c := max_le_max_right _ (by linarith)
  have hdiff : max (t+1) c-max t c ≤ 1 := by
    calc
      _ ≤ max ((t+1)-t) (c-c) := max_sub_max_le_max _ _ _ _
      _ = 1 := by norm_num
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hlo hmono)
  · have hh := Real.log_le_sub_one_of_pos (div_pos hhi hlo)
    rw [Real.log_div (ne_of_gt hhi) (ne_of_gt hlo)] at hh
    change Real.log (max (t+1) c)-Real.log (max t c) ≤ _
    calc
      _ ≤ max (t+1) c/max t c-1 := hh
      _ = (max (t+1) c-max t c)/max t c := by field_simp
      _ ≤ 1/max t c := div_le_div_of_nonneg_right hdiff hlo.le
      _ ≤ 1/c := one_div_le_one_div_of_le hc (le_max_right _ _)

theorem etaTwo_log_clipped (y t : ℝ) (hy : 0 < y) :
    Real.log t*etaTwo (t/y) = clippedLog (y/8) t*etaTwo (t/y) := by
  by_cases ht : y/8 ≤ t
  · simp [clippedLog,max_eq_left ht]
  · have ht' : t/y < 1/4 := (div_lt_iff₀ hy).mpr (by linarith)
    have hz := etaTwo_eq_zero_of_not_mem (t/y) (fun hh => (not_le_of_gt ht') hh.1)
    rw [hz,mul_zero,mul_zero]

theorem clippedLog_endpoint_bound (y t : ℝ) (hy : 8 ≤ y) (ht : t ≤ y) :
    |clippedLog (y/8) (t+2)| ≤ Real.log (y+2) := by
  have hlo : (1:ℝ) ≤ max (t+2) (y/8) := le_trans (by linarith) (le_max_right _ _)
  have hhi : max (t+2) (y/8) ≤ y+2 := max_le (by linarith) (by linarith)
  rw [clippedLog,abs_of_nonneg (Real.log_nonneg hlo)]
  exact Real.log_le_log (by linarith) hhi

theorem etaTwo_log_second_pointwise (y t : ℝ) (hy : 8 ≤ y) :
    |Real.log (t+2)*etaTwo ((t+2)/y)-2*(Real.log (t+1)*etaTwo ((t+1)/y))+
        Real.log t*etaTwo (t/y)| ≤
      Real.log (y+2)*|etaTwo ((t+2)/y)-2*etaTwo ((t+1)/y)+etaTwo (t/y)| +
      (16/y)*|etaTwo ((t+1)/y)-etaTwo (t/y)| +
      (4*Real.log 2)*|clippedLog (y/8) (t+2)-2*clippedLog (y/8) (t+1)+clippedLog (y/8) t| := by
  have hyp : 0 < y := by linarith
  let a := clippedLog (y/8)
  let b : ℝ → ℝ := fun t => etaTwo (t/y)
  have heq : Real.log (t+2)*etaTwo ((t+2)/y)-2*(Real.log (t+1)*etaTwo ((t+1)/y))+
        Real.log t*etaTwo (t/y) =
      a (t+2)*(b (t+2)-2*b (t+1)+b t)+2*(a (t+2)-a (t+1))*(b (t+1)-b t)+
        (a (t+2)-2*a (t+1)+a t)*b t := by
    simp_rw [etaTwo_log_clipped y _ hyp]
    dsimp [a,b]
    ring
  have hfirst : |a (t+2)*(b (t+2)-2*b (t+1)+b t)| ≤
      Real.log (y+2)*|b (t+2)-2*b (t+1)+b t| := by
    by_cases ht : t ≤ y
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (clippedLog_endpoint_bound y t hy ht) (abs_nonneg _)
    · have hb0 : b t = 0 := etaTwo_zero_large y t hyp (le_of_not_ge ht)
      have hb1 : b (t+1) = 0 := etaTwo_zero_large y (t+1) hyp (by linarith)
      have hb2 : b (t+2) = 0 := etaTwo_zero_large y (t+2) hyp (by linarith)
      simp [hb0,hb1,hb2]
  have hinc : |a (t+2)-a (t+1)| ≤ 8/y := by
    have hh := clippedLog_increment_bounds (y/8) (t+1) (by positivity)
    rw [show t+1+1 = t+2 by ring] at hh
    rw [abs_of_nonneg hh.1]
    convert hh.2 using 1 <;> ring
  have hcross : |2*(a (t+2)-a (t+1))*(b (t+1)-b t)| ≤ (16/y)*|b (t+1)-b t| := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      _ ≤ (2*(8/y))*|b (t+1)-b t| := by gcongr
      _ = _ := by ring
  have hlast : |(a (t+2)-2*a (t+1)+a t)*b t| ≤
      (4*Real.log 2)*|a (t+2)-2*a (t+1)+a t| := by
    rw [abs_mul,abs_of_nonneg (etaTwo_nonneg _)]
    calc
      _ ≤ |a (t+2)-2*a (t+1)+a t| * (4*Real.log 2) :=
        mul_le_mul_of_nonneg_left (etaTwo_le_log_two _) (abs_nonneg _)
      _ = _ := by ring
  rw [heq]
  calc
    _ ≤ |a (t+2)*(b (t+2)-2*b (t+1)+b t)+2*(a (t+2)-a (t+1))*(b (t+1)-b t)| +
        |(a (t+2)-2*a (t+1)+a t)*b t| := abs_add_le _ _
    _ ≤ (|a (t+2)*(b (t+2)-2*b (t+1)+b t)| + |2*(a (t+2)-a (t+1))*(b (t+1)-b t)|) +
        |(a (t+2)-2*a (t+1)+a t)*b t| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add hfirst hcross) hlast

theorem etaTwo_log_second_variation (y : ℝ) (hy : 8 ≤ y) :
    Summable (fun n : ℤ => |Real.log ((n:ℝ)+2)*etaTwo (((n:ℝ)+2)/y)-
      2*(Real.log ((n:ℝ)+1)*etaTwo (((n:ℝ)+1)/y))+Real.log (n:ℝ)*etaTwo ((n:ℝ)/y)|) ∧
    (∑' n : ℤ, |Real.log ((n:ℝ)+2)*etaTwo (((n:ℝ)+2)/y)-
      2*(Real.log ((n:ℝ)+1)*etaTwo (((n:ℝ)+1)/y))+Real.log (n:ℝ)*etaTwo ((n:ℝ)/y)|) ≤
        (72*Real.log (y+2)+192*Real.log 2)/y := by
  have hyp : 0 < y := by linarith
  let f : ℤ → ℝ := fun n => |Real.log ((n:ℝ)+2)*etaTwo (((n:ℝ)+2)/y)-
    2*(Real.log ((n:ℝ)+1)*etaTwo (((n:ℝ)+1)/y))+Real.log (n:ℝ)*etaTwo ((n:ℝ)/y)|
  let d2 : ℤ → ℝ := fun n => |etaTwo (((n:ℝ)+2)/y)-2*etaTwo (((n:ℝ)+1)/y)+etaTwo ((n:ℝ)/y)|
  let d1 : ℤ → ℝ := fun n => |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|
  let dc : ℤ → ℝ := fun n => |clippedLog (y/8) ((n:ℝ)+2)-2*clippedLog (y/8) ((n:ℝ)+1)+clippedLog (y/8) n|
  have hd2 := etaTwo_second_variation y hyp
  have hd1 := etaTwo_first_variation y hyp
  have hdc := clippedLog_second_variation (y/8) (by positivity)
  have hmajor : Summable (fun n : ℤ => Real.log (y+2)*d2 n+(16/y)*d1 n+(4*Real.log 2)*dc n) :=
    ((hd2.1.mul_left _).add (hd1.1.mul_left _)).add (hdc.1.mul_left _)
  have hpoint : ∀ n, f n ≤ Real.log (y+2)*d2 n+(16/y)*d1 n+(4*Real.log 2)*dc n :=
    fun n => etaTwo_log_second_pointwise y n hy
  have hf : Summable f := Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpoint hmajor
  refine ⟨hf,?_⟩
  change (∑' n : ℤ, f n) ≤ _
  calc
    _ ≤ ∑' n : ℤ, (Real.log (y+2)*d2 n+(16/y)*d1 n+(4*Real.log 2)*dc n) := hf.tsum_le_tsum hpoint hmajor
    _ = Real.log (y+2)*(∑' n : ℤ, d2 n)+(16/y)*(∑' n : ℤ, d1 n)+(4*Real.log 2)*(∑' n : ℤ, dc n) := by
      rw [Summable.tsum_add ((hd2.1.mul_left _).add (hd1.1.mul_left _)) (hdc.1.mul_left _),
        Summable.tsum_add (hd2.1.mul_left _) (hd1.1.mul_left _)]
      simp only [tsum_mul_left,d2,d1,dc]
    _ ≤ Real.log (y+2)*(72/y)+(16/y)*(8*Real.log 2)+(4*Real.log 2)*(2/(y/8)) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left hd2.2 (Real.log_nonneg (by linarith))
        · exact mul_le_mul_of_nonneg_left hd1.2 (by positivity)
      · exact mul_le_mul_of_nonneg_left hdc.2 (by positivity)
    _ = _ := by ring

end HelfgottQuadratic

end

section

open scoped BigOperators
namespace HelfgottQuadratic

theorem integer_sum_eq_expSum (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (hneg : ∀ n < (0:ℤ), a n = 0) (theta : ℝ) :
    (∑' n : ℤ, a n*(Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n) =
      Helfgott.expSum (fun n : ℕ => a n) (theta:AddCircle (1:ℝ)) := by
  let z := Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))
  let f : ℤ → ℂ := fun n => a n*z^n
  have hz : ‖z‖ = 1 := by simp [z,Complex.norm_exp]
  have hs : Summable f := summable_twisted a ha z hz
  have hzneg : ∀ n : ℕ, f (-((n:ℤ)+1)) = 0 := by
    intro n
    simp only [f,hneg (-((n:ℤ)+1)) (by omega),zero_mul]
  change (∑' n : ℤ, f n) = _
  rw [tsum_of_nat_of_neg_add_one (hs.comp_injective Nat.cast_injective)
    (hs.comp_injective (by
      intro n m h
      apply Nat.cast_injective (R:=ℤ)
      linarith : Function.Injective (fun n:ℕ => -((n:ℤ)+1))))]
  simp_rw [hzneg]
  rw [tsum_zero,add_zero]
  unfold Helfgott.expSum
  apply tsum_congr
  intro n
  change a n*z^(n:ℤ) = a n*fourier (n:ℤ) (theta:AddCircle (1:ℝ))
  apply congrArg (fun w:ℂ => a n*w)
  change (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^(n:ℤ) =
    fourier (n:ℤ) (theta:AddCircle (1:ℝ))
  rw [fourier_coe_apply,← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem real_sampled_expSum_second_difference (w : ℝ → ℝ)
    (hw : Summable (fun n : ℤ => ‖((w n):ℂ)‖))
    (hneg : ∀ t ≤ (0:ℝ), w t = 0) (theta : ℝ) :
    4*(Real.sin (Real.pi*theta))^2*
      ‖Helfgott.expSum (fun n => ((w (n:ℝ)):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
        ∑' n : ℤ, |w ((n:ℝ)+2)-2*w ((n:ℝ)+1)+w n| := by
  have hn : ∀ n < (0:ℤ), ((w (n:ℝ)):ℂ) = 0 := by
    intro n hn
    rw [hneg _ (by exact_mod_cast (le_of_lt hn)),Complex.ofReal_zero]
  have hh := second_difference_exponential_bound (fun n : ℤ => ((w (n:ℝ)):ℂ)) hw theta
  rw [integer_sum_eq_expSum _ hw hn theta] at hh
  have heq : (∑' n : ℤ, ‖((w ((n-2:ℤ):ℝ)):ℂ)-2*((w ((n-1:ℤ):ℝ)):ℂ)+((w (n:ℝ)):ℂ)‖) =
      ∑' n : ℤ, |w ((n:ℝ)+2)-2*w ((n:ℝ)+1)+w n| := by
    let f : ℤ → ℝ := fun n => |w ((n:ℝ)+2)-2*w ((n:ℝ)+1)+w n|
    have hp : ∀ n : ℤ, ‖((w ((n-2:ℤ):ℝ)):ℂ)-2*((w ((n-1:ℤ):ℝ)):ℂ)+((w (n:ℝ)):ℂ)‖ = f (n-2) := by
      intro n
      rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_add,
        Complex.norm_real,Real.norm_eq_abs]
      dsimp [f]
      push_cast
      rw [show (n:ℝ)-2+2 = (n:ℝ) by ring,show (n:ℝ)-2+1 = (n:ℝ)-1 by ring]
      congr 1
      ring
    simp_rw [hp]
    exact (Equiv.subRight (2:ℤ)).tsum_eq f
  rw [heq] at hh
  exact hh

theorem sampled_expSum_norm_le (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (hneg : ∀ n < (0:ℤ), a n = 0) (theta : ℝ) :
    ‖Helfgott.expSum (fun n : ℕ => a n) (theta:AddCircle (1:ℝ))‖ ≤ ∑' n : ℤ, ‖a n‖ := by
  rw [← integer_sum_eq_expSum a ha hneg theta]
  have hz : ‖Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))‖ = 1 := by simp [Complex.norm_exp]
  have heq : ∀ n : ℤ, ‖a n*(Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n‖ = ‖a n‖ := by
    intro n
    simp only [norm_mul,norm_zpow,hz,one_zpow,mul_one]
  have hh := norm_tsum_le_tsum_norm (show Summable (fun n : ℤ => ‖a n*
      (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n‖) by simpa only [heq] using ha)
  simpa only [heq] using hh

end HelfgottQuadratic

end

section

open Helfgott Finset
open scoped BigOperators
namespace HelfgottQuadratic

theorem etaTwo_log_norm_bound (y t : ℝ) (hy : 8 ≤ y) :
    ‖((Real.log t*etaTwo (t/y):ℝ):ℂ)‖ ≤ Real.log (y+2)*‖((etaTwo (t/y)):ℂ)‖ := by
  have hyp : 0 < y := by linarith
  rw [Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,etaTwo_log_clipped y t hyp,abs_mul]
  by_cases ht : t ≤ y
  · have hh := clippedLog_endpoint_bound y (t-2) hy (by linarith)
    rw [show t-2+2 = t by ring] at hh
    exact mul_le_mul_of_nonneg_right hh (abs_nonneg _)
  · rw [etaTwo_zero_large y t hyp (le_of_not_ge ht),abs_zero,mul_zero,mul_zero]

theorem etaTwo_log_int_summable (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℤ => ‖((Real.log (n:ℝ)*etaTwo ((n:ℝ)/y):ℝ):ℂ)‖) := by
  apply summable_of_ne_finset_zero (s := Icc (1:ℤ) ⌊y⌋)
  intro n hn
  rw [etaTwo_int_support y hy n hn,mul_zero,Complex.ofReal_zero,norm_zero]

theorem etaTwo_log_expSum_trivial (y theta : ℝ) (hy : 8 ≤ y) :
    ‖expSum (fun n => ((Real.log (n:ℝ)*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      (4*Real.log 2)*(⌊y⌋₊:ℝ)*Real.log (y+2) := by
  have hyp : 0 < y := by linarith
  have hs := etaTwo_log_int_summable y hyp
  have hneg : ∀ n < (0:ℤ), ((Real.log (n:ℝ)*etaTwo ((n:ℝ)/y):ℝ):ℂ) = 0 := by
    intro n hn
    rw [etaTwo_zero_nonpos _ (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (le_of_lt hn)) hyp.le),
      mul_zero,Complex.ofReal_zero]
  have hmajor := (etaTwo_int_summable y hyp).mul_left (Real.log (y+2))
  calc
    _ ≤ ∑' n : ℤ, ‖((Real.log (n:ℝ)*etaTwo ((n:ℝ)/y):ℝ):ℂ)‖ := sampled_expSum_norm_le _ hs hneg theta
    _ ≤ ∑' n : ℤ, Real.log (y+2)*‖((etaTwo ((n:ℝ)/y)):ℂ)‖ :=
      hs.tsum_le_tsum (fun n => etaTwo_log_norm_bound y n hy) hmajor
    _ = Real.log (y+2)*(∑' n : ℤ, ‖((etaTwo ((n:ℝ)/y)):ℂ)‖) := tsum_mul_left
    _ ≤ Real.log (y+2)*((4*Real.log 2)*(⌊y⌋₊:ℝ)) :=
      mul_le_mul_of_nonneg_left (etaTwo_int_energy y hyp) (Real.log_nonneg (by linarith))
    _ = _ := by ring

theorem etaTwo_log_expSum_quadratic (y theta : ℝ) (hy : 8 ≤ y) :
    4*(Real.sin (Real.pi*theta))^2*
      ‖expSum (fun n => ((Real.log (n:ℝ)*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
        (72*Real.log (y+2)+192*Real.log 2)/y := by
  have hyp : 0 < y := by linarith
  have hn : ∀ t ≤ (0:ℝ), Real.log t*etaTwo (t/y) = 0 := by
    intro t ht
    rw [etaTwo_zero_nonpos _ (div_nonpos_of_nonpos_of_nonneg ht hyp.le),mul_zero]
  exact (real_sampled_expSum_second_difference (fun t => Real.log t*etaTwo (t/y))
    (etaTwo_log_int_summable y hyp) hn theta).trans (etaTwo_log_second_variation y hy).2

theorem etaTwo_log_expSum_quadratic_cap (y theta : ℝ) (hy : 8 ≤ y) :
    ‖expSum (fun n => ((Real.log (n:ℝ)*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      if Real.sin (Real.pi*theta) = 0 then (4*Real.log 2)*(⌊y⌋₊:ℝ)*Real.log (y+2)
      else min ((4*Real.log 2)*(⌊y⌋₊:ℝ)*Real.log (y+2))
        ((18*Real.log (y+2)+48*Real.log 2)/(y*(Real.sin (Real.pi*theta))^2)) := by
  by_cases hsin : Real.sin (Real.pi*theta) = 0
  · rw [if_pos hsin]
    exact etaTwo_log_expSum_trivial y theta hy
  · rw [if_neg hsin]
    refine le_min (etaTwo_log_expSum_trivial y theta hy) ?_
    have hyp : 0 < y := by linarith
    apply (le_div_iff₀ (mul_pos hyp (sq_pos_of_ne_zero hsin))).mpr
    have hh := (le_div_iff₀ hyp).mp (etaTwo_log_expSum_quadratic y theta hy)
    nlinarith

end HelfgottQuadratic

end

open Helfgott
theorem solution (y theta : ℝ) (hy : 8 ≤ y) :
    ‖expSum (fun n => ((Real.log (n:ℝ)*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      if Real.sin (Real.pi*theta) = 0 then (4*Real.log 2)*(⌊y⌋₊:ℝ)*Real.log (y+2)
      else min ((4*Real.log 2)*(⌊y⌋₊:ℝ)*Real.log (y+2))
        ((18*Real.log (y+2)+48*Real.log 2)/(y*(Real.sin (Real.pi*theta))^2)) := by
  exact HelfgottQuadratic.etaTwo_log_expSum_quadratic_cap y theta hy
