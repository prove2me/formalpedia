-- Prove2me | solution 1 for Helfgott.etaTwo_expSum_quadratic_cap
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T17:51:22.901021+00:00
-- url     : https://prove2.me/submissions/bbd87e05-6e16-45ee-9ef3-116041b662ab

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

theorem solution (y theta : ℝ) (hy : 0 < y) :
    ‖Helfgott.expSum (fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      if Real.sin (Real.pi*theta) = 0 then (4*Real.log 2)*(⌊y⌋₊:ℝ)
      else min ((4*Real.log 2)*(⌊y⌋₊:ℝ)) (18/(y*(Real.sin (Real.pi*theta))^2)) := by
  exact HelfgottQuadratic.etaTwo_expSum_quadratic_cap y theta hy
