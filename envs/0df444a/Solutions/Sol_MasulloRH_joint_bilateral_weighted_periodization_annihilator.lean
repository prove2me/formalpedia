-- Prove2me | solution 1 for MasulloRH.joint_bilateral_weighted_periodization_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T10:40:07.922661+00:00
-- url     : https://prove2.me/submissions/c5879996-33c3-478c-8db9-6fe67d688967

import Mathlib
open Set
theorem solution (r : ℝ) (hr : 0 < r) (hlt : r < 1) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
    (∀ x : ℝ, |x| ≤ 1/2 → f x = 0) ∧
    (∀ x : ℝ, (∑' n : ℤ, r^n * f (x+n)) = 0 ∧
               (∑' n : ℤ, (r⁻¹)^n * f (x+n)) = 0) ∧
    (∀ n : ℤ, f n = if n = -1 ∨ n = 1 then r^2+(r⁻¹)^2
      else if n = -2 ∨ n = 2 then -(r+r⁻¹) else 0) ∧
    0 < r*(f 1+f (-1)) + r^2*(f 2+f (-2)) := by
  classical
  let b : ContDiffBump (0:ℝ) := ⟨1/8,1/4,by norm_num,by norm_num⟩
  let A := r^2+(r⁻¹)^2
  let B := r+r⁻¹
  let f (x : ℝ) := A*(b (x+1)+b (x-1))-B*(b (x+2)+b (x-2))
  have away (y : ℝ) (h : 1/4 ≤ |y|) : b y = 0 := by
    apply b.zero_of_le_dist
    simpa [b,Real.dist_eq] using h
  have hfc : ContDiff ℝ (⊤ : ℕ∞) f := by
    dsimp only [f]
    have hb : ContDiff ℝ (⊤ : ℕ∞) (b : ℝ → ℝ) := b.contDiff
    fun_prop
  have hK : HasCompactSupport f := by
    apply HasCompactSupport.intro (K := Icc (-4:ℝ) 4) isCompact_Icc
    intro y hy
    simp only [mem_Icc,not_and_or,not_le] at hy
    rcases hy with h|h
    · simp [f,away _ (by rw [abs_of_neg (by linarith : y+1<0)]; linarith),
        away _ (by rw [abs_of_neg (by linarith : y-1<0)]; linarith),
        away _ (by rw [abs_of_neg (by linarith : y+2<0)]; linarith),
        away _ (by rw [abs_of_neg (by linarith : y-2<0)]; linarith)]
    · simp [f,away _ (by rw [abs_of_pos (by linarith : 0<y+1)]; linarith),
        away _ (by rw [abs_of_pos (by linarith : 0<y-1)]; linarith),
        away _ (by rw [abs_of_pos (by linarith : 0<y+2)]; linarith),
        away _ (by rw [abs_of_pos (by linarith : 0<y-2)]; linarith)]
  have h0 (y : ℝ) (hy : |y| ≤ 1/2) : f y = 0 := by
    obtain ⟨h1,h2⟩ := abs_le.mp hy
    simp [f, away (y+1) ((by linarith : 1/4 ≤ y+1).trans (le_abs_self _)),
      away (y-1) ((by linarith : 1/4 ≤ -(y-1)).trans (neg_le_abs _)),
      away (y+2) ((by linarith : 1/4 ≤ y+2).trans (le_abs_self _)),
      away (y-2) ((by linarith : 1/4 ≤ -(y-2)).trans (neg_le_abs _))]
  have atint (j : ℤ) : b (j:ℝ) = if j=0 then 1 else 0 := by
    split_ifs with h
    · subst j
      apply b.one_of_mem_closedBall
      simp [b,Metric.mem_closedBall]
    · apply away
      rcases lt_or_gt_of_ne h with hj|hj
      · have hn : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
        linarith [neg_le_abs (j:ℝ)]
      · have hn : (1:ℝ) ≤ j := by exact_mod_cast (show (1:ℤ) ≤ j by omega)
        linarith [le_abs_self (j:ℝ)]
  have fi (n : ℤ) : f n = if n = -1 ∨ n = 1 then A
        else if n = -2 ∨ n = 2 then -B else 0 := by
    dsimp only [f]
    rw [← Int.cast_one, ← Int.cast_add, ← Int.cast_sub,
      ← Int.cast_ofNat 2, ← Int.cast_add, ← Int.cast_sub]
    simp only [atint]
    change A*((if n+1=0 then 1 else 0)+(if n-1=0 then 1 else 0)) -
      B*((if n+2=0 then 1 else 0)+(if n-2=0 then 1 else 0)) = _
    by_cases hp1 : n = 1
    · subst n; norm_num
    by_cases hn1 : n = -1
    · subst n; norm_num
    by_cases hp2 : n = 2
    · subst n; norm_num
    by_cases hn2 : n = -2
    · subst n; norm_num
    simp [show n+1 ≠ 0 by omega, show n-1 ≠ 0 by omega,
      show n+2 ≠ 0 by omega, show n-2 ≠ 0 by omega, hp1,hn1,hp2,hn2]
  refine ⟨f,hfc,hK,h0,?_,fi,?_⟩
  · intro x
    have period (t : ℝ) (ht : t ≠ 0)
        (hpoly : A*(t+t⁻¹)-B*(t^2+(t⁻¹)^2)=0) :
        (∑' n : ℤ, t^n * f (x+n)) = 0 := by
      let g (j n : ℤ) := t^n * b (x+((n+j:ℤ):ℝ))
      have hg (j : ℤ) : Summable (g j) := by
        obtain ⟨N,hN⟩ := exists_nat_gt (|x+(j:ℝ)|+2)
        apply (hasSum_sum_of_ne_finset_zero (s := Finset.Icc (-(N:ℤ)) N) ?_).summable
        intro n hn
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        have hz : 1/4 ≤ |x+((n+j:ℤ):ℝ)| := by
          push_cast
          rcases hn with hn|hn
          · have h : (n:ℝ) < -(N:ℝ) := by exact_mod_cast hn
            linarith [le_abs_self (x+(j:ℝ)), neg_le_abs (x+((n:ℝ)+j))]
          · have h : (N:ℝ) < n := by exact_mod_cast hn
            linarith [neg_le_abs (x+(j:ℝ)), le_abs_self (x+((n:ℝ)+j))]
        change t^n * b (x+((n+j:ℤ):ℝ))=0
        rw [away _ hz,mul_zero]
      have shift (j : ℤ) : ∑' n : ℤ, g j n = t^(-j) * ∑' n : ℤ, g 0 n := by
        rw [← (Equiv.addRight j).tsum_eq (g 0), ← tsum_mul_left]
        apply tsum_congr
        intro n
        change t^n * b (x+((n+j:ℤ):ℝ)) = t^(-j)*(t^(n+j)*b (x+(((n+j)+0:ℤ):ℝ)))
        rw [add_zero,← mul_assoc,← zpow_add₀ ht, show -j+(n+j)=n by omega]
      have heq (n : ℤ) : t^n*f (x+n) =
          A*(g 1 n+g (-1) n)-B*(g 2 n+g (-2) n) := by
        simp [g,f,sub_eq_add_neg,add_assoc]
        ring
      simp_rw [heq]
      rw [(((hg 1).add (hg (-1))).mul_left A).tsum_sub (((hg 2).add (hg (-2))).mul_left B),
        tsum_mul_left,tsum_mul_left,(hg 1).tsum_add (hg (-1)),(hg 2).tsum_add (hg (-2))]
      rw [shift 1,shift (-1),shift 2,shift (-2)]
      simp only [neg_neg,zpow_neg,zpow_one,zpow_ofNat]
      rw [← inv_pow]
      linear_combination (∑' n : ℤ, g 0 n) * hpoly
    exact ⟨period r hr.ne' (by dsimp [A,B]; ring),
      period r⁻¹ (inv_ne_zero hr.ne') (by simp [A,B]; ring)⟩
  · have eqn : r*(f 1+f (-1)) + r^2*(f 2+f (-2)) = 2*(r⁻¹-r) := by
      have h1 := fi 1
      have h2 := fi (-1)
      have h3 := fi 2
      have h4 := fi (-2)
      norm_num at h1 h2 h3 h4
      rw [h1,h2,h3,h4]
      dsimp [A,B]; field_simp; ring
    rw [eqn]
    have hh : 1 < r⁻¹ := one_lt_inv₀ hr |>.2 hlt
    linarith
