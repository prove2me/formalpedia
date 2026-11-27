-- Prove2me | solution 1 for MasulloRH.uniform_gaussian_mass_bound_for_separated_zeta_zeros
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:19:22.00666+00:00
-- url     : https://prove2.me/submissions/64b73f6e-c43c-4526-96b5-03f323b2adb1

import Theorems.Thm_MasulloRH_finite_zeta_zero_configurations_gaussian_gram_bound
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset MasulloRH.WindowLaplaceGram
open scoped ComplexConjugate

private noncomputable def w (i j : ℕ) : ℝ := 1 / ((j:ℝ)-i)^2
private noncomputable def primitive (i j : ℕ) : ℝ :=
  if j ≤ i then 2 / ((i:ℝ)-j+1) else 4 - 2 / ((j:ℝ)-i)

private lemma telescoping (a : ℝ) (ha : 1 ≤ a) : 1/a^2 ≤ 2/a - 2/(a+1) := by
  have hp : 0<a := by linarith
  have hp' : 0<a+1 := by linarith
  rw [div_sub_div _ _ hp.ne' hp'.ne',div_le_div_iff₀ (sq_pos_of_pos hp) (mul_pos hp hp')]
  nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr ha)]

private lemma diff_bound (i j : ℕ) : w i j ≤ primitive i (j+1)-primitive i j := by
  rcases lt_trichotomy j i with h|rfl|h
  · have h₁ : (j:ℝ)+1 ≤ i := by exact_mod_cast (Nat.succ_le_of_lt h)
    simp only [w,primitive,if_pos (Nat.succ_le_of_lt h),if_pos h.le,Nat.cast_add,Nat.cast_one]
    rw [show (i:ℝ)-((j:ℝ)+1)+1=(i:ℝ)-j by ring,show ((j:ℝ)-i)^2=((i:ℝ)-j)^2 by ring]
    exact telescoping _ (by linarith)
  · norm_num [w,primitive]
  · have h₁ : (i:ℝ)+1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt h)
    have h₂ : ¬ (j + 1 ≤ i) := by omega
    simp only [w,primitive,if_neg h₂,if_neg (not_le.mpr h),Nat.cast_add,Nat.cast_one]
    rw [show (j:ℝ)+1-i=(j:ℝ)-i+1 by ring]
    linarith only [telescoping ((j:ℝ)-i) (by linarith only [h₁])]

private lemma row (i n : ℕ) : (∑ j : Fin n, w i j.val) ≤ 4 := by
  have tel (m : ℕ) : (∑ j ∈ range m, w i j) ≤ primitive i m-primitive i 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ];linarith only [ih,diff_bound i m]
  have top : primitive i n ≤ 4 := by
    unfold primitive
    split_ifs with hn
    · have hc : (n:ℝ) ≤ i := by exact_mod_cast hn
      rw [div_le_iff₀ (by linarith)];linarith
    · have hc : (i:ℝ)<n := by exact_mod_cast (lt_of_not_ge hn)
      exact sub_le_self _ (div_nonneg (by norm_num) (by linarith))
  have bot : 0 ≤ primitive i 0 := by simp [primitive];positivity
  rw [Fin.sum_univ_eq_sum_range (w i)]
  linarith only [tel n,top,bot]

private lemma off_diag (s z : ℂ) (hne : z.im ≠ s.im) :
    ‖kernel (3/4) (1/4) s z‖ ≤ 1/(z.im-s.im)^2 := by
  let l := s + conj z - 1
  let r := 2 - (s + conj z)
  have h : 0 < |z.im-s.im| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hi₁ : |z.im-s.im| ≤ ‖l‖ := by
    have hh := Complex.abs_im_le_norm l
    rw [abs_sub_comm z.im s.im];simpa [l,sub_eq_add_neg] using hh
  have hi₂ : |z.im-s.im| ≤ ‖r‖ := by
    have hh := Complex.abs_im_le_norm r
    simpa [r,sub_eq_add_neg] using hh
  have hl := norm_pos_iff.mp (h.trans_le hi₁)
  have hr := norm_pos_iff.mp (h.trans_le hi₂)
  have id : kernel (3/4) (1/4) s z = 1/(l*r) := by
    rw [kernel,show 2*((3/4:ℝ)-1/4)=1 by norm_num,show 2*((3/4:ℝ)+1/4)=2 by norm_num]
    norm_cast
    change 1/l+1/r=1/(l*r)
    rw [div_add_div _ _ hl hr]
    congr 1
    dsimp [l,r];ring
  rw [id,norm_div,norm_one,norm_mul]
  apply one_div_le_one_div_of_le (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
  simpa only [←sq_abs (z.im-s.im),pow_two] using mul_le_mul hi₁ hi₂ (abs_nonneg _) (norm_nonneg _)

private lemma diagonal (s : ℂ) (hl : 9/16 ≤ s.re) (hr : s.re ≤ 15/16) :
    ‖kernel (3/4) (1/4) s s‖ ≤ 64/7 := by
  have a : 0<2*s.re-1 := by linarith
  have b : 0<2-2*s.re := by linarith
  have eq : kernel (3/4) (1/4) s s = ((1/(2*s.re-1)+1/(2-2*s.re):ℝ):ℂ) := by
    rw [kernel,Complex.add_conj,show 2*((3/4:ℝ)-1/4)=1 by norm_num,show 2*((3/4:ℝ)+1/4)=2 by norm_num]
    push_cast;rfl
  rw [eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),div_add_div _ _ a.ne' b.ne',
    div_le_iff₀ (mul_pos a b)]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)]

private lemma symmetry (i j : ℕ) : w i j=w j i := by
  unfold w
  rw [show ((j:ℝ)-i)^2=((i:ℝ)-j)^2 by ring]

theorem solution {n : ℕ} (s : Fin n → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hl : ∀ i, 9/16 ≤ (s i).re) (hr : ∀ i, (s i).re ≤ 15/16)
    (hz : ∀ i, riemannZeta (s i)=0)
    (hsep : ∀ i j : Fin n, i<j → δ*((j.val:ℝ)-i.val) ≤ (s j).im-(s i).im) :
    (∑ i, Real.exp (((s i).re^2-(s i).im^2)/2)) ≤ (64/7+4/δ^2)/32000000000 := by
  classical
  let H (i j : Fin n) : ℝ := (if i=j then 64/7 else 0) + (1/δ^2)*w i.val j.val
  have hs (i j : Fin n) : H i j=H j i := by simp only [H,(eq_comm (a:=i) (b:=j)),symmetry i.val j.val]
  have rowBound (i : Fin n) : (∑ j, H i j) ≤ 64/7+4/δ^2 := by
    simp only [H,sum_add_distrib,←mul_sum]
    rw [sum_ite_eq,if_pos (mem_univ i)]
    have hh := mul_le_mul_of_nonneg_left (row i.val n) (by positivity : 0≤1/δ^2)
    apply add_le_add_right
    simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using hh
  have kg (i j : Fin n) : ‖kernel (3/4) (1/4) (s i) (s j)‖ ≤ H i j := by
    by_cases same : i=j
    · subst j;simpa [H,w] using diagonal (s i) (hl i) (hr i)
    have spacing : δ*|(j.val:ℝ)-i.val| ≤ |(s j).im-(s i).im| := by
      rcases lt_or_gt_of_ne same with h|h
      · have h' : (i.val:ℝ) < j.val := by exact_mod_cast h
        rw [abs_of_pos (sub_pos.mpr h')]
        exact (hsep i j h).trans (le_abs_self _)
      · have h' : (j.val:ℝ) < i.val := by exact_mod_cast h
        rw [abs_sub_comm (j.val:ℝ) i.val,abs_sub_comm (s j).im (s i).im,abs_of_pos (sub_pos.mpr h')]
        exact (hsep j i h).trans (le_abs_self _)
    have ni : (j.val:ℝ) ≠ i.val := by
      have natNe : j.val ≠ i.val := fun h => same (Fin.ext h.symm)
      exact_mod_cast natNe
    have pp := mul_pos hδ (abs_pos.mpr (sub_ne_zero.mpr ni))
    have im := sub_ne_zero.mp (abs_pos.mp (pp.trans_le spacing))
    have upper := one_div_le_one_div_of_le (sq_pos_of_pos pp) (pow_le_pow_left₀ pp.le spacing 2)
    rw [mul_pow,sq_abs,sq_abs] at upper
    apply (off_diag (s i) (s j) im).trans
    simpa [H,w,same,div_eq_mul_inv,mul_comm] using upper
  let v (i : Fin n) := Complex.exp ((s i)^2/4)
  let a (i : Fin n) := ‖v i‖
  let S := ∑ i, (a i)^2
  have posS : 0≤S := sum_nonneg (fun i _ => sq_nonneg (a i))
  have hei (i : Fin n) : Real.exp (((s i).re^2-(s i).im^2)/2) = (a i)^2 := by
    dsimp [a,v];rw [Complex.norm_exp,←Real.exp_nat_mul];congr 1
    norm_num [pow_two,Complex.div_re,Complex.mul_re];ring
  simp_rw [hei]
  change S ≤ _
  have zeroBound := MasulloRH.finite_zeta_zero_configurations_gaussian_gram_bound s (fun i => conj (v i))
    (fun i => by linarith [hl i]) (fun i => by linarith [hr i]) hz
  have dot : ‖∑ i, conj (v i)*Complex.exp ((s i)^2/4)‖ = S := by
    have d (i : Fin n) : conj (v i)*Complex.exp ((s i)^2/4) = ((a i)^2:ℝ) := by
      change conj (v i)*v i = ((‖v i‖^2:ℝ):ℂ)
      rw [mul_comm,Complex.mul_conj,Complex.sq_norm]
    simp_rw [d]
    rw [←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg posS]
  have term (i j : Fin n) :
      (conj (v i)*conj (conj (v j))*kernel (3/4) (1/4) (s i) (s j)).re ≤
        ((a i)^2+(a j)^2)/2 * H i j := by
    apply (Complex.re_le_norm _).trans
    simp only [norm_mul,Complex.norm_conj]
    change a i*a j*_≤_
    apply mul_le_mul _ (kg i j) (norm_nonneg _) _
    · nlinarith only [sq_nonneg (a i-a j)]
    · positivity
  let T := ∑ i, ∑ j, (a i)^2*H i j
  have swap : (∑ i, ∑ j, (a j)^2*H i j)=T := by
    rw [Finset.sum_comm];dsimp [T]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by rw [hs]))
  have sumBound : gramValue (3/4) (1/4) s (fun i => conj (v i)) ≤ T := by
    have h := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => term i j))
    have distribute (i j : Fin n) : ((a i)^2+(a j)^2)/2*H i j = ((a i)^2*H i j+(a j)^2*H i j)/2 := by ring
    simp only [distribute,← Finset.sum_div,Finset.sum_add_distrib] at h
    dsimp only [gramValue];simp only [Complex.re_sum]
    apply h.trans_eq
    change (T+(∑ i, ∑ j, (a j)^2*H i j))/2 = T
    rw [swap];ring
  have cap : T ≤ S*(64/7+4/δ^2) := by
    dsimp only [T,S];rw [Finset.sum_mul]
    apply sum_le_sum;intro i _
    rw [←Finset.mul_sum];exact mul_le_mul_of_nonneg_left (rowBound i) (sq_nonneg _)
  rw [dot] at zeroBound
  have hp := zeroBound.trans (mul_le_mul_of_nonneg_left (sumBound.trans cap) (by norm_num))
  by_cases hS : S=0
  · rw [hS];positivity
  · have hpos := lt_of_le_of_ne posS (Ne.symm hS)
    apply le_of_mul_le_mul_right _ hpos
    linarith only [hp]
