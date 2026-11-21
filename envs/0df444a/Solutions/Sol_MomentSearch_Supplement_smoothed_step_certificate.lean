-- Prove2me | solution 1 for MomentSearch.Supplement.smoothed_step_certificate
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:30:30.330191+00:00
-- url     : https://prove2.me/submissions/9f05caff-23e1-4847-9b31-d7e3b170f201

import Mathlib
open Polynomial Finset
open Polynomial.Chebyshev

private theorem kernel (n k W : ℕ) (hn : 3 ≤ n) (hk : 16 ≤ k)
    (hw : 96 * ((n : ℝ) / k) * Real.logb 2 n ≤ (W:ℝ)) (half : 2*W ≤ n-1) :
    ∃ B : Polynomial ℝ, B.natDegree ≤ k ∧ (∀ x, 0 ≤ B.eval x) ∧
      2*(n:ℝ)^3 ≤ B.eval 0 ∧
      ∀ x : ℝ, |x| ≤ 2*n → (W:ℝ) ≤ 2*|x| → B.eval x ≤ 1 := by
  let d := k/4
  let u := (W:ℝ)/(2*n)
  let θ := Real.log (1+u)
  let A : Polynomial ℝ := C (Real.cosh θ) - C (1/(2*(n:ℝ)^2))*X^2
  let B := ((T ℝ (d:ℤ)).comp A)^2
  have np : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have kp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have un : 0 ≤ u := by dsimp [u]; positivity
  have u1 : u ≤ 1 := (div_le_iff₀ (by positivity : 0 < 2*(n:ℝ))).mpr (by exact_mod_cast (by omega : W ≤ 1*(2*n)))
  have op : 0 < 1+u := by linarith
  have θlo : u/2 ≤ θ := by
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr op)
    rw [Real.log_inv] at hh
    have ht : 1 - (1+u)⁻¹ ≤ θ := by dsimp [θ]; linarith
    apply le_trans _ ht
    have h1 : (1+u)⁻¹ ≤ 1-u/2 := by
      rw [← one_div,div_le_iff₀ op]
      nlinarith [mul_nonneg un (sub_nonneg.mpr u1)]
    linarith
  have cosid : Real.cosh θ = 1+u^2/(2*(1+u)) := by
    rw [Real.cosh_eq,Real.exp_neg,Real.exp_log op]
    field_simp; ring
  have cosub : Real.cosh θ ≤ 1+u^2/2 := by
    rw [cosid]
    have := div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num : (0:ℝ)<2)
      (by linarith : (2:ℝ) ≤ 2*(1+u))
    linarith
  have hdegree : A.natDegree ≤ 2 := by
    apply (natDegree_sub_le ..).trans
    apply max_le
    · simp
    · exact (natDegree_C_mul_le ..).trans (by simp)
  refine ⟨B,?_,fun x => by dsimp [B]; rw [eval_pow]; positivity,?_,?_⟩
  · have h1 := (natDegree_comp_le (p := T ℝ (d:ℤ)) (q := A)).trans
          (Nat.mul_le_mul_left _ hdegree)
    simp only [natDegree_T,Int.natAbs_natCast] at h1
    apply natDegree_pow_le.trans (Nat.mul_le_mul_left 2 h1) |>.trans
    dsimp [d]; omega
  · have l2 := Real.log_pos (by norm_num : (1:ℝ)<2)
    have ln0 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n) : (1:ℝ) ≤ n)
    have ln : Real.log n ≤ Real.logb 2 n := by
      rw [Real.logb,le_div_iff₀ l2]
      simpa using mul_le_mul_of_nonneg_left (show Real.log 2 ≤ 1 by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]) ln0
    have budget : 96*(n:ℝ)*Real.log n ≤ W*k := by
      have e : 96*((n:ℝ)/k)*Real.logb 2 n = (96*n*Real.logb 2 n)/k := by ring
      rw [e] at hw
      exact (mul_le_mul_of_nonneg_left ln (by positivity)).trans ((div_le_iff₀ kp).mp hw)
    have dk : (k:ℝ) ≤ 8*d := by exact_mod_cast (show k ≤ 8*d by dsimp [d]; omega)
    have bd : 3*Real.log n ≤ (d:ℝ)*(u/2) := by
      dsimp [u]
      field_simp
      nlinarith [mul_le_mul_of_nonneg_left dk (Nat.cast_nonneg W)]
    have exponent := bd.trans (mul_le_mul_of_nonneg_left θlo (Nat.cast_nonneg d))
    have en := Real.exp_le_exp.mpr exponent
    rw [show (3:ℝ)*Real.log n = ((3:ℕ):ℝ)*Real.log n by norm_num,
      Real.exp_nat_mul,Real.exp_log np] at en
    have cb : (n:ℝ)^3/2 ≤ Real.cosh ((d:ℝ)*θ) := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-((d:ℝ)*θ))]
    have n3 : 8 ≤ (n:ℝ)^3 := by
      calc
        _ = (2:ℝ)^3 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n)) _
    have ev : B.eval 0 = (Real.cosh ((d:ℝ)*θ))^2 := by
      simp [B,A,eval_comp,T_real_cosh]
    rw [ev]
    nlinarith [sq_nonneg (Real.cosh ((d:ℝ)*θ)-(n:ℝ)^3/2),
      mul_nonneg (show 0 ≤ (n:ℝ)^3 by positivity) (sub_nonneg.mpr cb),
      mul_nonneg (show 0 ≤ (n:ℝ)^3 by positivity) (sub_nonneg.mpr n3)]
  · intro x xmax xmin
    have y := abs_nonneg x
    have form : A.eval x = Real.cosh θ - x^2/(2*(n:ℝ)^2) := by simp [A]; ring
    have ax : |A.eval x| ≤ 1 := by
      rw [form,abs_le]
      have small : u^2/2 ≤ x^2/(2*(n:ℝ)^2) := by
        dsimp [u]; field_simp
        nlinarith [sq_abs x, mul_nonneg (sub_nonneg.mpr xmin)
          (by positivity : 0 ≤ 2*|x|+(W:ℝ))]
      have big : x^2/(2*(n:ℝ)^2) ≤ 2 := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [sq_abs x,mul_nonneg (sub_nonneg.mpr xmax) (by positivity : 0 ≤ 2*(n:ℝ)+|x|)]
      constructor <;> linarith [Real.one_le_cosh θ]
    have bounds := abs_le.mp (abs_eval_T_real_le_one (d:ℤ) ax)
    simp only [B,eval_pow,eval_comp]
    nlinarith [mul_nonneg (sub_nonneg.mpr bounds.2) (by linarith [bounds.1] : 0 ≤ (T ℝ (d:ℤ)).eval (A.eval x)+1)]

theorem solution (n k M W : ℕ) (hn : 3 ≤ n) (hk : 16 ≤ k)
    (hW : 96 * ((n : ℝ) / k) * Real.logb 2 n ≤ (W : ℝ))
    (hhalf : 2 * W ≤ n - 1) (hMW : M + W ≤ n - 1) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ k ∧
      (∀ t : Fin n, 0 ≤ q.eval (t.val : ℝ)) ∧
      (∀ t : Fin n, t.val ≤ M → 1 ≤ q.eval (t.val : ℝ)) ∧
      (∀ t : Fin n, q.eval (t.val : ℝ) ≤ 1 + 1 / (n : ℝ)^2) ∧
      (∀ t : Fin n, M + W ≤ t.val → q.eval (t.val : ℝ) ≤ 1 / (n : ℝ)^2) := by
  classical
  obtain ⟨B,degree,pos,peak,tail⟩ := kernel n k W hn hk hW hhalf
  have wp : 0 < W := by
    have l := Real.logb_pos (by norm_num : (1:ℝ)<2) (by exact_mod_cast (by omega : 1<n) : (1:ℝ)<n)
    have np : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
    have kp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0<k)
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 96*((n:ℝ)/k)*Real.logb 2 n) hW)
  let centers : Finset ℤ := Icc (-(n:ℤ)) ((M:ℤ)+(W:ℤ)/2)
  let core : Finset ℤ := (Icc (-(2*(n:ℤ))) (2*(n:ℤ))).filter (fun z => -(W:ℤ)<2*z ∧ 2*z<W)
  let f (z : ℤ) := B.eval (z:ℝ)
  let Z := ∑ z ∈ core, f z
  have cz : (0:ℤ) ∈ core := by simp [core]; omega
  have mass : 2*(n:ℝ)^3 ≤ Z := peak.trans (by
    simpa [f] using (single_le_sum (f := f) (fun i _ => pos _) cz))
  have np : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have zp : 0 < Z := lt_of_lt_of_le (by positivity) mass
  let P := ∑ a ∈ centers, B.comp (X-C (a:ℝ))
  let D (t : Fin n) := centers.image (fun a => (t.val:ℤ)-a)
  have ev (t : Fin n) : P.eval (t.val:ℝ) = ∑ z ∈ D t, f z := by
    rw [show D t = _ from rfl, sum_image (by intro a _ b _ eq; dsimp at eq; omega :
      Set.InjOn (fun a : ℤ => (t.val:ℤ)-a) ↑centers)]
    simp [P,eval_finsetSum,eval_comp,f]
  have memD (t : Fin n) (z : ℤ) :
      z ∈ D t ↔ -(n:ℤ) ≤ (t.val:ℤ)-z ∧ (t.val:ℤ)-z ≤ (M:ℤ)+(W:ℤ)/2 := by
    simp only [D,mem_image,centers,mem_Icc]
    constructor
    · rintro ⟨a,ha,rfl⟩; omega
    · intro h; exact ⟨_,h,by omega⟩
  have memC (z : ℤ) : z ∈ core ↔ -(2*(n:ℤ)) ≤ z ∧ z ≤ 2*(n:ℤ) ∧ -(W:ℤ)<2*z ∧ 2*z<W := by
    simp only [core,mem_filter,mem_Icc]; tauto
  have outer (t : Fin n) (z : ℤ) (hz : z ∈ D t) : -(2*(n:ℤ)) ≤ z ∧ z ≤ 2*(n:ℤ) := by
    have := (memD t z).mp hz; have := t.isLt; omega
  have tiny (t : Fin n) (z : ℤ) (hz : z ∈ D t) (hc : z ∉ core) : f z ≤ 1 := by
    have h := outer t z hz
    apply tail
    · rw [abs_le]; exact_mod_cast h
    · have dis : (W:ℤ) ≤ 2*z ∨ (W:ℤ) ≤ 2*(-z) := by
        rw [memC] at hc; omega
      rcases dis with h | h
      · exact (show (W:ℝ) ≤ 2*(z:ℝ) by exact_mod_cast h).trans
          (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
      · exact (show (W:ℝ) ≤ 2*(-(z:ℝ)) by exact_mod_cast h).trans
          (mul_le_mul_of_nonneg_left (neg_le_abs _) (by norm_num))
  have cardD (t : Fin n) : ((D t).card:ℝ) ≤ 2*n := by
    have h : (D t).card ≤ centers.card := card_image_le
    have e : centers.card ≤ 2*n := by rw [show centers = _ from rfl,Int.card_Icc]; omega
    exact_mod_cast h.trans e
  have sumsmall (t : Fin n) (s : Finset ℤ) (sub : s ⊆ D t) (hs : ∀ z ∈ s, z ∉ core) :
      ∑ z ∈ s, f z ≤ 2*n := by
    calc
      _ ≤ ∑ _z ∈ s, (1:ℝ) := sum_le_sum fun z hz => tiny t z (sub hz) (hs z hz)
      _ = s.card := by simp
      _ ≤ ((D t).card:ℝ) := by exact_mod_cast card_le_card sub
      _ ≤ _ := cardD t
  have ratio : (2*(n:ℝ))/Z ≤ 1/(n:ℝ)^2 := by
    apply (div_le_div_iff₀ zp (sq_pos_of_pos np)).mpr; nlinarith only [mass]
  refine ⟨C Z⁻¹ * P,(natDegree_C_mul_le ..).trans ?_,?_,?_,?_,?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro i _
    have deg1 : (X-C (i:ℝ)).natDegree ≤ 1 := (natDegree_sub_le ..).trans (by simp)
    simpa using natDegree_comp_le.trans (Nat.mul_le_mul degree deg1)
  all_goals intro t; simp only [eval_mul,eval_C,ev,← div_eq_inv_mul]
  · exact div_nonneg (sum_nonneg fun i _ => pos _) zp.le
  · intro ht
    apply (one_le_div zp).mpr
    apply sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => pos _)
    intro z hz
    have := (memC z).mp hz; rw [memD]; omega
  · let s := D t ∩ core
    have sub := inter_subset_left (s₁ := D t) (s₂ := core)
    have h1 := sumsmall t (D t \ s) sdiff_subset (by
      intro z hz hc
      exact (mem_sdiff.mp hz).2 (mem_inter.mpr ⟨(mem_sdiff.mp hz).1,hc⟩))
    have h2 : ∑ z ∈ s, f z ≤ Z := sum_le_sum_of_subset_of_nonneg inter_subset_right
      (fun z _ _ => pos _)
    have e := sum_sdiff (f := f) sub
    change _ + (∑ z ∈ s, f z) = _ at e
    calc
      _ ≤ (Z+2*n)/Z := div_le_div_of_nonneg_right (by linarith only [e,h1,h2]) zp.le
      _ = 1+(2*n)/Z := by field_simp
      _ ≤ _ := by linarith
  · intro ht
    exact (div_le_div_of_nonneg_right (sumsmall t (D t) (fun _ h => h) (by
      intro z hz hc
      have := (memD t z).mp hz; have := (memC z).mp hc; omega)) zp.le).trans ratio
