-- Prove2me | solution 1 for KoanaKPaths.Main.amplified_estimator_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:27:07.840527+00:00
-- url     : https://prove2.me/submissions/5140e535-1d09-496a-8b60-7ef66dc7ee9a

import Definitions.Def_KoanaKPaths_GraphEstimator
import Definitions.Def_KoanaKPaths_Main_Inputs
import Theorems.Thm_KoanaKPaths_Main_recursive_estimator_moments
set_option synthInstance.maxSize 4096
open KoanaKPaths.Main

open scoped BigOperators
namespace KoanaKPaths.Main.SignMoments

lemma mean_add {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun w => f w + g w) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

lemma mean_mul {Ω : Type} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun w => a * f w) = a * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

lemma mean_const {Ω : Type} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    uniformMean (fun _ : Ω => a) = a := by
  simp [uniformMean]

lemma mean_mono {Ω : Type} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ w, f w ≤ g w) :
    uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun w _ => h w) (by positivity)

lemma mean_sum {Ω I : Type} [Fintype Ω] [Fintype I] (f : I → Ω → ℝ) :
    uniformMean (fun w => ∑ i, f i w) = ∑ i, uniformMean (f i) := by
  simp only [uniformMean, ← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

lemma mean_pi_succ {α : Type} [Fintype α] (n : ℕ) (f : (Fin (n + 1) → α) → ℝ) :
    uniformMean f = uniformMean (fun a : α =>
      uniformMean (fun r : Fin n → α => f (Fin.cons a r))) := by
  have hs := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α))
    (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)
  rw [Fintype.sum_prod_type] at hs
  simp only [uniformMean, Fintype.card_fun, Fintype.card_fin, ← Finset.sum_div]
  rw [← hs]
  simp only [Nat.cast_pow, pow_succ, Nat.cast_mul]
  ring


end KoanaKPaths.Main.SignMoments

open scoped BigOperators
namespace KoanaKPaths.Main.FiniteSampling
open SignMoments KoanaKPaths.Sampling

lemma mean_sub {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun w => f w - g w) = uniformMean f - uniformMean g := by
  simp [uniformMean,Finset.sum_sub_distrib,sub_div]

lemma mean_sum_zero {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ)
    (hf : uniformMean f = 0) (m : ℕ) :
    uniformMean (fun w : Fin m → Ω => ∑ i, f (w i)) = 0 := by
  induction m with
  | zero => simp [uniformMean]
  | succ m ih =>
    rw [mean_pi_succ]
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    simp_rw [mean_add,mean_const,ih]
    simpa only [add_zero] using hf

lemma mean_sum_sq {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ)
    (hf : uniformMean f = 0) (m : ℕ) :
    uniformMean (fun w : Fin m → Ω => (∑ i, f (w i))^2) =
      (m : ℝ) * uniformMean (fun x => f x ^ 2) := by
  induction m with
  | zero => simp [uniformMean]
  | succ m ih =>
    rw [mean_pi_succ]
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    simp_rw [add_sq,mean_add,mean_mul,mean_const,mean_sum_zero f hf,ih]
    simp only [mul_zero,add_zero,mean_add,mean_const]
    rw [Nat.cast_succ]
    ring

lemma centered_second {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ)
    (N : ℝ) (hN : uniformMean f = N) :
    uniformMean (fun x => (f x - N)^2) = uniformMean (fun x => f x^2) - N^2 := by
  have he (x : Ω) : (f x - N)^2 = f x^2 - (2*N)*f x + N^2 := by ring
  simp_rw [he]
  rw [mean_add,mean_sub,mean_mul,mean_const,hN]
  ring

lemma sample_centered_second {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ)
    (N : ℝ) (hN : uniformMean f = N) (m : ℕ) (hm : 0 < m) :
    uniformMean (fun w : Fin m → Ω => (sampleMean f w - N)^2) =
      (uniformMean (fun x => f x^2) - N^2) / m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hz : uniformMean (fun x => f x - N) = 0 := by rw [mean_sub,mean_const,hN]; ring
  have he (w : Fin m → Ω) : sampleMean f w - N = (∑ i, (f (w i)-N)) / m := by
    simp only [sampleMean,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    field_simp
  simp_rw [he,div_pow,div_eq_mul_inv]
  simp_rw [mul_comm _ ((m : ℝ)^2)⁻¹]
  rw [mean_mul,mean_sum_sq _ hz,centered_second f N hN]
  field_simp

lemma finite_chebyshev {Ω : Type} [Fintype Ω] (F : Ω → ℝ) (t : ℝ) (ht : 0 < t) :
    t^2 * uniformMean (fun x => if t < |F x| then (1 : ℝ) else 0) ≤
      uniformMean (fun x => F x^2) := by
  rw [← mean_mul]
  apply mean_mono
  intro x
  split_ifs with h
  · have hh : t^2 < |F x|^2 := pow_lt_pow_left₀ h ht.le (by decide : 2 ≠ 0)
    simpa only [mul_one,sq_abs] using hh.le
  · simp [sq_nonneg]

lemma mean_sq_zero {Ω : Type} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ)
    (hf : uniformMean (fun x => f x^2) = 0) : ∀ x, f x = 0 := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : ∑ x, f x^2 = 0 := by
    have h := (div_eq_iff hc).mp hf
    simpa using h
  intro x
  have hh : f x^2 = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (f y))).mp hs x (Finset.mem_univ x)
  nlinarith

theorem sample_relative_failure {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (N C ε : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C) (hε : 0 < ε)
    (hmean : uniformMean f = N)
    (hsecond : uniformMean (fun x => f x^2) ≤ C*N^2)
    (m : ℕ) (hm : 0 < m) :
    uniformMean (fun w : Fin m → Ω => if ε*N < |sampleMean f w - N| then (1 : ℝ) else 0) ≤
      C / ((m : ℝ)*ε^2) := by
  by_cases hzero : N = 0
  · have hs0 : uniformMean (fun x => f x^2) ≤ 0 := by simpa only [hzero,zero_pow (by decide : 2 ≠ 0),mul_zero] using hsecond
    have hsq : uniformMean (fun x => f x^2) = 0 := by
      apply le_antisymm
      · exact hs0
      · exact le_trans (by simp [mean_const]) (mean_mono (fun x => sq_nonneg (f x)))
    have hf := mean_sq_zero f hsq
    rw [hzero]
    simp only [hf,sampleMean,Finset.sum_const_zero,zero_div,sub_zero,abs_zero,mul_zero,lt_self_iff_false,ite_false,mean_const]
    positivity
  · have hpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hzero)
    have ht : 0 < ε*N := mul_pos hε hpos
    have hs := finite_chebyshev (fun w : Fin m → Ω => sampleMean f w-N) (ε*N) ht
    rw [sample_centered_second f N hmean m hm] at hs
    have hv : (uniformMean (fun x => f x^2)-N^2)/(m : ℝ) ≤ C*N^2/(m : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg N]
    calc
      _ ≤ (C*N^2/(m : ℝ))/(ε*N)^2 :=
        (le_div_iff₀ (sq_pos_of_pos ht)).mpr (by simpa only [mul_comm] using hs.trans hv)
      _ = C/((m : ℝ)*ε^2) := by field_simp

lemma badCount_exp {Ω : Type} [Fintype Ω] [Nonempty Ω] (p : Ω → Prop) [DecidablePred p]
    (q : ℕ) :
    uniformMean (fun w : Fin q → Ω => (4 : ℝ)^badCount p w) =
      (1+3*uniformMean (fun x => if p x then (1 : ℝ) else 0))^q := by
  induction q with
  | zero => simp [badCount,mean_const]
  | succ q ih =>
    rw [mean_pi_succ]
    simp only [badCount,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,pow_add]
    simp_rw [mean_mul]
    change uniformMean (fun a => (4 : ℝ)^(if p a then 1 else 0) *
      uniformMean (fun w : Fin q → Ω => (4 : ℝ)^badCount p w)) = _
    rw [ih]
    have he (a : Ω) : (4 : ℝ)^(if p a then 1 else 0) = 1+3*(if p a then 1 else 0) := by
      split_ifs <;> norm_num
    simp_rw [he]
    rw [show uniformMean (fun a : Ω => (1+3*(if p a then (1 : ℝ) else 0))*
      (1+3*uniformMean (fun x => if p x then (1 : ℝ) else 0))^q) =
      (1+3*uniformMean (fun x => if p x then (1 : ℝ) else 0))^q *
        uniformMean (fun a : Ω => 1+3*(if p a then (1 : ℝ) else 0)) from by
          simp_rw [mul_comm _ ((1+3*uniformMean (fun x => if p x then (1 : ℝ) else 0))^q)]
          exact mean_mul _ _]
    rw [mean_add,mean_const,mean_mul,pow_succ]
    ring

theorem majority_failure {Ω : Type} [Fintype Ω] [Nonempty Ω] (p : Ω → Prop) [DecidablePred p]
    (hp : uniformMean (fun x => if p x then (1 : ℝ) else 0) ≤ 1/16) (b : ℕ) :
    uniformMean (fun w : Fin (2*b+1) → Ω => if b+1 ≤ badCount p w then (1 : ℝ) else 0) ≤
      (2 : ℝ)⁻¹^b := by
  have hs : (4 : ℝ)^(b+1) *
      uniformMean (fun w : Fin (2*b+1) → Ω => if b+1 ≤ badCount p w then (1 : ℝ) else 0) ≤
      uniformMean (fun w : Fin (2*b+1) → Ω => (4 : ℝ)^badCount p w) := by
    rw [← mean_mul]
    apply mean_mono
    intro w
    split_ifs with h
    · simpa only [mul_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) h
    · simp only [mul_zero]
      exact pow_nonneg (by norm_num) _
  rw [badCount_exp] at hs
  have hprob : 0 ≤ uniformMean (fun x => if p x then (1 : ℝ) else 0) := by
    unfold uniformMean
    positivity
  have he : (1+3*uniformMean (fun x => if p x then (1 : ℝ) else 0))^(2*b+1) ≤
      (5/4 : ℝ)^(2*b+1) := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have hnum : (5/4 : ℝ)^(2*b+1) ≤ (4 : ℝ)^(b+1)*(2 : ℝ)⁻¹^b := by
    have hh : ((5/4 : ℝ)^2)^b ≤ (4*(2 : ℝ)⁻¹)^b :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) b
    calc
      _ = ((5/4 : ℝ)^2)^b*(5/4) := by rw [pow_succ,pow_mul]
      _ ≤ (4*(2 : ℝ)⁻¹)^b*4 := mul_le_mul hh (by norm_num) (by norm_num) (by positivity)
      _ = _ := by rw [mul_pow,pow_succ]; ring

  exact (mul_le_mul_iff_right₀ (by positivity : 0 < (4 : ℝ)^(b+1))).mp
    (by simpa only [mul_comm] using hs.trans (he.trans hnum))

end KoanaKPaths.Main.FiniteSampling

namespace KoanaKPaths.Sampling

lemma median_interval {α : Type} [LinearOrder α] [Inhabited α] (b : ℕ)
    (x : Fin (2*b+1) → α) (L U : α) (g : Finset (Fin (2*b+1)))
    (hg : b+1 ≤ g.card) (hx : ∀ i ∈ g, L ≤ x i ∧ x i ≤ U) :
    L ≤ median b x ∧ median b x ≤ U := by
  have hm {s : Finset (Fin (2*b+1))} (hs : s ∈ Finset.univ.powersetCard (b+1)) :
      s.Nonempty := by
    have hc := (Finset.mem_powersetCard.mp hs).2
    exact Finset.card_pos.mp (by omega)
  constructor
  · obtain ⟨s,hsg,hsc⟩ := Finset.exists_subset_card_eq hg
    have hs : s ∈ Finset.univ.powersetCard (b+1) := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s,hsc⟩
    apply le_trans _ (Finset.le_sup' (fun s => selectedMin s x) hs)
    rw [selectedMin,dif_pos (hm hs)]
    apply Finset.le_inf'
    intro i hi
    exact (hx i (hsg hi)).1
  · apply Finset.sup'_le
    intro s hs
    have hc := (Finset.mem_powersetCard.mp hs).2
    have hi : (s ∩ g).Nonempty := Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.subset_univ s) (Finset.subset_univ g) (by simp only [Finset.card_univ,Fintype.card_fin]; omega)
    obtain ⟨i,hi⟩ := hi
    obtain ⟨his,hig⟩ := Finset.mem_inter.mp hi
    rw [selectedMin,dif_pos (hm hs)]
    exact (Finset.inf'_le x his).trans (hx i hig).2

lemma median_map {α β : Type} [LinearOrder α] [LinearOrder β] [Inhabited α] [Inhabited β]
    (f : α → β) (hf : Monotone f) (b : ℕ) (x : Fin (2*b+1) → α) :
    f (median b x) = median b (fun i => f (x i)) := by
  unfold median
  rw [Finset.apply_sup'_eq_sup'_comp _ f (fun a b => hf.map_sup a b)]
  apply Finset.sup'_congr _ rfl
  intro s hs
  have hc := (Finset.mem_powersetCard.mp hs).2
  have hn : s.Nonempty := Finset.card_pos.mp (by omega)
  simp only [Function.comp_apply,selectedMin,dif_pos hn]
  exact Finset.apply_inf'_eq_inf'_comp hn f (fun a b => hf.map_inf a b)

end KoanaKPaths.Sampling

open scoped BigOperators
namespace KoanaKPaths.Main.FiniteSampling
open KoanaKPaths.Sampling SignMoments

lemma badCount_eq_card {Ω : Type} (p : Ω → Prop) [DecidablePred p] {q : ℕ} (w : Fin q → Ω) :
    badCount p w = (Finset.univ.filter (fun i => p (w i))).card := by
  simp only [badCount,Finset.card_filter]

lemma median_bad_majority (b : ℕ) (x : Fin (2*b+1) → ℝ) (N t : ℝ)
    (hbad : t < |median b x-N|) :
    b+1 ≤ badCount (fun y : ℝ => t < |y-N|) x := by
  classical
  by_contra hcount
  let g := Finset.univ.filter (fun i => ¬ t < |x i-N|)
  have he : (Finset.univ.filter (fun i => t < |x i-N|)).card + g.card = 2*b+1 := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => t < |x i-N|))
  have hg : b+1 ≤ g.card := by rw [badCount_eq_card] at hcount; omega
  have hi := median_interval b x (N-t) (N+t) g hg (by
    intro i hi
    have hh : |x i-N| ≤ t := le_of_not_gt (Finset.mem_filter.mp hi).2
    have hh' := abs_le.mp hh
    constructor <;> linarith)
  have hh : |median b x-N| ≤ t := abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
  exact (not_lt_of_ge hh) hbad

theorem median_of_means_failure {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (N C ε : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C) (hε : 0 < ε)
    (hmean : uniformMean f = N)
    (hsecond : uniformMean (fun x => f x^2) ≤ C*N^2)
    (m : ℕ) (hm : 0 < m) (hgroup : C / ((m : ℝ)*ε^2) ≤ 1/16) (b : ℕ) :
    uniformMean (fun w : Fin (2*b+1) → Fin m → Ω =>
      if ε*N < |median b (fun i => sampleMean f (w i))-N| then (1 : ℝ) else 0) ≤
        (2 : ℝ)⁻¹^b := by
  classical
  have hp := (sample_relative_failure f N C ε hN hC hε hmean hsecond m hm).trans hgroup
  apply le_trans _ (majority_failure (fun w : Fin m → Ω => ε*N < |sampleMean f w-N|) hp b)
  apply mean_mono
  intro w
  split_ifs with hmed hcnt hcnt
  · rfl
  · exact False.elim (hcnt (median_bad_majority b _ N (ε*N) hmed))
  · norm_num
  · rfl

theorem median_success_probability {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (N C ε : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C) (hε : 0 < ε)
    (hmean : uniformMean f = N)
    (hsecond : uniformMean (fun x => f x^2) ≤ C*N^2)
    (m : ℕ) (hm : 0 < m) (hgroup : C / ((m : ℝ)*ε^2) ≤ 1/16) (b : ℕ) :
    1-(2 : ℝ)⁻¹^b ≤
      uniformMean (fun w : Fin (2*b+1) → Fin m → Ω =>
        if |median b (fun i => sampleMean f (w i))-N| ≤ ε*N then (1 : ℝ) else 0) := by
  classical
  have h := median_of_means_failure f N C ε hN hC hε hmean hsecond m hm hgroup b
  have he (w : Fin (2*b+1) → Fin m → Ω) :
      (if |median b (fun i => sampleMean f (w i))-N| ≤ ε*N then (1 : ℝ) else 0) =
      1-(if ε*N < |median b (fun i => sampleMean f (w i))-N| then (1 : ℝ) else 0) := by
    split_ifs <;> simp_all <;> linarith
  simp_rw [he,mean_sub,mean_const]
  linarith

end KoanaKPaths.Main.FiniteSampling

namespace KoanaKPaths.Main

lemma inv_le_two_pow_ctrl (x : ℝ) (hx : 0 < x) : x⁻¹ ≤ (2 : ℝ)^(ctrl x) := by
  have hl : Real.logb 2 x⁻¹ ≤ (ctrl x : ℝ) := Nat.le_ceil _
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (inv_pos.mpr hx)).mp hl
  simpa only [Real.rpow_natCast] using h

lemma control_failure_bound (x : ℝ) (hx : 0 < x) : (2 : ℝ)⁻¹^(ctrl x) ≤ x := by
  have h := inv_anti₀ (inv_pos.mpr hx) (inv_le_two_pow_ctrl x hx)
  simpa only [inv_inv,inv_pow] using h

lemma control_accuracy_bound (x : ℝ) (hx : 0 < x) : 1 ≤ (4 : ℝ)^(ctrl x)*x^2 := by
  have h := inv_le_two_pow_ctrl x hx
  have hh : (1 : ℝ)/x ≤ (2 : ℝ)^(ctrl x) := by simpa only [one_div] using h
  have hm : 1 ≤ (2 : ℝ)^(ctrl x)*x := (div_le_iff₀ hx).mp hh
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hm 2
  have he : ((2 : ℝ)^(ctrl x))^2 = (4 : ℝ)^(ctrl x) := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  simpa only [one_pow,mul_pow,he] using hs

lemma ctrl_pos (x : ℝ) (hx : 0 < x) (hx1 : x < 1) : 1 ≤ ctrl x := by
  have hlog : 0 < Real.logb 2 x⁻¹ := (Real.logb_pos_iff (by norm_num : (1 : ℝ) < 2) (inv_pos.mpr hx)).mpr (one_lt_inv₀ hx |>.mpr hx1)
  have h : 0 < (ctrl x : ℝ) := lt_of_lt_of_le hlog (Nat.le_ceil _)
  exact_mod_cast h

lemma exp_two_le_sixteen : Real.exp 2 ≤ 16 := by
  have h := Real.exp_one_lt_three
  have hp := Real.exp_pos 1
  rw [show (2 : ℝ) = 1+1 by norm_num,Real.exp_add]
  nlinarith

lemma controlled_group_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    (Real.exp 2*(k : ℝ)^3) / ((1024*(k : ℝ)^3*4^(ctrl ε))*ε^2) ≤ 1/16 := by
  have hacc := control_accuracy_bound ε hε
  have hk0 : 0 < (k : ℝ)^3 := by positivity
  have he := exp_two_le_sixteen
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (1024*(k : ℝ)^3*4^(ctrl ε))*ε^2)).mpr
  have hh := mul_le_mul_of_nonneg_left hacc (le_of_lt hk0)
  nlinarith

end KoanaKPaths.Main

set_option synthInstance.maxSize 4096

open scoped BigOperators
namespace KoanaKPaths.Main
open KoanaKPaths.Sampling FiniteSampling

lemma walkTensor_zeroOne (n : ℕ) (arcs : List (Fin n × Fin n)) (k : ℕ) :
    IsZeroOneTensor (walkTensor n arcs k) := by
  intro τ
  unfold walkTensor
  split_ifs <;> simp

lemma walkTensor_count (n : ℕ) (arcs : List (Fin n × Fin n)) (k : ℕ) :
    tensorN (walkTensor n arcs k) = (PathCount2k.N n arcs.toFinset k : ℤ) := by
  classical
  simp [tensorN,walkTensor,PathCount2k.N,PathCount2k.paths,Finset.sum_ite,
    Finset.filter_filter,and_comm]

lemma tensorN_nonneg {n k : ℕ} (c : (Fin k → Fin n) → ℤ) (hc : IsZeroOneTensor c) :
    0 ≤ tensorN c := by
  apply Finset.sum_nonneg
  intro τ _
  rcases hc τ with h | h <;> simp [h]

lemma sketchFrobSq_nonneg {n k ℓ : ℕ} (c : (Fin k → Fin n) → ℤ)
    (σ : Labels n k) (R : SketchSigns n k ℓ) (i : ℕ) : 0 ≤ sketchFrobSq c σ R i := by
  cases i <;> simp only [sketchFrobSq,psiFrobSq] <;> positivity

lemma trialDenominator_pos (k : ℕ) (hk : 1 ≤ k) : 0 < trialDenominator k := by
  unfold trialDenominator
  positivity

lemma groupTrials_pos (k a : ℕ) (hk : 1 ≤ k) : 0 < groupTrials k a := by
  unfold groupTrials
  positivity

lemma trial_value {n k : ℕ} (c : (Fin k → Fin n) → ℤ)
    (w : Labels n k × SketchSigns n k k) :
    (trialNumerator c w : ℝ) / (trialDenominator k : ℝ) = Yhat c k w.1 w.2 := by
  have hz := sketchFrobSq_nonneg c w.1 w.2 k
  simp only [trialNumerator,trialDenominator,Yhat,Nat.cast_mul,Nat.cast_pow]
  rw [← Int.cast_natCast (R := ℝ) (sketchFrobSq c w.1 w.2 k).toNat,Int.toNat_of_nonneg hz]

lemma estimateFraction_den_pos {n k : ℕ} (c : (Fin k → Fin n) → ℤ)
    (hk : 1 ≤ k) (a b : ℕ)
    (w : Fin (2*b+1) → Fin (groupTrials k a) → Labels n k × SketchSigns n k k) :
    0 < (estimateFraction c a b w).den := by
  exact Nat.mul_pos (groupTrials_pos k a hk) (trialDenominator_pos k hk)

lemma estimateFraction_value {n k : ℕ} (c : (Fin k → Fin n) → ℤ)
    (hk : 1 ≤ k) (a b : ℕ)
    (w : Fin (2*b+1) → Fin (groupTrials k a) → Labels n k × SketchSigns n k k) :
    (((estimateFraction c a b w).val : ℚ) : ℝ) =
      median b (fun i => sampleMean (fun z => Yhat c k z.1 z.2) (w i)) := by
  have hm : 0 < (groupTrials k a : ℝ) := by exact_mod_cast groupTrials_pos k a hk
  have hd : 0 < (trialDenominator k : ℝ) := by exact_mod_cast trialDenominator_pos k hk
  simp only [HypergraphUnreliability.FPRAS.Frac.val,estimateFraction,Rat.cast_div,
    Rat.cast_natCast,Nat.cast_mul,Rat.cast_mul]
  have hmono : Monotone (fun z : ℕ => (z : ℝ)/((groupTrials k a : ℝ)*(trialDenominator k : ℝ))) := by
    intro u v huv
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr huv) (by positivity)
  rw [median_map _ hmono]
  congr 1
  funext i
  simp only [sampleMean,← trial_value,Nat.cast_sum,← Finset.sum_div]
  ring

theorem amplified_estimator_accuracy (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (c : (Fin k → Fin n) → ℤ) (hc : IsZeroOneTensor c)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    1-δ ≤ uniformMean (fun w :
      Fin (2*ctrl δ+1) → Fin (groupTrials k (ctrl ε)) → Labels n k × SketchSigns n k k =>
      if |(((estimateFraction c (ctrl ε) (ctrl δ) w).val : ℚ) : ℝ)-(tensorN c : ℝ)| ≤
          ε*(tensorN c : ℝ) then (1 : ℝ) else 0) := by
  classical
  have ht := (recursive_estimator_moments n k k hn hk hk c hc).2 rfl
  have hN : 0 ≤ (tensorN c : ℝ) := by exact_mod_cast tensorN_nonneg c hc
  have hC : 0 ≤ Real.exp 2*(k : ℝ)^3 := by positivity
  have hg : Real.exp 2*(k : ℝ)^3/((groupTrials k (ctrl ε) : ℝ)*ε^2) ≤ 1/16 := by
    simpa only [groupTrials,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using controlled_group_bound k hk ε hε
  have h := median_success_probability (fun z : Labels n k × SketchSigns n k k => Yhat c k z.1 z.2)
    (tensorN c : ℝ) (Real.exp 2*(k : ℝ)^3) ε hN hC hε ht.1 (by convert ht.2 using 1 <;> ring)
    (groupTrials k (ctrl ε)) (groupTrials_pos k _ hk) hg (ctrl δ)
  simp_rw [estimateFraction_value c hk] 
  exact le_trans (by linarith [control_failure_bound δ hδ]) h

end KoanaKPaths.Main

theorem solution (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (c : (Fin k → Fin n) → ℤ) (hc : IsZeroOneTensor c)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    1-δ ≤ uniformMean (fun w :
      Fin (2*ctrl δ+1) → Fin (groupTrials k (ctrl ε)) → Labels n k × SketchSigns n k k =>
      if |(((estimateFraction c (ctrl ε) (ctrl δ) w).val : ℚ) : ℝ)-(tensorN c : ℝ)| ≤
          ε*(tensorN c : ℝ) then (1 : ℝ) else 0) := by
  exact KoanaKPaths.Main.amplified_estimator_accuracy n k hn hk c hc ε δ hε hδ
