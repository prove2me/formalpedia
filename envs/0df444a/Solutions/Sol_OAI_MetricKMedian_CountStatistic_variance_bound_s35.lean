-- Prove2me | solution 1 for OAI.MetricKMedian.CountStatistic.variance_bound_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:53:48.691374+00:00
-- url     : https://prove2.me/submissions/1f0eea6f-67ba-45c2-96d8-51bb5daf7a9e

import Mathlib
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K012

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

omit [Fintype Ξ] in
theorem variance_const (μ : FiniteLaw Ω) (c : ℝ) : μ.variance (fun _ => c)=0 := by
  rw [variance_eq, expect_const, expect_const, sub_self]

omit [Fintype Ξ] in
theorem expect_abs_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    |μ.expect f| ≤ μ.expect (fun ω => |f ω|) := by
  unfold expect
  calc
    _ ≤ ∑ ω, |μ.weight ω*f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_congr rfl (fun ω _ => by rw [abs_mul, abs_of_nonneg (μ.nonneg ω)])

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw

theorem bernoulli_expect_succ {n : ℕ} (p : Fin (n+1) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : (Fin (n+1) → Bool) → ℝ) :
    (bernoulli p hp0 hp1).expect f =
      (1-p 0)*(bernoulli (fun i => p i.succ) (fun i => hp0 i.succ) (fun i => hp1 i.succ)).expect
        (fun ω => f (Fin.cons false ω))+
      p 0*(bernoulli (fun i => p i.succ) (fun i => hp0 i.succ) (fun i => hp1 i.succ)).expect
        (fun ω => f (Fin.cons true ω)) := by
  unfold expect bernoulli
  rw [← (bitsConsEquiv n).sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [bitsConsEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, coinWeight_true, coinWeight_false, mul_assoc, Finset.mul_sum]
  ring

theorem bernoulli_variance_succ {n : ℕ} (p : Fin (n+1) → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : (Fin (n+1) → Bool) → ℝ) :
    let μ := bernoulli (fun i : Fin n => p i.succ) (fun i => hp0 i.succ) (fun i => hp1 i.succ)
    (bernoulli p hp0 hp1).variance f =
      (1-p 0)*μ.variance (fun ω => f (Fin.cons false ω))+
      p 0*μ.variance (fun ω => f (Fin.cons true ω))+
      p 0*(1-p 0)*(μ.expect (fun ω => f (Fin.cons true ω))-
        μ.expect (fun ω => f (Fin.cons false ω)))^2 := by
  dsimp only
  simp only [variance_eq, bernoulli_expect_succ]
  ring

theorem bernoulli_variance_bounded_differences : ∀ n : ℕ,
    ∀ (p C : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
      (_hC : ∀ i, 0 ≤ C i) (f : (Fin n → Bool) → ℝ),
    (∀ i ω, |f (Function.update ω i true)-f (Function.update ω i false)| ≤ C i) →
    (bernoulli p hp0 hp1).variance f ≤ ∑ i, p i*(1-p i)*(C i)^2 := by
  intro n
  induction n with
  | zero =>
    intro p C hp0 hp1 _ f _
    have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext ω
      congr 1
      exact Subsingleton.elim _ _
    rw [hf, variance_const]
    simp
  | succ n ih =>
    intro p C hp0 hp1 hC f hdiff
    let μ := bernoulli (fun i : Fin n => p i.succ) (fun i => hp0 i.succ) (fun i => hp1 i.succ)
    let tailBound := ∑ i : Fin n, p i.succ*(1-p i.succ)*(C i.succ)^2
    have hb : ∀ b : Bool, μ.variance (fun ω => f (Fin.cons b ω)) ≤ tailBound := by
      intro b
      apply ih (fun i => p i.succ) (fun i => C i.succ)
        (fun i => hp0 i.succ) (fun i => hp1 i.succ) (fun i => hC i.succ)
        (fun ω => f (Fin.cons b ω))
      intro i ω
      simpa only [Fin.cons_update] using hdiff i.succ (Fin.cons b ω)
    have hm : |μ.expect (fun ω => f (Fin.cons true ω))-
        μ.expect (fun ω => f (Fin.cons false ω))| ≤ C 0 := by
      rw [← μ.expect_sub]
      calc
        _ ≤ μ.expect (fun ω => |f (Fin.cons true ω)-f (Fin.cons false ω)|) := μ.expect_abs_le _
        _ ≤ μ.expect (fun _ => C 0) := μ.expect_mono (fun ω => by
          simpa only [Fin.update_cons_zero] using hdiff 0 (Fin.cons false ω))
        _ = C 0 := μ.expect_const _
    have hmsq : (μ.expect (fun ω => f (Fin.cons true ω))-
        μ.expect (fun ω => f (Fin.cons false ω)))^2 ≤ (C 0)^2 :=
      by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (hC 0)).mpr hm
    rw [bernoulli_variance_succ, Fin.sum_univ_succ]
    change (1-p 0)*μ.variance (fun ω => f (Fin.cons false ω))+
      p 0*μ.variance (fun ω => f (Fin.cons true ω))+
      p 0*(1-p 0)*(μ.expect (fun ω => f (Fin.cons true ω))-
        μ.expect (fun ω => f (Fin.cons false ω)))^2 ≤ p 0*(1-p 0)*(C 0)^2+tailBound
    have h0 := mul_le_mul_of_nonneg_left (hb false) (sub_nonneg.mpr (hp1 0))
    have h1 := mul_le_mul_of_nonneg_left (hb true) (hp0 0)
    have h2 := mul_le_mul_of_nonneg_left hmsq (mul_nonneg (hp0 0) (sub_nonneg.mpr (hp1 0)))
    nlinarith only [h0, h1, h2]

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem bernoulli_expect_equiv (e : I ≃ J) (p : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : (I → Bool) → ℝ) :
    (bernoulli p hp0 hp1).expect f =
      (bernoulli (fun j => p (e.symm j)) (fun j => hp0 (e.symm j))
        (fun j => hp1 (e.symm j))).expect (fun ω => f (ω ∘ e)) := by
  unfold expect bernoulli
  rw [← (bitsEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  change (∏ i, coinWeight (p i) (ω (e i)))*f (ω ∘ e)=_
  have he := e.prod_comp (fun j => coinWeight (p (e.symm j)) (ω j))
  simp only [Equiv.symm_apply_apply] at he
  rw [he]

theorem bernoulli_variance_equiv (e : I ≃ J) (p : I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : (I → Bool) → ℝ) :
    (bernoulli p hp0 hp1).variance f =
      (bernoulli (fun j => p (e.symm j)) (fun j => hp0 (e.symm j))
        (fun j => hp1 (e.symm j))).variance (fun ω => f (ω ∘ e)) := by
  simp only [variance_eq,bernoulli_expect_equiv e p hp0 hp1]

theorem bernoulli_variance_bounded_differences_fintype
    (p C : I → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hC : ∀ i, 0 ≤ C i) (f : (I → Bool) → ℝ)
    (hdiff : ∀ i ω, |f (Function.update ω i true)-f (Function.update ω i false)| ≤ C i) :
    (bernoulli p hp0 hp1).variance f ≤ ∑ i, p i*(1-p i)*(C i)^2 := by
  let e := Fintype.equivFin I
  rw [bernoulli_variance_equiv e]
  have hd : ∀ i ω,
      |f (Function.update ω i true ∘ e)-f (Function.update ω i false ∘ e)| ≤ C (e.symm i) := by
    intro i ω
    simpa only [Function.update_comp_equiv] using hdiff (e.symm i) (ω ∘ e)
  have hh := bernoulli_variance_bounded_differences (Fintype.card I)
    (fun i => p (e.symm i)) (fun i => C (e.symm i))
    (fun i => hp0 (e.symm i)) (fun i => hp1 (e.symm i)) (fun i => hC (e.symm i))
    (fun ω => f (ω ∘ e)) hd
  exact hh.trans_eq (e.symm.sum_comp (fun i => p i*(1-p i)*(C i)^2))

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_QuadraticCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountStatistic
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem bit_nonneg (ω : I → Bool) (i : I) : 0 ≤ bit ω i := by unfold bit; split_ifs <;> norm_num
omit [Fintype I] [DecidableEq I] in
theorem bit_le_one (ω : I → Bool) (i : I) : bit ω i ≤ 1 := by unfold bit; split_ifs <;> norm_num

omit [Fintype I] in
theorem bit_update (ω : I → Bool) (i j : I) (v : Bool) :
    bit (Function.update ω i v) j=if j=i then (if v then (1:ℝ) else 0) else bit ω j := by
  by_cases h : j=i
  · subst j; simp only [bit, Function.update_self, ite_true]
  · simp only [bit, Function.update_of_ne h, ite_eq_right h]

theorem difference (b : I → ℝ) (c : I → I → ℝ)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (ω : I → Bool) (e : I) :
    statistic b c (Function.update ω e true)-statistic b c (Function.update ω e false)=
      b e+∑ j, c e j*bit ω j := by
  let xt := bit (Function.update ω e true)
  let xf := bit (Function.update ω e false)
  have hlin : (∑ i, b i*xt i)-(∑ i, b i*xf i)=b e := by
    rw [← Finset.sum_sub_distrib]
    have hp : ∀ i, b i*xt i-b i*xf i=if i=e then b e else 0 := by
      intro i
      dsimp only [xt, xf]
      simp only [bit_update, Bool.false_eq_true, ite_true, ite_false]
      by_cases hi : i=e
      · subst i; simp only [ite_true, mul_one, mul_zero, sub_zero]
      · simp only [ite_eq_right hi, sub_self]
    simp_rw [hp]
    simp
  have hprod : ∀ i j, c i j*xt i*xt j-c i j*xf i*xf j =
      (if i=e then c e j*bit ω j else 0)+(if j=e then c i e*bit ω i else 0) := by
    intro i j
    dsimp only [xt, xf]
    simp only [bit_update, Bool.false_eq_true, ite_true, ite_false]
    by_cases hi : i=e <;> by_cases hj : j=e
    · subst i; subst j; simp only [hdiag, zero_mul, sub_self, ite_true, add_zero]
    · subst i; simp only [ite_true, ite_eq_right hj, mul_one, mul_zero, zero_mul, sub_zero, add_zero]
    · subst j; simp only [ite_true, ite_eq_right hi, mul_one, mul_zero, sub_zero, zero_add]
    · simp only [ite_eq_right hi, ite_eq_right hj, sub_self, zero_add]
  have hquad : (∑ i, ∑ j, c i j*xt i*xt j)-(∑ i, ∑ j, c i j*xf i*xf j) =
      2*∑ j, c e j*bit ω j := by
    simp only [← Finset.sum_sub_distrib]
    simp_rw [hprod]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hswap : (∑ i, c i e*bit ω i)=(∑ i, c e i*bit ω i) :=
      Finset.sum_congr rfl (fun i _ => by rw [hc i e])
    rw [hswap]
    ring
  unfold statistic
  change (∑ i, b i*xt i)+(1/2)*(∑ i, ∑ j, c i j*xt i*xt j)-
    ((∑ i, b i*xf i)+(1/2)*(∑ i, ∑ j, c i j*xf i*xf j))=_
  linarith only [hlin, hquad]

theorem difference_bound (b : I → ℝ) (c : I → I → ℝ)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (ω : I → Bool) (e : I) :
    |statistic b c (Function.update ω e true)-statistic b c (Function.update ω e false)| ≤
      |b e|+∑ j, c e j := by
  rw [difference b c hc hdiag]
  have hs0 : 0 ≤ ∑ j, c e j*bit ω j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hc0 e j) (bit_nonneg ω j))
  calc
    _ ≤ |b e|+|∑ j, c e j*bit ω j| := abs_add_le _ _
    _ = |b e|+∑ j, c e j*bit ω j := by rw [abs_of_nonneg hs0]
    _ ≤ _ := add_le_add_right (Finset.sum_le_sum (fun j _ =>
      mul_le_of_le_one_right (hc0 e j) (bit_le_one ω j))) _

end MetricKMedian.CountStatistic
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountStatistic

open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem action_difference_bound (a m : I → ℝ) (c : I → I → ℝ)
    {D : ℝ} (hD : 1 ≤ D) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, c i j ≤ (D-1)*m i) (ω : I → Bool) (e : I) :
    |statistic (fun i => a i-m i) c (Function.update ω e true)-
      statistic (fun i => a i-m i) c (Function.update ω e false)| ≤ D*(a e+m e) := by
  have hd := difference_bound (fun i => a i-m i) c hc hdiag hc0 ω e
  have habs : |a e-m e| ≤ a e+m e := by
    apply abs_le.mpr
    constructor <;> linarith only [ha e, hm e]
  have hda : a e ≤ D*a e := le_mul_of_one_le_left (ha e) hD
  linarith [hrow e]

theorem variance_bound_s35_oai (p a m : I → ℝ) (c : I → I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {D P B : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P)
    (hpP : ∀ i, p i ≤ P) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, a i+m i ≤ B)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, c i j ≤ (D-1)*m i) :
    (FiniteLaw.bernoulli p hp0 hp1).variance (statistic (fun i => a i-m i) c) ≤
      P*D^2*B*(∑ i : I, (a i+m i)) := by
  have hD0 : 0 ≤ D := by linarith only [hD]
  apply (FiniteLaw.bernoulli_variance_bounded_differences_fintype p (fun i => D*(a i+m i))
    hp0 hp1 (fun i => mul_nonneg hD0 (add_nonneg (ha i) (hm i))) _
    (fun e ω => action_difference_bound a m c hD ha hm hc hdiag hc0 hrow ω e)).trans
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hsum0 := add_nonneg (ha i) (hm i)
  have hbase : p i*(1-p i) ≤ P := by
    calc
      _ ≤ p i := mul_le_of_le_one_right (hp0 i) (by linarith only [hp0 i])
      _ ≤ P := hpP i
  have hsq : (a i+m i)^2 ≤ B*(a i+m i) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hsize i)) hsum0]
  calc
    p i*(1-p i)*(D*(a i+m i))^2 ≤ P*(D*(a i+m i))^2 :=
      mul_le_mul_of_nonneg_right hbase (sq_nonneg _)
    _ = P*D^2*(a i+m i)^2 := by ring
    _ ≤ P*D^2*(B*(a i+m i)) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg hP (sq_nonneg _))
    _ = P*D^2*B*(a i+m i) := by ring

end MetricKMedian.CountStatistic
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.CountStatistic.variance_bound_s35_oai.{u_1} := @OAI.MetricKMedian.CountStatistic.variance_bound_s35_oai.{u_1}
