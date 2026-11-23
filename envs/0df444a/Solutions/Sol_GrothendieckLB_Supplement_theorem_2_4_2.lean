-- Prove2me | solution 2 for GrothendieckLB.Supplement.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:15:00.471667+00:00
-- url     : https://prove2.me/submissions/da86e12a-f0cc-4107-88ed-8da85880c67e

import Definitions.Def_GrothendieckLB_IsLocalInverseBranch
import Definitions.Def_GrothendieckLB_taylorCoeff
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Filter Finset GrothendieckLB FormalMultilinearSeries
open scoped Topology ENNReal NNReal

/-
The finite reindexing in this lemma adapts Sébastien Gouëzel's proof of
FormalMultilinearSeries.radius_right_inv_pos_of_radius_pos_aux1 in mathlib
(Apache 2.0). Giving each length its own weight retains the exact tail mass.
-/
private theorem weighted_compositions (n : ℕ) (u w : ℕ → ℝ)
    (hu : ∀ k, 0 ≤ u k) (hw : ∀ k, 0 ≤ w k) :
    ∑ k ∈ Ico 2 (n+1), ∑ c ∈ {c : Composition k | 1 < c.length}.toFinset,
      w c.length * ∏ j, u (c.blocksFun j) ≤
    ∑ j ∈ Ico 2 (n+1), w j * (∑ k ∈ Ico 1 n, u k)^j := by
  classical
  calc
    _ ≤ ∑ d ∈ compPartialSumTarget 2 (n+1) n,
        w d.2.length * ∏ j : Fin d.2.length, u (d.2.blocksFun j) := by
      rw [sum_sigma']
      gcongr
      · intro x _ _
        exact mul_nonneg (hw _) (prod_nonneg fun _ _ => hu _)
      rintro ⟨k, c⟩ hd
      simp only [Set.mem_toFinset (s := {c | 1 < Composition.length c}), mem_Ico, mem_sigma,
        Set.mem_ofPred_eq] at hd
      simp only [mem_compPartialSumTarget_iff]
      refine ⟨hd.2, c.length_le.trans_lt hd.1.2, fun j => ?_⟩
      have hn : c ≠ Composition.single k (zero_lt_two.trans_le hd.1.1) := by
        simp [Composition.eq_single_iff_length, ne_of_gt hd.2]
      rw [Composition.ne_single_iff] at hn
      exact (hn j).trans_le (Nat.lt_succ_iff.mp hd.1.2)
    _ = ∑ e ∈ compPartialSumSource 2 (n+1) n, w e.1 * ∏ j : Fin e.1, u (e.2 j) := by
      symm
      apply compChangeOfVariables_sum
      rintro ⟨k, blocks⟩ H
      have K : (compChangeOfVariables 2 (n+1) n ⟨k, blocks⟩ H).snd.length = k := by simp
      apply congrArg₂ (· * ·) (congrArg w K.symm)
      congr 2 <;> try rw [K]
      rw [Fin.heq_fun_iff K.symm]
      intro j
      rw [compChangeOfVariables_blocksFun]
    _ = _ := by
      rw [compPartialSumSource,
        ← sum_sigma' (Ico 2 (n+1))
          (fun k : ℕ => (Fintype.piFinset fun _ : Fin k => Ico 1 n : Finset (Fin k → ℕ)))
          (fun k e => w k * ∏ j : Fin k, u (e j))]
      apply sum_congr rfl
      intro k _
      rw [← mul_sum, sum_pow']

private theorem power_series_of_sum (b : ℕ → ℝ) (hb : Summable fun n => |b n|)
    (H : ℝ → ℝ) (hH : ∀ t : ℝ, |t| < 1 → H t = ∑' n, b n * t^n) :
    HasFPowerSeriesAt H (ofScalars ℝ b) 0 := by
  let p := ofScalars ℝ b
  have hr : (1 : ℝ≥0∞) ≤ p.radius := by
    have h := p.le_radius_of_summable_norm (r := (1 : ℝ≥0)) (by
      simpa [p, ofScalars_norm, Real.norm_eq_abs] using hb)
    simpa using h
  apply (p.hasFPowerSeriesOnBall (lt_of_lt_of_le zero_lt_one hr)).hasFPowerSeriesAt.congr
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
      (by norm_num : |(0:ℝ)| < 1)] with x hx
  calc
    p.sum x = ∑' n, b n * x^n := ofScalars_sum_eq b x
    _ = H x := (hH x hx).symm

private theorem coefficient_relations (b : ℕ → ℝ) (hb : Summable fun n => |b n|)
    (H : ℝ → ℝ) (hH : ∀ t : ℝ, |t| < 1 → H t = ∑' n, b n * t^n)
    (G : ℝ → ℝ) (hG : IsLocalInverseBranch H G) :
    b 1 * taylorCoeff 1 G = 1 ∧
    ∀ n : ℕ, 2 ≤ n → b 1 * taylorCoeff n G =
      -(∑ c ∈ {c : Composition n | 1 < c.length}.toFinset,
        b c.length * ∏ j, taylorCoeff (c.blocksFun j) G) := by
  classical
  let a (n : ℕ) := taylorCoeff n G
  let p := ofScalars ℝ b
  let q := ofScalars ℝ a
  have hps : HasFPowerSeriesAt H p (G 0) := by
    rw [hG.2.1]
    exact power_series_of_sum b hb H hH
  have hqs : HasFPowerSeriesAt G q 0 := hG.1.hasFPowerSeriesAt
  have hid : AnalyticAt ℝ (_root_.id : ℝ → ℝ) 0 := analyticAt_id
  have hcomp := (hps.comp hqs).eq_formalMultilinearSeries_of_eventually
    hid.hasFPowerSeriesAt hG.2.2
  have hc (n : ℕ) : (p.comp q) n (fun _ => 1) = if n = 1 then 1 else 0 := by
    rw [hcomp, ofScalars_apply_eq, iteratedDeriv_id]
    by_cases hz : n = 0
    · subst n
      norm_num
    by_cases h1 : n = 1
    · subst n
      norm_num
    simp [hz, h1]
  have hlin (n : ℕ) : (p 1 fun _ => q n (fun _ => 1)) = b 1 * a n := by
    simp [p, q, ofScalars_apply_eq, smul_eq_mul, mul_comm]
  have hblock {n : ℕ} (c : Composition n) :
      p c.length (q.applyComposition c (fun _ => 1)) = b c.length * ∏ j, a (c.blocksFun j) := by
    rw [apply_eq_prod_smul_coeff, smul_eq_mul, mul_comm]
    simp only [p, coeff_ofScalars]
    congr 1
    apply prod_congr rfl
    intro j _
    change (ofScalars ℝ a) (c.blocksFun j) (fun _ => 1) = a (c.blocksFun j)
    simp [ofScalars_apply_eq, smul_eq_mul]
  constructor
  · have h := hc 1
    rw [comp_coeff_one, hlin] at h
    simpa only [ite_true, eq_self] using h
  · intro n hn
    have h := hc n
    rw [comp_rightInv_aux1 (by omega : 0 < n), if_neg (by omega : n ≠ 1), hlin] at h
    simp only [hblock] at h
    change b 1 * a n = _
    exact eq_neg_of_add_eq_zero_right (by simpa only [add_comm] using h)

private theorem majorant_at (b a : ℕ → ℝ) (hb : Summable fun n => |b n|)
    (hb₁ : 0 < b 1) (hlin : b 1 * a 1 = 1)
    (hcoeff : ∀ n : ℕ, 2 ≤ n → b 1 * a n =
      -(∑ c ∈ {c : Composition n | 1 < c.length}.toFinset,
        b c.length * ∏ j, a (c.blocksFun j))) (r : ℝ) (hr : 0 < r)
    (hgap : r + (∑' m, |b (m+2)|) < b 1) :
    Summable (fun n : ℕ => |a (n+1)| * r^(n+1)) ∧
    ∑' n : ℕ, |a (n+1)| * r^(n+1) ≤ (r + ∑' m, |b (m+2)|) / b 1 := by
  classical
  let u (k : ℕ) := |a k| * r^k
  let D := ∑' m, |b (m+2)|
  let Q := (r + D) / b 1
  have hu (k : ℕ) : 0 ≤ u k := mul_nonneg (abs_nonneg _) (pow_nonneg hr.le _)
  have hD : 0 ≤ D := tsum_nonneg fun _ => abs_nonneg _
  have hQ : 0 ≤ Q := div_nonneg (add_nonneg hr.le hD) hb₁.le
  have hlt : Q < 1 := (div_lt_one hb₁).2 hgap
  have hu1 : b 1 * u 1 = r := by
    have h := congrArg abs hlin
    rw [abs_mul, abs_of_pos hb₁, abs_one] at h
    dsimp only [u]
    rw [pow_one, ← mul_assoc, h, one_mul]
  have hstep (k : ℕ) (hk : 2 ≤ k) : b 1 * u k ≤
      ∑ c ∈ {c : Composition k | 1 < c.length}.toFinset,
        |b c.length| * ∏ j, u (c.blocksFun j) := by
    have h := congrArg abs (hcoeff k hk)
    rw [abs_mul, abs_of_pos hb₁, abs_neg] at h
    calc
      b 1 * u k = (b 1 * |a k|) * r^k := by dsimp [u]; ring
      _ = _ := congrArg (· * r^k) h
      _ ≤ (∑ c ∈ {c : Composition k | 1 < c.length}.toFinset,
        |b c.length * ∏ j, a (c.blocksFun j)|) * r^k :=
        mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (pow_nonneg hr.le _)
      _ = _ := by
        rw [sum_mul]
        apply sum_congr rfl
        intro c _
        simp only [abs_mul, Finset.abs_prod, u, prod_mul_distrib, prod_pow_eq_pow_sum,
          Composition.sum_blocksFun]
        ring
  have hTail : Summable (fun m : ℕ => |b (m+2)|) := (summable_nat_add_iff 2).2 hb
  have hfin (n : ℕ) : ∑ k ∈ Ico 1 n, u k ≤ Q := by
    induction n with
    | zero => simpa using hQ
    | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simpa using hQ
      have hN : 1 < n+1 := by omega
      apply (le_div_iff₀ hb₁).2
      rw [mul_comm, sum_eq_sum_Ico_succ_bot hN, mul_add, hu1, mul_sum]
      apply add_le_add_right
      calc
        _ ≤ ∑ k ∈ Ico 2 (n+1), ∑ c ∈ {c : Composition k | 1 < c.length}.toFinset,
            |b c.length| * ∏ j, u (c.blocksFun j) :=
          sum_le_sum fun k hk => hstep k (mem_Ico.mp hk).1
        _ ≤ ∑ j ∈ Ico 2 (n+1), |b j| * (∑ k ∈ Ico 1 n, u k)^j :=
          weighted_compositions n u (fun j => |b j|) hu (fun _ => abs_nonneg _)
        _ ≤ ∑ j ∈ Ico 2 (n+1), |b j| := by
          apply sum_le_sum
          intro j _
          exact mul_le_of_le_one_right (abs_nonneg _)
            (pow_le_one₀ (sum_nonneg fun _ _ => hu _) (ih.trans hlt.le))
        _ ≤ D := by
          rw [sum_Ico_eq_sum_range]
          simpa only [Nat.add_comm 2] using
            (hTail.sum_le_tsum (range (n+1-2)) (fun _ _ => abs_nonneg _))
  have hbound (n : ℕ) : ∑ i ∈ range n, u (i+1) ≤ Q := by
    have h := hfin (n+1)
    simpa [sum_Ico_eq_sum_range, Nat.add_comm 1] using h
  exact ⟨summable_of_sum_range_le (fun n => hu (n+1)) hbound,
    Real.tsum_le_of_sum_range_le (fun n => hu (n+1)) hbound⟩

theorem solution (b : ℕ → ℝ) (hb_even : ∀ m, Even m → b m = 0) (hb₁ : 0 < b 1)
    (hb_sum : Summable (fun m => |b m|)) (H : ℝ → ℝ)
    (hH : ∀ t : ℝ, |t| < 1 → H t = ∑' m, b m * t ^ m) (G : ℝ → ℝ)
    (hG : IsLocalInverseBranch H G) (γ : ℝ) (hγ : 0 < γ)
    (hgap : γ + ∑' m, |b (m + 2)| < b 1) :
    (∃ R : ℝ, γ < R ∧ Summable (fun n => |taylorCoeff n G| * R ^ n)) ∧
      Summable (fun n => |taylorCoeff (n + 1) G| * γ ^ (n + 1)) ∧
      ∑' n, |taylorCoeff (n + 1) G| * γ ^ (n + 1) ≤ (γ + ∑' m, |b (m + 2)|) / b 1 ∧
      (γ + ∑' m, |b (m + 2)|) / b 1 < 1 := by
  let D := ∑' m, |b (m+2)|
  let R := (γ + (b 1 - D))/2
  have hg : γ + D < b 1 := hgap
  have hR : γ < R := by dsimp [R]; linarith
  have hRgap : R + D < b 1 := by dsimp [R]; linarith
  obtain ⟨hlin, hcoeff⟩ := coefficient_relations b hb_sum H hH G hG
  have hmajor := majorant_at b (fun n => taylorCoeff n G) hb_sum hb₁ hlin hcoeff
  obtain ⟨hs, hbound⟩ := hmajor γ hγ hgap
  exact ⟨⟨R, hR, (summable_nat_add_iff 1).1 (hmajor R (hγ.trans hR) hRgap).1⟩,
    hs, hbound, (div_lt_one hb₁).2 hgap⟩
