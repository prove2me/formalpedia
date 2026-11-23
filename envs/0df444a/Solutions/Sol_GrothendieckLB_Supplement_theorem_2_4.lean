-- Prove2me | solution 1 for GrothendieckLB.Supplement.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T16:57:59.025477+00:00
-- url     : https://prove2.me/submissions/feabc851-c559-4181-b6d0-b42cc4940e5c

import Definitions.Def_GrothendieckLB_IsLocalInverseBranch
import Definitions.Def_GrothendieckLB_taylorCoeff
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open Filter FormalMultilinearSeries GrothendieckLB
open scoped Topology

private theorem expansion_of_abs (b : ℕ → ℝ) (hs : Summable fun n => |b n|)
    (H : ℝ → ℝ) (hH : ∀ t : ℝ, |t| < 1 → H t = ∑' n, b n * t^n) :
    HasFPowerSeriesAt H (ofScalars ℝ b) 0 := by
  have hrad : (1 : ENNReal) ≤ (ofScalars ℝ b).radius := by
    apply le_radius_of_summable (ofScalars ℝ b) (r := 1)
    simpa [ofScalars_norm, Real.norm_eq_abs] using hs
  apply ((ofScalars ℝ b).hasFPowerSeriesOnBall (lt_of_lt_of_le zero_lt_one hrad)).hasFPowerSeriesAt.congr
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
  filter_upwards [hnear] with t ht
  exact (ofScalars_sum_eq b t).trans (hH t ht).symm

private noncomputable def idCoeff (n : ℕ) : ℝ := if n = 1 then 1 else 0

private theorem inverse_coefficients (b : ℕ → ℝ) (hs : Summable fun n => |b n|)
    (H : ℝ → ℝ) (hH : ∀ t : ℝ, |t| < 1 → H t = ∑' n, b n * t^n)
    (G : ℝ → ℝ) (hG : IsLocalInverseBranch H G) :
    (ofScalars ℝ b).comp (ofScalars ℝ fun n => taylorCoeff n G) = ofScalars ℝ idCoeff := by
  have hp : HasFPowerSeriesAt H (ofScalars ℝ b) (G 0) := by
    rw [hG.2.1]
    exact expansion_of_abs b hs H hH
  have hid : HasFPowerSeriesAt (fun x : ℝ => x) (ofScalars ℝ idCoeff) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards with t
    simpa +contextual [idCoeff, smul_eq_mul, mul_ite] using (hasSum_ite_eq (1 : ℕ) (t : ℝ))
  exact (hp.comp hG.1.hasFPowerSeriesAt).eq_formalMultilinearSeries_of_eventually hid hG.2.2

private theorem scalar_piece (b a : ℕ → ℝ) {n : ℕ} (c : Composition n) (r : ℝ) :
    (ofScalars ℝ b).compAlongComposition (ofScalars ℝ a) c (fun _ => r) =
      b c.length * ∏ i : Fin c.length, (a (c.blocksFun i) * r^(c.blocksFun i)) := by
  rw [compAlongComposition_apply, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    coeff_ofScalars, smul_eq_mul, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact ofScalars_apply_eq a r _

private def multiBlocks (n : ℕ) : Finset (Composition n) :=
  Finset.univ.filter (fun c => 2 ≤ c.length)

private theorem coeff_estimate (a b : ℕ → ℝ)
    (hc : (ofScalars ℝ b).comp (ofScalars ℝ a) = ofScalars ℝ idCoeff)
    (hb : 0 < b 1) (r : ℝ) (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) :
    b 1 * (|a n| * r^n) ≤ (if n = 1 then r else 0) +
      ∑ c ∈ multiBlocks n, |b c.length| * ∏ i : Fin c.length, (|a (c.blocksFun i)| * r^(c.blocksFun i)) := by
  classical
  let term (c : Composition n) := b c.length * ∏ i : Fin c.length, (a (c.blocksFun i) * r^(c.blocksFun i))
  have hsum : (∑ c : Composition n, term c) = if n = 1 then r else 0 := by
    have h := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p n (fun _ => r)) hc
    change ((ofScalars ℝ b).comp (ofScalars ℝ a) n) (fun _ => r) = _ at h
    simp only [FormalMultilinearSeries.comp, ContinuousMultilinearMap.sum_apply, scalar_piece,
      ofScalars_apply_eq, idCoeff, smul_eq_mul] at h
    by_cases hn1 : n = 1 <;> simpa [term, hn1] using h
  have hsingle : term (Composition.single n hn) = b 1 * (a n * r^n) := by
    have hp :
        (∏ i : Fin (Composition.single n hn).length,
          a ((Composition.single n hn).blocksFun i) * r^((Composition.single n hn).blocksFun i)) =
          ∏ _i : Fin (Composition.single n hn).length, (a n * r^n) :=
      Finset.prod_congr rfl fun i _ => congrArg (fun k => a k * r^k) (Composition.single_blocksFun hn i)
    dsimp only [term]
    rw [hp, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Composition.single_length, pow_one]
  have hset : multiBlocks n = Finset.univ.erase (Composition.single n hn) := by
    ext c
    simp only [multiBlocks, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    have hlen := Composition.length_pos_of_pos c hn
    rw [ne_eq, Composition.eq_single_iff_length]
    omega
  have hsplit : (∑ c ∈ multiBlocks n, term c) + b 1 * (a n * r^n) =
      (if n = 1 then r else 0) := by
    rw [hset, ← hsingle, Finset.sum_erase_add _ _ (Finset.mem_univ _), hsum]
  have habs : |(if n = 1 then r else 0 : ℝ)| = (if n = 1 then r else 0) := by
    split <;> simp [abs_of_nonneg hr]
  calc
    b 1 * (|a n| * r^n) = |b 1 * (a n * r^n)| := by
      rw [abs_mul, abs_mul, abs_of_pos hb, abs_of_nonneg (pow_nonneg hr n)]
    _ = |(if n = 1 then r else 0) - ∑ c ∈ multiBlocks n, term c| := by congr 1; linarith only [hsplit]
    _ ≤ (if n = 1 then r else 0) + |∑ c ∈ multiBlocks n, term c| := by
      simpa only [habs] using abs_sub (if n = 1 then r else 0) (∑ c ∈ multiBlocks n, term c)
    _ ≤ _ := by
      apply add_le_add_right
      simpa only [term, abs_mul, Finset.abs_prod, abs_of_nonneg (pow_nonneg hr _)] using
        Finset.abs_sum_le_sum_abs term (multiBlocks n)

private noncomputable def nonlinear (b : ℕ → ℝ) (k : ℕ) : ℝ := if 2 ≤ k then |b k| else 0

private theorem sum_nonlinear_le (b : ℕ → ℝ) (hs : Summable fun n => |b (n+2)|) (M : ℕ) :
    (∑ k ∈ Finset.range M, nonlinear b k) ≤ ∑' n, |b (n+2)| := by
  have hsame : (∑ k ∈ Finset.range M, nonlinear b k) = ∑ k ∈ Finset.Ico 2 M, |b k| := by
    unfold nonlinear
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp [Finset.mem_Ico, and_comm]
  rw [hsame, Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_comm 2] using hs.sum_le_tsum (Finset.range (M-2)) (fun _ _ => abs_nonneg _)

private theorem prefix_bound (a b : ℕ → ℝ)
    (hc : (ofScalars ℝ b).comp (ofScalars ℝ a) = ofScalars ℝ idCoeff)
    (hb : 0 < b 1) (hs : Summable fun n => |b (n+2)|)
    (r : ℝ) (hr : 0 ≤ r) (hgap : r + ∑' n, |b (n+2)| ≤ b 1) (N : ℕ) :
    (∑ i ∈ Finset.Ico 1 (N+1), |a i| * r^i) ≤ (r + ∑' n, |b (n+2)|) / b 1 := by
  classical
  let w (i : ℕ) := |a i| * r^i
  have hw (i : ℕ) : 0 ≤ w i := mul_nonneg (abs_nonneg _) (pow_nonneg hr _)
  have he (i : ℕ) : 0 ≤ nonlinear b i := by unfold nonlinear; split <;> positivity
  let W (x : Σ n, Composition n) := nonlinear b x.2.length * ∏ i : Fin x.2.length, w (x.2.blocksFun i)
  have hW (x : Σ n, Composition n) : 0 ≤ W x := mul_nonneg (he _) (Finset.prod_nonneg fun _ _ => hw _)
  have hdelta : 0 ≤ ∑' n, |b (n+2)| := tsum_nonneg fun _ => abs_nonneg _
  change (∑ i ∈ Finset.Ico 1 (N+1), w i) ≤ _
  induction N with
  | zero => simpa using div_nonneg (add_nonneg hr hdelta) hb.le
  | succ N ih =>
    let t := ∑ i ∈ Finset.Ico 1 (N+1), w i
    have ht : 0 ≤ t := Finset.sum_nonneg fun _ _ => hw _
    have ht1 : t ≤ 1 := ih.trans ((div_le_one hb).mpr hgap)
    let I := Finset.Ico 1 (N+2)
    let J := I.sigma multiBlocks
    have hpiece (n : ℕ) (hn : n ∈ I) : b 1 * w n ≤ (if n = 1 then r else 0) +
        ∑ c ∈ multiBlocks n, W ⟨n,c⟩ := by
      apply (coeff_estimate a b hc hb r hr (Finset.mem_Ico.mp hn).1).trans_eq
      congr 1
      apply Finset.sum_congr rfl
      intro c hcm
      have hl : 2 ≤ c.length := (Finset.mem_filter.mp hcm).2
      simp [W, w, nonlinear, hl]
    have hsub : J ⊆ compPartialSumTarget 0 (N+2) (N+1) := by
      rintro ⟨n,c⟩ hx
      obtain ⟨hn, hcm⟩ := Finset.mem_sigma.mp hx
      obtain ⟨hn1,hn2⟩ := Finset.mem_Ico.mp hn
      change 1 ≤ n at hn1
      change n < N+2 at hn2
      have hl : 2 ≤ c.length := (Finset.mem_filter.mp hcm).2
      have hne : c ≠ Composition.single n hn1 := by
        intro eq
        have := (Composition.eq_single_iff_length hn1).mp eq
        omega
      exact mem_compPartialSumTarget_iff.mpr ⟨Nat.zero_le _, lt_of_le_of_lt c.length_le hn2,
        fun i => by
          change c.blocksFun i < N+1
          have hblock : c.blocksFun i < n := (Composition.ne_single_iff (n := n) hn1).mp hne i
          omega⟩
    have htarget : (∑ x ∈ compPartialSumTarget 0 (N+2) (N+1), W x) =
        ∑ k ∈ Finset.range (N+2), nonlinear b k * t^k := by
      have h := comp_partialSum (ofScalars ℝ (nonlinear b)) (ofScalars ℝ w) (N+2) (N+1) 1
      simpa only [FormalMultilinearSeries.partialSum, ofScalars_apply_eq, one_pow, smul_eq_mul,
        mul_one, scalar_piece, W, t] using h.symm
    apply (le_div_iff₀ hb).mpr
    rw [mul_comm]
    change b 1 * (∑ i ∈ I, w i) ≤ _
    calc
      _ = ∑ n ∈ I, b 1 * w n := Finset.mul_sum _ _ _
      _ ≤ ∑ n ∈ I, ((if n = 1 then r else 0) + ∑ c ∈ multiBlocks n, W ⟨n,c⟩) :=
        Finset.sum_le_sum hpiece
      _ = r + ∑ x ∈ J, W x := by
        rw [Finset.sum_add_distrib]
        dsimp only [J]
        rw [Finset.sum_sigma']
        simp [I]
      _ ≤ r + ∑ x ∈ compPartialSumTarget 0 (N+2) (N+1), W x :=
        add_le_add_right (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hW i)) _
      _ ≤ r + ∑' n, |b (n+2)| := by
        rw [htarget]
        apply add_le_add_right
        exact (Finset.sum_le_sum fun k _ => mul_le_of_le_one_right (he k) (pow_le_one₀ ht ht1)).trans
          (sum_nonlinear_le b hs _)

theorem solution (b : ℕ → ℝ) (hb_even : ∀ m, Even m → b m = 0) (hb₁ : 0 < b 1)
    (hb_sum : Summable (fun m => |b m|)) (H : ℝ → ℝ)
    (hH : ∀ t : ℝ, |t| < 1 → H t = ∑' m, b m * t ^ m) (G : ℝ → ℝ)
    (hG : IsLocalInverseBranch H G) (γ : ℝ) (hγ : 0 < γ)
    (hgap : γ + ∑' m, |b (m+2)| < b 1) :
    (∃ R : ℝ, γ < R ∧ Summable (fun n => |taylorCoeff n G| * R^n)) ∧
      Summable (fun n => |taylorCoeff (n+1) G| * γ^(n+1)) ∧
      ∑' n, |taylorCoeff (n+1) G| * γ^(n+1) ≤ (γ + ∑' m, |b (m+2)|) / b 1 ∧
      (γ + ∑' m, |b (m+2)|) / b 1 < 1 := by
  let a (n : ℕ) := taylorCoeff n G
  let Δ := ∑' m, |b (m+2)|
  have hc := inverse_coefficients b hb_sum H hH G hG
  have hs : Summable (fun m => |b (m+2)|) := (summable_nat_add_iff 2).2 hb_sum
  have hmajor (r : ℝ) (hr : 0 ≤ r) (hg : r + Δ ≤ b 1) :
      Summable (fun n : ℕ => |a (n+1)| * r^(n+1)) ∧
        (∑' n : ℕ, |a (n+1)| * r^(n+1)) ≤ (r+Δ)/b 1 := by
    have hN (N : ℕ) : (∑ i ∈ Finset.range N, |a (i+1)| * r^(i+1)) ≤ (r+Δ)/b 1 := by
      simpa [Finset.sum_Ico_eq_sum_range, Nat.add_comm 1, a, Δ] using
        prefix_bound a b hc hb₁ hs r hr hg N
    have hw (n : ℕ) : 0 ≤ |a (n+1)| * r^(n+1) := mul_nonneg (abs_nonneg _) (pow_nonneg hr _)
    exact ⟨summable_of_sum_range_le hw hN, Real.tsum_le_of_sum_range_le hw hN⟩
  change γ + Δ < b 1 at hgap
  obtain ⟨R,hR,hR'⟩ := exists_between (show γ < b 1-Δ by linarith only [hgap])
  have hRsum := (hmajor R (hγ.trans hR).le (by linarith only [hR'])).1
  obtain ⟨hsγ, hM⟩ := hmajor γ hγ.le hgap.le
  exact ⟨⟨R,hR,(summable_nat_add_iff 1).1 hRsum⟩, hsγ, hM, (div_lt_one hb₁).mpr hgap⟩
