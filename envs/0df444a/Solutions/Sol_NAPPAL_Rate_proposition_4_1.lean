-- Prove2me | solution 1 for NAPPAL.Rate.proposition_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T23:37:01.081151+00:00
-- url     : https://prove2.me/submissions/29bfce47-6d84-443a-bfb3-c1a5aec64a18
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NAPPAL_Rate_Setting
import Theorems.Thm_NAPPAL_Rate_theorem_4_1
import Theorems.Thm_NAPPAL_Rate_lemma_4_3
open Filter Topology
open scoped InnerProductSpace

/-- If `b ≥ 0` is summable, then `k * min_{k/2 ≤ i < k} b i ≤ 2 ∑_{j} b (j + k/2)`. -/
lemma nappal_p41_min_le_tail (b : ℕ → ℝ) (hb0 : ∀ i, 0 ≤ b i) (hbs : Summable b) (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ i, k / 2 ≤ i ∧ i < k ∧ (k : ℝ) * b i ≤ 2 * ∑' j, b (j + k / 2) := by
  have hne : (Finset.Ico (k / 2) k).Nonempty := ⟨k / 2, by simp; omega⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.Ico (k / 2) k) b hne
  refine ⟨i, (Finset.mem_Ico.1 hi).1, (Finset.mem_Ico.1 hi).2, ?_⟩
  have hcard : ((Finset.Ico (k / 2) k).card : ℝ) * b i ≤ ∑ x ∈ Finset.Ico (k / 2) k, b x := by
    have := Finset.card_nsmul_le_sum (Finset.Ico (k / 2) k) b (b i) hmin
    simpa [nsmul_eq_mul] using this
  have hsum : ∑ x ∈ Finset.Ico (k / 2) k, b x ≤ ∑' j, b (j + k / 2) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hs : Summable (fun j => b (j + k / 2)) := (summable_nat_add_iff (k / 2)).2 hbs
    calc ∑ j ∈ Finset.range (k - k / 2), b (k / 2 + j)
        = ∑ j ∈ Finset.range (k - k / 2), b (j + k / 2) := by
          refine Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm]
      _ ≤ ∑' j, b (j + k / 2) := hs.sum_le_tsum _ (fun j _ => hb0 _)
  have hc : (Finset.Ico (k / 2) k).card = k - k / 2 := Nat.card_Ico _ _
  rw [hc] at hcard
  have hk2 : (k : ℝ) ≤ 2 * ((k - k / 2 : ℕ) : ℝ) := by
    have : k ≤ 2 * (k - k / 2) := by omega
    exact_mod_cast this
  have hbi := hb0 i
  nlinarith

theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : NAPPAL.KL.E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) :
    Tendsto
      (fun k : ℕ => ENNReal.ofReal (Real.sqrt k) *
        ⨅ j ∈ Finset.Icc 1 k, NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u j, v j, p j)))
      atTop (𝓝 0) := by
  obtain ⟨Λs, ⟨hbdd, -⟩, -, -, ⟨⟨c5, hc5pos, hc5⟩, -⟩, -⟩ :=
    NAPPAL.Rate.theorem_4_1 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun
  obtain ⟨hc4, hdec⟩ := NAPPAL.Rate.lemma_4_3 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun
  have hγ : 0 < γ := hrun.2.2.1.1
  set Lam := NAPPAL.KL.Lam P LG LH L0 γ u v p with hLam
  set c3 := NAPPAL.KL.c3 P LG LH γ with hc3def
  have hc3 : 0 < c3 := by
    simp only [hc3def, NAPPAL.KL.c3]
    refine lt_min (by norm_num) (lt_min hc4 ?_)
    positivity
  -- step lengths
  set a : ℕ → ℝ := fun i =>
    NAPPAL.KL.wdist (u i, v i, p i) (u (i + 1), v (i + 1), p (i + 1)) with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => Real.sqrt_nonneg _
  set b : ℕ → ℝ := fun i => a i ^ 2 with hb
  have hb0 : ∀ i, 0 ≤ b i := fun i => sq_nonneg _
  obtain ⟨L, hL⟩ := hbdd
  have hLk : ∀ k, 1 ≤ k → L ≤ Lam k := fun k hk => hL ⟨k, Set.mem_Ici.2 hk, rfl⟩
  -- telescoping
  have htel : ∀ N, c3 * ∑ i ∈ Finset.range N, b (i + 1) ≤ Lam 1 - Lam (N + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hdec (N + 1) (by omega)
      simp only [hb, ha]
      simp only [hb, ha] at ih
      linarith
  have hbs : Summable b := by
    refine summable_of_sum_range_le (c := b 0 + (Lam 1 - L) / c3) hb0 fun N => ?_
    cases N with
    | zero => simp; exact add_nonneg (hb0 0) (div_nonneg (by linarith [hLk 1 le_rfl]) hc3.le)
    | succ N =>
      rw [Finset.sum_range_succ']
      have h1 := htel N
      have h2 := hLk (N + 1) (by omega)
      have : ∑ i ∈ Finset.range N, b (i + 1) ≤ (Lam 1 - L) / c3 := by
        rw [le_div_iff₀ hc3]; linarith
      linarith
  -- tail sums
  set T : ℕ → ℝ := fun N => ∑' j, b (j + N) with hT
  have hT0 : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add b
  have hTk : Tendsto (fun k : ℕ => T (k / 2)) atTop (𝓝 0) :=
    hT0.comp (Nat.tendsto_div_const_atTop (by norm_num))
  have hg : Tendsto (fun k : ℕ => ENNReal.ofReal (c5 * Real.sqrt (2 * T (k / 2)))) atTop
      (𝓝 0) := by
    have : Tendsto (fun k : ℕ => c5 * Real.sqrt (2 * T (k / 2))) atTop (𝓝 (c5 * Real.sqrt (2 * 0))) :=
      (((hTk.const_mul 2).sqrt).const_mul c5)
    simpa using (ENNReal.tendsto_ofReal this)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨i, -, hik, hki⟩ := nappal_p41_min_le_tail b hb0 hbs k hk
  have hinf : (⨅ j ∈ Finset.Icc 1 k, NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u j, v j, p j)))
      ≤ ENNReal.ofReal (c5 * a i) := by
    refine (iInf₂_le (i + 1) (by simp; omega)).trans ?_
    exact hc5 i
  calc ENNReal.ofReal (Real.sqrt k) *
        ⨅ j ∈ Finset.Icc 1 k, NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u j, v j, p j))
      ≤ ENNReal.ofReal (Real.sqrt k) * ENNReal.ofReal (c5 * a i) := by gcongr
    _ = ENNReal.ofReal (c5 * Real.sqrt ((k : ℝ) * b i)) := by
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      congr 1
      rw [Real.sqrt_mul (Nat.cast_nonneg _), hb]
      simp only
      rw [Real.sqrt_sq (ha0 i)]
      ring
    _ ≤ ENNReal.ofReal (c5 * Real.sqrt (2 * T (k / 2))) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
