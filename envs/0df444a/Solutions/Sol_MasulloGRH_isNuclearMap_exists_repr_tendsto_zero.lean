-- Prove2me | solution 1 for MasulloGRH.isNuclearMap_exists_repr_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T17:07:12.948417+00:00
-- url     : https://prove2.me/submissions/bfbc4bca-7ac0-4b37-8839-fa858de07673

import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_NuclearMap

open Filter Topology MasulloGRH

set_option autoImplicit false

private theorem existsNullScales (a : ℕ → ℝ) (ha : Summable a)
    (ha₀ : ∀ n, 0 ≤ a n) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ (∀ n, r n ≤ 1) ∧
      Tendsto r atTop (𝓝 0) ∧ Summable (fun n => a n / r n ^ 2) := by
  let b : ℕ → ℝ := fun n => a n + (1 / 2 : ℝ) ^ n
  have hb : Summable b := ha.add (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hbPos (n : ℕ) : 0 < b n :=
    add_pos_of_nonneg_of_pos (ha₀ n) (pow_pos (by norm_num) _)
  let tail : ℕ → ℝ := fun n => ∑' k, b (k + n)
  have hTailSummable (n : ℕ) : Summable (fun k => b (k + n)) :=
    (summable_nat_add_iff n).2 hb
  have hStep (n : ℕ) : tail n = b n + tail (n + 1) := by
    change (∑' k, b (k + n)) = _
    rw [(hTailSummable n).tsum_eq_zero_add, zero_add]
    congr 1
    exact tsum_congr fun k => by congr 1; omega
  have hTailPos (n : ℕ) : 0 < tail n := by
    rw [hStep]
    exact add_pos_of_pos_of_nonneg (hbPos n) (tsum_nonneg fun k => (hbPos (k + (n + 1))).le)
  let u : ℕ → ℝ := fun n => Real.sqrt (tail n)
  have hu (n : ℕ) : 0 < u n := Real.sqrt_pos_of_pos (hTailPos n)
  have huSq (n : ℕ) : u n ^ 2 = tail n := Real.sq_sqrt (hTailPos n).le
  have huLim : Tendsto u atTop (𝓝 0) := by
    simpa [u, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0).comp (tendsto_sum_nat_add b)
  have hDiff (n : ℕ) : b n / u n ≤ 2 * (u n - u (n + 1)) := by
    rw [div_le_iff₀ (hu n)]
    nlinarith only [sq_nonneg (u n - u (n + 1)), huSq n, huSq (n + 1), hStep n]
  have hSum : Summable (fun n => b n / u n) := by
    refine summable_of_sum_range_le (c := 2 * u 0)
      (fun n => div_nonneg (hbPos n).le (hu n).le) fun N => ?_
    calc
      _ ≤ ∑ n ∈ Finset.range N, 2 * (u n - u (n + 1)) :=
        Finset.sum_le_sum fun n _ => hDiff n
      _ = 2 * (u 0 - u N) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
      _ ≤ 2 * u 0 := by linarith [(hu N).le]
  let r : ℕ → ℝ := fun n => Real.sqrt (u n / (1 + u n))
  have hrPos (n : ℕ) : 0 < r n := Real.sqrt_pos_of_pos (div_pos (hu n) (by linarith [hu n]))
  have hrSq (n : ℕ) : r n ^ 2 = u n / (1 + u n) :=
    Real.sq_sqrt (div_nonneg (hu n).le (by linarith [hu n]))
  have hrLe (n : ℕ) : r n ≤ 1 := by
    apply Real.sqrt_le_one.2
    exact (div_le_one (by linarith [hu n])).2 (by linarith)
  have hrLim : Tendsto r atTop (𝓝 0) := by
    have hRatio := huLim.div (tendsto_const_nhds.add huLim) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simpa [r, Function.comp_def] using
      (Real.continuous_sqrt.tendsto (0 / (1 + 0))).comp hRatio
  refine ⟨r, hrPos, hrLe, hrLim, ?_⟩
  refine (hb.add hSum).of_nonneg_of_le (fun n => div_nonneg (ha₀ n) (sq_nonneg _)) fun n => ?_
  calc
    a n / r n ^ 2 ≤ b n / r n ^ 2 :=
      div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n)) (sq_nonneg _)
    _ = b n + b n / u n := by
      rw [hrSq]
      field_simp [(hu n).ne', show (1 + u n) ≠ 0 by linarith [hu n]]
      ring

theorem solution {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (_hE : IsHLCS E) (_hF : IsHLCS F) (T : E →L[ℂ] F) (hT : IsNuclearMap T) :
    ∃ (c : ℕ → ℂ) (φ : ℕ → StrongDual ℂ E) (y : ℕ → F) (U : Set E) (B : Set F),
      IsNuclearRepr T c φ y ∧
      U ∈ 𝓝 (0 : E) ∧
      TendstoUniformlyOn (fun (n : ℕ) (x : E) => φ n x) (fun _ => (0 : ℂ)) atTop U ∧
      IsBanachDisc B ∧ (∀ n, y n ∈ B) ∧
      Tendsto (fun n => gauge B (y n)) atTop (𝓝 0) ∧
      Tendsto y atTop (𝓝 0) := by
  obtain ⟨c, φ, y, hc, hφ, ⟨B, hB, hy⟩, hTsum⟩ := hT
  obtain ⟨r, hrPos, hrLe, hrLim, hrSum⟩ :=
    existsNullScales (fun n => ‖c n‖) hc (fun n => norm_nonneg _)
  let s : ℕ → ℂ := fun n => (r n : ℂ)
  have hsNorm (n : ℕ) : ‖s n‖ = r n := by simp [s, abs_of_pos (hrPos n)]
  have hsNe (n : ℕ) : s n ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [hsNorm]; exact (hrPos n).ne')
  let c' : ℕ → ℂ := fun n => c n / s n ^ 2
  let φ' : ℕ → StrongDual ℂ E := fun n => s n • φ n
  let y' : ℕ → F := fun n => s n • y n
  let U : Set E := {x | ∀ n, ‖φ n x‖ < 1}
  have hU : U ∈ 𝓝 (0 : E) := by
    have h := (Metric.equicontinuousAt_iff_right.mp (hφ 0)) 1 one_pos
    exact h.mono fun x hx n => by simpa [dist_comm, dist_eq_norm] using hx n
  have hφ' : Equicontinuous (fun n x => φ' n x) := by
    intro x
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [(Metric.equicontinuousAt_iff_right.mp (hφ x)) ε hε] with z hz n
    change dist (s n * φ n x) (s n * φ n z) < ε
    rw [dist_eq_norm, ← mul_sub, norm_mul, hsNorm]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hrLe n)).trans_lt
      (by simpa only [dist_eq_norm] using hz n)
  have hy' (n : ℕ) : y' n ∈ B := by
    have hLe : ‖s n‖ ≤ 1 := by rw [hsNorm]; exact hrLe n
    exact hB.2.2.1 (s n) hLe (Set.smul_mem_smul_set (hy n))
  refine ⟨c', φ', y', U, B, ⟨?_, hφ', ⟨B, hB, hy'⟩, ?_⟩, hU, ?_, hB, hy', ?_, ?_⟩
  · simpa [c', norm_div, norm_pow, hsNorm] using hrSum
  · intro x
    convert hTsum x using 1
    funext n
    change (c n / s n ^ 2 * (s n * φ n x)) • (s n • y n) = (c n * φ n x) • y n
    rw [smul_smul]
    congr 1
    field_simp [hsNe n]
  · refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    filter_upwards [hrLim (Iio_mem_nhds hε)] with n hn x hx
    change dist 0 (s n * φ n x) < ε
    rw [dist_zero_left, norm_mul, hsNorm]
    exact (mul_le_of_le_one_right (hrPos n).le (hx n).le).trans_lt hn
  · refine squeeze_zero (fun n => gauge_nonneg _) (fun n => ?_) hrLim
    change gauge B (s n • y n) ≤ r n
    rw [gauge_smul hB.2.2.1, hsNorm]
    exact mul_le_of_le_one_right (hrPos n).le (gauge_le_one_of_mem (hy n))
  · have hsLim : Tendsto s atTop (𝓝 0) := by
      simpa [s, Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hrLim
    exact hB.2.1.smul_tendsto_zero (Eventually.of_forall hy) hsLim
