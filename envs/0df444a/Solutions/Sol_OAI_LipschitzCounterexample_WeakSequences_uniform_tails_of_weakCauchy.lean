-- Prove2me | solution 1 for OAI.LipschitzCounterexample.WeakSequences.uniform_tails_of_weakCauchy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:57:18.45514+00:00
-- url     : https://prove2.me/submissions/4eb20b38-8973-4591-8faf-b8d54e967e10

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
universe uE uF uG
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
theorem h50_tailR (x : RealL1) : Tendsto (fun K => ‖x - trunc K x‖) atTop (𝓝 0) := by
  have heq : ∀ K, ‖x - trunc K x‖ = ∑' i, |x (i + K)| := by
    intro K
    rw [WeightedGraph.norm_l1]
    simp only [Real.norm_eq_abs]
    rw [← (summable_norm (x - trunc K x)).sum_add_tsum_nat_add K]
    rw [Finset.sum_eq_zero (fun i hi => by
      simp only [Finset.mem_range] at hi
      simp [lp.coeFn_sub, trunc_apply, hi]), zero_add]
    congr 1
    funext i
    simp [lp.coeFn_sub, trunc_apply]
  simp_rw [heq]
  exact tendsto_sum_nat_add (fun i => |x i|)

theorem h50_headR {u : ℕ → RealL1} (hu : WeakNull u) (N : ℕ) :
    Tendsto (fun n => trunc N (u n)) atTop (𝓝 0) := by
  have hc : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 0) :=
    fun i => hu (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 i)
  simp_rw [trunc_eq_sum]
  have h0 : (0 : RealL1) = ∑ i ∈ Finset.range N,
      lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 1 i 0 := by simp
  rw [h0]
  apply tendsto_finsetSum
  intro i _
  exact ((lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 1 i).continuous.tendsto 0).comp (hc i)

theorem h50_schur {u : ℕ → RealL1} (hu : WeakNull u) : Tendsto u atTop (𝓝 0) := by
  by_contra hne
  obtain ⟨ε, hε, hfreq⟩ : ∃ ε > 0, ∀ M, ∃ n ≥ M, ε ≤ ‖u n‖ := by
    rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop] at hne
    push Not at hne
    obtain ⟨ε, hε, h⟩ := hne
    refine ⟨ε, hε, fun M => ?_⟩
    obtain ⟨n, hn, h2⟩ := h M
    exact ⟨n, hn, by simpa using h2⟩
  have step : ∀ a : ℕ, ∃ n ≥ a, ∃ a' > a, ‖trunc a (u n)‖ < ε/8 ∧
      ‖u n - trunc a' (u n)‖ < ε/8 ∧ ε ≤ ‖u n‖ := by
    intro a
    have h1 := (h50_headR hu a).norm
    rw [norm_zero] at h1
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      (h1.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε/8)))
    obtain ⟨n, hn, hbig⟩ := hfreq (max M a)
    obtain ⟨a', ha'⟩ := eventually_atTop.mp
      ((h50_tailR (u n)).eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε/8)))
    exact ⟨n, le_of_max_le_right hn, max a' (a+1), by omega, hM n (le_of_max_le_left hn),
      ha' _ (le_max_left _ _), hbig⟩
  choose nf hnf af haf hhead htail hbig using step
  let N : ℕ → ℕ := fun j => af^[j] 0
  have hNs : ∀ j, N (j+1) = af (N j) := fun j => Function.iterate_succ_apply' af j 0
  have hmono : StrictMono N := strictMono_nat_of_lt_succ (fun j => by rw [hNs]; exact haf _)
  have hex : ∀ i, ∃ j, i < N (j+1) :=
    fun i => ⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (hmono.id_le _)⟩
  classical
  let J : ℕ → ℕ := fun i => Nat.find (hex i)
  have hJ : ∀ j i, N j ≤ i → i < N (j+1) → J i = j := by
    intro j i h1 h2
    show Nat.find (hex i) = j
    rw [Nat.find_eq_iff]
    refine ⟨h2, fun k hk hlt => ?_⟩
    have := hmono.monotone (show k+1 ≤ j by omega)
    omega
  let b : ℕ → ℝ := fun i => if 0 ≤ u (nf (N (J i))) i then 1 else -1
  have hb : ∀ i, |b i| ≤ 1 := fun i => by simp only [b]; split_ifs <;> simp
  have hf := hu (pairing b hb)
  have hnorm : ‖pairing b hb‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hlim : Tendsto (fun j => pairing b hb (u (nf (N j)))) atTop (𝓝 0) :=
    hf.comp (tendsto_atTop_mono (fun j => (hmono.id_le j).trans (hnf (N j))) tendsto_id)
  have hlow : ∀ j, ε/2 ≤ pairing b hb (u (nf (N j))) := by
    intro j
    have hh := hhead (N j)
    have ht := htail (N j)
    have hB := hbig (N j)
    rw [← hNs] at ht
    obtain ⟨x, hx⟩ : ∃ x, x = u (nf (N j)) := ⟨_, rfl⟩
    rw [← hx] at hh ht hB ⊢
    have hlt : N j < N (j+1) := hmono (Nat.lt_succ_self j)
    have hdec : x = trunc (N j) x + (trunc (N (j+1)) x - trunc (N j) x) +
        (x - trunc (N (j+1)) x) := by abel
    have hm : pairing b hb (trunc (N (j+1)) x - trunc (N j) x) =
        ‖trunc (N (j+1)) x - trunc (N j) x‖ := by
      rw [pairing_apply, WeightedGraph.norm_l1]
      congr 1
      funext i
      rw [lp.coeFn_sub, Pi.sub_apply, trunc_apply, trunc_apply, Real.norm_eq_abs]
      by_cases h1 : N j ≤ i
      · by_cases h2 : i < N (j+1)
        · have hJi : J i = j := hJ j i h1 h2
          have hbi : b i = if 0 ≤ x i then 1 else -1 := by simp only [b, hJi, ← hx]
          rw [hbi, if_pos h2, if_neg (show ¬ i < N j by omega)]
          split_ifs with h3
          · rw [sub_zero, one_mul, abs_of_nonneg h3]
          · rw [sub_zero, abs_of_neg (by linarith)]; ring
        · rw [if_neg h2, if_neg (by omega)]; simp
      · rw [if_pos (by omega), if_pos (by omega)]; simp
    have e1 := (pairing b hb).le_of_opNorm_le hnorm (trunc (N j) x)
    have e2 := (pairing b hb).le_of_opNorm_le hnorm (x - trunc (N (j+1)) x)
    have e3 := norm_add₃_le (a := trunc (N j) x) (b := trunc (N (j+1)) x - trunc (N j) x)
      (c := x - trunc (N (j+1)) x)
    rw [← hdec] at e3
    have hfx : pairing b hb x = pairing b hb (trunc (N j) x) +
        pairing b hb (trunc (N (j+1)) x - trunc (N j) x) +
        pairing b hb (x - trunc (N (j+1)) x) := by
      conv_lhs => rw [hdec]
      rw [map_add, map_add]
    rw [hfx, hm]
    rw [Real.norm_eq_abs, one_mul] at e1 e2
    have := abs_le.mp e1
    have := abs_le.mp e2
    linarith
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε/2))).exists
  linarith [hlow j]

theorem h50_schur_cauchy {u : ℕ → RealL1} (hu : WeakCauchy u) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  by_contra hne
  push Not at hne
  obtain ⟨ε, hε, h⟩ := hne
  choose m hm n hn hd using h
  have hw : WeakNull (fun k => u (m k) - u (n k)) := by
    intro f
    have hc := Metric.cauchySeq_iff.mp (hu f)
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨K, hK⟩ := hc δ hδ
    refine ⟨K, fun k hk => ?_⟩
    rw [map_sub, dist_zero_right, Real.norm_eq_abs, ← Real.dist_eq]
    exact hK _ (le_trans hk (hm k)) _ (le_trans hk (hn k))
  have hs := (h50_schur hw).norm
  rw [norm_zero] at hs
  obtain ⟨k, hk⟩ := (hs.eventually (gt_mem_nhds hε)).exists
  have := hd k
  rw [dist_eq_norm] at this
  linarith

theorem h50_tail_le (N : ℕ) (y : SumL1 G) : ‖tailL1 N y‖ ≤ ‖y‖ := by
  rw [sumL1_norm, sumL1_norm]
  apply Summable.tsum_le_tsum (fun i => ?_) (sumL1_summable (tailL1 N y)) (sumL1_summable y)
  rw [tailL1_apply]
  split_ifs <;> simp

theorem h50_tail_tendsto (y : SumL1 G) : Tendsto (fun N => ‖tailL1 N y‖) atTop (𝓝 0) := by
  have heq : ∀ N, ‖tailL1 N y‖ = ∑' i, ‖y (i + N)‖ := by
    intro N
    rw [sumL1_norm]
    rw [← (sumL1_summable (tailL1 N y)).sum_add_tsum_nat_add N]
    rw [Finset.sum_eq_zero (fun i hi => by
      rw [tailL1_apply, if_neg (by simp at hi; omega), norm_zero]), zero_add]
    congr 1
    funext i
    rw [tailL1_apply, if_pos (by omega)]
  simp_rw [heq]
  exact tendsto_sum_nat_add (fun i => ‖y i‖)

theorem h50_tail_mono {a b : ℕ} (hab : a ≤ b) (y : SumL1 G) : ‖tailL1 b y‖ ≤ ‖tailL1 a y‖ := by
  rw [sumL1_norm, sumL1_norm]
  apply Summable.tsum_le_tsum (fun i => ?_) (sumL1_summable _) (sumL1_summable _)
  rw [tailL1_apply, tailL1_apply]
  split_ifs with h1 h2 h2
  · exact le_refl _
  · exfalso; omega
  · simp
  · simp

theorem h50_unif_cauchy (u : ℕ → SumL1 G) (hu : CauchySeq u)
    (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ k, ‖tailL1 N (u k)‖ < ε := by
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.mp hu (ε/2) (half_pos hε)
  have hev : ∀ᶠ N in atTop, ∀ k ∈ Finset.range (M+1), ‖tailL1 N (u k)‖ < ε/2 := by
    rw [Filter.eventually_all_finset]
    intro k _
    exact (h50_tail_tendsto (u k)).eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨N, fun k => ?_⟩
  by_cases hk : k ≤ M
  · exact (hN k (Finset.mem_range.mpr (by omega))).trans (half_lt_self hε)
  · have h1 := hM k (by omega)
    rw [dist_eq_norm] at h1
    have h2 := hN M (Finset.mem_range.mpr (by omega))
    have h3 : tailL1 N (u k) = tailL1 N (u k - u M) + tailL1 N (u M) := by
      rw [map_sub]; abel
    rw [h3]
    calc _ ≤ ‖tailL1 N (u k - u M)‖ + ‖tailL1 N (u M)‖ := norm_add_le _ _
      _ ≤ ‖u k - u M‖ + ‖tailL1 N (u M)‖ := by gcongr; exact h50_tail_le _ _
      _ < ε/2 + ε/2 := add_lt_add h1 h2
      _ = ε := by ring

theorem h50_block (g : ∀ i, G i →L[ℝ] ℝ) (hg : ∀ i, ‖g i‖ ≤ 1) {a a' : ℕ} (haa : a ≤ a')
    (y : SumL1 G) (hblock : ∀ i, a ≤ i → i < a' → g i (y i) = ‖y i‖) :
    ‖tailL1 a y‖ - ‖tailL1 a' y‖ ≤
      ‖tailL1 (G := fun _ : ℕ => ℝ) a (coordinateTests g hg y)‖ := by
  rw [sumL1_norm, sumL1_norm, sumL1_norm]
  rw [← Summable.tsum_sub (sumL1_summable _) (sumL1_summable _)]
  apply Summable.tsum_le_tsum (fun i => ?_) ((sumL1_summable _).sub (sumL1_summable _))
    (sumL1_summable _)
  simp only [tailL1_apply, coordinateTests_apply]
  by_cases h1 : a ≤ i
  · by_cases h2 : a' ≤ i
    · simp [h1, h2]
    · simp [h1, h2, hblock i h1 (by omega)]
  · have h2 : ¬ a' ≤ i := by omega
    simp [h1, h2]

theorem solution (u : ℕ → SumL1 G) (hu : WeakCauchy u)
    (ε : ℝ) (hε : 0 < ε) : ∃ N, ∀ k, ‖tailL1 N (u k)‖ < ε := by
  by_contra hne
  push Not at hne
  have step : ∀ a : ℕ, ∃ k, ∃ a' > a, ε ≤ ‖tailL1 a (u k)‖ ∧ ‖tailL1 a' (u k)‖ < ε/4 := by
    intro a
    obtain ⟨k, hk⟩ := hne a
    obtain ⟨a', ha'⟩ := eventually_atTop.mp
      ((h50_tail_tendsto (u k)).eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε/4)))
    exact ⟨k, max a' (a+1), by omega, hk, ha' _ (le_max_left _ _)⟩
  choose kf af haf hbig hsmall using step
  let N : ℕ → ℕ := fun j => af^[j] 0
  have hNs : ∀ j, N (j+1) = af (N j) := fun j => Function.iterate_succ_apply' af j 0
  have hmono : StrictMono N := strictMono_nat_of_lt_succ (fun j => by rw [hNs]; exact haf _)
  have hex : ∀ i, ∃ j, i < N (j+1) :=
    fun i => ⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (hmono.id_le _)⟩
  classical
  let J : ℕ → ℕ := fun i => Nat.find (hex i)
  have hJ : ∀ j i, N j ≤ i → i < N (j+1) → J i = j := by
    intro j i h1 h2
    show Nat.find (hex i) = j
    rw [Nat.find_eq_iff]
    refine ⟨h2, fun k hk hlt => ?_⟩
    have := hmono.monotone (show k+1 ≤ j by omega)
    omega
  let g : ∀ i, G i →L[ℝ] ℝ := fun i =>
    (exists_dual_vector'' (𝕜 := ℝ) (u (kf (N (J i))) i)).choose
  have hg : ∀ i, ‖g i‖ ≤ 1 := fun i =>
    (exists_dual_vector'' (𝕜 := ℝ) (u (kf (N (J i))) i)).choose_spec.1
  have hgv : ∀ i, g i (u (kf (N (J i))) i) = ‖u (kf (N (J i))) i‖ := fun i =>
    (exists_dual_vector'' (𝕜 := ℝ) (u (kf (N (J i))) i)).choose_spec.2
  have hv : CauchySeq (fun k => coordinateTests g hg (u k)) :=
    h50_schur_cauchy (fun f => hu (f.comp (coordinateTests g hg)))
  obtain ⟨M, hM⟩ := h50_unif_cauchy (G := fun _ : ℕ => ℝ) _ hv (ε/4) (by positivity)
  have hNM : M ≤ N M := hmono.id_le M
  have hlow := h50_block g hg (le_of_lt (hmono (Nat.lt_succ_self M))) (u (kf (N M)))
    (fun i h1 h2 => by
      have := hgv i
      rw [hJ M i h1 h2] at this
      exact this)
  have h1 := hbig (N M)
  have h2 := hsmall (N M)
  rw [← hNs] at h2
  have h3 := h50_tail_mono (G := fun _ : ℕ => ℝ) hNM (coordinateTests g hg (u (kf (N M))))
  have h4 := hM (kf (N M))
  linarith

