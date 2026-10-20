-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.uniform_radius_approx_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:55:49.544586+00:00
-- url     : https://prove2.me/submissions/08376358-ef7f-4d66-961d-e4f9b488a5d4

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
universe uM
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]
section h50bdtv
open WeakSequences
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

theorem h50_spec {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) :
    ∀ j, j ≠ activeIndex hd x → h j x = 0 := (hd.exists_index x).choose_spec

theorem h50_dm_apply {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) (i : ℕ) :
    disjointMap hd x i = h i x := by
  unfold disjointMap
  rw [lp.single_apply]
  by_cases hi : i = activeIndex hd x
  · rw [hi, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hi, h50_spec hd x i hi]

theorem h50_dm_lip {h : ℕ → M → ℝ} (hd : DisjointTests h) {K : ℝ≥0}
    (hh : ∀ i, LipschitzWith K (h i)) : LipschitzWith (2 * K) (disjointMap hd) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have ex : disjointMap hd x = lp.single 1 (activeIndex hd x) (h (activeIndex hd x) x) := rfl
  have ey : disjointMap hd y = lp.single 1 (activeIndex hd y) (h (activeIndex hd y) y) := rfl
  have sx0 := h50_spec hd x
  have sy0 := h50_spec hd y
  generalize activeIndex hd x = i at ex sx0
  generalize activeIndex hd y = j at ey sy0
  rw [ex, ey]
  have hdecomp : lp.single 1 i (h i x) - lp.single (E := fun _ : ℕ => ℝ) 1 j (h j y) =
      lp.single 1 i (h i x - h i y) + (lp.single 1 i (h i y) - lp.single (E := fun _ : ℕ => ℝ) 1 j (h j y)) := by
    rw [lp.single_sub]; abel
  rw [hdecomp]
  have hp : (0:ℝ≥0∞) < 1 := by norm_num
  have t1 : ‖lp.single (E := fun _ : ℕ => ℝ) 1 i (h i x - h i y)‖ ≤ K * dist x y := by
    rw [lp.norm_single hp, ← dist_eq_norm]; exact (hh i).dist_le_mul x y
  have t2 : ‖lp.single (E := fun _ : ℕ => ℝ) 1 i (h i y) - lp.single (E := fun _ : ℕ => ℝ) 1 j (h j y)‖ ≤ K * dist x y := by
    by_cases hij : i = j
    · subst hij; rw [sub_self, norm_zero]; positivity
    · rw [sy0 i hij, lp.single_zero, zero_sub, norm_neg, lp.norm_single hp]
      have e : h j y = h j y - h j x := by rw [sx0 j (Ne.symm hij), sub_zero]
      rw [e, ← dist_eq_norm, dist_comm x y]
      exact (hh j).dist_le_mul y x
  have t3 := norm_add_le (lp.single (E := fun _ : ℕ => ℝ) 1 i (h i x - h i y))
    (lp.single (E := fun _ : ℕ => ℝ) 1 i (h i y) - lp.single (E := fun _ : ℕ => ℝ) 1 j (h j y))
  push_cast
  linarith

theorem h50b_coord {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) (μ : FreeSpace.Space M) (i : ℕ) :
    disjointOperator hd μ i = test (normalized (h i) (hh i)) μ := by
  have hD : LipschitzWith (2*K) (fun x => disjointMap hd x - disjointMap hd 0) :=
    lipschitz_sub_const _ (h50_dm_lip hd hh) _
  have h0 : (fun x => disjointMap hd x - disjointMap hd 0) 0 = 0 := sub_self _
  have key : (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 i).comp (disjointOperator hd) =
      test (normalized (h i) (hh i)) := by
    have hdn := FreeSpace.dense_combinations (M := M)
    apply DFunLike.coe_injective
    refine hdn.equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
      (funext fun a => ?_)
    simp only [Function.comp_apply]
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single x r =>
      simp only [Finsupp.linearCombination_single, map_smul]
      congr 1
      change (disjointOperator hd (FreeSpace.point x)) i =
        test (normalized (h i) (hh i)) (FreeSpace.point x)
      rw [disjointOperator, FreeSpace.linearize_point _ hD h0, test_point]
      change (disjointMap hd x - disjointMap hd 0) i = h i x - h i 0
      rw [lp.coeFn_sub, Pi.sub_apply, h50_dm_apply, h50_dm_apply]
  exact congrArg (fun T => T μ) key

theorem h50b_dtv {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakCauchy μ) :
    Tendsto (fun i => test (normalized (h i) (hh i)) (μ i)) atTop (𝓝 0) := by
  set T := disjointOperator hd with hT
  have hwc : WeakCauchy (fun i => T (μ i)) := fun f => hw (f.comp T)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (h50_schur_cauchy hwc)
  have hxi : Tendsto (fun i => x i) atTop (𝓝 0) := by
    have := (summable_norm x).tendsto_atTop_zero
    rw [tendsto_zero_iff_abs_tendsto_zero]; exact this
  have hdiff : Tendsto (fun i => ‖T (μ i) - x‖) atTop (𝓝 0) := by
    rw [← tendsto_iff_norm_sub_tendsto_zero]; exact hx
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun i => abs_nonneg _) (g := fun i => ‖T (μ i) - x‖ + |x i|)
  · intro i
    rw [← h50b_coord hd hh]
    have h1 : |(T (μ i) - x) i| ≤ ‖T (μ i) - x‖ := by
      have := lp.norm_apply_le_norm (by norm_num : (1:ℝ≥0∞) ≠ 0) (T (μ i) - x) i
      rwa [Real.norm_eq_abs] at this
    have h2 : (T (μ i) - x) i = T (μ i) i - x i := rfl
    rw [h2] at h1
    calc |T (μ i) i| = |(T (μ i) i - x i) + x i| := by ring_nf
      _ ≤ |T (μ i) i - x i| + |x i| := abs_add_le _ _
      _ ≤ _ := by linarith
  · have h3 : Tendsto (fun i => |x i|) atTop (𝓝 0) := by
      exact (tendsto_zero_iff_abs_tendsto_zero _).mp hxi
    simpa using hdiff.add h3

end h50bdtv
theorem h50b_test_sub (a b : LipZero M) (μ : Space M) :
    LocalizedLinearization.test a μ - LocalizedLinearization.test b μ =
      LocalizedLinearization.test (a - b) μ := by
  change μ.1 a - μ.1 b = μ.1 (a - b)
  rw [map_sub]

theorem h50b_abs_test_le (a : LipZero M) {K : ℝ≥0} (ha : LipschitzWith K a.1) (μ : Space M) :
    |LocalizedLinearization.test a μ| ≤ K * ‖μ‖ := by
  have h1 : |LocalizedLinearization.test a μ| ≤ ‖a‖ * ‖μ‖ := by
    change |μ.1 a| ≤ ‖a‖ * ‖μ‖
    have := μ.1.le_opNorm a
    rw [Real.norm_eq_abs] at this
    calc |μ.1 a| ≤ ‖μ.1‖ * ‖a‖ := this
      _ = ‖a‖ * ‖μ‖ := by rw [mul_comm]; rfl
  exact h1.trans (mul_le_mul_of_nonneg_right (norm_le_of_lipschitz a ha) (norm_nonneg _))

theorem h50b_test_vanish {K : Set M} (a : LipZero M) (ha : ∀ x ∈ K, a.1 x = 0) {μ : Space M}
    (hμ : μ ∈ supported K) : LocalizedLinearization.test a μ = 0 := by
  have hle : supported K ≤ LinearMap.ker (LocalizedLinearization.test a).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [LocalizedLinearization.test_point]
      exact ha x hx
    · exact (LocalizedLinearization.test a).isClosed_ker
  exact hle hμ

theorem h50b_normalized_lip (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (LocalizedLinearization.normalized f hf).1 :=
  LocalizedLinearization.lipschitz_sub_const f hf (f 0)
theorem h50b_supported_mono {K L : Set M} (h : K ⊆ L) : supported K ≤ supported L :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono h))

theorem h50b_approx_ball (μ : Space M) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, Approximable μ (Metric.closedBall 0 R) ε := by
  classical
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp dense_combinations μ ε hε
  obtain ⟨R, hR⟩ := (a.support.finite_toSet.isBounded).subset_closedBall (0 : M)
  refine ⟨R, Finsupp.linearCombination ℝ point a, ?_, ?_⟩
  · apply Submodule.le_topologicalClosure
    rw [Finsupp.mem_span_image_iff_linearCombination]
    exact ⟨a, (Finsupp.mem_supported ℝ a).mpr hR, rfl⟩
  · rw [← dist_eq_norm]; exact ha

theorem h50b_approx_mono {μ : Space M} {K L : Set M} {ε : ℝ} (h : K ⊆ L)
    (hK : Approximable μ K ε) : Approximable μ L ε := by
  obtain ⟨ν, hν, hd⟩ := hK
  exact ⟨ν, h50b_supported_mono h hν, hd⟩
theorem h50b_clm_ext (S T : Space M →L[ℝ] ℝ) (h : ∀ x, S (point x) = T (point x)) : S = T := by
  have hlin : S.toLinearMap ∘ₗ Finsupp.linearCombination ℝ point =
      T.toLinearMap ∘ₗ Finsupp.linearCombination ℝ point := by
    apply Finsupp.lhom_ext
    intro x c
    simp [h x]
  have := dense_combinations.equalizer S.continuous T.continuous (by
    funext a
    exact LinearMap.congr_fun hlin a)
  exact ContinuousLinearMap.coe_injective (by
    ext μ
    exact congrFun this μ)

theorem h50b_vanishing (K : Set M) (μ : Space M) {ε : ℝ}
    (hfar : ∀ ν : Space M, ν ∈ supported K → ε ≤ ‖μ-ν‖) :
    ∃ f : M → ℝ, LipschitzWith 1 f ∧ f 0 = 0 ∧ (∀ x ∈ K, f x = 0) ∧
      ∀ hf : LipschitzWith 1 f, ε ≤ LocalizedLinearization.test (LocalizedLinearization.normalized f hf) μ := by
  by_cases hε : ε ≤ 0
  · refine ⟨fun _ => 0, (LipschitzWith.const 0).weaken (zero_le_one), rfl, fun _ _ => rfl, fun hf => ?_⟩
    have : LocalizedLinearization.test (LocalizedLinearization.normalized (fun _ : M => (0:ℝ)) hf) μ = 0 := by
      change μ.1 _ = 0
      have : LocalizedLinearization.normalized (fun _ : M => (0:ℝ)) hf = 0 := by
        apply Subtype.ext; funext x; change (0:ℝ) - 0 = 0; ring
      rw [this, map_zero]
    rw [this]; exact hε
  push Not at hε
  set W := supported K with hW
  have : IsClosed (W : Set (Space M)) := Submodule.isClosed_topologicalClosure _
  set q : Space M ⧸ W := Submodule.Quotient.mk μ with hq
  have hqnorm : ε ≤ ‖q‖ := by
    apply le_of_forall_pos_lt_add
    intro δ hδ
    obtain ⟨m, hm, hmn⟩ := Submodule.Quotient.norm_mk_lt q hδ
    have hmem : μ - m ∈ W := by
      have := (Submodule.Quotient.eq W).mp (hm.trans hq)
      rw [← neg_mem_iff, neg_sub]; exact this
    have := hfar _ hmem
    rw [sub_sub_cancel] at this
    linarith
  have hq0 : ‖q‖ ≠ 0 := by
    intro h0; rw [h0] at hqnorm; linarith
  obtain ⟨g, hg1, hgq⟩ := exists_dual_vector ℝ q hq0
  set T : Space M →L[ℝ] ℝ := g.comp W.mkQL with hT
  have hTn : ‖T‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    calc ‖T x‖ = ‖g (W.mkQL x)‖ := rfl
      _ ≤ ‖g‖ * ‖W.mkQL x‖ := g.le_opNorm _
      _ ≤ 1 * ‖x‖ := by rw [hg1]; exact mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le W x) zero_le_one
  have hlip : LipschitzWith 1 (fun x => T (point x)) := (dual_point_lipschitz T).weaken hTn
  refine ⟨fun x => T (point x), hlip, by simp, ?_, fun hf => ?_⟩
  · intro x hx
    change g (W.mkQL (point x)) = 0
    have : W.mkQL (point x) = 0 := by
      change Submodule.Quotient.mk (point x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x, hx, rfl⟩)
    rw [this, map_zero]
  · have : LocalizedLinearization.test (LocalizedLinearization.normalized _ hf) = T := by
      apply h50b_clm_ext
      intro x
      rw [LocalizedLinearization.test_point]
      change T (point x) - T (point 0) = T (point x)
      simp
    rw [this]
    change ε ≤ g q
    rw [hgq]; exact hqnorm

theorem h50b_pairing_diff {K : Set M} (h0 : (0 : M) ∈ K)
    (f g : M → ℝ) {C D : ℝ≥0} (hf : LipschitzWith C f) (hg : LipschitzWith D g)
    (he : ∀ x ∈ K, f x = g x) (μ ν : Space M) (hν : ν ∈ supported K) :
    |LocalizedLinearization.test (LocalizedLinearization.normalized f hf) μ -
      LocalizedLinearization.test (LocalizedLinearization.normalized g hg) μ| ≤ (C+D)*‖μ-ν‖ := by
  set a := LocalizedLinearization.normalized f hf - LocalizedLinearization.normalized g hg with ha
  have hvan : ∀ x ∈ K, a.1 x = 0 := by
    intro x hx
    change (f x - f 0) - (g x - g 0) = 0
    rw [he x hx, he 0 h0]; ring
  have hlip : LipschitzWith (C + D) a.1 :=
    (h50b_normalized_lip f hf).sub (h50b_normalized_lip g hg)
  have h1 := h50b_test_vanish a hvan hν
  rw [h50b_test_sub, ← ha]
  have : LocalizedLinearization.test a μ = LocalizedLinearization.test a (μ - ν) := by
    rw [map_sub, h1, sub_zero]
  rw [this]
  have := h50b_abs_test_le a hlip (μ - ν)
  simpa using this

theorem h50b_cutoff_one {S : ℝ} (hS : 0 < S) {sN : ℝ≥0} (hsN : (sN : ℝ) = 2 * S) {x : M}
    (hx : dist x 0 ≤ S) : LocalizedLinearization.cutoff (0 : M) sN x = 1 := by
  unfold LocalizedLinearization.cutoff
  have : 1 ≤ 2 - 2 / (sN : ℝ) * dist x 0 := by
    rw [hsN]
    have : 2 / (2 * S) * dist x 0 ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]; linarith
    linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem h50b_radius_escape {μ : ℕ → Space M} {ε : ℝ} (hε : 0 < ε)
    (hfail : ∀ R : ℝ, 0 < R → ∃ i, ¬ Approximable (μ i) (Metric.closedBall 0 R) ε)
    (p : ℕ) (r : ℝ) : ∃ i : ℕ, ∃ s : ℝ, ∃ g : M → ℝ,
      p < i ∧ r < s ∧ LipschitzWith 3 g ∧ g 0 = 0 ∧
      (∀ x, dist x 0 ≤ r → g x = 0) ∧ (∀ x, s ≤ dist x 0 → g x = 0) ∧
      ∀ hg : LipschitzWith 3 g, ε/2 < |test (normalized g hg) (μ i)| := by
  choose Ri hRi using fun i => h50b_approx_ball (μ i) hε
  set R := |r| + 1 + ∑ i ∈ Finset.range (p+1), |Ri i| with hRdef
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (p+1), |Ri i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hRpos : 0 < R := by linarith [abs_nonneg r]
  have hrR : r ≤ R := by linarith [le_abs_self r]
  obtain ⟨i, hi⟩ := hfail R hRpos
  have hpi : p < i := by
    by_contra hle
    push Not at hle
    apply hi
    apply h50b_approx_mono _ (hRi i)
    apply Metric.closedBall_subset_closedBall
    have h1 : |Ri i| ≤ ∑ j ∈ Finset.range (p+1), |Ri j| :=
      Finset.single_le_sum (f := fun j => |Ri j|) (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
    linarith [le_abs_self (Ri i), abs_nonneg r]
  have hfar : ∀ ν : Space M, ν ∈ supported (Metric.closedBall 0 R) → ε ≤ ‖μ i - ν‖ := by
    intro ν hν
    by_contra hlt
    push Not at hlt
    exact hi ⟨ν, hν, hlt⟩
  obtain ⟨f, hf1, hf0, hfK, hftest⟩ := h50b_vanishing _ (μ i) hfar
  obtain ⟨R', ν, hν, hνd⟩ := h50b_approx_ball (μ i) (show 0 < ε / 16 by positivity)
  set S := |R'| + |r| + 1 with hSdef
  have hSpos : 0 < S := by positivity
  set sN : ℝ≥0 := ⟨2 * S, by positivity⟩ with hsNdef
  have hsN : (sN : ℝ) = 2 * S := rfl
  have hsNpos : 0 < sN := by rw [← NNReal.coe_pos, hsN]; positivity
  set g : M → ℝ := fun x => f x * LocalizedLinearization.cutoff (0 : M) sN x with hgdef
  have hglip : LipschitzWith 3 g := by
    have := LocalizedLinearization.cutoff_product_lipschitz (0 : M) hsNpos f hf1 hf0
    simpa using this
  refine ⟨i, 2 * S, g, hpi, by linarith [le_abs_self r, abs_nonneg R'], hglip, by simp [hgdef, hf0], ?_, ?_, ?_⟩
  · intro x hx
    simp only [hgdef]
    rw [hfK x (Metric.mem_closedBall.mpr (le_trans hx hrR)), zero_mul]
  · intro x hx
    simp only [hgdef]
    rw [LocalizedLinearization.cutoff_zero (0 : M) hsNpos (by rw [hsN]; exact hx), mul_zero]
  · intro hg
    have heq : ∀ x ∈ Metric.closedBall (0 : M) S, f x = g x := by
      intro x hx
      simp only [hgdef]
      rw [h50b_cutoff_one hSpos hsN (Metric.mem_closedBall.mp hx), mul_one]
    have hν' : ν ∈ supported (Metric.closedBall (0 : M) S) :=
      h50b_supported_mono (Metric.closedBall_subset_closedBall (by linarith [le_abs_self R', abs_nonneg r])) hν
    have hd := h50b_pairing_diff (Metric.mem_closedBall_self hSpos.le) f g hf1 hg heq (μ i) ν hν'
    have h1 := hftest hf1
    have h2 := abs_le.mp hd
    push_cast at h2
    rw [lt_abs]
    left
    nlinarith

theorem solution {μ : ℕ → Space M} (hw : WeakSequences.WeakCauchy μ)
    {ε : ℝ} (hε : 0 < ε) : ∃ R : ℝ, 0 < R ∧
      ∀ i, Approximable (μ i) (Metric.closedBall 0 R) ε := by
  by_contra hne
  push Not at hne
  choose I S G hIp hrS hGl hG0 hGin hGout hGtest using h50b_radius_escape hε hne
  let st : ℕ → ℕ × ℝ := fun k => Nat.rec (0, 0) (fun _ q => (I q.1 q.2, S q.1 q.2)) k
  have st_succ : ∀ k, st (k+1) = (I (st k).1 (st k).2, S (st k).1 (st k).2) := fun k => rfl
  let idx : ℕ → ℕ := fun k => I (st k).1 (st k).2
  let h : ℕ → M → ℝ := fun k => G (st k).1 (st k).2
  have hh : ∀ k, LipschitzWith 3 (h k) := fun k => hGl _ _
  have hidx : StrictMono idx := by
    apply strictMono_nat_of_lt_succ
    intro k
    have := hIp (st (k+1)).1 (st (k+1)).2
    simp only [idx, st_succ] at this ⊢
    exact this
  have hrr : StrictMono (fun k => (st k).2) := by
    apply strictMono_nat_of_lt_succ
    intro k
    simp only [st_succ]
    exact hrS _ _
  have hd : LocalizedLinearization.DisjointTests h := by
    have key : ∀ i j, i < j → ∀ x, h i x ≠ 0 → h j x ≠ 0 → False := by
      intro i j hij x hi hj
      have h1 : dist x 0 < S (st i).1 (st i).2 := by
        by_contra hc; push Not at hc; exact hi (hGout _ _ x hc)
      have h2 : (st j).2 < dist x 0 := by
        by_contra hc; push Not at hc; exact hj (hGin _ _ x hc)
      have h3 : (st (i+1)).2 ≤ (st j).2 := hrr.monotone (show i + 1 ≤ j by omega)
      rw [st_succ] at h3
      simp only at h3
      linarith
    intro x i j hi hj
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (key i j hij x hi hj).elim
    · exact hij
    · exact (key j i hij x hj hi).elim
  have hwc : WeakSequences.WeakCauchy (fun k => μ (idx k)) := by
    intro f
    exact (hw f).comp_tendsto hidx.tendsto_atTop
  have hlim := h50b_dtv hd hh hwc
  have hev := (hlim.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / 2 by positivity))).exists
  obtain ⟨k, hk⟩ := hev
  have := hGtest (st k).1 (st k).2 (hh k)
  rw [Real.dist_eq, sub_zero] at hk
  exact absurd hk (not_lt.mpr this.le)

