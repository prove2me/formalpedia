-- Prove2me | solution 1 for KingmanSubadditive.Ergodic.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T02:42:41.747117+00:00
-- url     : https://prove2.me/submissions/6b3ab79e-b4cc-43a3-b591-4ae183cf92d9

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

-- BEGIN COMPLETE MODULE SubCocycle
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

/-- A pointwise cocycle inequality, with the irrelevant time-zero coordinate normalized. -/
structure SubCocycle (T : Ω → Ω) (g : ℕ → Ω → ℝ) : Prop where
  zero : g 0 = 0
  add_le : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)

namespace SubCocycle

variable {T : Ω → Ω} {g : ℕ → Ω → ℝ}

theorem le_sum_one (h : SubCocycle T g) (n : ℕ) (x : Ω) :
    g n x ≤ ∑ i ∈ Finset.range n, g 1 (T^[i] x) := by
  induction n with
  | zero => simp [h.zero]
  | succ n ih =>
    calc
      g (n + 1) x ≤ g n x + g 1 (T^[n] x) := h.add_le n 1 x
      _ ≤ (∑ i ∈ Finset.range n, g 1 (T^[i] x)) + g 1 (T^[n] x) := by linarith
      _ = _ := by rw [Finset.sum_range_succ]

def normalized (g : ℕ → Ω → ℝ) (T : Ω → Ω) (n : ℕ) (x : Ω) : ℝ :=
  g n x - ∑ i ∈ Finset.range n, g 1 (T^[i] x)

theorem normalized_nonpos (h : SubCocycle T g) (n : ℕ) (x : Ω) :
    normalized g T n x ≤ 0 := sub_nonpos.mpr (h.le_sum_one n x)

theorem normalized_subCocycle (h : SubCocycle T g) :
    SubCocycle T (normalized g T) := by
  constructor
  · funext x; simp [normalized, h.zero]
  · intro m n x
    have hh := h.add_le m n x
    simp only [normalized, Finset.sum_range_add]
    have he : (∑ i ∈ Finset.range n, g 1 (T^[m + i] x)) =
        ∑ i ∈ Finset.range n, g 1 (T^[i] (T^[m] x)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [add_comm m i, Function.iterate_add_apply]
    rw [he]
    linarith

def clipped (g : ℕ → Ω → ℝ) (M : ℝ) (n : ℕ) (x : Ω) : ℝ :=
  max (g n x) (-M * n)

theorem clipped_subCocycle (h : SubCocycle T g) (M : ℝ) :
    SubCocycle T (clipped g M) := by
  constructor
  · funext x; simp [clipped, h.zero]
  · intro m n x
    apply max_le
    · exact (h.add_le m n x).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
    · simp only [Nat.cast_add]
      calc
        -M * ((m : ℝ) + n) = -M * m + -M * n := by ring
        _ ≤ max (g m x) (-M * m) + max (g n (T^[m] x)) (-M * n) :=
          add_le_add (le_max_right _ _) (le_max_right _ _)

theorem clipped_nonpos (hg : ∀ n x, g n x ≤ 0) {M : ℝ} (hM : 0 ≤ M)
    (n : ℕ) (x : Ω) : clipped g M n x ≤ 0 := by
  exact max_le (hg n x) (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hM) (Nat.cast_nonneg n))

theorem clipped_lower (M : ℝ) (n : ℕ) (x : Ω) :
    -M * n ≤ clipped g M n x := le_max_right _ _

theorem clipped_nested {M N : ℝ} (hMN : M ≤ N) (n : ℕ) (x : Ω) :
    clipped g M n x = max (clipped g N n x) (-M * n) := by
  have h : -N * (n : ℝ) ≤ -M * n := mul_le_mul_of_nonneg_right (neg_le_neg hMN) (Nat.cast_nonneg n)
  simp only [clipped, max_assoc, max_eq_right h]

end SubCocycle
end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE SubCocycle

-- BEGIN COMPLETE MODULE MaximalSums
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

noncomputable def ergodicAverage (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * birkhoffSum T f n ω

noncomputable def runningMax (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, ω => max 0 (f ω + runningMax T f n (T ω))

lemma runningMax_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ runningMax T f n ω := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma runningMax_mono (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) :
    Monotone (fun n => runningMax T f n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing ω with
  | zero => exact runningMax_nonneg T f 1 ω
  | succ n ih =>
    apply max_le_max le_rfl
    linarith [ih (T ω)]

lemma runningMax_attained (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∃ k ≤ n, runningMax T f n ω = birkhoffSum T f k ω := by
  induction n generalizing ω with
  | zero => exact ⟨0,le_rfl,rfl⟩
  | succ n ih =>
    obtain ⟨k,hk,he⟩ := ih (T ω)
    by_cases h : f ω + runningMax T f n (T ω) ≤ 0
    · exact ⟨0,by omega,by simp only [runningMax,max_eq_left h,birkhoffSum_zero]⟩
    · refine ⟨k+1,by omega,?_⟩
      rw [runningMax,max_eq_right (le_of_not_ge h),birkhoffSum_succ',he]

lemma sum_le_runningMax (T : Ω → Ω) (f : Ω → ℝ) {k n : ℕ} (hkn : k ≤ n) (ω : Ω) :
    birkhoffSum T f k ω ≤ runningMax T f n ω := by
  induction n generalizing k ω with
  | zero =>
    have hk : k=0 := by omega
    subst k
    rfl
  | succ n ih =>
    cases k with
    | zero => simpa only [birkhoffSum_zero] using runningMax_nonneg T f (n+1) ω
    | succ k =>
      rw [birkhoffSum_succ',runningMax]
      have hh := ih (k := k) (by omega) (T ω)
      linarith [le_max_right (0 : ℝ) (f ω + runningMax T f n (T ω))]

lemma runningMax_pos_iff (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 < runningMax T f n ω ↔ ∃ k ≤ n, 0 < birkhoffSum T f k ω := by
  constructor
  · intro h
    obtain ⟨k,hk,he⟩ := runningMax_attained T f n ω
    exact ⟨k,hk,he ▸ h⟩
  · rintro ⟨k,hk,hpos⟩
    exact hpos.trans_le (sum_le_runningMax T f hk ω)

lemma runningMax_indicator_lower (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    runningMax T f (n+1) ω - runningMax T f n (T ω) ≤
      {x | 0 < runningMax T f (n+1) x}.indicator f ω := by
  classical
  by_cases h : 0 < runningMax T f (n+1) ω
  · rw [Set.indicator_of_mem (show ω ∈ {x | 0 < runningMax T f (n+1) x} from h)]
    have hp : 0 < f ω + runningMax T f n (T ω) := by
      simpa only [runningMax,lt_max_iff,lt_self_iff_false,false_or] using h
    rw [runningMax,max_eq_right hp.le]
    linarith
  · rw [Set.indicator_of_notMem (show ω ∉ {x | 0 < runningMax T f (n+1) x} from h)]
    have hz : runningMax T f (n+1) ω = 0 := le_antisymm (le_of_not_gt h) (runningMax_nonneg T f _ ω)
    rw [hz]
    linarith [runningMax_nonneg T f n (T ω)]

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE MaximalSums

-- BEGIN COMPLETE MODULE HopfFinite
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

lemma integral_preserving (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Measurable f) :
    (∫ ω, f (T ω) ∂μ) = ∫ ω,f ω ∂μ := by
  have he := integral_map hT.measurable.aemeasurable
    (hf.aestronglyMeasurable : AEStronglyMeasurable f (Measure.map T μ))
  rw [hT.map_eq] at he
  exact he.symm

lemma runningMax_measurable (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (runningMax T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

lemma runningMax_integrable (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    (n : ℕ) : Integrable (runningMax T f n) μ := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih => exact (integrable_zero _ _ _).sup (hf.add (hT.integrable_comp_of_integrable ih))

lemma hopf_finite (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) (n : ℕ) :
    0 ≤ ∫ ω in {ω | 0 < runningMax T f n ω}, f ω ∂μ := by
  cases n with
  | zero => simp [runningMax]
  | succ n =>
    have hm : MeasurableSet {ω | 0 < runningMax T f (n+1) ω} :=
      measurableSet_lt measurable_const (runningMax_measurable hT.measurable hf _)
    have h0 := runningMax_integrable hT hi n
    have h1 := runningMax_integrable hT hi (n+1)
    have hb := integral_mono (h1.sub (hT.integrable_comp_of_integrable h0)) (hi.indicator hm)
      (runningMax_indicator_lower T f n)
    simp only [Pi.sub_apply,Function.comp_def] at hb
    have hc : Integrable (fun ω => runningMax T f n (T ω)) μ := hT.integrable_comp_of_integrable h0
    rw [integral_sub h1 hc,
      integral_preserving hT (runningMax_measurable hT.measurable hf n),integral_indicator hm] at hb
    have hm' := integral_mono h0 h1 (fun ω => runningMax_mono T f ω (Nat.le_succ n))
    linarith

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE HopfFinite

-- BEGIN COMPLETE MODULE HopfMaximal
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

def maximalEvent (T : Ω → Ω) (f : Ω → ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, 0 < birkhoffSum T f n ω}

lemma sum_measurable (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffSum T f n) := by
  unfold birkhoffSum
  fun_prop

lemma maximalEvent_measurable (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f) :
    MeasurableSet (maximalEvent T f) := by
  change MeasurableSet {ω | ∃ n : ℕ, 0 < birkhoffSum T f n ω}
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => measurableSet_lt measurable_const (sum_measurable hT hf n))

omit [MeasurableSpace Ω] in
lemma maximal_indicator_tendsto (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) :
    Tendsto (fun n => {x | 0 < runningMax T f n x}.indicator f ω) atTop
      (𝓝 ((maximalEvent T f).indicator f ω)) := by
  classical
  by_cases h : ω ∈ maximalEvent T f
  · obtain ⟨k,hk⟩ := h
    rw [Set.indicator_of_mem (show ω ∈ maximalEvent T f from ⟨k,hk⟩)]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (Set.indicator_of_mem (show ω ∈ {x | 0 < runningMax T f n x} from
      hk.trans_le (sum_le_runningMax T f hn ω)) f).symm
  · rw [Set.indicator_of_notMem h]
    have he (n : ℕ) : ω ∉ {x | 0 < runningMax T f n x} := by
      intro hp
      obtain ⟨k,_,hk⟩ := (runningMax_pos_iff T f n ω).mp hp
      exact h ⟨k,hk⟩
    simpa only [Set.indicator_of_notMem (he _)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

lemma hopf_maximal (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) :
    0 ≤ ∫ ω in maximalEvent T f, f ω ∂μ := by
  have hm n : MeasurableSet {ω | 0 < runningMax T f n ω} :=
    measurableSet_lt measurable_const (runningMax_measurable hT.measurable hf n)
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (fun ω => ‖f ω‖)
    (fun n => hf.aestronglyMeasurable.indicator (hm n)) hi.norm
    (fun n => ae_of_all _ (fun ω => norm_indicator_le_norm_self _ _))
    (ae_of_all _ (maximal_indicator_tendsto T f))
  simp only [integral_indicator (hm _),integral_indicator (maximalEvent_measurable hT.measurable hf)] at ht
  exact ge_of_tendsto ht (Eventually.of_forall (hopf_finite hT hf hi))

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE HopfMaximal

-- BEGIN COMPLETE MODULE BoundedSequenceLimits
section

open Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

lemma limsup_le_limsup_error {u v e : ℕ → ℝ}
    (hu : atTop.IsCoboundedUnder (· ≤ ·) u)
    (hv : atTop.IsBoundedUnder (· ≤ ·) v)
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ᶠ n in atTop, u n ≤ v n + e n) :
    limsup u atTop ≤ limsup v atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hf := frequently_lt_of_lt_limsup hu (show limsup u atTop - ε/2 < limsup u atTop by linarith)
  have he' := he.eventually (gt_mem_nhds (show (0:ℝ)<ε/2 by positivity))
  have hb : limsup u atTop - ε ≤ limsup v atTop := by
    apply le_limsup_of_frequently_le _ hv
    exact ((hf.and_eventually he').and_eventually h).mono fun n hn => by
      linarith [hn.1.1,hn.1.2,hn.2]
  linarith

lemma limsup_eq_of_sub_tendsto_zero {u v : ℕ → ℝ}
    (hul : BddBelow (Set.range u)) (huu : BddAbove (Set.range u))
    (hvl : BddBelow (Set.range v)) (hvu : BddAbove (Set.range v))
    (he : Tendsto (fun n => u n-v n) atTop (𝓝 0)) :
    limsup u atTop = limsup v atTop := by
  apply le_antisymm
  · exact limsup_le_limsup_error hul.isBoundedUnder_of_range.isCobounded_le
      hvu.isBoundedUnder_of_range he (Eventually.of_forall fun n => by linarith)
  · have he' : Tendsto (fun n => v n-u n) atTop (𝓝 0) := by
      simpa only [neg_sub, neg_zero] using he.neg
    exact limsup_le_limsup_error hvl.isBoundedUnder_of_range.isCobounded_le
      huu.isBoundedUnder_of_range he' (Eventually.of_forall fun n => by linarith)

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BoundedSequenceLimits

-- BEGIN COMPLETE MODULE ErgodicAverageBasic
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

lemma average_measurable (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (ergodicAverage T f n) := by
  exact measurable_const.mul (sum_measurable hT hf n)

lemma sum_integrable (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) (n : ℕ) : Integrable (birkhoffSum T f n) μ := by
  unfold birkhoffSum
  exact integrable_finsetSum _ fun i _ => (hT.iterate i).integrable_comp_of_integrable hf

lemma average_integrable (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) (n : ℕ) : Integrable (ergodicAverage T f n) μ :=
  (sum_integrable hT hf n).const_mul _

omit [MeasurableSpace Ω] in
lemma average_abs_bound (T : Ω → Ω) {f : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ B) (n : ℕ) (ω : Ω) : |ergodicAverage T f n ω| ≤ B := by
  by_cases hn : n=0
  · simp [hn,ergodicAverage,hB]
  have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : |birkhoffSum T f n ω| ≤ (n:ℝ)*B := by
    unfold birkhoffSum
    calc
      _ ≤ ∑ i ∈ Finset.range n, |f (T^[i] ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, B := Finset.sum_le_sum fun i _ => hf _
      _ = _ := by simp
  rw [ergodicAverage,abs_mul,abs_inv,abs_of_pos hn']
  exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn'.le)).trans_eq (by field_simp)

omit [MeasurableSpace Ω] in
lemma average_shift_tendsto {f : Ω → ℝ} {B : ℝ} (hf : ∀ ω, |f ω| ≤ B)
    (T : Ω → Ω) (ω : Ω) :
    Tendsto (fun n => ergodicAverage T f n (T ω)-ergodicAverage T f n ω) atTop (𝓝 0) := by
  have hb : Bornology.IsBounded (Set.range f) := Metric.isBounded_range_iff.mpr ⟨2*B,by
    intro x y
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by linarith [hf x,hf y])⟩
  simpa only [ergodicAverage,birkhoffAverage,smul_eq_mul] using
    tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ hb T ω

lemma integral_average (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {n : ℕ} (hn : n ≠ 0) :
    (∫ ω,ergodicAverage T f n ω ∂μ) = ∫ ω,f ω ∂μ := by
  unfold ergodicAverage birkhoffSum
  have hc (i : ℕ) : Integrable (fun ω => f (T^[i] ω)) μ :=
    (hT.iterate i).integrable_comp_of_integrable hi
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => hc i)]
  simp only [integral_preserving (hT.iterate _) hf,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
  field_simp

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE ErgodicAverageBasic

-- BEGIN COMPLETE MODULE FixedBlockBound
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} {T : Ω → Ω} {g : ℕ → Ω → ℝ}

lemma fixed_block_sum (hg : SubCocycle T g) (k n : ℕ) (x : Ω) :
    g (n*k) x ≤ birkhoffSum (T^[k]) (g k) n x := by
  induction n with
  | zero => simp [hg.zero]
  | succ n ih =>
    rw [Nat.succ_mul,birkhoffSum_succ]
    have hh := hg.add_le (n*k) k x
    have he : (T^[k])^[n] x = T^[n*k] x := by rw [← Function.iterate_mul]; rw [Nat.mul_comm]
    rw [he]
    linarith

lemma fixed_block_rate (hg : SubCocycle T g) {k n : ℕ} (hk : 0<k) (hn : 0<n)
    (x : Ω) : g (n*k) x / (n*k:ℕ) ≤ ergodicAverage (T^[k]) (g k) n x / k := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hh := div_le_div_of_nonneg_right (fixed_block_sum hg k n x) (mul_nonneg hn'.le hk'.le)
  simpa only [Nat.cast_mul,mul_inv_rev,ergodicAverage,div_mul_eq_div_div,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE FixedBlockBound

-- BEGIN COMPLETE MODULE CocycleRates
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

noncomputable def rate (g : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) : ℝ := g n x / n
noncomputable def lowerRate (g : ℕ → Ω → ℝ) (x : Ω) : ℝ :=
  liminf (fun n => rate g n x) atTop

lemma rate_bounds {T : Ω → Ω} {g : ℕ → Ω → ℝ} (hg : SubCocycle T g)
    {M : ℝ} (hM : 0 ≤ M) (hl : ∀ n x, -M * n ≤ g n x)
    (hu : ∀ n x, g n x ≤ 0) (n : ℕ) (x : Ω) :
    -M ≤ rate g n x ∧ rate g n x ≤ 0 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [rate, hg.zero, hM]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact ⟨(le_div_iff₀ hn').mpr (hl n x), div_nonpos_of_nonpos_of_nonneg (hu n x) hn'.le⟩

lemma lowerRate_bounds {T : Ω → Ω} {g : ℕ → Ω → ℝ} (hg : SubCocycle T g)
    {M : ℝ} (hM : 0 ≤ M) (hl : ∀ n x, -M * n ≤ g n x)
    (hu : ∀ n x, g n x ≤ 0) (x : Ω) : -M ≤ lowerRate g x ∧ lowerRate g x ≤ 0 := by
  have hlo : atTop.IsBoundedUnder (· ≥ ·) (fun n => rate g n x) :=
    (show BddBelow (Set.range (fun n => rate g n x)) from
      ⟨-M, by rintro _ ⟨n,rfl⟩; exact (rate_bounds hg hM hl hu n x).1⟩).isBoundedUnder_of_range
  have hup : atTop.IsBoundedUnder (· ≤ ·) (fun n => rate g n x) :=
    (show BddAbove (Set.range (fun n => rate g n x)) from
      ⟨0, by rintro _ ⟨n,rfl⟩; exact (rate_bounds hg hM hl hu n x).2⟩).isBoundedUnder_of_range
  exact ⟨le_liminf_of_le hup.isCobounded_ge (Eventually.of_forall fun n => (rate_bounds hg hM hl hu n x).1),
    liminf_le_of_frequently_le (Frequently.of_forall fun n => (rate_bounds hg hM hl hu n x).2) hlo⟩

lemma measurable_lowerRate [MeasurableSpace Ω] {g : ℕ → Ω → ℝ}
    (hg : ∀ n, Measurable (g n)) : Measurable (lowerRate g) :=
  Measurable.liminf fun n => (hg n).div_const _

lemma liminf_le_liminf_error {u v e : ℕ → ℝ}
    (hu : atTop.IsBoundedUnder (· ≥ ·) u)
    (hv : atTop.IsCoboundedUnder (· ≥ ·) v)
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ᶠ n in atTop, u n ≤ v n + e n) :
    liminf u atTop ≤ liminf v atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hf := frequently_lt_of_liminf_lt hv (show liminf v atTop < liminf v atTop + ε/2 by linarith)
  have he' := he.eventually (gt_mem_nhds (show (0:ℝ)<ε/2 by positivity))
  apply liminf_le_of_frequently_le _ hu
  exact ((hf.and_eventually he').and_eventually h).mono fun n hn => by linarith [hn.1.1,hn.1.2,hn.2]

lemma lowerRate_shift_le {T : Ω → Ω} {g : ℕ → Ω → ℝ} (hg : SubCocycle T g)
    {M : ℝ} (hM : 0 ≤ M) (hl : ∀ n x, -M * n ≤ g n x)
    (hu : ∀ n x, g n x ≤ 0) (x : Ω) : lowerRate g x ≤ lowerRate g (T x) := by
  have hlo : atTop.IsBoundedUnder (· ≥ ·) (fun n => rate g (n+1) x) :=
    (show BddBelow (Set.range (fun n => rate g (n+1) x)) from
      ⟨-M, by rintro _ ⟨n,rfl⟩; exact (rate_bounds hg hM hl hu (n+1) x).1⟩).isBoundedUnder_of_range
  have hup : atTop.IsBoundedUnder (· ≤ ·) (fun n => rate g n (T x)) :=
    (show BddAbove (Set.range (fun n => rate g n (T x))) from
      ⟨0, by rintro _ ⟨n,rfl⟩; exact (rate_bounds hg hM hl hu n (T x)).2⟩).isBoundedUnder_of_range
  have he : Tendsto (fun n : ℕ => (|g 1 x|+M)/(n+1:ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hh : ∀ᶠ n : ℕ in atTop,
      rate g (n+1) x ≤ rate g n (T x) + (|g 1 x|+M)/(n+1:ℕ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hnp : (0:ℝ)<n+1 := by positivity
    have hs := hg.add_le 1 n x
    simp only [Function.iterate_one] at hs
    rw [Nat.add_comm 1 n] at hs
    have hlow := hl n (T x)
    dsimp [rate]
    rw [Nat.cast_add, Nat.cast_one]
    apply (div_le_iff₀ hnp).mpr
    have heq : g n (T x) / n * n = g n (T x) := div_mul_cancel₀ _ hn'.ne'
    have hb := (le_div_iff₀ hn').mpr hlow
    have heq' : (|g 1 x|+M)/(n+1)*(n+1) = |g 1 x|+M := div_mul_cancel₀ _ hnp.ne'
    nlinarith [le_abs_self (g 1 x)]
  have h := liminf_le_liminf_error hlo hup.isCobounded_ge he hh
  rw [show liminf (fun n => rate g (n+1) x) atTop = lowerRate g x from
    liminf_nat_add (fun n => rate g n x) 1] at h
  exact h

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE CocycleRates

-- BEGIN COMPLETE MODULE CocycleInvariant
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integrable_lowerRate {T : Ω → Ω} {g : ℕ → Ω → ℝ} (hg : SubCocycle T g)
    (hm : ∀ n, Measurable (g n)) {M : ℝ} (hM : 0 ≤ M)
    (hl : ∀ n x, -M * n ≤ g n x) (hu : ∀ n x, g n x ≤ 0) :
    Integrable (lowerRate g) μ := by
  apply (integrable_const M).mono' (measurable_lowerRate hm).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonpos (lowerRate_bounds hg hM hl hu x).2]
  linarith [(lowerRate_bounds hg hM hl hu x).1]

lemma lowerRate_invariant {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : ℕ → Ω → ℝ} (hg : SubCocycle T g) (hm : ∀ n, Measurable (g n))
    {M : ℝ} (hM : 0 ≤ M) (hl : ∀ n x, -M * n ≤ g n x)
    (hu : ∀ n x, g n x ≤ 0) :
    ∀ᵐ x ∂μ, lowerRate g (T x) = lowerRate g x := by
  have hi := integrable_lowerRate (μ:=μ) hg hm hM hl hu
  have he := (integral_eq_iff_of_ae_le hi (hT.integrable_comp_of_integrable hi)
    (Eventually.of_forall (lowerRate_shift_le hg hM hl hu))).mp
      (integral_preserving hT (measurable_lowerRate hm)).symm
  exact he.symm

omit [IsProbabilityMeasure μ] in
lemma ae_iterate_invariant {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : ∀ᵐ x ∂μ, f (T x) = f x) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, f (T^[n] x) = f x := by
  apply ae_all_iff.mpr
  intro n
  induction n with
  | zero => exact Eventually.of_forall fun x => rfl
  | succ n ih =>
    filter_upwards [ih, (hT.iterate n).quasiMeasurePreserving.ae hf] with x hx hy
    simpa only [Function.iterate_succ_apply', hx] using hy

omit [MeasurableSpace Ω] in
lemma exists_small_block {T : Ω → Ω} {g : ℕ → Ω → ℝ} (hg : SubCocycle T g)
    {M : ℝ} (hM : 0 ≤ M) (hl : ∀ n x, -M * n ≤ g n x)
    (hu : ∀ n x, g n x ≤ 0) (x : Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧ g k x ≤ (lowerRate g x + ε) * k := by
  have hup : atTop.IsBoundedUnder (· ≤ ·) (fun n => rate g n x) :=
    isBoundedUnder_of ⟨0, fun n => (rate_bounds hg hM hl hu n x).2⟩
  have hf := frequently_lt_of_liminf_lt hup.isCobounded_ge
    (show lowerRate g x < lowerRate g x + ε by linarith)
  obtain ⟨k,hk,hkpos⟩ := (hf.and_eventually (eventually_ge_atTop 1)).exists
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  exact ⟨k,by omega, ((div_lt_iff₀ hk').mp hk).le⟩

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE CocycleInvariant

-- BEGIN COMPLETE MODULE BadBlocks
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

noncomputable def badBlockSet (g : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ) : Set Ω :=
  {x | ∀ k : ℕ, 0 < k → k ≤ N → (lowerRate g x + ε) * k < g k x}

noncomputable def badBlockIndicator (g : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ) : Ω → ℝ :=
  (badBlockSet g ε N).indicator (fun _ => 1)

lemma badBlockSet_measurable [MeasurableSpace Ω] {g : ℕ → Ω → ℝ}
    (hg : ∀ n, Measurable (g n)) (ε : ℝ) (N : ℕ) :
    MeasurableSet (badBlockSet g ε N) := by
  unfold badBlockSet
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro hk
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro hkN
  exact measurableSet_lt ((measurable_lowerRate hg).add_const ε |>.mul_const _) (hg k)

lemma badBlockIndicator_measurable [MeasurableSpace Ω] {g : ℕ → Ω → ℝ}
    (hg : ∀ n, Measurable (g n)) (ε : ℝ) (N : ℕ) :
    Measurable (badBlockIndicator g ε N) :=
  measurable_const.indicator (badBlockSet_measurable hg ε N)

lemma badBlockIndicator_bounds (g : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ) (x : Ω) :
    0 ≤ badBlockIndicator g ε N x ∧ badBlockIndicator g ε N x ≤ 1 := by
  classical
  unfold badBlockIndicator
  by_cases hx : x ∈ badBlockSet g ε N <;> simp [hx]

lemma badBlockIndicator_antitone (g : ℕ → Ω → ℝ) (ε : ℝ) (x : Ω) :
    Antitone (fun N => badBlockIndicator g ε N x) := by
  classical
  intro N K hNK
  by_cases hx : x ∈ badBlockSet g ε K
  · have hx' : x ∈ badBlockSet g ε N := fun k hk hkN => hx k hk (hkN.trans hNK)
    simp [badBlockIndicator,hx,hx']
  · simp only [badBlockIndicator, Set.indicator_of_notMem hx]
    exact (badBlockIndicator_bounds g ε N x).1

lemma not_badBlock_iff (g : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ) (x : Ω) :
    x ∉ badBlockSet g ε N ↔ ∃ k : ℕ, 0 < k ∧ k ≤ N ∧ g k x ≤ (lowerRate g x + ε) * k := by
  simp only [badBlockSet, Set.mem_ofPred_eq]
  push Not
  rfl

lemma badBlockIndicator_tendsto_zero {T : Ω → Ω} {g : ℕ → Ω → ℝ}
    (hg : SubCocycle T g) {M : ℝ} (hM : 0 ≤ M)
    (hl : ∀ n x, -M*n ≤ g n x) (hu : ∀ n x, g n x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) (x : Ω) :
    Tendsto (fun N => badBlockIndicator g ε N x) atTop (𝓝 0) := by
  obtain ⟨k,hk,hsmall⟩ := exists_small_block hg hM hl hu x hε
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with N hN
  have hx : x ∉ badBlockSet g ε N := (not_badBlock_iff g ε N x).mpr ⟨k,hk,hN,hsmall⟩
  simp [badBlockIndicator,hx]

lemma badBlockIndicator_integrable [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {g : ℕ → Ω → ℝ} (hg : ∀ n, Measurable (g n)) (ε : ℝ) (N : ℕ) :
    Integrable (badBlockIndicator g ε N) μ :=
  (integrable_const (1:ℝ)).indicator (badBlockSet_measurable hg ε N)

lemma integral_badBlock_tendsto_zero [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} {g : ℕ → Ω → ℝ} (hg : SubCocycle T g)
    (hm : ∀ n, Measurable (g n)) {M : ℝ} (hM : 0 ≤ M)
    (hl : ∀ n x, -M*n ≤ g n x) (hu : ∀ n x, g n x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => ∫ x, badBlockIndicator g ε N x ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : Ω => (1:ℝ))
    (fun N => (badBlockIndicator_measurable hm ε N).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (badBlockIndicator_bounds g ε N x).1]
      exact (badBlockIndicator_bounds g ε N x).2)
    (Eventually.of_forall (badBlockIndicator_tendsto_zero hg hM hl hu hε))
  simpa using h

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BadBlocks

-- BEGIN COMPLETE MODULE DecreasingIntegral
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

lemma ae_tendsto_zero_of_antitone_integrals {f : ℕ → Ω → ℝ}
    (hm : ∀ n, Measurable (f n))
    (hb : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f n x ∧ f n x ≤ 1)
    (hanti : ∀ᵐ x ∂μ, Antitone (fun n => f n x))
    (hi : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0) := by
  let z : Ω → ℝ := fun x => ⨅ n, f n x
  have hzmeas : Measurable z := Measurable.iInf hm
  have hzbound : ∀ᵐ x ∂μ, 0 ≤ z x ∧ z x ≤ 1 := by
    filter_upwards [hb] with x hx
    have hbelow : BddBelow (Set.range (fun n => f n x)) := ⟨0,by rintro _ ⟨n,rfl⟩; exact (hx n).1⟩
    exact ⟨le_ciInf fun n => (hx n).1, (ciInf_le hbelow 0).trans (hx 0).2⟩
  have hzint : Integrable z μ := by
    apply (integrable_const (1:ℝ)).mono' hzmeas.aestronglyMeasurable
    filter_upwards [hzbound] with x hx
    simpa [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (z x)) := by
    filter_upwards [hb,hanti] with x hx ha
    exact tendsto_atTop_ciInf ha ⟨0,by rintro _ ⟨n,rfl⟩; exact (hx n).1⟩
  have hh := tendsto_integral_of_dominated_convergence (μ:=μ) (fun _ : Ω => (1:ℝ))
    (fun n => (hm n).aestronglyMeasurable) (integrable_const 1)
    (fun n => hb.mono fun x hx => by simpa [Real.norm_eq_abs,abs_of_nonneg (hx n).1] using (hx n).2) ht
  have hz0 : ∫ x,z x ∂μ = 0 := tendsto_nhds_unique hh hi
  have he := (integral_eq_zero_iff_of_nonneg_ae (hzbound.mono fun x hx => hx.1) hzint).mp hz0
  filter_upwards [ht,he] with x hx he
  simpa only [he,Pi.zero_apply] using hx

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE DecreasingIntegral

-- BEGIN COMPLETE MODULE BoundedAverageLimits
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

noncomputable def upperAverage (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  limsup (fun n => ergodicAverage T f n ω) atTop

lemma average_range_bounds (T : Ω → Ω) {f : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ B) (ω : Ω) :
    BddBelow (Set.range (fun n => ergodicAverage T f n ω)) ∧
    BddAbove (Set.range (fun n => ergodicAverage T f n ω)) := by
  constructor
  · exact ⟨-B,by rintro _ ⟨n,rfl⟩; exact (abs_le.mp (average_abs_bound T hB hf n ω)).1⟩
  · exact ⟨B,by rintro _ ⟨n,rfl⟩; exact (abs_le.mp (average_abs_bound T hB hf n ω)).2⟩

lemma upperAverage_bound (T : Ω → Ω) {f : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ B) (ω : Ω) : |upperAverage T f ω| ≤ B := by
  obtain ⟨hl,hu⟩ := average_range_bounds T hB hf ω
  apply abs_le.mpr
  constructor
  · exact le_limsup_of_frequently_le (Frequently.of_forall fun n =>
      (abs_le.mp (average_abs_bound T hB hf n ω)).1) hu.isBoundedUnder_of_range
  · exact limsup_le_of_le hl.isBoundedUnder_of_range.isCobounded_le
      (Eventually.of_forall fun n => (abs_le.mp (average_abs_bound T hB hf n ω)).2)

lemma upperAverage_invariant (T : Ω → Ω) {f : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ B) (ω : Ω) : upperAverage T f (T ω)=upperAverage T f ω := by
  obtain ⟨hl,hu⟩ := average_range_bounds T hB hf ω
  obtain ⟨hl',hu'⟩ := average_range_bounds T hB hf (T ω)
  exact limsup_eq_of_sub_tendsto_zero hl' hu' hl hu (average_shift_tendsto hf T ω)

lemma upperAverage_measurable [MeasurableSpace Ω] {T : Ω → Ω} (hT : Measurable T)
    {f : Ω → ℝ} (hf : Measurable f) : Measurable (upperAverage T f) :=
  Measurable.limsup fun n => average_measurable hT hf n

lemma upperAverage_integrable [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω, |f ω| ≤ B) : Integrable (upperAverage T f) μ := by
  apply Integrable.mono' (integrable_const B) (upperAverage_measurable hT hf).aestronglyMeasurable
  exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using upperAverage_bound T hB hb ω

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BoundedAverageLimits

-- BEGIN COMPLETE MODULE HopfInvariantComparison
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

lemma average_sub_invariant {T : Ω → Ω} (f g : Ω → ℝ)
    (hg : ∀ ω, g (T ω)=g ω) {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
    ergodicAverage T (fun x => f x-g x) n ω = ergodicAverage T f n ω-g ω := by
  have hs := congrFun (birkhoffSum_of_comp_eq (show g ∘ T=g from funext hg) n) ω
  simp only [Pi.smul_apply,nsmul_eq_mul] at hs
  have he : birkhoffSum T (fun x => f x-g x) n ω = birkhoffSum T f n ω-birkhoffSum T g n ω :=
    birkhoffSum_sub T f g n ω
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
  rw [ergodicAverage,he,hs,ergodicAverage]
  field_simp

lemma maximalEvent_upper_sub_eps {T : Ω → Ω} {f : Ω → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ ω, |f ω| ≤ B) {ε : ℝ} (hε : 0<ε) :
    maximalEvent T (fun x => f x-(upperAverage T f x-ε))=Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  obtain ⟨hl,_⟩ := average_range_bounds T hB hf ω
  have hh := frequently_lt_of_lt_limsup hl.isBoundedUnder_of_range.isCobounded_le
    (show upperAverage T f ω-ε < upperAverage T f ω by linarith)
  obtain ⟨n,hn,hpos⟩ := (hh.and_eventually (eventually_gt_atTop 0)).exists
  have hn0 : n≠0 := Nat.ne_of_gt hpos
  have hn' : (0:ℝ)<n := by exact_mod_cast hpos
  have ha := average_sub_invariant f (fun x=>upperAverage T f x-ε)
    (fun x=>by rw [upperAverage_invariant T hB hf x]) hn0 ω
  have hp : 0<ergodicAverage T (fun x=>f x-(upperAverage T f x-ε)) n ω := by linarith
  exact ⟨n,(mul_pos_iff.mp hp).resolve_right (by intro h; exact (inv_pos.mpr hn').not_gt h.1) |>.2⟩

lemma integral_upperAverage_le [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω, |f ω| ≤ B) : (∫ ω,upperAverage T f ω ∂μ) ≤ ∫ ω,f ω ∂μ := by
  have hm := upperAverage_measurable hT.measurable hf
  have hu := upperAverage_integrable hT.measurable hf hB hb (μ:=μ)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hh := hopf_maximal hT (hf.sub (hm.sub measurable_const))
    (hi.sub (hu.sub (integrable_const ε)))
  change 0 ≤ ∫ ω in maximalEvent T (fun x=> f x-(upperAverage T f x-ε)), f ω-(upperAverage T f ω-ε) ∂μ at hh
  rw [maximalEvent_upper_sub_eps hB hb hε,Measure.restrict_univ] at hh
  have hc : Integrable (fun ω=>upperAverage T f ω-ε) μ := hu.sub (integrable_const ε)
  rw [integral_sub hi hc,integral_sub hu (integrable_const ε)] at hh
  simp only [integral_const] at hh
  simp at hh
  linarith

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE HopfInvariantComparison

-- BEGIN COMPLETE MODULE BoundedAverageConvergence
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

lemma real_limsup_neg {u : ℕ → ℝ} (hl : BddBelow (Set.range u))
    (hu : BddAbove (Set.range u)) : limsup (fun n => -u n) atTop = -liminf u atTop := by
  let e : ℝ ≃o ℝᵒᵈ := { toEquiv := Equiv.neg ℝ, map_rel_iff' := by intro a b; exact neg_le_neg_iff }
  have hl' : BddBelow (Set.range (fun n => e (u n))) := by
    obtain ⟨b,hb⟩ := hl
    exact ⟨-b,by rintro _ ⟨n,rfl⟩; change -u n ≤ -b; exact neg_le_neg (hb ⟨n,rfl⟩)⟩
  have hu' : BddAbove (Set.range (fun n => e (u n))) := by
    obtain ⟨b,hb⟩ := hu
    exact ⟨-b,by rintro _ ⟨n,rfl⟩; change -b ≤ -u n; exact neg_le_neg (hb ⟨n,rfl⟩)⟩
  exact (e.liminf_apply hl.isBoundedUnder_of_range hu.isBoundedUnder_of_range.isCobounded_ge
    hl'.isBoundedUnder_of_range hu'.isBoundedUnder_of_range.isCobounded_ge).symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

omit [MeasurableSpace Ω] in
lemma upperAverage_neg {f : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ B) (ω : Ω) :
    upperAverage T (fun x=>-f x) ω = -liminf (fun n=>ergodicAverage T f n ω) atTop := by
  obtain ⟨hl,hu⟩ := average_range_bounds T hB hf ω
  have he (n : ℕ) : ergodicAverage T (fun x=>-f x) n ω = -ergodicAverage T f n ω := by
    simp [ergodicAverage,birkhoffSum,Finset.sum_neg_distrib]
  simp only [upperAverage,he]
  exact real_limsup_neg hl hu

lemma bounded_average_ae_converges (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω, |f ω| ≤ B) :
    ∀ᵐ ω ∂μ, Tendsto (fun n=>ergodicAverage T f n ω) atTop (𝓝 (upperAverage T f ω)) := by
  have hbn : ∀ ω, |(-f ω)|≤B := by intro ω; simpa using hb ω
  have hu := upperAverage_integrable hT.measurable hf hB hb (μ:=μ)
  have hv := upperAverage_integrable hT.measurable hf.neg hB hbn (μ:=μ)
  change Integrable (upperAverage T (fun x=>-f x)) μ at hv
  have hp (ω : Ω) : 0 ≤ upperAverage T f ω+upperAverage T (fun x=>-f x) ω := by
    rw [upperAverage_neg hB hb ω]
    obtain ⟨hl,hh⟩ := average_range_bounds T hB hb ω
    exact sub_nonneg.mpr (liminf_le_limsup hh.isBoundedUnder_of_range hl.isBoundedUnder_of_range)
  have he : (∫ ω,upperAverage T f ω+upperAverage T (fun x=>-f x) ω ∂μ)=0 := by
    apply le_antisymm
    · rw [integral_add hu hv]
      have h1 := integral_upperAverage_le hT hf hi hB hb
      have h2 := integral_upperAverage_le hT hf.neg hi.neg hB hbn
      change (∫ ω,upperAverage T (fun x=>-f x) ω ∂μ) ≤ ∫ ω,-f ω ∂μ at h2
      rw [integral_neg] at h2
      linarith
    · exact integral_nonneg hp
  have hz := (integral_eq_zero_iff_of_nonneg hp (hu.add hv)).mp he
  filter_upwards [hz] with ω hω
  rw [upperAverage_neg hB hb ω] at hω
  simp only [Pi.zero_apply] at hω
  obtain ⟨hl,hh⟩ := average_range_bounds T hB hb ω
  apply tendsto_of_liminf_eq_limsup (show liminf (fun n=>ergodicAverage T f n ω) atTop = upperAverage T f ω by linarith) rfl
    hh.isBoundedUnder_of_range hl.isBoundedUnder_of_range

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BoundedAverageConvergence

-- BEGIN COMPLETE MODULE BoundedBirkhoff
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

lemma bounded_birkhoff_convergence (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω, |f ω| ≤ B) :
    ∃ ξ : Ω → ℝ, Measurable ξ ∧ Integrable ξ μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n=>ergodicAverage T f n ω) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun n=>∫ ω,|ergodicAverage T f n ω-ξ ω| ∂μ) atTop (𝓝 0) ∧
      (∫ ω,ξ ω ∂μ) = ∫ ω,f ω ∂μ := by
  have hm := upperAverage_measurable hT.measurable hf
  have hu := upperAverage_integrable hT.measurable hf hB hb (μ:=μ)
  have ha := bounded_average_ae_converges hT hf hi hB hb
  refine ⟨upperAverage T f,hm,hu,ha,?_,?_⟩
  · have hd := tendsto_integral_of_dominated_convergence (μ:=μ) (fun _ : Ω => 2*B)
      (fun n => ((average_measurable hT.measurable hf n).sub hm).abs.aestronglyMeasurable)
      (integrable_const _)
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs,abs_abs]
        exact (abs_sub _ _).trans (by linarith [average_abs_bound T hB hb n ω,upperAverage_bound T hB hb ω]))
      (ha.mono fun ω hω => by simpa using (hω.sub_const (upperAverage T f ω)).abs)
    simpa using hd
  · have hd := tendsto_integral_of_dominated_convergence (μ:=μ) (fun _ : Ω => B)
      (fun n => (average_measurable hT.measurable hf n).aestronglyMeasurable)
      (integrable_const _)
      (fun n => ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using average_abs_bound T hB hb n ω) ha
    have hc : Tendsto (fun n=>∫ ω,ergodicAverage T f n ω ∂μ) atTop (𝓝 (∫ ω,f ω ∂μ)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_gt_atTop 0] with n hn
        exact (integral_average hT hf hi (Nat.ne_of_gt hn)).symm)
    exact tendsto_nhds_unique hd hc

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BoundedBirkhoff

-- BEGIN COMPLETE MODULE BadFrequency
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

omit [MeasurableSpace Ω] in
lemma average_pointwise_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) (n : ℕ) (x : Ω) :
    ergodicAverage T f n x ≤ ergodicAverage T g n x := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact Finset.sum_le_sum fun i hi => h _

omit [MeasurableSpace Ω] in
lemma average_pointwise_nonneg {f : Ω → ℝ} (h : ∀ x, 0 ≤ f x) (n : ℕ) (x : Ω) :
    0 ≤ ergodicAverage T f n x := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (Finset.sum_nonneg fun i hi => h _)

lemma bad_frequency_exists (hT : MeasurePreserving T μ μ)
    {g : ℕ → Ω → ℝ} (hg : SubCocycle T g) (hm : ∀ n, Measurable (g n))
    {M : ℝ} (hM : 0 ≤ M) (hl : ∀ n x, -M*n ≤ g n x) (hu : ∀ n x, g n x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℕ → Ω → ℝ, (∀ N, Measurable (β N)) ∧
      (∀ᵐ x ∂μ, ∀ N, Tendsto (fun n => ergodicAverage T (badBlockIndicator g ε N) n x)
        atTop (𝓝 (β N x))) ∧
      (∀ᵐ x ∂μ, Tendsto (fun N => β N x) atTop (𝓝 0)) := by
  have hex : ∀ N : ℕ, ∃ z : Ω → ℝ, Measurable z ∧ Integrable z μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => ergodicAverage T (badBlockIndicator g ε N) n x) atTop (𝓝 (z x))) ∧
      Tendsto (fun n => ∫ x, |ergodicAverage T (badBlockIndicator g ε N) n x-z x| ∂μ) atTop (𝓝 0) ∧
      (∫ x,z x ∂μ) = ∫ x,badBlockIndicator g ε N x ∂μ := by
    intro N
    exact bounded_birkhoff_convergence hT (badBlockIndicator_measurable hm ε N)
      (badBlockIndicator_integrable hm ε N) (by norm_num : (0:ℝ)≤1)
      (fun x => by rw [abs_of_nonneg (badBlockIndicator_bounds g ε N x).1]; exact (badBlockIndicator_bounds g ε N x).2)
  choose β hβm hβi hβt hβL hβe using hex
  have ht : ∀ᵐ x ∂μ, ∀ N, Tendsto (fun n => ergodicAverage T (badBlockIndicator g ε N) n x)
      atTop (𝓝 (β N x)) := ae_all_iff.mpr hβt
  refine ⟨β,hβm,ht,?_⟩
  apply ae_tendsto_zero_of_antitone_integrals hβm
  · filter_upwards [ht] with x hx
    intro N
    constructor
    · exact ge_of_tendsto' (hx N) fun n => average_pointwise_nonneg (fun y => (badBlockIndicator_bounds g ε N y).1) n x
    · apply le_of_tendsto' (hx N)
      intro n
      exact (le_abs_self _).trans (average_abs_bound T (by norm_num : (0:ℝ)≤1)
        (fun y => by rw [abs_of_nonneg (badBlockIndicator_bounds g ε N y).1]; exact (badBlockIndicator_bounds g ε N y).2) n x)
  · filter_upwards [ht] with x hx
    intro N K hNK
    apply le_of_tendsto_of_tendsto (hx K) (hx N)
    exact Eventually.of_forall fun n => average_pointwise_mono
      (fun y => badBlockIndicator_antitone g ε y hNK) n x
  · simpa only [hβe] using integral_badBlock_tendsto_zero (μ:=μ) hg hm hM hl hu hε

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BadFrequency

-- BEGIN COMPLETE MODULE GreedyBlockBound
section

namespace KingmanSubadditive.Ergodic.Proof

/-- The finite greedy-block estimate. Bad starting points cost at most `M`,
and the final unfinished block costs at most `M*N`. -/
theorem greedy_block_bound (F : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (a M : ℝ) (N : ℕ) (hN : 0 < N) (hM : 0 ≤ M) (ha : -M ≤ a)
    (hsub : ∀ s m n, F s (m + n) ≤ F s m + F (s + m) n)
    (hneg : ∀ s n, F s n ≤ 0) (hb : ∀ s, 0 ≤ b s)
    (hgood : ∀ s, b s < 1 → ∃ k, 0 < k ∧ k ≤ N ∧ F s k ≤ a * k)
    (s n : ℕ) :
    F s n ≤ a * n + M * ((∑ i ∈ Finset.range n, b (s + i)) + N) := by
  have sum_nonneg : ∀ s n, 0 ≤ ∑ i ∈ Finset.range n, b (s + i) := by
    intro s n; exact Finset.sum_nonneg fun i hi => hb _
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hn : n < N
    · have hcast : (n : ℝ) ≤ N := Nat.cast_le.mpr (Nat.le_of_lt hn)
      have hprod := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n)
      have hmn := mul_le_mul_of_nonneg_left hcast hM
      have hs := mul_nonneg hM (sum_nonneg s n)
      exact (hneg s n).trans (by nlinarith)
    · have hNn : N ≤ n := Nat.le_of_not_gt hn
      obtain ⟨k, hk, hkN, hFk⟩ : ∃ k, 0 < k ∧ k ≤ N ∧
          F s k ≤ a * k + M * ∑ i ∈ Finset.range k, b (s + i) := by
        by_cases hbs : 1 ≤ b s
        · refine ⟨1, by omega, hN, ?_⟩
          simp only [Finset.sum_range_one, Nat.add_zero, Nat.cast_one, mul_one]
          have hm := mul_le_mul_of_nonneg_left hbs hM
          exact (hneg s 1).trans (by linarith)
        · obtain ⟨k, hk, hkN, hFk⟩ := hgood s (lt_of_not_ge hbs)
          exact ⟨k, hk, hkN, hFk.trans (le_add_of_nonneg_right (mul_nonneg hM (sum_nonneg s k)))⟩
      have hkn : k ≤ n := hkN.trans hNn
      have hi := ih (n - k) (by omega) (s + k)
      have hs := hsub s k (n - k)
      have hsplit : (∑ i ∈ Finset.range n, b (s + i)) =
          (∑ i ∈ Finset.range k, b (s + i)) +
          ∑ i ∈ Finset.range (n - k), b (s + k + i) := by
        conv_lhs => rw [← Nat.add_sub_of_le hkn]
        rw [Finset.sum_range_add]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        omega
      have hcast : (n : ℝ) = k + (n - k : ℕ) := by exact_mod_cast (Nat.add_sub_of_le hkn).symm
      rw [Nat.add_sub_of_le hkn] at hs
      rw [hsplit, hcast]
      nlinarith

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE GreedyBlockBound

-- BEGIN COMPLETE MODULE OrbitBlockBound
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

lemma orbit_block_bound {T : Ω → Ω} {g : ℕ → Ω → ℝ} (hg : SubCocycle T g)
    {M : ℝ} (hM : 0 ≤ M) (hl : ∀ n x, -M*n ≤ g n x) (hu : ∀ n x, g n x ≤ 0)
    (x : Ω) (hinv : ∀ k, lowerRate g (T^[k] x) = lowerRate g x)
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 0 < N) {n : ℕ} (hn : 0 < n) :
    rate g n x ≤ lowerRate g x + ε +
      M * (ergodicAverage T (badBlockIndicator g ε N) n x + (N:ℝ)/n) := by
  classical
  have hb := greedy_block_bound (fun s n => g n (T^[s] x))
    (fun s => badBlockIndicator g ε N (T^[s] x)) (lowerRate g x+ε) M N hN hM
    (by linarith [(lowerRate_bounds hg hM hl hu x).1])
    (by
      intro s m n
      rw [Nat.add_comm s m, Function.iterate_add_apply]
      exact hg.add_le m n (T^[s] x))
    (fun s n => hu n _) (fun s => (badBlockIndicator_bounds g ε N _).1)
    (by
      intro s hs
      have hnot : T^[s] x ∉ badBlockSet g ε N := by
        intro hh
        simp [badBlockIndicator,hh] at hs
      obtain ⟨k,hk,hkN,hkbound⟩ := (not_badBlock_iff g ε N (T^[s] x)).mp hnot
      rw [hinv s] at hkbound
      exact ⟨k,hk,hkN,hkbound⟩) 0 n
  simp only [Function.iterate_zero_apply,Nat.zero_add] at hb
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  unfold rate
  apply (div_le_iff₀ hn').mpr
  calc
    g n x ≤ (lowerRate g x+ε)*n + M*((∑ i ∈ Finset.range n,
        badBlockIndicator g ε N (T^[i] x))+N) := hb
    _ = (lowerRate g x+ε+M*(ergodicAverage T (badBlockIndicator g ε N) n x+(N:ℝ)/n))*n := by
      unfold ergodicAverage birkhoffSum
      field_simp

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE OrbitBlockBound

-- BEGIN COMPLETE MODULE BoundedCocycle
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} {g : ℕ → Ω → ℝ}

lemma bounded_cocycle_upper (hT : MeasurePreserving T μ μ)
    (hg : SubCocycle T g) (hm : ∀ n, Measurable (g n))
    {M : ℝ} (hM : 0 ≤ M) (hl : ∀ n x, -M*n ≤ g n x) (hu : ∀ n x, g n x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ, limsup (fun n => rate g n x) atTop ≤ lowerRate g x+ε := by
  obtain ⟨β,hβm,hβ,hβ0⟩ := bad_frequency_exists hT hg hm hM hl hu hε
  have hinv := ae_iterate_invariant hT (lowerRate_invariant hT hg hm hM hl hu)
  filter_upwards [hβ,hβ0,hinv] with x hx hx0 hxi
  have hlo : atTop.IsBoundedUnder (· ≥ ·) (fun n => rate g n x) :=
    isBoundedUnder_of ⟨-M, fun n => (rate_bounds hg hM hl hu n x).1⟩
  have hN : ∀ N : ℕ, limsup (fun n => rate g n x) atTop ≤
      lowerRate g x+ε+M*β (N+1) x := by
    intro N
    have hz : Tendsto (fun n : ℕ => ((N+1:ℕ):ℝ)/n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have ht : Tendsto (fun n => lowerRate g x+ε+M*(ergodicAverage T (badBlockIndicator g ε (N+1)) n x+((N+1:ℕ):ℝ)/n))
        atTop (𝓝 (lowerRate g x+ε+M*(β (N+1) x+0))) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul ((hx (N+1)).add hz))
    have hb : ∀ᶠ n : ℕ in atTop, rate g n x ≤ lowerRate g x+ε+
        M*(ergodicAverage T (badBlockIndicator g ε (N+1)) n x+((N+1:ℕ):ℝ)/n) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact orbit_block_bound hg hM hl hu x hxi hε (by omega) hn
    have hh := limsup_le_limsup hb hlo.isCobounded_le ht.isBoundedUnder_le
    rw [ht.limsup_eq] at hh
    simpa only [add_zero] using hh
  have hz := hx0.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun N => lowerRate g x+ε+M*β (N+1) x) atTop (𝓝 (lowerRate g x+ε)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hz)
  exact ge_of_tendsto' ht hN

lemma bounded_cocycle_convergence (hT : MeasurePreserving T μ μ)
    (hg : SubCocycle T g) (hm : ∀ n, Measurable (g n))
    {M : ℝ} (hM : 0 ≤ M) (hl : ∀ n x, -M*n ≤ g n x) (hu : ∀ n x, g n x ≤ 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n => rate g n x) atTop (𝓝 (lowerRate g x)) := by
  have hh : ∀ k : ℕ, ∀ᵐ x ∂μ, limsup (fun n => rate g n x) atTop ≤
      lowerRate g x+1/((k+1:ℕ):ℝ) := fun k =>
    bounded_cocycle_upper hT hg hm hM hl hu (by positivity)
  filter_upwards [ae_all_iff.mpr hh] with x hx
  have hz : Tendsto (fun k : ℕ => (1:ℝ)/((k+1:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hs : limsup (fun n => rate g n x) atTop ≤ lowerRate g x := by
    apply ge_of_tendsto' (show Tendsto (fun k => lowerRate g x+1/((k+1:ℕ):ℝ)) atTop (𝓝 (lowerRate g x)) from by
      simpa using tendsto_const_nhds.add hz)
    exact hx
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hs
    (isBoundedUnder_of ⟨0, fun n => (rate_bounds hg hM hl hu n x).2⟩)
    (isBoundedUnder_of ⟨-M, fun n => (rate_bounds hg hM hl hu n x).1⟩)

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BoundedCocycle

-- BEGIN COMPLETE MODULE ClippedLimits
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} {g : ℕ → Ω → ℝ}

noncomputable def clippedLimit (g : ℕ → Ω → ℝ) (M : ℕ) : Ω → ℝ :=
  lowerRate (SubCocycle.clipped g (M:ℝ))

lemma clipped_measurable (hm : ∀ n, Measurable (g n)) (M : ℝ) (n : ℕ) :
    Measurable (SubCocycle.clipped g M n) := (hm n).max measurable_const

lemma clippedLimit_measurable (hm : ∀ n, Measurable (g n)) (M : ℕ) :
    Measurable (clippedLimit g M) := measurable_lowerRate (clipped_measurable hm M)

omit [MeasurableSpace Ω] in
lemma clippedLimit_bounds (hg : SubCocycle T g) (hu : ∀ n x, g n x ≤ 0)
    (M : ℕ) (x : Ω) : -(M:ℝ) ≤ clippedLimit g M x ∧ clippedLimit g M x ≤ 0 :=
  lowerRate_bounds (hg.clipped_subCocycle M) (Nat.cast_nonneg M)
    (SubCocycle.clipped_lower _) (SubCocycle.clipped_nonpos hu (Nat.cast_nonneg M)) x

lemma clippedLimit_integrable (hg : SubCocycle T g) (hm : ∀ n, Measurable (g n))
    (hu : ∀ n x, g n x ≤ 0) (M : ℕ) : Integrable (clippedLimit g M) μ :=
  integrable_lowerRate (hg.clipped_subCocycle M) (clipped_measurable hm M)
    (Nat.cast_nonneg M) (SubCocycle.clipped_lower _) (SubCocycle.clipped_nonpos hu (Nat.cast_nonneg M))

lemma clippedLimit_convergence (hT : MeasurePreserving T μ μ) (hg : SubCocycle T g)
    (hm : ∀ n, Measurable (g n)) (hu : ∀ n x, g n x ≤ 0) (M : ℕ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => rate (SubCocycle.clipped g (M:ℝ)) n x) atTop (𝓝 (clippedLimit g M x)) :=
  bounded_cocycle_convergence hT (hg.clipped_subCocycle M) (clipped_measurable hm M)
    (Nat.cast_nonneg M) (SubCocycle.clipped_lower _) (SubCocycle.clipped_nonpos hu (Nat.cast_nonneg M))

lemma integral_clippedLimit_lower (hT : MeasurePreserving T μ μ) (hg : SubCocycle T g)
    (hm : ∀ n, Measurable (g n)) (hi : ∀ n, Integrable (g n) μ)
    (hu : ∀ n x, g n x ≤ 0) {C : ℝ}
    (hC : ∀ n : ℕ, 0<n → -C*(n:ℝ) ≤ ∫ x,g n x ∂μ) (M : ℕ) :
    -C ≤ ∫ x,clippedLimit g M x ∂μ := by
  have hc := hg.clipped_subCocycle (M:ℝ)
  have hb := rate_bounds hc (Nat.cast_nonneg M) (SubCocycle.clipped_lower (g:=g) (M:ℝ))
    (SubCocycle.clipped_nonpos hu (Nat.cast_nonneg M))
  have hd := tendsto_integral_of_dominated_convergence (μ:=μ) (fun _ : Ω => (M:ℝ))
    (fun n => ((clipped_measurable hm M n).div_const n).aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall fun x => by
      change |rate (SubCocycle.clipped g (M:ℝ)) n x| ≤ (M:ℝ)
      rw [abs_of_nonpos (hb n x).2]
      linarith [(hb n x).1]) (clippedLimit_convergence hT hg hm hu M)
  apply ge_of_tendsto hd
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hr : Integrable (fun x => rate (SubCocycle.clipped g (M:ℝ)) n x) μ :=
    ((hi n).sup (integrable_const _)).div_const n
  have hh := integral_mono ((hi n).div_const n) hr (fun x =>
    div_le_div_of_nonneg_right (le_max_left (g n x) (-(M:ℝ)*n)) hn'.le)
  rw [integral_div] at hh
  exact ((le_div_iff₀ hn').mpr (hC n hn)).trans hh

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE ClippedLimits

-- BEGIN COMPLETE MODULE NonStuckLimits
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma ae_exists_above_floor {f : ℕ → Ω → ℝ} {C : ℝ}
    (hm : ∀ n, Measurable (f n)) (hi : ∀ n, Integrable (f n) μ)
    (hb : ∀ (n : ℕ) x, -(n:ℝ) ≤ f n x ∧ f n x ≤ 0)
    (hC : ∀ n, -C ≤ ∫ x,f n x ∂μ) :
    ∀ᵐ x ∂μ, ∃ n : ℕ, -(n:ℝ) < f n x := by
  let E : Set Ω := {x | ∀ n, f n x = -(n:ℝ)}
  have hE : MeasurableSet E := by
    simp only [E,Set.ofPred_forall]
    exact MeasurableSet.iInter fun n => measurableSet_eq_fun (hm n) measurable_const
  have hbound (n : ℕ) : (n:ℝ) * μ.real E ≤ C := by
    have hle : ∀ x, E.indicator (fun _ => (n:ℝ)) x ≤ -f n x := by
      intro x
      by_cases hx : x ∈ E
      · simp only [Set.indicator_of_mem hx]
        rw [hx n]
        simp
      · simp only [Set.indicator_of_notMem hx]
        exact neg_nonneg.mpr (hb n x).2
    have hh := integral_mono ((integrable_const (n:ℝ)).indicator hE) (hi n).neg hle
    simp only [Pi.neg_apply] at hh
    rw [integral_indicator_const _ hE,integral_neg] at hh
    simp only [smul_eq_mul] at hh
    nlinarith [hC n]
  have hz : μ.real E = 0 := by
    by_contra hn
    have hp : 0 < μ.real E := lt_of_le_of_ne (measureReal_nonneg) (Ne.symm hn)
    obtain ⟨n,hn⟩ := exists_nat_gt (C / μ.real E)
    have := (div_lt_iff₀ hp).mp hn
    linarith [hbound n]
  have hae : ∀ᵐ x ∂μ, x ∉ E := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using (measureReal_eq_zero_iff).mp hz
  filter_upwards [hae] with x hx
  simp only [E,Set.mem_ofPred_eq,not_forall] at hx
  obtain ⟨n,hn⟩ := hx
  exact ⟨n,lt_of_le_of_ne (hb n x).1 (Ne.symm hn)⟩

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE NonStuckLimits

-- BEGIN COMPLETE MODULE UnclippedConvergence
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

lemma tendsto_of_clipped {a : ℕ → ℝ} {M z : ℝ}
    (ht : Tendsto (fun n => max (a n) (-M)) atTop (𝓝 z)) (hz : -M < z) :
    Tendsto a atTop (𝓝 z) := by
  have he := ht.eventually (eventually_gt_nhds hz)
  apply ht.congr'
  filter_upwards [he] with n hn
  have ha : -M ≤ a n := by
    by_contra h
    rw [max_eq_right (le_of_not_ge h)] at hn
    exact (lt_irrefl _ hn)
  exact max_eq_left ha

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} {g : ℕ → Ω → ℝ}

lemma nonpositive_cocycle_convergence (hT : MeasurePreserving T μ μ)
    (hg : SubCocycle T g) (hm : ∀ n, Measurable (g n))
    (hi : ∀ n, Integrable (g n) μ) (hu : ∀ n x, g n x ≤ 0) {C : ℝ}
    (hC : ∀ n : ℕ, 0<n → -C*(n:ℝ) ≤ ∫ x,g n x ∂μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => rate g n x) atTop (𝓝 (lowerRate g x)) := by
  have he := ae_exists_above_floor (clippedLimit_measurable hm)
    (clippedLimit_integrable hg hm hu) (clippedLimit_bounds hg hu)
    (integral_clippedLimit_lower hT hg hm hi hu hC)
  have hc := ae_all_iff.mpr (clippedLimit_convergence hT hg hm hu)
  filter_upwards [he,hc] with x hx hconv
  obtain ⟨M,hM⟩ := hx
  have ht : Tendsto (fun n => max (rate g n x) (-(M:ℝ))) atTop
      (𝓝 (clippedLimit g M x)) := by
    apply (hconv M).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    dsimp [rate,SubCocycle.clipped]
    rw [← max_div_div_right hn'.le]
    congr 1
    field_simp
  have hh := tendsto_of_clipped ht hM
  have hl : lowerRate g x = clippedLimit g M x := hh.liminf_eq
  simpa only [hl] using hh

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE UnclippedConvergence

-- BEGIN COMPLETE MODULE FatouL1Bound
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma fatou_L1_bound {u : ℕ → Ω → ℝ} {f : Ω → ℝ} {C : ℝ} (hC : 0≤C)
    (hu : ∀ n, Integrable (u n) μ) (hf : Measurable f)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n=>u n ω) atTop (𝓝 (f ω)))
    (hb : ∀ n, (∫ ω,|u n ω| ∂μ)≤C) : Integrable f μ ∧ (∫ ω,|f ω| ∂μ)≤C := by
  have he : (∫⁻ ω,‖f ω‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    have hlim : (∫⁻ ω,‖f ω‖ₑ ∂μ) = ∫⁻ ω,liminf (fun n=>‖u n ω‖ₑ) atTop ∂μ :=
      lintegral_congr_ae (ht.mono fun ω hω=>hω.enorm.liminf_eq.symm)
    rw [hlim]
    apply (lintegral_liminf_le' (fun n=>(hu n).aestronglyMeasurable.aemeasurable.enorm)).trans
    apply liminf_le_of_frequently_le' (Frequently.of_forall fun n=> ?_)
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hu n)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hb n)
  have hfi : Integrable f μ := ⟨hf.aestronglyMeasurable,he.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hfi,?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfi] at he
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (by simpa only [Real.norm_eq_abs] using he)

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE FatouL1Bound

-- BEGIN COMPLETE MODULE NonpositiveIntegrability
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} {g : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
lemma integral_abs_rate_bound (hg : SubCocycle T g) (_hi : ∀ n, Integrable (g n) μ)
    (hu : ∀ n x, g n x ≤ 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n : ℕ, 0<n → -C*(n:ℝ) ≤ ∫ x,g n x ∂μ) (n : ℕ) :
    (∫ x, |rate g n x| ∂μ) ≤ C := by
  by_cases hn : n=0
  · subst n
    simpa [rate,hg.zero] using hC0
  have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : (fun x => |rate g n x|) = fun x => -(g n x / n) := by
    funext x
    exact abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (hu n x) hn'.le)
  rw [he,integral_neg,integral_div]
  have := (le_div_iff₀ hn').mpr (hC n (Nat.pos_of_ne_zero hn))
  linarith

lemma nonpositive_limit_integrable (hT : MeasurePreserving T μ μ)
    (hg : SubCocycle T g) (hm : ∀ n, Measurable (g n))
    (hi : ∀ n, Integrable (g n) μ) (hu : ∀ n x, g n x ≤ 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n : ℕ, 0<n → -C*(n:ℝ) ≤ ∫ x,g n x ∂μ) :
    Integrable (lowerRate g) μ ∧ (∫ x,|lowerRate g x| ∂μ) ≤ C :=
  fatou_L1_bound hC0 (fun n => (hi n).div_const n) (measurable_lowerRate hm)
    (nonpositive_cocycle_convergence hT hg hm hi hu hC)
    (integral_abs_rate_bound hg hi hu hC0 hC)

lemma nonpositive_limit_nonpos (hT : MeasurePreserving T μ μ)
    (hg : SubCocycle T g) (hm : ∀ n, Measurable (g n))
    (hi : ∀ n, Integrable (g n) μ) (hu : ∀ n x, g n x ≤ 0) {C : ℝ}
    (hC : ∀ n : ℕ, 0<n → -C*(n:ℝ) ≤ ∫ x,g n x ∂μ) :
    ∀ᵐ x ∂μ, lowerRate g x ≤ 0 := by
  filter_upwards [nonpositive_cocycle_convergence hT hg hm hi hu hC] with x hx
  exact le_of_tendsto hx (Eventually.of_forall fun n =>
    div_nonpos_of_nonpos_of_nonneg (hu n x) (Nat.cast_nonneg n))

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE NonpositiveIntegrability

-- BEGIN COMPLETE MODULE MaximalL1Bound
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

omit [MeasurableSpace Ω] in
lemma average_abs_le (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    |ergodicAverage T f n ω| ≤ ergodicAverage T (fun x=>|f x|) n ω := by
  unfold ergodicAverage birkhoffSum
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr (Nat.cast_nonneg n))

omit [MeasurableSpace Ω] in
lemma average_sub (T : Ω → Ω) (f g : Ω → ℝ) (n : ℕ) (ω : Ω) :
    ergodicAverage T (fun x=>f x-g x) n ω = ergodicAverage T f n ω-ergodicAverage T g n ω := by
  simp [ergodicAverage,birkhoffSum,Finset.sum_sub_distrib,mul_sub]

lemma maximalL1_bound (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {a : ℝ} (ha : 0<a) :
    μ {ω | ∃ n, a < |ergodicAverage T f n ω|} ≤ ENNReal.ofReal ((∫ ω,|f ω| ∂μ)/a) := by
  let E := maximalEvent T (fun ω=>|f ω|-a)
  have hm : MeasurableSet E := maximalEvent_measurable hT.measurable (hf.abs.sub measurable_const)
  have hh := hopf_maximal hT (hf.abs.sub measurable_const) (hi.abs.sub (integrable_const a))
  change 0 ≤ ∫ ω in E, |f ω|-a ∂μ at hh
  rw [integral_sub hi.abs.integrableOn (integrable_const a)] at hh
  simp only [setIntegral_const,smul_eq_mul] at hh
  have hb : (∫ ω in E, |f ω| ∂μ) ≤ ∫ ω,|f ω| ∂μ :=
    setIntegral_le_integral hi.abs (ae_of_all _ fun ω => abs_nonneg _) 
  have he : μ.real E ≤ (∫ ω,|f ω| ∂μ)/a := by
    rw [le_div_iff₀ ha]
    linarith
  apply le_trans (measure_mono ?_) ((ENNReal.toReal_le_toReal (measure_ne_top μ E) ENNReal.ofReal_ne_top).mp ?_)
  · intro ω hω
    obtain ⟨n,hn⟩ := hω
    have hn0 : n≠0 := by intro h; simp [h,ergodicAverage] at hn; linarith
    have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hs := average_sub_invariant (T:=T) (fun x=>|f x|) (fun _=>a) (fun _=>rfl) hn0 ω
    have hp : 0<ergodicAverage T (fun x=>|f x|-a) n ω := by
      linarith [average_abs_le T f n ω]
    exact ⟨n,(mul_pos_iff.mp hp).resolve_right (by intro h; exact (inv_pos.mpr hn').not_gt h.1) |>.2⟩
  · rw [ENNReal.toReal_ofReal (div_nonneg (integral_nonneg fun ω=>abs_nonneg _) ha.le)]
    exact he

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE MaximalL1Bound

-- BEGIN COMPLETE MODULE BoundedTruncation
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def boundedTruncation (f : Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ := max (-(N:ℝ)) (min (N:ℝ) (f ω))

lemma truncation_measurable {f : Ω → ℝ} (hf : Measurable f) (N : ℕ) :
    Measurable (boundedTruncation f N) := measurable_const.max (measurable_const.min hf)

lemma truncation_integrable {f : Ω → ℝ} (hf : Integrable f μ) (N : ℕ) :
    Integrable (boundedTruncation f N) μ := (integrable_const _).sup ((integrable_const _).inf hf)

omit [MeasurableSpace Ω] in
lemma truncation_abs_bound (f : Ω → ℝ) (N : ℕ) (ω : Ω) : |boundedTruncation f N ω|≤N := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith [Nat.cast_nonneg (α:=ℝ) N]) (min_le_left _ _)

omit [MeasurableSpace Ω] in
lemma truncation_error_bound (f : Ω → ℝ) (N : ℕ) (ω : Ω) :
    |f ω-boundedTruncation f N ω|≤|f ω| := by
  unfold boundedTruncation
  have hN : (0:ℝ)≤N := Nat.cast_nonneg _
  have hf := le_abs_self (f ω)
  have hf' := neg_abs_le (f ω)
  simp only [max_def,min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

omit [MeasurableSpace Ω] in
lemma truncation_tendsto (f : Ω → ℝ) (ω : Ω) :
    Tendsto (fun N=>boundedTruncation f N ω) atTop (𝓝 (f ω)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop |f ω|)] with N hN
  dsimp [boundedTruncation]
  rw [min_eq_right (le_abs_self _ |>.trans hN),max_eq_right (by linarith [neg_abs_le (f ω)])]

omit [IsProbabilityMeasure μ] in
lemma truncation_L1_tendsto {f : Ω → ℝ} (hf : Measurable f) (hi : Integrable f μ) :
    Tendsto (fun N=>∫ ω,|f ω-boundedTruncation f N ω| ∂μ) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence (μ:=μ) (fun ω=>|f ω|)
    (fun N=>(hf.sub (truncation_measurable hf N)).abs.aestronglyMeasurable) hi.abs
    (fun N=>ae_of_all _ fun ω=>by simpa only [Real.norm_eq_abs,abs_abs,Pi.sub_apply] using truncation_error_bound f N ω)
    (ae_of_all _ fun ω=>by simpa using (tendsto_const_nhds.sub (truncation_tendsto f ω)).abs)
  simpa using ht

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BoundedTruncation

-- BEGIN COMPLETE MODULE OscillationTransfer
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*}

def oscillationEvent (u : ℕ → Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω | ∀ N : ℕ, ∃ m≥N, ∃ n≥N, ε ≤ |u m ω-u n ω|}

lemma oscillation_subset (u v : ℕ → Ω → ℝ) (ξ : Ω → ℝ) {ε : ℝ} (hε : 0<ε) :
    oscillationEvent u ε ⊆ {ω | ¬ Tendsto (fun n=>v n ω) atTop (𝓝 (ξ ω))} ∪
      {ω | ∃ n, ε/4 < |u n ω-v n ω|} := by
  intro ω hω
  by_cases hv : Tendsto (fun n=>v n ω) atTop (𝓝 (ξ ω))
  · apply Or.inr
    by_contra he
    change ¬ ∃ n, ε/4 < |u n ω-v n ω| at he
    push Not at he
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hv.cauchySeq (ε/2) (by positivity)
    obtain ⟨m,hm,n,hn,hbig⟩ := hω N
    have hsmall := hN m hm n hn
    rw [Real.dist_eq] at hsmall
    have hh : |u m ω-u n ω| ≤ |u m ω-v m ω|+|v m ω-v n ω|+|u n ω-v n ω| := by
      calc
        _ = |(u m ω-v m ω)+(v m ω-v n ω)-(u n ω-v n ω)| := by congr 1; ring
        _ ≤ |(u m ω-v m ω)+(v m ω-v n ω)|+|u n ω-v n ω| := abs_sub ((u m ω-v m ω)+(v m ω-v n ω)) (u n ω-v n ω)
        _ ≤ _ := by linarith [abs_add_le (u m ω-v m ω) (v m ω-v n ω)]
    linarith [he m,he n]
  · exact Or.inl hv

lemma cauchy_of_not_oscillation (u : ℕ → ℝ)
    (h : ∀ k : ℕ, ¬ ∀ N : ℕ, ∃ m≥N, ∃ n≥N, (1:ℝ)/(k+1) ≤ |u m-u n|) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  have hh := h k
  push Not at hh
  obtain ⟨N,hN⟩ := hh
  exact ⟨N,fun m hm n hn => by rw [Real.dist_eq]; exact (hN m hm n hn).trans hk⟩

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE OscillationTransfer

-- BEGIN COMPLETE MODULE BirkhoffAECauchy
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

lemma average_oscillation_null (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {ε : ℝ} (hε : 0<ε) :
    μ (oscillationEvent (ergodicAverage T f) ε)=0 := by
  have hb (N : ℕ) : μ (oscillationEvent (ergodicAverage T f) ε) ≤
      ENNReal.ofReal ((∫ ω,|f ω-boundedTruncation f N ω| ∂μ)/(ε/4)) := by
    obtain ⟨ξ,_,_,hξ,_,_⟩ := bounded_birkhoff_convergence hT
      (truncation_measurable hf N) (truncation_integrable hi N) (Nat.cast_nonneg N)
      (truncation_abs_bound f N)
    have hs := oscillation_subset (ergodicAverage T f)
      (ergodicAverage T (boundedTruncation f N)) ξ hε
    have hn : μ {ω | ¬ Tendsto (fun n=>ergodicAverage T (boundedTruncation f N) n ω) atTop (𝓝 (ξ ω))}=0 :=
      ae_iff.mp hξ
    have hm := maximalL1_bound hT (hf.sub (truncation_measurable hf N))
      (hi.sub (truncation_integrable hi N)) (show 0<ε/4 by positivity)
    change μ {ω | ∃ n, ε/4 < |ergodicAverage T (fun x=>f x-boundedTruncation f N x) n ω|} ≤ _ at hm
    simp only [average_sub,Pi.sub_apply] at hm
    exact (measure_mono hs).trans ((measure_union_le _ _).trans (by simpa only [hn,zero_add] using hm))
  have ht : Tendsto (fun N => ENNReal.ofReal ((∫ ω,|f ω-boundedTruncation f N ω| ∂μ)/(ε/4))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_div,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((truncation_L1_tendsto hf hi).div_const (ε/4))
  exact le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) (bot_le)

lemma birkhoff_ae_cauchy (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ ω ∂μ, CauchySeq (fun n=>ergodicAverage T f n ω) := by
  have hh (k : ℕ) : ∀ᵐ ω ∂μ, ω ∉ oscillationEvent (ergodicAverage T f) ((1:ℝ)/(k+1)) := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using average_oscillation_null hT hf hi (show (0:ℝ)<1/(k+1) by positivity)
  filter_upwards [ae_all_iff.mpr hh] with ω hω
  exact cauchy_of_not_oscillation _ hω

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BirkhoffAECauchy

-- BEGIN COMPLETE MODULE AverageL1Contraction
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

lemma average_L1_bound (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) (n : ℕ) :
    (∫ ω,|ergodicAverage T f n ω| ∂μ) ≤ ∫ ω,|f ω| ∂μ := by
  by_cases hn : n=0
  · subst n
    simpa [ergodicAverage] using integral_nonneg (μ:=μ) (fun ω=>abs_nonneg (f ω))
  have h := integral_mono (average_integrable hT hi n).abs
    (average_integrable hT hi.abs n) (average_abs_le T f n)
  have he := integral_average hT hf.abs hi.abs hn
  change (∫ ω,ergodicAverage T (fun x=>|f x|) n ω ∂μ) = ∫ ω,|f ω| ∂μ at he
  exact h.trans_eq he

lemma average_L1_difference_bound (hT : MeasurePreserving T μ μ) {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hi : Integrable f μ) (hj : Integrable g μ) (n : ℕ) :
    (∫ ω,|ergodicAverage T f n ω-ergodicAverage T g n ω| ∂μ) ≤ ∫ ω,|f ω-g ω| ∂μ := by
  have h := average_L1_bound hT (hf.sub hg) (hi.sub hj) n
  change (∫ ω,|ergodicAverage T (fun x=>f x-g x) n ω| ∂μ) ≤ ∫ ω,|f ω-g ω| ∂μ at h
  simpa only [average_sub] using h

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE AverageL1Contraction

-- BEGIN COMPLETE MODULE BirkhoffLimit
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

lemma birkhoff_ae_tendsto (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n=>ergodicAverage T f n ω) atTop (𝓝 (upperAverage T f ω)) := by
  filter_upwards [birkhoff_ae_cauchy hT hf hi] with ω hω
  obtain ⟨c,hc⟩ := cauchySeq_tendsto_of_complete hω
  simpa only [upperAverage,hc.limsup_eq] using hc

lemma birkhoff_limit_integrable (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) : Integrable (upperAverage T f) μ :=
  (fatou_L1_bound (integral_nonneg fun ω=>abs_nonneg (f ω))
    (average_integrable hT hi) (upperAverage_measurable hT.measurable hf)
    (birkhoff_ae_tendsto hT hf hi) (average_L1_bound hT hf hi)).1

lemma birkhoff_limit_L1_difference (hT : MeasurePreserving T μ μ) {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hi : Integrable f μ) (hj : Integrable g μ) :
    (∫ ω,|upperAverage T f ω-upperAverage T g ω| ∂μ) ≤ ∫ ω,|f ω-g ω| ∂μ := by
  apply (fatou_L1_bound (integral_nonneg fun ω=>abs_nonneg (f ω-g ω))
    (fun n=>(average_integrable hT hi n).sub (average_integrable hT hj n))
    ((upperAverage_measurable hT.measurable hf).sub (upperAverage_measurable hT.measurable hg))
    ?_ (average_L1_difference_bound hT hf hg hi hj)).2
  filter_upwards [birkhoff_ae_tendsto hT hf hi,birkhoff_ae_tendsto hT hg hj] with ω h1 h2
  exact h1.sub h2

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BirkhoffLimit

-- BEGIN COMPLETE MODULE BirkhoffL1Convergence
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

lemma bounded_average_L1_tendsto (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) {B : ℝ} (hB : 0≤B)
    (hb : ∀ ω,|f ω|≤B) :
    Tendsto (fun n=>∫ ω,|ergodicAverage T f n ω-upperAverage T f ω| ∂μ) atTop (𝓝 0) := by
  obtain ⟨ξ,_,_,hξ,hl,_⟩ := bounded_birkhoff_convergence hT hf hi hB hb
  have he : upperAverage T f =ᵐ[μ] ξ := by
    filter_upwards [birkhoff_ae_tendsto hT hf hi,hξ] with ω h1 h2
    exact tendsto_nhds_unique h1 h2
  apply hl.congr
  intro n
  exact integral_congr_ae (he.mono fun ω hω=>by dsimp only; rw [hω])

lemma birkhoff_L1_tendsto (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) :
    Tendsto (fun n=>∫ ω,|ergodicAverage T f n ω-upperAverage T f ω| ∂μ) atTop (𝓝 0) := by
  have hξ := birkhoff_limit_integrable hT hf hi
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := ((truncation_L1_tendsto hf hi).eventually (gt_mem_nhds (show 0<ε/4 by positivity))).exists
  let g := boundedTruncation f N
  have hg : Measurable g := truncation_measurable hf N
  have hj : Integrable g μ := truncation_integrable hi N
  have hη := birkhoff_limit_integrable hT hg hj
  have hgL := bounded_average_L1_tendsto hT hg hj (Nat.cast_nonneg N) (truncation_abs_bound f N)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hgL.eventually (gt_mem_nhds (show 0<ε/2 by positivity)))
  refine ⟨M,fun n hn=>?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun ω=>abs_nonneg _)]
  have hb : (∫ ω,|ergodicAverage T f n ω-upperAverage T f ω| ∂μ) ≤
      (∫ ω,|ergodicAverage T f n ω-ergodicAverage T g n ω| ∂μ)+
      (∫ ω,|ergodicAverage T g n ω-upperAverage T g ω| ∂μ)+
      ∫ ω,|upperAverage T f ω-upperAverage T g ω| ∂μ := by
    have hA : Integrable (fun ω=>|ergodicAverage T f n ω-ergodicAverage T g n ω|) μ :=
      ((average_integrable hT hi n).sub (average_integrable hT hj n)).abs
    have hB : Integrable (fun ω=>|ergodicAverage T g n ω-upperAverage T g ω|) μ :=
      ((average_integrable hT hj n).sub hη).abs
    have hC : Integrable (fun ω=>|upperAverage T f ω-upperAverage T g ω|) μ := (hξ.sub hη).abs
    have hAB : Integrable (fun ω=>|ergodicAverage T f n ω-ergodicAverage T g n ω|+|ergodicAverage T g n ω-upperAverage T g ω|) μ := hA.add hB
    rw [← integral_add hA hB,← integral_add hAB hC]
    have hm := integral_mono ((average_integrable hT hi n).sub hξ).abs
      ((hA.add hB).add hC) (fun ω => ?_)
    · simpa only [Pi.add_apply,Pi.abs_apply,Pi.sub_apply] using hm
    · dsimp only [Pi.add_apply,Pi.sub_apply]
      have hh1 := abs_sub_le (ergodicAverage T f n ω) (ergodicAverage T g n ω) (upperAverage T f ω)
      have hh2 := abs_sub_le (ergodicAverage T g n ω) (upperAverage T g ω) (upperAverage T f ω)
      rw [abs_sub_comm (upperAverage T g ω) (upperAverage T f ω)] at hh2
      linarith
  have h1 := average_L1_difference_bound hT hf hg hi hj n
  have h2 := birkhoff_limit_L1_difference hT hf hg hi hj
  have h3 := hM n hn
  change (∫ ω,|f ω-g ω| ∂μ)<ε/4 at hN
  linarith

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BirkhoffL1Convergence

-- BEGIN COMPLETE MODULE BirkhoffConvergence
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω}

lemma birkhoff_convergence (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) :
    ∃ ξ : Ω → ℝ, Measurable ξ ∧ Integrable ξ μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n=>ergodicAverage T f n ω) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun n=>∫ ω,|ergodicAverage T f n ω-ξ ω| ∂μ) atTop (𝓝 0) ∧
      (∫ ω,ξ ω ∂μ) = ∫ ω,f ω ∂μ := by
  have hξ := birkhoff_limit_integrable hT hf hi
  have hl := birkhoff_L1_tendsto hT hf hi
  refine ⟨upperAverage T f,upperAverage_measurable hT.measurable hf,hξ,
    birkhoff_ae_tendsto hT hf hi,hl,?_⟩
  have hb : |(∫ ω,f ω ∂μ)-(∫ ω,upperAverage T f ω ∂μ)|≤0 := by
    apply ge_of_tendsto hl
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← integral_average hT hf hi (Nat.ne_of_gt hn),← integral_sub (average_integrable hT hi n) hξ]
    exact abs_integral_le_integral_abs
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))).symm

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE BirkhoffConvergence

-- BEGIN COMPLETE MODULE FixedBlockMean
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} {g : ℕ → Ω → ℝ}

lemma fixed_block_mean_bound (hT : MeasurePreserving T μ μ)
    (hg : SubCocycle T g) (hm : ∀ n, Measurable (g n))
    (hi : ∀ n, Integrable (g n) μ) {ξ : Ω → ℝ} (hξ : Integrable ξ μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => rate g n x) atTop (𝓝 (ξ x)))
    {k : ℕ} (hk : 0<k) : (∫ x,ξ x ∂μ) ≤ (∫ x,g k x ∂μ) / k := by
  obtain ⟨z,hzm,hzi,hzt,hzl,hze⟩ := birkhoff_convergence (hT.iterate k) (hm k) (hi k)
  have hsub : Tendsto (fun n : ℕ => n*k) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hk) tendsto_id
  have he : ∀ᵐ x ∂μ, ξ x ≤ z x / k := by
    filter_upwards [ht,hzt] with x hx hz
    apply le_of_tendsto_of_tendsto (hx.comp hsub) (hz.div_const k)
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact fixed_block_rate hg hk hn x
  have hh := integral_mono_ae hξ (hzi.div_const k) he
  simpa only [integral_div,hze] using hh

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE FixedBlockMean

-- BEGIN COMPLETE MODULE CocycleMean
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : Ω → Ω} {g : ℕ → Ω → ℝ}

noncomputable def cocycleMeanInf (μ : Measure Ω) (g : ℕ → Ω → ℝ) : ℝ :=
  ⨅ k : {k : ℕ // 1 ≤ k}, (∫ x,g k x ∂μ) / k

lemma integral_subadditive (hT : MeasurePreserving T μ μ) (hg : SubCocycle T g)
    (hm : ∀ n, Measurable (g n)) (hi : ∀ n, Integrable (g n) μ) :
    Subadditive (fun n => ∫ x,g n x ∂μ) := by
  intro m n
  have hh := integral_mono (hi (m+n))
    ((hi m).add ((hT.iterate m).integrable_comp_of_integrable (hi n))) (hg.add_le m n)
  simp only [Pi.add_apply,Function.comp_apply] at hh
  have hcomp : Integrable (fun x => g n (T^[m] x)) μ :=
    (hT.iterate m).integrable_comp_of_integrable (hi n)
  rwa [integral_add (hi m) hcomp,
    integral_preserving (hT.iterate m) (hm n)] at hh

lemma mean_rates_bddBelow {C : ℝ} (hC0 : 0≤C)
    (hC : ∀ n : ℕ, 0<n → -C*(n:ℝ) ≤ ∫ x,g n x ∂μ) :
    BddBelow (Set.range (fun n : ℕ => (∫ x,g n x ∂μ) / n)) := by
  refine ⟨-C,?_⟩
  rintro _ ⟨n,rfl⟩
  by_cases hn : n=0
  · simp [hn,hC0]
  · have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
    exact (le_div_iff₀ hn').mpr (hC n (Nat.pos_of_ne_zero hn))

lemma meanInf_eq_fekete (h : Subadditive (fun n => ∫ x,g n x ∂μ)) :
    cocycleMeanInf μ g = h.lim := by
  rw [cocycleMeanInf,Subadditive.lim]
  change sInf (Set.range (fun k : {k : ℕ // 1 ≤ k} => (∫ x,g k x ∂μ) / k)) = _
  congr 1
  ext y
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨k.val,k.property,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    exact ⟨⟨k,hk⟩,rfl⟩

lemma mean_rates_tendsto (hT : MeasurePreserving T μ μ) (hg : SubCocycle T g)
    (hm : ∀ n, Measurable (g n)) (hi : ∀ n, Integrable (g n) μ) {C : ℝ} (hC0 : 0≤C)
    (hC : ∀ n : ℕ, 0<n → -C*(n:ℝ) ≤ ∫ x,g n x ∂μ) :
    Tendsto (fun n => ∫ x,rate g n x ∂μ) atTop (𝓝 (cocycleMeanInf μ g)) := by
  have hs := integral_subadditive hT hg hm hi
  simpa only [rate,integral_div,meanInf_eq_fekete hs] using hs.tendsto_lim (mean_rates_bddBelow hC0 hC)

lemma integral_limit_le_meanInf [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hg : SubCocycle T g)
    (hm : ∀ n, Measurable (g n)) (hi : ∀ n, Integrable (g n) μ)
    {ξ : Ω → ℝ} (hξ : Integrable ξ μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => rate g n x) atTop (𝓝 (ξ x))) :
    (∫ x,ξ x ∂μ) ≤ cocycleMeanInf μ g := by
  apply le_ciInf
  intro k
  exact fixed_block_mean_bound hT hg hm hi hξ ht (lt_of_lt_of_le Nat.zero_lt_one k.property)

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE CocycleMean

-- BEGIN COMPLETE MODULE NonpositiveScheffe
section

open MeasureTheory Filter
open scoped Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma nonpositive_max_integral_tendsto {u : ℕ → Ω → ℝ} {ξ : Ω → ℝ}
    (hu : ∀ n, Integrable (u n) μ) (hξ : Integrable ξ μ)
    (hn : ∀ n, ∀ᵐ ω ∂μ, u n ω≤0) (hξn : ∀ᵐ ω ∂μ, ξ ω≤0)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n=>u n ω) atTop (𝓝 (ξ ω))) :
    Tendsto (fun n=>∫ ω,max (u n ω) (ξ ω) ∂μ) atTop (𝓝 (∫ ω,ξ ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω=>|ξ ω|)
    (fun n=>(hu n).aestronglyMeasurable.sup hξ.aestronglyMeasurable) hξ.abs
  · intro n
    filter_upwards [hn n,hξn] with ω hω hω'
    change |max (u n ω) (ξ ω)|≤|ξ ω|
    rw [abs_of_nonpos (max_le hω hω'),abs_of_nonpos hω']
    exact neg_le_neg (le_max_right _ _)
  · filter_upwards [ht] with ω hω
    change Tendsto (fun n=>max (u n ω) (ξ ω)) atTop (𝓝 (ξ ω))
    simpa only [max_self] using hω.max (tendsto_const_nhds (x:=ξ ω))

lemma nonpositive_fatou {u : ℕ → Ω → ℝ} {ξ : Ω → ℝ} {l : ℝ}
    (hu : ∀ n, Integrable (u n) μ) (hξ : Integrable ξ μ)
    (hn : ∀ n, ∀ᵐ ω ∂μ, u n ω≤0) (hξn : ∀ᵐ ω ∂μ, ξ ω≤0)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n=>u n ω) atTop (𝓝 (ξ ω)))
    (hi : Tendsto (fun n=>∫ ω,u n ω ∂μ) atTop (𝓝 l)) : l≤∫ ω,ξ ω ∂μ := by
  apply le_of_tendsto_of_tendsto hi (nonpositive_max_integral_tendsto hu hξ hn hξn ht)
  exact Eventually.of_forall fun n=>integral_mono (hu n) ((hu n).sup hξ) (fun ω=>le_max_left _ _)

lemma nonpositive_scheffe {u : ℕ → Ω → ℝ} {ξ : Ω → ℝ} {l : ℝ}
    (hu : ∀ n, Integrable (u n) μ) (hξ : Integrable ξ μ)
    (hn : ∀ n, ∀ᵐ ω ∂μ, u n ω≤0) (hξn : ∀ᵐ ω ∂μ, ξ ω≤0)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n=>u n ω) atTop (𝓝 (ξ ω)))
    (hi : Tendsto (fun n=>∫ ω,u n ω ∂μ) atTop (𝓝 l))
    (hle : (∫ ω,ξ ω ∂μ)≤l) :
    (∫ ω,ξ ω ∂μ)=l ∧ Tendsto (fun n=>∫ ω,|u n ω-ξ ω| ∂μ) atTop (𝓝 0) := by
  have he : (∫ ω,ξ ω ∂μ)=l := le_antisymm hle (nonpositive_fatou hu hξ hn hξn ht hi)
  refine ⟨he,?_⟩
  have hm := nonpositive_max_integral_tendsto hu hξ hn hξn ht
  have hform (n : ℕ) : (∫ ω,|u n ω-ξ ω| ∂μ)=
      2*(∫ ω,max (u n ω) (ξ ω) ∂μ)-(∫ ω,u n ω ∂μ)-(∫ ω,ξ ω ∂μ) := by
    have hp (ω : Ω) : |u n ω-ξ ω|=2*max (u n ω) (ξ ω)-u n ω-ξ ω := by
      rcases le_total (u n ω) (ξ ω) with h|h
      · rw [max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [max_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
    simp only [hp]
    have hmax : Integrable (fun ω=>max (u n ω) (ξ ω)) μ := (hu n).sup hξ
    have hmul : Integrable (fun ω=>2*max (u n ω) (ξ ω)) μ := hmax.const_mul 2
    have hsub : Integrable (fun ω=>2*max (u n ω) (ξ ω)-u n ω) μ := hmul.sub (hu n)
    rw [integral_sub hsub hξ,integral_sub hmul (hu n),integral_const_mul]
  simp only [hform]
  have hz : 2*(∫ ω,ξ ω ∂μ)-l-(∫ ω,ξ ω ∂μ)=0 := by rw [he]; ring
  exact hz ▸ ((tendsto_const_nhds.mul hm).sub hi).sub_const (∫ ω,ξ ω ∂μ)

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE NonpositiveScheffe

-- BEGIN COMPLETE MODULE NonpositiveKingman
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} {g : ℕ → Ω → ℝ}

lemma nonpositive_kingman (hT : MeasurePreserving T μ μ) (hg : SubCocycle T g)
    (hm : ∀ n, Measurable (g n)) (hi : ∀ n, Integrable (g n) μ)
    (hu : ∀ n x, g n x ≤ 0) {C : ℝ} (hC0 : 0≤C)
    (hC : ∀ n : ℕ, 0<n → -C*(n:ℝ) ≤ ∫ x,g n x ∂μ) :
    Integrable (lowerRate g) μ ∧
    (∀ᵐ x ∂μ, Tendsto (fun n => rate g n x) atTop (𝓝 (lowerRate g x))) ∧
    Tendsto (fun n => ∫ x,|rate g n x-lowerRate g x| ∂μ) atTop (𝓝 0) ∧
    (∫ x,lowerRate g x ∂μ) = cocycleMeanInf μ g := by
  have hξ := (nonpositive_limit_integrable hT hg hm hi hu hC0 hC).1
  have ht := nonpositive_cocycle_convergence hT hg hm hi hu hC
  have hh := nonpositive_scheffe (fun n => (hi n).div_const n) hξ
    (fun n => Eventually.of_forall fun x => div_nonpos_of_nonpos_of_nonneg (hu n x) (Nat.cast_nonneg n))
    (nonpositive_limit_nonpos hT hg hm hi hu hC) ht (mean_rates_tendsto hT hg hm hi hC0 hC)
    (integral_limit_le_meanInf hT hg hm hi hξ ht)
  exact ⟨hξ,ht,hh.2,hh.1⟩

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE NonpositiveKingman

-- BEGIN COMPLETE MODULE NormalizedCocycle
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : Ω → Ω} {g : ℕ → Ω → ℝ}

lemma normalized_measurable (hT : Measurable T) (hm : ∀ n, Measurable (g n)) (n : ℕ) :
    Measurable (SubCocycle.normalized g T n) :=
  (hm n).sub (sum_measurable hT (hm 1) n)

lemma normalized_integrable (hT : MeasurePreserving T μ μ)
    (hi : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (SubCocycle.normalized g T n) μ := (hi n).sub (sum_integrable hT (hi 1) n)

lemma integral_normalized (hT : MeasurePreserving T μ μ)
    (hm : ∀ n, Measurable (g n)) (hi : ∀ n, Integrable (g n) μ) (n : ℕ) :
    (∫ x,SubCocycle.normalized g T n x ∂μ) = (∫ x,g n x ∂μ) - n*(∫ x,g 1 x ∂μ) := by
  unfold SubCocycle.normalized
  have hs : Integrable (fun x => ∑ i ∈ Finset.range n, g 1 (T^[i] x)) μ := sum_integrable hT (hi 1) n
  rw [integral_sub (hi n) hs]
  have hc (i : ℕ) : Integrable (fun x => g 1 (T^[i] x)) μ :=
    (hT.iterate i).integrable_comp_of_integrable (hi 1)
  rw [integral_finsetSum _ (fun i _ => hc i)]
  simp only [integral_preserving (hT.iterate _) (hm 1),Finset.sum_const,Finset.card_range,nsmul_eq_mul]

lemma normalized_mean_lower (hT : MeasurePreserving T μ μ)
    (hm : ∀ n, Measurable (g n)) (hi : ∀ n, Integrable (g n) μ) {C : ℝ}
    (hC : ∀ n : ℕ, 0<n → -C*(n:ℝ) ≤ ∫ x,g n x ∂μ) (n : ℕ) (hn : 0<n) :
    -(C+|∫ x,g 1 x ∂μ|)*(n:ℝ) ≤ ∫ x,SubCocycle.normalized g T n x ∂μ := by
  rw [integral_normalized hT hm hi]
  have hh := mul_le_mul_of_nonneg_right (le_abs_self (∫ x,g 1 x ∂μ)) (Nat.cast_nonneg n)
  nlinarith [hC n hn]

omit [MeasurableSpace Ω] in
lemma rate_normalized_add (n : ℕ) (x : Ω) :
    rate g n x = rate (SubCocycle.normalized g T) n x + ergodicAverage T (g 1) n x := by
  simp only [rate,SubCocycle.normalized,ergodicAverage,birkhoffSum]
  ring

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE NormalizedCocycle

-- BEGIN COMPLETE MODULE L1Sum
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma L1_sum_convergence {u v : ℕ → Ω → ℝ} {a b : Ω → ℝ}
    (hu : ∀ n, Integrable (u n) μ) (hv : ∀ n, Integrable (v n) μ)
    (ha : Integrable a μ) (hb : Integrable b μ)
    (htu : Tendsto (fun n => ∫ x,|u n x-a x| ∂μ) atTop (𝓝 0))
    (htv : Tendsto (fun n => ∫ x,|v n x-b x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,|u n x+v n x-(a x+b x)| ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg fun x => abs_nonneg _)
    (fun n => ?_) (by simpa using htu.add htv)
  have hiu : Integrable (fun x => |u n x-a x|) μ := ((hu n).sub ha).abs
  have hiv : Integrable (fun x => |v n x-b x|) μ := ((hv n).sub hb).abs
  rw [← integral_add hiu hiv]
  apply integral_mono (((hu n).add (hv n)).sub (ha.add hb)).abs (hiu.add hiv)
  intro x
  simpa only [Pi.add_apply,Pi.sub_apply,Pi.abs_apply] using
    (show |u n x+v n x-(a x+b x)| ≤ |u n x-a x|+|v n x-b x| by
      have he : u n x+v n x-(a x+b x) = (u n x-a x)+(v n x-b x) := by ring
      rw [he]
      exact abs_add_le _ _)

lemma integral_tendsto_of_L1 {u : ℕ → Ω → ℝ} {a : Ω → ℝ}
    (hu : ∀ n, Integrable (u n) μ) (ha : Integrable a μ)
    (ht : Tendsto (fun n => ∫ x,|u n x-a x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,u n x ∂μ) atTop (𝓝 (∫ x,a x ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) ht
  rw [← integral_sub (hu n) ha]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => u n x-a x)

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE L1Sum

-- BEGIN COMPLETE MODULE CocycleKingman
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} {g : ℕ → Ω → ℝ}

lemma cocycle_kingman (hT : MeasurePreserving T μ μ) (hg : SubCocycle T g)
    (hm : ∀ n, Measurable (g n)) (hi : ∀ n, Integrable (g n) μ) {C : ℝ} (hC0 : 0≤C)
    (hC : ∀ n : ℕ, 0<n → -C*(n:ℝ) ≤ ∫ x,g n x ∂μ) :
    ∃ ξ : Ω → ℝ, Measurable ξ ∧ Integrable ξ μ ∧
    (∀ᵐ x ∂μ, Tendsto (fun n => rate g n x) atTop (𝓝 (ξ x))) ∧
    Tendsto (fun n => ∫ x,|rate g n x-ξ x| ∂μ) atTop (𝓝 0) ∧
    (∫ x,ξ x ∂μ) = cocycleMeanInf μ g := by
  let h := SubCocycle.normalized g T
  have hhm : ∀ n, Measurable (h n) := normalized_measurable hT.measurable hm
  have hhi : ∀ n, Integrable (h n) μ := normalized_integrable hT hi
  obtain ⟨hη,hηt,hηl,_⟩ := nonpositive_kingman hT hg.normalized_subCocycle hhm hhi
    hg.normalized_nonpos (add_nonneg hC0 (abs_nonneg _)) (normalized_mean_lower hT hm hi hC)
  obtain ⟨z,hzm,hzi,hzt,hzl,_⟩ := birkhoff_convergence hT (hm 1) (hi 1)
  let ξ := fun x => lowerRate h x+z x
  have hξm : Measurable ξ := (measurable_lowerRate hhm).add hzm
  have hξi : Integrable ξ μ := hη.add hzi
  have ht : ∀ᵐ x ∂μ, Tendsto (fun n => rate g n x) atTop (𝓝 (ξ x)) := by
    filter_upwards [hηt,hzt] with x hx hz
    change Tendsto (fun n => rate g n x) atTop (𝓝 (lowerRate h x+z x))
    simp only [rate_normalized_add (T:=T) (g:=g)]
    exact hx.add hz
  have hl : Tendsto (fun n => ∫ x,|rate g n x-ξ x| ∂μ) atTop (𝓝 0) := by
    have hh := L1_sum_convergence (u := fun n x => rate h n x)
      (fun n => (hhi n).div_const n) (average_integrable hT (hi 1)) hη hzi hηl hzl
    change Tendsto (fun n => ∫ x,|rate g n x-(lowerRate h x+z x)| ∂μ) atTop (𝓝 0)
    simp only [rate_normalized_add (T:=T) (g:=g)]
    exact hh
  have he := tendsto_nhds_unique (integral_tendsto_of_L1 (fun n => (hi n).div_const n) hξi hl)
    (mean_rates_tendsto hT hg hm hi hC0 hC)
  exact ⟨ξ,hξm,hξi,ht,hl,he⟩

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE CocycleKingman

-- BEGIN COMPLETE MODULE StationaryPath
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

noncomputable def goodPaths : Set (Interval → ℝ) :=
  {φ | ∀ s t u : ℕ, ∀ hst : s < t, ∀ htu : t < u,
    φ ⟨(s,u),hst.trans htu⟩ ≤ φ ⟨(s,t),hst⟩ + φ ⟨(t,u),htu⟩}

lemma goodPaths_measurable : MeasurableSet goodPaths := by
  unfold goodPaths
  simp only [Set.ofPred_forall]
  repeat' (apply MeasurableSet.iInter; intro)
  rename_i s t u hst htu
  exact measurableSet_le (measurable_pi_apply (⟨(s,u),hst.trans htu⟩ : Interval))
    ((measurable_pi_apply (⟨(s,t),hst⟩ : Interval)).add (measurable_pi_apply (⟨(t,u),htu⟩ : Interval)))

abbrev GoodPath := goodPaths

def goodShift (φ : GoodPath) : GoodPath :=
  ⟨shift φ, fun s t u hst htu => φ.property (s+1) (t+1) (u+1) (by omega) (by omega)⟩

lemma goodShift_measurable : Measurable goodShift := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro p
  exact (measurable_pi_apply _).comp measurable_subtype_coe

variable {Ω : Type*} [MeasurableSpace Ω] {x : ℕ → ℕ → Ω → ℝ}

def goodPathMap (hx : S1 x) (ω : Ω) : GoodPath :=
  ⟨path x ω,fun s t u hst htu => hx s t u ω hst htu⟩

lemma goodPathMap_measurable (hx : S1 x) (hm : ∀ s t, s<t → Measurable (x s t)) :
    Measurable (goodPathMap hx) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro p
  exact hm p.1.1 p.1.2 p.2

lemma goodShift_preserving {P : Measure Ω} (hx : S1 x)
    (hm : ∀ s t, s<t → Measurable (x s t)) (hs : S2 P x) :
    MeasurePreserving goodShift (P.map (goodPathMap hx)) (P.map (goodPathMap hx)) := by
  refine ⟨goodShift_measurable,?_⟩
  apply (MeasurableEmbedding.subtype_coe goodPaths_measurable).map_injective
  rw [Measure.map_map measurable_subtype_coe goodShift_measurable,
    Measure.map_map (measurable_subtype_coe.comp goodShift_measurable) (goodPathMap_measurable hx hm),
    Measure.map_map measurable_subtype_coe (goodPathMap_measurable hx hm)]
  exact hs

noncomputable def pathValue (n : ℕ) (φ : GoodPath) : ℝ :=
  if hn : 0 < n then φ.val ⟨(0,n),hn⟩ else 0

lemma pathValue_measurable (n : ℕ) : Measurable (pathValue n) := by
  unfold pathValue
  split_ifs
  · exact (measurable_pi_apply _).comp measurable_subtype_coe
  · exact measurable_const

lemma goodShift_iterate (n : ℕ) (φ : GoodPath) (p : Interval) :
    (goodShift^[n] φ).val p = φ.val ⟨(p.val.1+n,p.val.2+n),by omega⟩ := by
  induction n generalizing φ p with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    rw [ih]
    rfl

lemma pathValue_subCocycle : SubCocycle goodShift pathValue := by
  constructor
  · funext φ; simp [pathValue]
  · intro m n φ
    rcases m.eq_zero_or_pos with rfl | hm
    · simp [pathValue]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [pathValue]
    have hmn : 0 < m+n := by omega
    simp only [pathValue, dif_pos hm, dif_pos hn, dif_pos hmn]
    rw [goodShift_iterate]
    simpa only [zero_add, Nat.add_comm n m] using φ.property 0 m (m+n) hm (by omega)

omit [MeasurableSpace Ω] in
lemma pathValue_map (hx : S1 x) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    pathValue n (goodPathMap hx ω) = x 0 n ω := by
  simp [pathValue,hn,goodPathMap,path]

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE StationaryPath

-- BEGIN COMPLETE MODULE PathIntegrals
section

open MeasureTheory Filter Topology

namespace KingmanSubadditive.Ergodic.Proof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {x : ℕ → ℕ → Ω → ℝ}

lemma pathValue_integral (hx : S1 x) (hm : ∀ s t, s<t → Measurable (x s t))
    {n : ℕ} (hn : 0<n) :
    (∫ φ,pathValue n φ ∂(P.map (goodPathMap hx))) = ∫ ω,x 0 n ω ∂P := by
  rw [integral_map (goodPathMap_measurable hx hm).aemeasurable (pathValue_measurable n).aestronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall (pathValue_map hx hn))

lemma pathValue_integrable (hx : S1 x) (hm : ∀ s t, s<t → Measurable (x s t))
    (hi : ∀ n, 1≤n → Integrable (x 0 n) P) (n : ℕ) :
    Integrable (pathValue n) (P.map (goodPathMap hx)) := by
  by_cases hn : n=0
  · subst n
    change Integrable (0 : GoodPath → ℝ) (P.map (goodPathMap hx))
    exact integrable_zero _ _ _
  rw [integrable_map_measure (pathValue_measurable n).aestronglyMeasurable
    (goodPathMap_measurable hx hm).aemeasurable]
  simpa only [Function.comp_def,pathValue_map hx (Nat.pos_of_ne_zero hn)] using hi n (Nat.one_le_iff_ne_zero.mpr hn)

lemma path_meanInf_eq (hx : S1 x) (hm : ∀ s t, s<t → Measurable (x s t)) :
    cocycleMeanInf (P.map (goodPathMap hx)) pathValue = gamma P x := by
  unfold cocycleMeanInf gamma mean
  congr 1
  funext n
  rw [pathValue_integral hx hm (lt_of_lt_of_le Nat.zero_lt_one n.property)]

end KingmanSubadditive.Ergodic.Proof
end
-- END COMPLETE MODULE PathIntegrals

-- BEGIN COMPLETE MODULE KingmanRoot
section

namespace KingmanSubadditive.Ergodic

open MeasureTheory Filter Topology
open Proof

theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hx : IsSubadditiveProcess P x) :
    ∃ ξ : Ω → ℝ, Integrable ξ P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℕ => x 0 t ω / (t : ℝ)) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun t : ℕ => ∫ ω, |x 0 t ω / (t : ℝ) - ξ ω| ∂P) atTop (𝓝 0) ∧
      ∫ ω, ξ ω ∂P = gamma P x := by
  obtain ⟨hm,hs,hstat,hi,A,hA⟩ := hx
  let F := goodPathMap hs
  have hF : Measurable F := goodPathMap_measurable hs hm
  let μ := P.map F
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hF.aemeasurable
  have hμT : MeasurePreserving goodShift μ μ := goodShift_preserving hs hm hstat
  have hlow : ∀ n : ℕ, 0<n → -(max A 0)*(n:ℝ) ≤ ∫ φ,pathValue n φ ∂μ := by
    intro n hn
    rw [pathValue_integral hs hm hn]
    have hh := hA n (by omega)
    have hh' := mul_le_mul_of_nonneg_right (le_max_left A 0) (Nat.cast_nonneg n)
    dsimp [mean] at hh
    linarith
  obtain ⟨z,hzm,hzi,hzt,hzl,hze⟩ := cocycle_kingman hμT pathValue_subCocycle
    pathValue_measurable (pathValue_integrable hs hm hi) (le_max_right A 0) hlow
  let ξ := z ∘ F
  have hξ : Integrable ξ P :=
    (integrable_map_measure hzm.aestronglyMeasurable hF.aemeasurable).mp hzi
  refine ⟨ξ,hξ,?_,?_,?_⟩
  · filter_upwards [ae_of_ae_map hF.aemeasurable hzt] with ω hω
    apply hω.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    dsimp only [rate]
    rw [pathValue_map hs hn]
  · apply hzl.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    change (∫ φ, |pathValue n φ / n-z φ| ∂(P.map F)) = _
    have hmeas : AEStronglyMeasurable (fun φ => |pathValue n φ / n-z φ|) (P.map F) :=
      (((pathValue_measurable n).div_const n).sub hzm).abs.aestronglyMeasurable
    rw [integral_map hF.aemeasurable hmeas]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp only [rate]
      rw [pathValue_map hs hn]
      rfl
  · change (∫ ω,z (F ω) ∂P) = gamma P x
    rw [← integral_map hF.aemeasurable hzm.aestronglyMeasurable]
    exact hze.trans (path_meanInf_eq hs hm)

end KingmanSubadditive.Ergodic

open MeasureTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hx : KingmanSubadditive.Ergodic.IsSubadditiveProcess P x) :
    ∃ ξ : Ω → ℝ, Integrable ξ P ∧
      (∀ᵐ ω ∂P, Tendsto (fun t : ℕ => x 0 t ω / (t : ℝ)) atTop (𝓝 (ξ ω))) ∧
      Tendsto (fun t : ℕ => ∫ ω, |x 0 t ω / (t : ℝ) - ξ ω| ∂P) atTop (𝓝 0) ∧
      ∫ ω, ξ ω ∂P = KingmanSubadditive.Ergodic.gamma P x :=
  KingmanSubadditive.Ergodic.theorem_1 P x hx
end
-- END COMPLETE MODULE KingmanRoot
