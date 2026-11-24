-- Prove2me | solution 1 for Kyprianou.Ch02.levyPoissonPathActualMassLeRawTruncatedV1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T05:08:29.72983+00:00
-- url     : https://prove2.me/submissions/097521c4-06b0-47e2-be41-72229435baee

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_ae_mem_levySmallJumpGoodSet
import Theorems.Thm_ProbabilityTheory_tendsto_levyBandPath_levySmallJumpPath
import Theorems.Thm_ProbabilityTheory_levyTruncationSeq_spec
import Theorems.Thm_ProbabilityTheory_lintegral_poissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_poissonTruncatedMarkMassMeanV1
import Theorems.Thm_Kyprianou_Ch02_locallySummableTimeRepresentationActualJumpsV2
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

private noncomputable def rawTruncFun (N : ℕ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  if 0 < p.1 ∧ p.1 ≤ (N : ℝ) then ENNReal.ofReal (min (1 : ℝ) |p.2|) else 0

private lemma measurable_rawTruncFun (N : ℕ) : Measurable (rawTruncFun N) := by
  have hw : Measurable (fun x : ℝ => ENNReal.ofReal (min (1 : ℝ) |x|)) :=
    ENNReal.measurable_ofReal.comp (continuous_const.min continuous_abs).measurable
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const))
    (hw.comp measurable_snd) measurable_const

private def largeBand (N : ℕ) : Set (ℝ × ℝ) :=
  Set.Ioc 0 (N : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}

private lemma measurableSet_largeBand (N : ℕ) : MeasurableSet (largeBand N) :=
  measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable)

private lemma integrable_min_one_abs_of_lintegral_lt_top
    {ν : Measure ℝ}
    (hfinite : (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) < ⊤) :
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) ν := by
  refine ⟨(continuous_const.min continuous_abs).measurable.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have heq : (fun x : ℝ => ‖min (1 : ℝ) |x|‖ₑ) =
      fun x : ℝ => ENNReal.ofReal (min (1 : ℝ) |x|) := by
    funext x
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (le_min zero_le_one (abs_nonneg x))]
  rwa [heq]

private lemma ae_good_and_finite
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hν : IsLevyMeasure ν)
    (hfinite : (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) < ⊤) :
    ∀ᵐ ω ∂P, ω ∈ levySmallJumpGoodSet hd hν ∧
      (∀ N : ℕ, (∫⁻ p, rawTruncFun N p ∂(poissonRandomMeasure K Z ω)) < ⊤) ∧
      (∀ N : ℕ, poissonRandomMeasure K Z ω (largeBand N) < ⊤) := by
  have h1 : ∀ᵐ ω ∂P, ω ∈ levySmallJumpGoodSet hd hν :=
    ProbabilityTheory.ae_mem_levySmallJumpGoodSet hd hν
  have h2 : ∀ᵐ ω ∂P, ∀ N : ℕ, (∫⁻ p, rawTruncFun N p ∂(poissonRandomMeasure K Z ω)) < ⊤ := by
    rw [ae_all_iff]
    intro N
    have hmeas_sum : Measurable (fun ω : Ω =>
        ∑' k : ℕ, ∑ n ∈ Finset.range (K k ω), rawTruncFun N (Z k n ω)) := by
      refine Measurable.tsum fun k => ?_
      have hPk : Measurable (fun p : Ω × ℕ =>
          ∑ n ∈ Finset.range p.2, rawTruncFun N (Z k n p.1)) :=
        measurable_from_prod_countable_left fun j =>
          Finset.measurable_sum (Finset.range j) fun n _ =>
            (measurable_rawTruncFun N).comp (hd.measurable_point k n)
      exact hPk.comp (measurable_id.prodMk (hd.measurable_count k))
    have hmeas : Measurable (fun ω : Ω =>
        ∫⁻ p, rawTruncFun N p ∂(poissonRandomMeasure K Z ω)) := by
      convert hmeas_sum using 1
      funext ω
      exact ProbabilityTheory.lintegral_poissonRandomMeasure (measurable_rawTruncFun N) ω
    have hmean : (∫⁻ ω, ∫⁻ p, rawTruncFun N p ∂(poissonRandomMeasure K Z ω) ∂P) < ⊤ := by
      change (∫⁻ ω, ∫⁻ p : ℝ × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (N : ℝ) then ENNReal.ofReal (min (1 : ℝ) |p.2|)
        else 0 ∂(poissonRandomMeasure K Z ω) ∂P) < ⊤
      rw [Kyprianou.Ch02.poissonTruncatedMarkMassMeanV1 P ν K Z hd N]
      exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top N) hfinite
    exact ae_lt_top hmeas hmean.ne
  have h3 : ∀ᵐ ω ∂P, ∀ N : ℕ, poissonRandomMeasure K Z ω (largeBand N) < ⊤ := by
    rw [ae_all_iff]
    intro N
    exact ae_poissonRandomMeasure_apply_lt_top hd (measurableSet_largeBand N)
      (volume_prod_Ioc_prod_lt_top (hν.measure_setOf_abs_ge_lt_top one_pos))
  filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
  exact ⟨hω1, hω2, hω3⟩

private noncomputable def absMarkT {Ω : Type} (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (T : ℝ≥0) (ω : Ω) (q : ℕ × ℕ) : ℝ :=
  if q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ)
  then |(Z q.1 q.2 ω).2| else 0

private noncomputable def signedMarkT {Ω : Type} (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (T : ℝ≥0) (ω : Ω) (q : ℕ × ℕ) : ℝ :=
  if q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ)
  then (Z q.1 q.2 ω).2 else 0

private noncomputable def markAtTime {Ω : Type} (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (ω : Ω) (s : ℝ≥0) : ℝ :=
  if (0 : ℝ≥0) < s then
    ∑' q : ℕ × ℕ,
      if q.2 < K q.1 ω ∧ (Z q.1 q.2 ω).1 = (s : ℝ) then (Z q.1 q.2 ω).2 else 0
  else 0

private lemma tsum_prod_eq_lintegral_prm {Ω : Type} [MeasurableSpace Ω]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ) (ω : Ω)
    {G : ℝ × ℝ → ℝ≥0∞} (hG : Measurable G) :
    (∑' q : ℕ × ℕ, if q.2 < K q.1 ω then G (Z q.1 q.2 ω) else 0) =
      ∫⁻ p, G p ∂(poissonRandomMeasure K Z ω) := by
  rw [ENNReal.tsum_prod', ProbabilityTheory.lintegral_poissonRandomMeasure hG ω]
  refine tsum_congr fun k => ?_
  rw [tsum_eq_sum (s := Finset.range (K k ω)) fun n hn => by
    rw [if_neg (by simpa [Finset.mem_range] using hn)]]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos (by simpa [Finset.mem_range] using hn)]

private lemma summable_absMarkT {Ω : Type} [MeasurableSpace Ω]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ) (ω : Ω)
    (htrunc : ∀ N : ℕ, (∫⁻ p, rawTruncFun N p ∂(poissonRandomMeasure K Z ω)) < ⊤)
    (hlarge : ∀ N : ℕ, poissonRandomMeasure K Z ω (largeBand N) < ⊤)
    (T : ℝ≥0) :
    Summable (absMarkT K Z T ω) := by
  classical
  let N : ℕ := Nat.ceil (T : ℝ)
  have hTN : (T : ℝ) ≤ (N : ℝ) := Nat.le_ceil (T : ℝ)
  have htsum_trunc : (∑' q : ℕ × ℕ,
      if q.2 < K q.1 ω then rawTruncFun N (Z q.1 q.2 ω) else 0) < ⊤ := by
    rw [tsum_prod_eq_lintegral_prm K Z ω (measurable_rawTruncFun N)]
    exact htrunc N
  have hsum_trunc_real : Summable (fun q : ℕ × ℕ =>
      (if q.2 < K q.1 ω then rawTruncFun N (Z q.1 q.2 ω) else 0).toReal) :=
    ENNReal.summable_toReal htsum_trunc.ne
  let smallAbs : ℕ × ℕ → ℝ := fun q =>
    if q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧ |(Z q.1 q.2 ω).2| < 1
    then |(Z q.1 q.2 ω).2| else 0
  have hsmall : Summable smallAbs := by
    refine Summable.of_nonneg_of_le
      (fun q => by dsimp [smallAbs]; split_ifs <;> positivity) (fun q => ?_) hsum_trunc_real
    dsimp [smallAbs]
    by_cases hq : q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
        |(Z q.1 q.2 ω).2| < 1
    · rcases hq with ⟨hk, hpos, hleT, hlt1⟩
      have hleN : (Z q.1 q.2 ω).1 ≤ (N : ℝ) := hleT.trans hTN
      rw [if_pos ⟨hk, hpos, hleT, hlt1⟩, if_pos hk]
      dsimp [rawTruncFun]
      rw [if_pos ⟨hpos, hleN⟩, min_eq_right (le_of_lt hlt1), ENNReal.toReal_ofReal (abs_nonneg _)]
    · rw [if_neg hq]
      exact ENNReal.toReal_nonneg
  let indLarge : ℝ × ℝ → ℝ≥0∞ := (largeBand N).indicator 1
  have hindMeas : Measurable indLarge := measurable_const.indicator (measurableSet_largeBand N)
  have htsum_large : (∑' q : ℕ × ℕ,
      if q.2 < K q.1 ω then indLarge (Z q.1 q.2 ω) else 0) < ⊤ := by
    rw [tsum_prod_eq_lintegral_prm K Z ω hindMeas,
      lintegral_indicator_one (measurableSet_largeBand N)]
    exact hlarge N
  have hfin_N : {q : ℕ × ℕ | (1 : ℝ≥0∞) ≤
      if q.2 < K q.1 ω then indLarge (Z q.1 q.2 ω) else 0}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top htsum_large.ne one_ne_zero
  have hfin_T : {q : ℕ × ℕ |
      q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
        1 ≤ |(Z q.1 q.2 ω).2|}.Finite := by
    refine hfin_N.subset fun q hq => ?_
    rcases hq with ⟨hk, hpos, hleT, hge1⟩
    have hmem : Z q.1 q.2 ω ∈ largeBand N := ⟨⟨hpos, hleT.trans hTN⟩, hge1⟩
    simp [hk, indLarge, Set.indicator_of_mem hmem]
  let largeAbs : ℕ × ℕ → ℝ := fun q =>
    if q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧ 1 ≤ |(Z q.1 q.2 ω).2|
    then |(Z q.1 q.2 ω).2| else 0
  have hlarge_sum : Summable largeAbs := by
    refine summable_of_ne_finset_zero (s := hfin_T.toFinset) fun q hq => ?_
    have hnot : ¬ (q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
        1 ≤ |(Z q.1 q.2 ω).2|) := by
      simpa [hfin_T.mem_toFinset] using hq
    simp [largeAbs, hnot]
  refine (hsmall.add hlarge_sum).congr fun q => ?_
  dsimp [smallAbs, largeAbs, absMarkT]
  by_cases hbase : q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ)
  · rcases hbase with ⟨h1, h2, h3⟩
    by_cases hlt : |(Z q.1 q.2 ω).2| < 1
    · have hge : ¬ (1 ≤ |(Z q.1 q.2 ω).2|) := not_le.mpr hlt
      rw [if_pos ⟨h1, h2, h3, hlt⟩, if_neg (fun h => hge h.2.2.2), if_pos ⟨h1, h2, h3⟩, add_zero]
    · have hge : 1 ≤ |(Z q.1 q.2 ω).2| := le_of_not_gt hlt
      rw [if_neg (fun h => hlt h.2.2.2), if_pos ⟨h1, h2, h3, hge⟩, if_pos ⟨h1, h2, h3⟩, zero_add]
  · have hns : ¬ (q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
        |(Z q.1 q.2 ω).2| < 1) := fun h => hbase ⟨h.1, h.2.1, h.2.2.1⟩
    have hnl : ¬ (q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
        1 ≤ |(Z q.1 q.2 ω).2|) := fun h => hbase ⟨h.1, h.2.1, h.2.2.1⟩
    rw [if_neg hns, if_neg hnl, if_neg hbase, add_zero]

private lemma tsum_pieceSum_eq_tsum_prod {Ω : Type}
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ) (T : ℝ≥0) (ω : Ω)
    (habs : Summable (absMarkT K Z T ω))
    (F : ℝ × ℝ → ℝ)
    (hF : ∀ p : ℝ × ℝ, |F p| ≤ if 0 < p.1 ∧ p.1 ≤ (T : ℝ) then |p.2| else 0) :
    (∑' k : ℕ, pieceSum K Z F k ω) =
      ∑' q : ℕ × ℕ, if q.2 < K q.1 ω then F (Z q.1 q.2 ω) else 0 := by
  have hsum : Summable (fun q : ℕ × ℕ => if q.2 < K q.1 ω then F (Z q.1 q.2 ω) else 0) := by
    refine Summable.of_norm_bounded habs fun q => ?_
    rw [Real.norm_eq_abs]
    dsimp [absMarkT]
    by_cases hk : q.2 < K q.1 ω
    · rw [if_pos hk]
      have hFp := hF (Z q.1 q.2 ω)
      by_cases ht : 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ)
      · rw [if_pos ⟨hk, ht.1, ht.2⟩]; simpa [ht] using hFp
      · rw [if_neg (fun h => ht ⟨h.2.1, h.2.2⟩)]; simpa [ht] using hFp
    · rw [if_neg hk, abs_zero]
      split_ifs <;> positivity
  rw [hsum.tsum_prod]
  refine (tsum_congr fun k => ?_).symm
  rw [pieceSum, tsum_eq_sum (s := Finset.range (K k ω)) fun n hn => by
    rw [if_neg (by simpa [Finset.mem_range] using hn)]]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos (by simpa [Finset.mem_range] using hn)]

private lemma eventually_finset_forall {ι : Type} [DecidableEq ι]
    (s : Finset ι) {P : ℕ → ι → Prop}
    (h : ∀ q ∈ s, ∀ᶠ j in atTop, P j q) :
    ∀ᶠ j in atTop, ∀ q ∈ s, P j q := by
  induction s using Finset.induction with
  | empty => exact Eventually.of_forall fun _ _ hq => absurd hq (Finset.notMem_empty _)
  | insert a u _ ih =>
    have ha : ∀ᶠ j in atTop, P j a := h a (Finset.mem_insert_self a u)
    have hu : ∀ᶠ j in atTop, ∀ q ∈ u, P j q :=
      ih (fun q hq => h q (Finset.mem_insert_of_mem hq))
    filter_upwards [ha, hu] with j hja hju q hq
    rcases Finset.mem_insert.mp hq with rfl | hqu
    · exact hja
    · exact hju q hqu

private lemma tendsto_tsum_of_eventually_eq {ι : Type}
    (F : ℕ → ι → ℝ) (f bound : ι → ℝ)
    (hb : Summable bound)
    (hF : ∀ j q, |F j q| ≤ bound q)
    (hf : ∀ q, |f q| ≤ bound q)
    (hev : ∀ q, ∀ᶠ j in atTop, F j q = f q) :
    Tendsto (fun j => ∑' q, F j q) atTop (𝓝 (∑' q, f q)) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have htail := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero bound)).2 (ε / 2) hε2
  rw [Filter.eventually_atTop] at htail
  obtain ⟨s, hs⟩ := htail
  have hhead : ∀ᶠ j in atTop, ∀ q ∈ s, F j q = f q :=
    eventually_finset_forall s (fun q _ => hev q)
  filter_upwards [hhead] with j hj
  have hsF : Summable (F j) :=
    Summable.of_norm_bounded hb fun q => by simpa [Real.norm_eq_abs] using hF j q
  have hsf : Summable f :=
    Summable.of_norm_bounded hb fun q => by simpa [Real.norm_eq_abs] using hf q
  have hsum_eq : ∑ q ∈ s, F j q = ∑ q ∈ s, f q := Finset.sum_congr rfl hj
  rw [Real.dist_eq, ← hsF.sum_add_tsum_subtype_compl s, ← hsf.sum_add_tsum_subtype_compl s,
    hsum_eq, add_sub_add_left_eq_sub]
  have hF_sub : Summable (fun q : {x // x ∉ s} => ‖F j q‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => by simpa [Real.norm_eq_abs] using hF j q.1) (hb.subtype _)
  have hf_sub : Summable (fun q : {x // x ∉ s} => ‖f q‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => by simpa [Real.norm_eq_abs] using hf q.1) (hb.subtype _)
  calc |∑' q : {x // x ∉ s}, F j q - ∑' q : {x // x ∉ s}, f q|
      ≤ |∑' q : {x // x ∉ s}, F j q| + |∑' q : {x // x ∉ s}, f q| := abs_sub _ _
    _ ≤ (∑' q : {x // x ∉ s}, ‖F j q‖) + (∑' q : {x // x ∉ s}, ‖f q‖) :=
        add_le_add (by simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hF_sub)
          (by simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf_sub)
    _ ≤ (∑' q : {x // x ∉ s}, bound q) + (∑' q : {x // x ∉ s}, bound q) :=
        add_le_add
          (hF_sub.tsum_le_tsum (fun q => by simpa [Real.norm_eq_abs] using hF j q.1) (hb.subtype _))
          (hf_sub.tsum_le_tsum (fun q => by simpa [Real.norm_eq_abs] using hf q.1) (hb.subtype _))
    _ < ε / 2 + ε / 2 := add_lt_add (hs s le_rfl) (hs s le_rfl)
    _ = ε := add_halves ε

private lemma eventually_mem_levyAnnulus_of_mem_Ioo {ν : Measure ℝ} [SigmaFinite ν]
    (hν : IsLevyMeasure ν) {y : ℝ} (hyIoo : y ∈ Set.Ioo (-1 : ℝ) 1) (hy0 : y ≠ 0) :
    ∀ᶠ j in atTop, y ∈ levyAnnulus (levyTruncationSeq hν j) := by
  have hφ : StrictMono (levyTruncationSeq hν) := (ProbabilityTheory.levyTruncationSeq_spec hν).1
  have habs : 0 < |y| := abs_pos.mpr hy0
  obtain ⟨M, hM⟩ := exists_nat_gt |y|⁻¹
  rw [Filter.eventually_atTop]
  refine ⟨M, fun j hj => ⟨hyIoo, ?_⟩⟩
  change ((levyTruncationSeq hν j : ℝ) + 1)⁻¹ ≤ |y|
  have hMj : (M : ℝ) ≤ (levyTruncationSeq hν j : ℝ) := by
    exact_mod_cast le_trans hj (hφ.id_le j)
  have hinv_lt : |y|⁻¹ < (levyTruncationSeq hν j : ℝ) + 1 := by linarith [hM, hMj]
  have hprod : 1 < |y| * ((levyTruncationSeq hν j : ℝ) + 1) := by
    have h := mul_lt_mul_of_pos_left hinv_lt habs
    rwa [mul_inv_cancel₀ (ne_of_gt habs)] at h
  rw [inv_eq_one_div, div_le_iff₀ (Nat.cast_add_one_pos _)]
  linarith

private lemma fiberwise_markAtTime {Ω : Type}
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ) (T : ℝ≥0) (ω : Ω)
    (habs : Summable (absMarkT K Z T ω)) :
    Summable (fun s : Set.Ioc (0 : ℝ≥0) T => |markAtTime K Z ω s|) ∧
      (∑' s : Set.Ioc (0 : ℝ≥0) T, markAtTime K Z ω s) = ∑' q : ℕ × ℕ, signedMarkT K Z T ω q := by
  classical
  let Act := {q : ℕ × ℕ // q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ)}
  let τ : Act → Set.Ioc (0 : ℝ≥0) T := fun a =>
    ⟨⟨(Z a.1.1 a.1.2 ω).1, le_of_lt a.2.2.1⟩,
      ⟨by exact_mod_cast a.2.2.1, by exact_mod_cast a.2.2.2⟩⟩
  have hAct_abs : Summable (fun a : Act => |(Z a.1.1 a.1.2 ω).2|) := by
    refine (habs.comp_injective (Subtype.val_injective : Function.Injective (Subtype.val : Act → ℕ × ℕ))).congr fun a => ?_
    dsimp [Function.comp, absMarkT]
    rw [if_pos a.2]
  have hAct_val : Summable (fun a : Act => (Z a.1.1 a.1.2 ω).2) :=
    Summable.of_norm_bounded hAct_abs fun a => by simp [Real.norm_eq_abs]
  have hfiber_val : ∀ s : Set.Ioc (0 : ℝ≥0) T,
      (∑' b : τ ⁻¹' {s}, (Z b.1.1.1 b.1.1.2 ω).2) = markAtTime K Z ω s := by
    intro s
    have hs_pos : (0 : ℝ≥0) < s.1 := s.2.1
    rw [markAtTime, if_pos hs_pos]
    let g : τ ⁻¹' {s} → ℕ × ℕ := fun b => b.1.1
    have hg_inj : Function.Injective g := Subtype.val_injective.comp Subtype.val_injective
    let f : ℕ × ℕ → ℝ := fun q =>
      if q.2 < K q.1 ω ∧ (Z q.1 q.2 ω).1 = ((s : ℝ≥0) : ℝ) then (Z q.1 q.2 ω).2 else 0
    have hsupp : Function.support f ⊆ Set.range g := by
      intro q hq
      rw [Function.mem_support] at hq
      have hcond : q.2 < K q.1 ω ∧ (Z q.1 q.2 ω).1 = ((s : ℝ≥0) : ℝ) := by
        by_contra hnc; exact hq (by simp [f, hnc])
      have hpos : 0 < (Z q.1 q.2 ω).1 := by
        rw [hcond.2]; exact_mod_cast s.2.1
      have hle : (Z q.1 q.2 ω).1 ≤ (T : ℝ) := by
        rw [hcond.2]; exact_mod_cast s.2.2
      let a : Act := ⟨q, hcond.1, hpos, hle⟩
      have hτa : τ a = s := by
        ext; exact hcond.2
      exact ⟨⟨a, hτa⟩, rfl⟩
    have hcomp : ∀ b : τ ⁻¹' {s}, f (g b) = (Z b.1.1.1 b.1.1.2 ω).2 := by
      intro b
      have hτb : τ b.1 = s := b.2
      have htime : (Z b.1.1.1 b.1.1.2 ω).1 = ((s : ℝ≥0) : ℝ) :=
        congrArg (fun u : Set.Ioc (0 : ℝ≥0) T => ((u : ℝ≥0) : ℝ)) hτb
      simp [f, g, b.1.2.1, htime]
    rw [← hg_inj.tsum_eq hsupp]
    exact tsum_congr fun b => (hcomp b).symm
  have hMajor : Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
      ∑' b : τ ⁻¹' {s}, |(Z b.1.1.1 b.1.1.2 ω).2|) :=
    (hAct_abs.hasSum.tsum_fiberwise τ).summable
  have hsum_mark : Summable (fun s : Set.Ioc (0 : ℝ≥0) T => |markAtTime K Z ω s|) := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun s => ?_) hMajor
    rw [← hfiber_val s]
    have hsub : Summable (fun b : τ ⁻¹' {s} => ‖(Z b.1.1.1 b.1.1.2 ω).2‖) :=
      (hAct_abs.subtype (τ ⁻¹' {s})).congr fun b => by simp [Function.comp, Real.norm_eq_abs]
    have hle := norm_tsum_le_tsum_norm hsub
    simpa only [Real.norm_eq_abs] using hle
  have htsum_eq : (∑' s : Set.Ioc (0 : ℝ≥0) T, markAtTime K Z ω s) =
      ∑' q : ℕ × ℕ, signedMarkT K Z T ω q := by
    have h1 : (∑' s : Set.Ioc (0 : ℝ≥0) T, markAtTime K Z ω s) =
        ∑' a : Act, (Z a.1.1 a.1.2 ω).2 := by
      simp_rw [← hfiber_val]
      exact (hAct_val.hasSum.tsum_fiberwise τ).tsum_eq
    rw [h1]
    have hinj : Function.Injective (Subtype.val : Act → ℕ × ℕ) := Subtype.val_injective
    have hsupp : Function.support (signedMarkT K Z T ω) ⊆ Set.range (Subtype.val : Act → ℕ × ℕ) := by
      intro q hq
      rw [Function.mem_support] at hq
      have hcond : q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) := by
        by_contra hnc; exact hq (by simp [signedMarkT, hnc])
      exact ⟨⟨q, hcond⟩, rfl⟩
    rw [← hinj.tsum_eq hsupp]
    exact tsum_congr fun a => by
      dsimp [signedMarkT]
      rw [if_pos a.2]
  exact ⟨hsum_mark, htsum_eq⟩

private lemma path_eq_drift_plus_signedMarkT
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {ν : Measure ℝ} [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hν : IsLevyMeasure ν) (b : ℝ)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) ν)
    {ω : Ω} (hgood : ω ∈ levySmallJumpGoodSet hd hν)
    (T : ℝ≥0) (habs : Summable (absMarkT K Z T ω)) :
    levyJumpPath hd hν b T ω =
      (b - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν) * (T : ℝ) +
      ∑' q : ℕ × ℕ, signedMarkT K Z T ω q := by
  classical
  let φ := levyTruncationSeq hν
  let largeMark : ℕ × ℕ → ℝ := fun q =>
    if q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧ 1 ≤ |(Z q.1 q.2 ω).2|
    then (Z q.1 q.2 ω).2 else 0
  have hlarge_eq : levyLargeJumpSum K Z (T : ℝ) ω = ∑' q : ℕ × ℕ, largeMark q := by
    rw [levyLargeJumpSum, tsum_pieceSum_eq_tsum_prod K Z T ω habs
      ((Set.Ioc 0 (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) (fun p => by
        by_cases hp : p ∈ Set.Ioc 0 (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
        · rw [Set.indicator_of_mem hp, if_pos ⟨hp.1.1, hp.1.2⟩]
        · rw [Set.indicator_of_notMem hp, abs_zero]; split_ifs <;> positivity)]
    refine tsum_congr fun q => ?_
    dsimp [largeMark]
    by_cases hk : q.2 < K q.1 ω
    · by_cases hp : Z q.1 q.2 ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
      · rw [if_pos hk, Set.indicator_of_mem hp]
        rcases hp with ⟨⟨h1, h2⟩, h3⟩
        have h3' : 1 ≤ |(Z q.1 q.2 ω).2| := h3
        rw [if_pos ⟨hk, h1, h2, h3'⟩]
      · have hnot : ¬ (0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧ 1 ≤ |(Z q.1 q.2 ω).2|) :=
          fun h => hp ⟨⟨h.1, h.2.1⟩, h.2.2⟩
        rw [if_pos hk, Set.indicator_of_notMem hp, if_neg (fun h => hnot h.2)]
    · rw [if_neg hk, if_neg (fun h => hk h.1)]
  let annMark : ℕ → ℕ × ℕ → ℝ := fun j q =>
    if q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
        (Z q.1 q.2 ω).2 ∈ levyAnnulus (φ j)
    then (Z q.1 q.2 ω).2 else 0
  let smallMark : ℕ × ℕ → ℝ := fun q =>
    if q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
        (Z q.1 q.2 ω).2 ∈ Set.Ioo (-1 : ℝ) 1
    then (Z q.1 q.2 ω).2 else 0
  have hann_eq : ∀ j : ℕ, bandJumpSum K Z (levyAnnulus (φ j)) (T : ℝ) ω =
      ∑' q : ℕ × ℕ, annMark j q := by
    intro j
    rw [bandJumpSum, tsum_pieceSum_eq_tsum_prod K Z T ω habs
      ((Set.Ioc 0 (T : ℝ) ×ˢ levyAnnulus (φ j)).indicator fun p => p.2) (fun p => by
        by_cases hp : p ∈ Set.Ioc 0 (T : ℝ) ×ˢ levyAnnulus (φ j)
        · rw [Set.indicator_of_mem hp, if_pos ⟨hp.1.1, hp.1.2⟩]
        · rw [Set.indicator_of_notMem hp, abs_zero]; split_ifs <;> positivity)]
    refine tsum_congr fun q => ?_
    dsimp [annMark]
    by_cases hk : q.2 < K q.1 ω
    · by_cases hp : Z q.1 q.2 ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ levyAnnulus (φ j)
      · rw [if_pos hk, Set.indicator_of_mem hp]
        rcases hp with ⟨⟨h1, h2⟩, h3⟩
        rw [if_pos ⟨hk, h1, h2, h3⟩]
      · have hnot : ¬ (0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
            (Z q.1 q.2 ω).2 ∈ levyAnnulus (φ j)) :=
          fun h => hp ⟨⟨h.1, h.2.1⟩, h.2.2⟩
        rw [if_pos hk, Set.indicator_of_notMem hp, if_neg (fun h => hnot h.2)]
    · rw [if_neg hk, if_neg (fun h => hk h.1)]
  have htend_bandJump : Tendsto (fun j => bandJumpSum K Z (levyAnnulus (φ j)) (T : ℝ) ω)
      atTop (𝓝 (∑' q : ℕ × ℕ, smallMark q)) := by
    simp_rw [hann_eq]
    refine tendsto_tsum_of_eventually_eq annMark smallMark (absMarkT K Z T ω) habs
      (fun j q => by
        dsimp [annMark, absMarkT]
        by_cases h1 : q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
            (Z q.1 q.2 ω).2 ∈ levyAnnulus (φ j)
        · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, h1.2.2.1⟩]
        · rw [if_neg h1, abs_zero]; split_ifs <;> positivity)
      (fun q => by
        dsimp [smallMark, absMarkT]
        by_cases h1 : q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
            (Z q.1 q.2 ω).2 ∈ Set.Ioo (-1 : ℝ) 1
        · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, h1.2.2.1⟩]
        · rw [if_neg h1, abs_zero]; split_ifs <;> positivity)
      (fun q => ?_)
    by_cases hy0 : (Z q.1 q.2 ω).2 = 0
    · exact Eventually.of_forall fun j => by
        dsimp [annMark, smallMark]
        rw [hy0]; split_ifs <;> rfl
    · by_cases hyIoo : (Z q.1 q.2 ω).2 ∈ Set.Ioo (-1 : ℝ) 1
      · filter_upwards [eventually_mem_levyAnnulus_of_mem_Ioo hν hyIoo hy0] with j hj
        have hj' : (Z q.1 q.2 ω).2 ∈ levyAnnulus (φ j) := hj
        dsimp [annMark, smallMark]
        by_cases hb : q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ)
        · rw [if_pos ⟨hb.1, hb.2.1, hb.2.2, hj'⟩, if_pos ⟨hb.1, hb.2.1, hb.2.2, hyIoo⟩]
        · rw [if_neg (fun h => hb ⟨h.1, h.2.1, h.2.2.1⟩),
            if_neg (fun h => hb ⟨h.1, h.2.1, h.2.2.1⟩)]
      · exact Eventually.of_forall fun j => by
          have hjnot : (Z q.1 q.2 ω).2 ∉ levyAnnulus (φ j) :=
            fun hm => hyIoo (levyAnnulus_subset (φ j) hm)
          dsimp [annMark, smallMark]
          rw [if_neg (fun h => hjnot h.2.2.2), if_neg (fun h => hyIoo h.2.2.2)]
  have htend_comp : Tendsto (fun j => ∫ x in levyAnnulus (φ j), x ∂ν)
      atTop (𝓝 (∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν)) := by
    have hrw : (fun j => ∫ x in levyAnnulus (φ j), x ∂ν) =
        fun j => ∫ x, (levyAnnulus (φ j)).indicator id x ∂ν :=
      funext fun j => (integral_indicator (measurableSet_levyAnnulus (φ j))).symm
    rw [hrw, ← integral_indicator measurableSet_Ioo]
    refine tendsto_integral_of_dominated_convergence (fun x : ℝ => min (1 : ℝ) |x|)
      (fun j => (measurable_id.indicator (measurableSet_levyAnnulus (φ j))).aestronglyMeasurable)
      hfin
      (fun j => ae_of_all _ fun x => by
        by_cases hx : x ∈ levyAnnulus (φ j)
        · rw [Set.indicator_of_mem hx, id, Real.norm_eq_abs]
          have hxIoo := levyAnnulus_subset (φ j) hx
          have habs1 : |x| ≤ 1 := abs_le.mpr ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩
          rw [min_eq_right habs1]
        · rw [Set.indicator_of_notMem hx, norm_zero]
          exact le_min zero_le_one (abs_nonneg x))
      (ae_of_all _ fun x => ?_)
    by_cases hx0 : x = 0
    · subst hx0
      exact tendsto_const_nhds.congr fun j => by simp [Set.indicator_apply]
    · by_cases hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_mem_levyAnnulus_of_mem_Ioo hν hxIoo hx0] with j hj
        have hj' : x ∈ levyAnnulus (φ j) := hj
        rw [Set.indicator_of_mem hj', Set.indicator_of_mem hxIoo]
        rfl
      · exact tendsto_const_nhds.congr fun j => by
          have hjnot : x ∉ levyAnnulus (φ j) := fun hm => hxIoo (levyAnnulus_subset (φ j) hm)
          rw [Set.indicator_of_notMem hjnot, Set.indicator_of_notMem hxIoo]
  have htend_band : Tendsto (fun j => levyBandPath K Z ν (levyAnnulus (φ j)) (T : ℝ) ω)
      atTop (𝓝 ((∑' q : ℕ × ℕ, smallMark q) - (T : ℝ) * ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν)) :=
    htend_bandJump.sub (tendsto_const_nhds.mul htend_comp)
  have hsmall_eq : levySmallJumpPath hd hν (T : ℝ) ω =
      (∑' q : ℕ × ℕ, smallMark q) - (T : ℝ) * ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν :=
    tendsto_nhds_unique
      (ProbabilityTheory.tendsto_levyBandPath_levySmallJumpPath hd hν hgood T.2)
      htend_band
  have hsum_large : Summable largeMark :=
    Summable.of_norm_bounded habs fun q => by
      rw [Real.norm_eq_abs]; dsimp [largeMark, absMarkT]
      by_cases h1 : q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
          1 ≤ |(Z q.1 q.2 ω).2|
      · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, h1.2.2.1⟩]
      · rw [if_neg h1, abs_zero]; split_ifs <;> positivity
  have hsum_small : Summable smallMark :=
    Summable.of_norm_bounded habs fun q => by
      rw [Real.norm_eq_abs]; dsimp [smallMark, absMarkT]
      by_cases h1 : q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
          (Z q.1 q.2 ω).2 ∈ Set.Ioo (-1 : ℝ) 1
      · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, h1.2.2.1⟩]
      · rw [if_neg h1, abs_zero]; split_ifs <;> positivity
  have hcombine : (∑' q : ℕ × ℕ, largeMark q) + (∑' q : ℕ × ℕ, smallMark q) =
      ∑' q : ℕ × ℕ, signedMarkT K Z T ω q := by
    rw [← hsum_large.tsum_add hsum_small]
    refine tsum_congr fun q => ?_
    dsimp [largeMark, smallMark, signedMarkT]
    by_cases hbase : q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ)
    · rcases hbase with ⟨h1, h2, h3⟩
      by_cases hIoo : (Z q.1 q.2 ω).2 ∈ Set.Ioo (-1 : ℝ) 1
      · have hlt : |(Z q.1 q.2 ω).2| < 1 := abs_lt.mpr hIoo
        have hnot1 : ¬ (1 ≤ |(Z q.1 q.2 ω).2|) := not_le.mpr hlt
        rw [if_neg (fun h => hnot1 h.2.2.2), if_pos ⟨h1, h2, h3, hIoo⟩,
          if_pos ⟨h1, h2, h3⟩, zero_add]
      · have hge1 : 1 ≤ |(Z q.1 q.2 ω).2| := le_of_not_gt (fun hlt => hIoo (abs_lt.mp hlt))
        rw [if_pos ⟨h1, h2, h3, hge1⟩, if_neg (fun h => hIoo h.2.2.2),
          if_pos ⟨h1, h2, h3⟩, add_zero]
    · have hnl : ¬ (q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
          1 ≤ |(Z q.1 q.2 ω).2|) := fun h => hbase ⟨h.1, h.2.1, h.2.2.1⟩
      have hns : ¬ (q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (T : ℝ) ∧
          (Z q.1 q.2 ω).2 ∈ Set.Ioo (-1 : ℝ) 1) := fun h => hbase ⟨h.1, h.2.1, h.2.2.1⟩
      rw [if_neg hnl, if_neg hns, if_neg hbase, add_zero]
  rw [levyJumpPath, hlarge_eq, hsmall_eq]
  linarith [hcombine]

private lemma tsum_markAtTime_le_rawTrunc {Ω : Type} [MeasurableSpace Ω]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ) (ω : Ω)
    (n : ℕ) (habs : Summable (absMarkT K Z (n : ℝ≥0) ω)) :
    (∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
      ENNReal.ofReal (min (1 : ℝ) |markAtTime K Z ω s|)) ≤
    ∫⁻ p : ℝ × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ) then ENNReal.ofReal (min (1 : ℝ) |p.2|)
      else 0 ∂(poissonRandomMeasure K Z ω) := by
  classical
  let Act := {q : ℕ × ℕ // q.2 < K q.1 ω ∧ 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ ((n : ℝ≥0) : ℝ)}
  let τ : Act → Set.Ioc (0 : ℝ≥0) (n : ℝ≥0) := fun a =>
    ⟨⟨(Z a.1.1 a.1.2 ω).1, le_of_lt a.2.2.1⟩,
      ⟨by exact_mod_cast a.2.2.1, by exact_mod_cast a.2.2.2⟩⟩
  have hAct_abs : Summable (fun a : Act => |(Z a.1.1 a.1.2 ω).2|) := by
    refine (habs.comp_injective (Subtype.val_injective : Function.Injective (Subtype.val : Act → ℕ × ℕ))).congr fun a => ?_
    dsimp [Function.comp, absMarkT]
    rw [if_pos a.2]
  have hfiber_val : ∀ s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
      (∑' b : τ ⁻¹' {s}, (Z b.1.1.1 b.1.1.2 ω).2) = markAtTime K Z ω s := by
    intro s
    rw [markAtTime, if_pos s.2.1]
    let g : τ ⁻¹' {s} → ℕ × ℕ := fun b => b.1.1
    have hg_inj : Function.Injective g := Subtype.val_injective.comp Subtype.val_injective
    let f : ℕ × ℕ → ℝ := fun q =>
      if q.2 < K q.1 ω ∧ (Z q.1 q.2 ω).1 = ((s : ℝ≥0) : ℝ) then (Z q.1 q.2 ω).2 else 0
    have hsupp : Function.support f ⊆ Set.range g := by
      intro q hq
      rw [Function.mem_support] at hq
      have hcond : q.2 < K q.1 ω ∧ (Z q.1 q.2 ω).1 = ((s : ℝ≥0) : ℝ) := by
        by_contra hnc; exact hq (by simp [f, hnc])
      have hpos : 0 < (Z q.1 q.2 ω).1 := by rw [hcond.2]; exact_mod_cast s.2.1
      have hle : (Z q.1 q.2 ω).1 ≤ ((n : ℝ≥0) : ℝ) := by rw [hcond.2]; exact_mod_cast s.2.2
      let a : Act := ⟨q, hcond.1, hpos, hle⟩
      have hτa : τ a = s := by ext; exact hcond.2
      exact ⟨⟨a, hτa⟩, rfl⟩
    have hcomp : ∀ b : τ ⁻¹' {s}, f (g b) = (Z b.1.1.1 b.1.1.2 ω).2 := by
      intro b
      have htime : (Z b.1.1.1 b.1.1.2 ω).1 = ((s : ℝ≥0) : ℝ) :=
        congrArg (fun u : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0) => ((u : ℝ≥0) : ℝ)) b.2
      simp [f, g, b.1.2.1, htime]
    rw [← hg_inj.tsum_eq hsupp]
    exact tsum_congr fun b => (hcomp b).symm
  have hfiber_le : ∀ s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
      ENNReal.ofReal (min (1 : ℝ) |markAtTime K Z ω s|) ≤
        ∑' b : τ ⁻¹' {s}, ENNReal.ofReal (min (1 : ℝ) |(Z b.1.1.1 b.1.1.2 ω).2|) := by
    intro s
    by_cases hex : ∃ b : τ ⁻¹' {s}, 1 ≤ |(Z b.1.1.1 b.1.1.2 ω).2|
    · obtain ⟨b₀, hb₀⟩ := hex
      calc ENNReal.ofReal (min (1 : ℝ) |markAtTime K Z ω s|)
          ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = ENNReal.ofReal (min (1 : ℝ) |(Z b₀.1.1.1 b₀.1.1.2 ω).2|) := by
            rw [min_eq_left hb₀]
        _ ≤ ∑' b : τ ⁻¹' {s}, ENNReal.ofReal (min (1 : ℝ) |(Z b.1.1.1 b.1.1.2 ω).2|) :=
            ENNReal.le_tsum b₀
    · have hex' : ∀ b : τ ⁻¹' {s}, |(Z b.1.1.1 b.1.1.2 ω).2| < 1 :=
        fun b => lt_of_not_ge fun h => hex ⟨b, h⟩
      have hsub_abs : Summable (fun b : τ ⁻¹' {s} => |(Z b.1.1.1 b.1.1.2 ω).2|) :=
        (hAct_abs.subtype (τ ⁻¹' {s})).congr fun b => rfl
      have hsub_norm : Summable (fun b : τ ⁻¹' {s} => ‖(Z b.1.1.1 b.1.1.2 ω).2‖) :=
        hsub_abs.congr fun b => by simp [Real.norm_eq_abs]
      have habs_le : |markAtTime K Z ω s| ≤ ∑' b : τ ⁻¹' {s}, |(Z b.1.1.1 b.1.1.2 ω).2| := by
        rw [← hfiber_val s]
        have hle := norm_tsum_le_tsum_norm hsub_norm
        simpa only [Real.norm_eq_abs] using hle
      have hmin_eq : ∀ b : τ ⁻¹' {s},
          min (1 : ℝ) |(Z b.1.1.1 b.1.1.2 ω).2| = |(Z b.1.1.1 b.1.1.2 ω).2| :=
        fun b => min_eq_right (le_of_lt (hex' b))
      calc ENNReal.ofReal (min (1 : ℝ) |markAtTime K Z ω s|)
          ≤ ENNReal.ofReal |markAtTime K Z ω s| := ENNReal.ofReal_le_ofReal (min_le_right _ _)
        _ ≤ ENNReal.ofReal (∑' b : τ ⁻¹' {s}, |(Z b.1.1.1 b.1.1.2 ω).2|) :=
            ENNReal.ofReal_le_ofReal habs_le
        _ = ∑' b : τ ⁻¹' {s}, ENNReal.ofReal |(Z b.1.1.1 b.1.1.2 ω).2| :=
            ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) hsub_abs
        _ = ∑' b : τ ⁻¹' {s}, ENNReal.ofReal (min (1 : ℝ) |(Z b.1.1.1 b.1.1.2 ω).2|) := by
            simp_rw [hmin_eq]
  calc (∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal (min (1 : ℝ) |markAtTime K Z ω s|))
      ≤ ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
          ∑' b : τ ⁻¹' {s}, ENNReal.ofReal (min (1 : ℝ) |(Z b.1.1.1 b.1.1.2 ω).2|) :=
        ENNReal.tsum_le_tsum hfiber_le
    _ = ∑' a : Act, ENNReal.ofReal (min (1 : ℝ) |(Z a.1.1 a.1.2 ω).2|) :=
        ENNReal.tsum_fiberwise
          (fun a : Act => ENNReal.ofReal (min (1 : ℝ) |(Z a.1.1 a.1.2 ω).2|)) τ
    _ = ∑' q : ℕ × ℕ, if q.2 < K q.1 ω then rawTruncFun n (Z q.1 q.2 ω) else 0 := by
        have hinj : Function.Injective (Subtype.val : Act → ℕ × ℕ) := Subtype.val_injective
        let G : ℕ × ℕ → ℝ≥0∞ := fun q =>
          if q.2 < K q.1 ω then rawTruncFun n (Z q.1 q.2 ω) else 0
        have hsupp : Function.support G ⊆ Set.range (Subtype.val : Act → ℕ × ℕ) := by
          intro q hq
          rw [Function.mem_support] at hq
          have hk : q.2 < K q.1 ω := by
            by_contra hnk; exact hq (by simp [G, hnk])
          have ht : 0 < (Z q.1 q.2 ω).1 ∧ (Z q.1 q.2 ω).1 ≤ (n : ℝ) := by
            by_contra hnt; exact hq (by simp [G, hk, rawTruncFun, hnt])
          have ht' : (Z q.1 q.2 ω).1 ≤ ((n : ℝ≥0) : ℝ) := by exact_mod_cast ht.2
          exact ⟨⟨q, hk, ht.1, ht'⟩, rfl⟩
        rw [← hinj.tsum_eq hsupp]
        refine tsum_congr fun a => ?_
        have hle_n : (Z a.1.1 a.1.2 ω).1 ≤ (n : ℝ) := by exact_mod_cast a.2.2.2
        dsimp [G, rawTruncFun]
        rw [if_pos a.2.1, if_pos ⟨a.2.2.1, hle_n⟩]
    _ = ∫⁻ p : ℝ × ℝ, rawTruncFun n p ∂(poissonRandomMeasure K Z ω) :=
        tsum_prod_eq_lintegral_prm K Z ω (measurable_rawTruncFun n)

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hν : IsLevyMeasure ν) (b : ℝ)
    (hfinite : (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) < ⊤) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |(levyJumpPath hd hν b) (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => (levyJumpPath hd hν b) u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |(levyJumpPath hd hν b) (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => (levyJumpPath hd hν b) u ω) (s : ℝ≥0)|
           else 0)) ≤
        (∫⁻ p : ℝ × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ) then ENNReal.ofReal (min (1 : ℝ) |p.2|)
      else 0 ∂(poissonRandomMeasure K Z ω)) := by
  have hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) ν :=
    integrable_min_one_abs_of_lintegral_lt_top hfinite
  filter_upwards [ae_good_and_finite P ν K Z hd hν hfinite] with ω ⟨hgood, htrunc, hlarge⟩ n
  have hrep : ∀ T : ℝ≥0, (levyJumpPath hd hν b) T ω =
      (b - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν) * (T : ℝ) +
      ∑' s : Set.Ioc (0 : ℝ≥0) T, markAtTime K Z ω s := by
    intro T
    have habs := summable_absMarkT K Z ω htrunc hlarge T
    rw [path_eq_drift_plus_signedMarkT K Z hd hν b hfin hgood T habs,
      (fiberwise_markAtTime K Z T ω habs).2]
  have hs_all : ∀ T : ℝ≥0, Summable (fun s : Set.Ioc (0 : ℝ≥0) T => |markAtTime K Z ω s|) :=
    fun T => (fiberwise_markAtTime K Z T ω (summable_absMarkT K Z ω htrunc hlarge T)).1
  have hjumps : ∀ t : ℝ≥0, 0 < t →
      (levyJumpPath hd hν b) t ω -
        Function.leftLim (fun u : ℝ≥0 => (levyJumpPath hd hν b) u ω) t =
      markAtTime K Z ω t :=
    Kyprianou.Ch02.locallySummableTimeRepresentationActualJumpsV2
      (fun u => (levyJumpPath hd hν b) u ω) (markAtTime K Z ω)
      (b - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν) hs_all hrep
  refine le_trans (ENNReal.tsum_le_tsum fun s => ?_)
    (tsum_markAtTime_le_rawTrunc K Z ω n (summable_absMarkT K Z ω htrunc hlarge (n : ℝ≥0)))
  rw [hjumps s.1 s.2.1]
  apply ENNReal.ofReal_le_ofReal
  by_cases hle1 : |markAtTime K Z ω s| ≤ (1 : ℝ)
  · rw [if_pos hle1, min_eq_right hle1]
  · rw [if_neg hle1]
    exact le_min zero_le_one (abs_nonneg _)
