-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiForwardMeasurableAndInitial
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T16:49:25.322256+00:00
-- url     : https://prove2.me/submissions/3581f194-d929-4aed-82f9-9b87bbe2c52f

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace LFMI

lemma rc_ev {f : ℝ≥0 → ℕ} {u : ℝ≥0} (h : ContinuousWithinAt f (Ici u) u) :
    ∃ v, u < v ∧ ∀ w ∈ Ico u v, f w = f u := by
  have : {w | f w = f u} ∈ 𝓝[≥] u := h ((isOpen_discrete {f u}).mem_nhds rfl)
  obtain ⟨v, hv, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp this
  exact ⟨v, hv, fun w hw => hsub hw⟩

lemma loc_bdd {f : ℝ≥0 → ℕ} (hf : IsCadlag f) (T : ℝ≥0) :
    ∃ C : ℕ, ∀ u ≤ T, f u ≤ C := by
  have key : ∀ u, ∃ C : ℕ, {v | f v ≤ C} ∈ 𝓝 u := by
    intro u
    obtain ⟨hr, l, hl⟩ := hf u
    refine ⟨max l (f u), ?_⟩
    rw [← nhdsLT_sup_nhdsGE]
    refine Filter.mem_sup.mpr ⟨?_, ?_⟩
    · have : {v | f v = l} ∈ 𝓝[<] u := hl ((isOpen_discrete {l}).mem_nhds rfl)
      filter_upwards [this] with v hv
      simp [hv]
    · have : {v | f v = f u} ∈ 𝓝[≥] u := hr ((isOpen_discrete {f u}).mem_nhds rfl)
      filter_upwards [this] with v hv
      simp [hv]
  choose C hC using key
  obtain ⟨t, -, hcov⟩ := (isCompact_Icc (a := (0:ℝ≥0)) (b := T)).elim_nhds_subcover
    (fun x => {v | f v ≤ C x}) (fun x _ => hC x)
  refine ⟨t.sup C, fun u hu => ?_⟩
  have hu' : u ∈ Icc (0:ℝ≥0) T := ⟨bot_le, hu⟩
  obtain ⟨x, hx, hux⟩ := mem_iUnion₂.mp (hcov hu')
  exact le_trans hux (Finset.le_sup hx)

lemma path_ii {f : ℝ≥0 → ℕ} (hf : IsCadlag f) (hm : Measurable f) (b : ℝ) (hb : 0 ≤ b) :
    IntervalIntegrable (fun u : ℝ => (f u.toNNReal : ℝ)) volume 0 b := by
  obtain ⟨C, hC⟩ := loc_bdd hf b.toNNReal
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
  refine Measure.integrableOn_of_bounded (M := C) (by simp)
    ((measurable_from_top.comp (hm.comp measurable_real_toNNReal)).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => ?_)
  simp only [Real.norm_natCast]
  exact_mod_cast hC _ (Real.toNNReal_le_toNNReal hu.2)

lemma J_mono {f : ℝ≥0 → ℕ} (hf : IsCadlag f) (hm : Measurable f) {s s' : ℝ≥0} (h : s ≤ s') :
    ∫ u in (0:ℝ)..(s:ℝ), (f u.toNNReal : ℝ) ≤ ∫ u in (0:ℝ)..(s':ℝ), (f u.toNNReal : ℝ) :=
  intervalIntegral.integral_mono_interval le_rfl s.2 (by exact_mod_cast h)
    (Eventually.of_forall (fun u => Nat.cast_nonneg _)) (path_ii hf hm _ s'.2)

open Classical in
lemma btp_eq {Ω : Type*} (W : ℝ≥0 → Ω → ℕ) (t : ℝ≥0) (ω : Ω) :
    branchingToPoisson W t ω =
      if (∃ s : ℝ≥0, (t:ℝ) < branchingOccupation W s ω) then
        W (sInf {s : ℝ≥0 | (t:ℝ) < branchingOccupation W s ω}) ω else 0 := by
  unfold branchingToPoisson inverseBranchingOccupation
  split_ifs <;> rfl

lemma btp_meas {Ω : Type*} [MeasurableSpace Ω] (W : ℝ≥0 → Ω → ℕ)
    (hW : Measurable (fun p : ℝ≥0 × Ω => W p.1 p.2))
    (hc : ∀ ω, IsCadlag (fun u => W u ω)) (t : ℝ≥0) :
    Measurable (branchingToPoisson W t) := by
  classical
  have hpath : ∀ ω, Measurable (fun u => W u ω) := fun ω => hW.comp measurable_prodMk_right
  have hJ : ∀ s : ℝ≥0, Measurable (fun ω => branchingOccupation W s ω) := by
    intro s
    have hF : Measurable (fun p : Ω × ℝ => (W p.2.toNNReal p.1 : ℝ)) :=
      measurable_from_top.comp
        (hW.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
    have := (hF.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0:ℝ) s))).measurable
    convert this using 1
    funext ω
    simp only [branchingOccupation]
    exact intervalIntegral.integral_of_le s.2
  have hmono : ∀ ω, Monotone (fun s => branchingOccupation W s ω) :=
    fun ω s s' h => J_mono (hc ω) (hpath ω) h
  have hE : MeasurableSet {ω | ∃ s : ℝ≥0, (t:ℝ) < branchingOccupation W s ω} := by
    have : {ω | ∃ s : ℝ≥0, (t:ℝ) < branchingOccupation W s ω} =
        ⋃ n : ℕ, {ω | (t:ℝ) < branchingOccupation W n ω} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨s, hs⟩
        obtain ⟨n, hn⟩ := exists_nat_ge s
        exact ⟨n, hs.trans_le (hmono ω hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, hn⟩
    rw [this]
    exact MeasurableSet.iUnion fun n => measurableSet_lt measurable_const (hJ n)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hσ : Measurable (fun ω => sInf {s : ℝ≥0 | (t:ℝ) < branchingOccupation W s ω}) := by
    refine measurable_of_Iio fun r => ?_
    have : (fun ω => sInf {s : ℝ≥0 | (t:ℝ) < branchingOccupation W s ω}) ⁻¹' Iio r =
        ({ω | ∃ s : ℝ≥0, (t:ℝ) < branchingOccupation W s ω} ∩
          ⋃ q ∈ D, ({ω | q < r} ∩ {ω | (t:ℝ) < branchingOccupation W q ω})) ∪
        ({ω | ∃ s : ℝ≥0, (t:ℝ) < branchingOccupation W s ω}ᶜ ∩ {ω | 0 < r}) := by
      ext ω
      simp only [mem_preimage, mem_Iio, mem_union, mem_inter_iff, mem_iUnion, mem_ofPred_eq,
        mem_compl_iff, exists_prop]
      by_cases hω : ∃ s : ℝ≥0, (t:ℝ) < branchingOccupation W s ω
      · simp only [hω, true_and, not_true_eq_false, false_and, or_false]
        rw [csInf_lt_iff (OrderBot.bddBelow _)
          (show ({s : ℝ≥0 | (t:ℝ) < branchingOccupation W s ω}).Nonempty from hω)]
        constructor
        · rintro ⟨a, ha, har⟩
          obtain ⟨q, hqD, hq⟩ := hDd.exists_between har
          exact ⟨q, hqD, hq.2, lt_of_lt_of_le ha (hmono ω hq.1.le)⟩
        · rintro ⟨q, hqD, hqr, hq⟩
          exact ⟨q, hq, hqr⟩
      · have hempty : {s : ℝ≥0 | (t:ℝ) < branchingOccupation W s ω} = ∅ := by
          ext s
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun h => hω ⟨s, h⟩
        simp only [hω, false_and, not_false_eq_true, true_and, false_or, hempty,
          NNReal.sInf_empty]
    rw [this]
    exact (hE.inter (MeasurableSet.biUnion hDc fun q _ =>
      (MeasurableSet.const _).inter (measurableSet_lt measurable_const (hJ q)))).union
      (hE.compl.inter (MeasurableSet.const _))
  have : branchingToPoisson W t = fun ω =>
      if (∃ s : ℝ≥0, (t:ℝ) < branchingOccupation W s ω) then
        W (sInf {s : ℝ≥0 | (t:ℝ) < branchingOccupation W s ω}) ω else 0 := by
    funext ω; rw [btp_eq]
  rw [this]
  exact Measurable.ite hE (hW.comp (hσ.prodMk measurable_id)) measurable_const

lemma btp_zero_pos {Ω : Type*} (W : ℝ≥0 → Ω → ℕ) (ω : Ω) (hc : IsCadlag (fun u => W u ω))
    (hm : Measurable (fun u => W u ω)) (hpos : 0 < W 0 ω) :
    branchingToPoisson W 0 ω = W 0 ω := by
  classical
  obtain ⟨v, hv, hvc⟩ := rc_ev (hc 0).1
  have hJpos : ∀ s : ℝ≥0, 0 < s → ((0:ℝ≥0):ℝ) < branchingOccupation W s ω := by
    intro s hs
    have ha : 0 < min s (v/2) := lt_min hs (half_pos hv)
    have hmono := J_mono hc hm (min_le_left s (v/2))
    refine lt_of_lt_of_le ?_ hmono
    have h1 : ∫ u in (0:ℝ)..((min s (v/2) : ℝ≥0):ℝ), (1:ℝ) ≤
        ∫ u in (0:ℝ)..((min s (v/2) : ℝ≥0):ℝ), (W u.toNNReal ω : ℝ) := by
      apply intervalIntegral.integral_mono_on (min s (v/2)).2 intervalIntegrable_const
        (path_ii hc hm _ (min s (v/2)).2)
      intro u hu
      have hmem : u.toNNReal ∈ Ico (0:ℝ≥0) v := by
        refine ⟨bot_le, ?_⟩
        calc u.toNNReal ≤ min s (v/2) := Real.toNNReal_le_iff_le_coe.mpr hu.2
          _ < v := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hv)
      rw [hvc _ hmem]
      exact_mod_cast hpos
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at h1
    refine lt_of_lt_of_le ?_ h1
    simp only [NNReal.coe_zero]
    exact_mod_cast ha
  rw [btp_eq, if_pos ⟨1, hJpos 1 one_pos⟩]
  have : sInf {s : ℝ≥0 | ((0:ℝ≥0):ℝ) < branchingOccupation W s ω} = 0 := by
    by_contra hne
    have hpos' := pos_iff_ne_zero.mpr hne
    have hmem : sInf {s : ℝ≥0 | ((0:ℝ≥0):ℝ) < branchingOccupation W s ω} / 2 ∈
        {s : ℝ≥0 | ((0:ℝ≥0):ℝ) < branchingOccupation W s ω} := hJpos _ (half_pos hpos')
    have := csInf_le (OrderBot.bddBelow _) hmem
    exact absurd this (not_le.mpr (half_lt_self hpos'))
  rw [this]

open Classical in
lemma exists_mod {Ω : Type*} [MeasurableSpace Ω] (Y : ℝ≥0 → Ω → ℕ)
    (hMeas : ∀ t, Measurable (Y t)) (S : Set Ω) (hS : MeasurableSet S)
    (hc : ∀ ω ∈ S, IsCadlag (fun t => Y t ω)) :
    Measurable (fun p : ℝ≥0 × Ω => if p.2 ∈ S then Y p.1 p.2 else 0) := by
  let d : ℕ → ℝ≥0 → ℝ≥0 := fun n u => (⌈((n:ℝ≥0) + 1) * u⌉₊ : ℝ≥0) / ((n:ℝ≥0) + 1)
  have hZ : ∀ n, Measurable (fun p : ℝ≥0 × Ω => if p.2 ∈ S then Y (d n p.1) p.2 else 0) := by
    intro n
    refine Measurable.ite (measurable_snd hS) ?_ measurable_const
    have hG : Measurable (fun q : Ω × ℕ => Y ((q.2 : ℝ≥0) / ((n:ℝ≥0) + 1)) q.1) :=
      measurable_from_prod_countable_left (fun k => hMeas ((k:ℝ≥0) / ((n:ℝ≥0) + 1)))
    have hk : Measurable (fun p : ℝ≥0 × Ω => (p.2, ⌈((n:ℝ≥0) + 1) * p.1⌉₊)) :=
      measurable_snd.prodMk (Nat.measurable_ceil.comp (measurable_const.mul measurable_fst))
    exact hG.comp hk
  refine measurable_of_tendsto_metrizable hZ ?_
  rw [tendsto_pi_nhds]
  rintro ⟨u, ω⟩
  by_cases hω : ω ∈ S
  · simp only [hω, if_true]
    obtain ⟨v, huv, hv⟩ := rc_ev (hc ω hω u).1
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr (show (u:ℝ) < v from huv))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    symm
    apply hv
    have hn1 : (0:ℝ≥0) < (n:ℝ≥0) + 1 := by positivity
    constructor
    · show u ≤ (⌈((n:ℝ≥0) + 1) * u⌉₊ : ℝ≥0) / ((n:ℝ≥0) + 1)
      rw [le_div_iff₀ hn1, mul_comm]
      exact Nat.le_ceil _
    · show (⌈((n:ℝ≥0) + 1) * u⌉₊ : ℝ≥0) / ((n:ℝ≥0) + 1) < v
      rw [← NNReal.coe_lt_coe]
      have h1 : ((⌈((n:ℝ≥0) + 1) * u⌉₊ : ℝ≥0) : ℝ) < ((n:ℝ) + 1) * u + 1 := by
        have := Nat.ceil_lt_add_one (show (0:ℝ≥0) ≤ ((n:ℝ≥0) + 1) * u from bot_le)
        have := NNReal.coe_lt_coe.mpr this
        push_cast at this ⊢
        exact this
      have hNn : ((N:ℝ) + 1) ≤ (n:ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
      have hN' : 1 < ((v:ℝ) - u) * ((N:ℝ) + 1) := by
        rw [div_lt_iff₀ (by positivity)] at hN; exact hN
      push_cast
      rw [div_lt_iff₀ (by positivity)]
      push_cast at h1
      nlinarith [sub_pos.mpr (show (u:ℝ) < v from huv)]
  · simp only [hω, if_false]
    exact tendsto_const_nhds

lemma zero_absorb {law : PopulationLaws} (h : HasBranchingProperty law) (t : ℝ≥0) :
    law 0 t 0 = 1 := by
  set μ := law 0 t with hμ
  have hconv : ∀ k, μ k = ∑' n, μ n * ∑' m, (if k = n + m then μ m else 0) := by
    intro k
    have := congrArg (fun p : PMF ℕ => p k) (h 0 0 t)
    simp only [Nat.add_zero, PMF.bind_apply, PMF.map_apply] at this
    convert this
  have h0 : μ 0 = μ 0 * μ 0 := by
    have := hconv 0
    rw [tsum_eq_single 0 (fun n hn => by
      rw [ENNReal.tsum_eq_zero.mpr (fun m => by rw [if_neg (by omega)]), mul_zero])] at this
    rw [tsum_eq_single 0 (fun m hm => by rw [if_neg (by omega)])] at this
    simpa using this
  by_cases hz : μ 0 = 0
  · exfalso
    have hex : ∃ k, μ k ≠ 0 := by
      by_contra hall
      push Not at hall
      have := μ.tsum_coe
      simp [hall] at this
    have hk := Nat.find_spec hex
    have hmin : ∀ j < Nat.find hex, μ j = 0 := fun j hj => by
      have := Nat.find_min hex hj
      push Not at this
      exact this
    apply hk
    rw [hconv]
    refine ENNReal.tsum_eq_zero.mpr fun n => ?_
    by_cases hn : n < Nat.find hex
    · rw [hmin n hn, zero_mul]
    · rw [ENNReal.tsum_eq_zero.mpr (fun m => ?_), mul_zero]
      split_ifs with hm
      · have : m = 0 := by omega
        rw [this, hz]
      · rfl
  · have htop : μ 0 ≠ ⊤ := PMF.apply_ne_top _ _
    have : μ 0 * 1 = μ 0 * μ 0 := by rw [mul_one]; exact h0
    exact ((ENNReal.mul_right_inj hz htop).mp this).symm

end LFMI

open LFMI in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∀ y : ℕ,
      (∀ t : ℝ≥0, AEMeasurable (fun ω => branchingToPoisson Y t ω) (P y)) ∧
      P y {ω | branchingToPoisson Y 0 ω = y} = 1 := by
  classical
  intro y
  have := hMarkov.1 y
  have hB : P y {ω | ¬ IsCadlag (fun t : ℝ≥0 => Y t ω)} = 0 := ae_iff.mp (hCadlag y)
  set S := (toMeasurable (P y) {ω | ¬ IsCadlag (fun t : ℝ≥0 => Y t ω)})ᶜ with hSdef
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSc : ∀ ω ∈ S, IsCadlag (fun t => Y t ω) := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hSae : ∀ᵐ ω ∂(P y), ω ∈ S := by
    rw [ae_iff]
    simp only [hSdef, mem_compl_iff, not_not, ofPred_mem_eq, measure_toMeasurable, hB]
  let W : ℝ≥0 → Ω → ℕ := fun u ω => if ω ∈ S then Y u ω else 0
  have hW : Measurable (fun p : ℝ≥0 × Ω => W p.1 p.2) := by
    convert exists_mod Y hMeas S hSm hSc
  have hWc : ∀ ω, IsCadlag (fun u => W u ω) := by
    intro ω
    by_cases hω : ω ∈ S
    · simpa [W, hω] using hSc ω hω
    · simp only [W, hω, if_false]
      exact fun t => ⟨continuousWithinAt_const, ⟨0, tendsto_const_nhds⟩⟩
  have hWp : ∀ ω, Measurable (fun u => W u ω) := fun ω => hW.comp measurable_prodMk_right
  have hagree : ∀ ω ∈ S, ∀ t, branchingToPoisson Y t ω = branchingToPoisson W t ω := by
    intro ω hω t
    unfold branchingToPoisson inverseBranchingOccupation branchingOccupation
    simp only [W, hω, if_true]
  refine ⟨fun t => ⟨branchingToPoisson W t, btp_meas W hW hWc t, ?_⟩, ?_⟩
  · filter_upwards [hSae] with ω hω using hagree ω hω t
  have hY0 : ∀ᵐ ω ∂(P y), Y 0 ω = y := by
    rw [ae_iff_measure_eq (p := fun ω => Y 0 ω = y)
      ((measurableSet_singleton y).preimage (hMeas 0)).nullMeasurableSet,
      hInitial y, measure_univ]
  have hgoal : ∀ᵐ ω ∂(P y), branchingToPoisson Y 0 ω = y := by
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · have hq : ∀ q : ℝ≥0, ∀ᵐ ω ∂(P 0), Y q ω = 0 := fun q => by
        rw [ae_iff_measure_eq (p := fun ω => Y q ω = 0)
          ((measurableSet_singleton 0).preimage (hMeas q)).nullMeasurableSet,
          hMarkov.2.1 0 q 0, zero_absorb hBranching, measure_univ]
      obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
      have := hDc.to_subtype
      have hD : ∀ᵐ ω ∂(P 0), ∀ q : D, Y q ω = 0 := ae_all_iff.mpr (fun q => hq q)
      filter_upwards [hSae, hD] with ω hω hDω
      have hzero : ∀ u, Y u ω = 0 := by
        intro u
        obtain ⟨v, huv, hv⟩ := rc_ev (hSc ω hω u).1
        obtain ⟨q, hqD, hq⟩ := hDd.exists_between huv
        rw [← hv q ⟨hq.1.le, hq.2⟩]
        exact hDω ⟨q, hqD⟩
      rw [btp_eq]
      split_ifs <;> simp [hzero]
    · filter_upwards [hSae, hY0] with ω hω h0
      rw [hagree ω hω, btp_zero_pos W ω (hWc ω) (hWp ω) (by simp [W, hω, h0, hy])]
      simp [W, hω, h0]
  have h : {ω | branchingToPoisson Y 0 ω = y} =ᵐ[P y] (univ : Set Ω) :=
    ae_eq_univ.mpr (ae_iff.mp hgoal)
  rw [measure_congr h, measure_univ]
