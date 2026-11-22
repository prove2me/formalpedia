-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiForwardGenerator
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T19:13:18.646277+00:00
-- url     : https://prove2.me/submissions/ff65573b-f12e-4f73-8377-2b00a4dc9fac

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_branchingTwoJumpsLittleO
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace LFG

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

lemma d_ev {u v : ℝ≥0} (huv : u < v) :
    ∀ᶠ n : ℕ in atTop, (⌈((n:ℝ≥0) + 1) * u⌉₊ : ℝ≥0) / ((n:ℝ≥0) + 1) ∈ Ico u v := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr (show (u:ℝ) < v from huv))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn1 : (0:ℝ≥0) < (n:ℝ≥0) + 1 := by positivity
  constructor
  · rw [le_div_iff₀ hn1, mul_comm]
    exact Nat.le_ceil _
  · rw [← NNReal.coe_lt_coe]
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

lemma cadlag_meas {f : ℝ≥0 → ℕ} (hf : IsCadlag f) : Measurable f := by
  have hZ : ∀ n : ℕ, Measurable
      (fun u : ℝ≥0 => f ((⌈((n:ℝ≥0) + 1) * u⌉₊ : ℝ≥0) / ((n:ℝ≥0) + 1))) := by
    intro n
    exact (measurable_from_top (f := fun k : ℕ => f ((k : ℝ≥0) / ((n:ℝ≥0) + 1)))).comp
      (Nat.measurable_ceil.comp (measurable_const.mul measurable_id))
  refine measurable_of_tendsto_metrizable hZ ?_
  rw [tendsto_pi_nhds]
  intro u
  obtain ⟨v, huv, hv⟩ := rc_ev (hf u).1
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [d_ev huv] with n hn
  exact (hv _ hn).symm

lemma path_ii {f : ℝ≥0 → ℕ} (hf : IsCadlag f) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => (f u.toNNReal : ℝ)) volume a b := by
  set R := |a| + |b|
  obtain ⟨C, hC⟩ := loc_bdd hf R.toNNReal
  have hI : IntegrableOn (fun u : ℝ => (f u.toNNReal : ℝ)) (Icc (-R) R) volume := by
    refine Measure.integrableOn_of_bounded (M := C) measure_Icc_lt_top.ne
      ((measurable_from_top.comp ((cadlag_meas hf).comp measurable_real_toNNReal)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun u hu => ?_)
    simp only [Real.norm_natCast]
    exact_mod_cast hC _ (Real.toNNReal_le_toNNReal hu.2)
  refine IntegrableOn.intervalIntegrable (hI.mono_set (uIcc_subset_Icc ?_ ?_))
  · constructor <;> linarith [neg_abs_le a, le_abs_self a, abs_nonneg b]
  · constructor <;> linarith [neg_abs_le b, le_abs_self b, abs_nonneg a]

/-- Occupation clock of a single path. -/
noncomputable def Jf (f : ℝ≥0 → ℕ) (r : ℝ≥0) : ℝ :=
  ∫ u in (0:ℝ)..(r:ℝ), (f u.toNNReal : ℝ)

open Classical in
/-- Lamperti time change of a single path. -/
noncomputable def Xf (f : ℝ≥0 → ℕ) (t : ℝ≥0) : ℕ :=
  if (∃ r : ℝ≥0, (t:ℝ) < Jf f r) then f (sInf {r : ℝ≥0 | (t:ℝ) < Jf f r}) else 0

lemma btp_eq' {Ω : Type*} (W : ℝ≥0 → Ω → ℕ) (t : ℝ≥0) (ω : Ω) :
    branchingToPoisson W t ω = Xf (fun u => W u ω) t := by
  classical
  unfold branchingToPoisson inverseBranchingOccupation Xf
  by_cases h : ∃ r : ℝ≥0, (t:ℝ) < branchingOccupation W r ω
  · rw [if_pos h, if_pos (show ∃ r, (t:ℝ) < Jf (fun u => W u ω) r from h)]; rfl
  · rw [if_neg h, if_neg (show ¬ ∃ r, (t:ℝ) < Jf (fun u => W u ω) r from h)]

lemma Jf_mono {f : ℝ≥0 → ℕ} (hf : IsCadlag f) {s s' : ℝ≥0} (h : s ≤ s') :
    Jf f s ≤ Jf f s' :=
  intervalIntegral.integral_mono_interval le_rfl s.2 (by exact_mod_cast h)
    (Eventually.of_forall (fun u => Nat.cast_nonneg _)) (path_ii hf _ _)

lemma Jf_cont {f : ℝ≥0 → ℕ} (hf : IsCadlag f) : Continuous (Jf f) :=
  (intervalIntegral.continuous_primitive (path_ii hf) 0).comp NNReal.continuous_coe

lemma Jf_zero (f : ℝ≥0 → ℕ) : Jf f 0 = 0 := by unfold Jf; simp

lemma Jf_shift {f : ℝ≥0 → ℕ} (hf : IsCadlag f) (σ r : ℝ≥0) :
    Jf f (σ + r) = Jf f σ + Jf (fun u => f (σ + u)) r := by
  unfold Jf
  push_cast
  rw [← intervalIntegral.integral_add_adjacent_intervals (path_ii hf 0 σ) (path_ii hf σ (σ + r))]
  congr 1
  have h := intervalIntegral.integral_comp_add_right (fun x : ℝ => (f x.toNNReal : ℝ)) (σ : ℝ)
    (a := 0) (b := (r:ℝ))
  rw [zero_add, add_comm (r:ℝ)] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le (NNReal.coe_nonneg r)] at hx
  show (f (x + (σ:ℝ)).toNNReal : ℝ) = (f (σ + x.toNNReal) : ℝ)
  have : (x + (σ:ℝ)).toNNReal = σ + x.toNNReal := by
    apply NNReal.coe_injective
    simp only [Real.coe_toNNReal', NNReal.coe_add, max_eq_left hx.1]
    rw [max_eq_left (by linarith [hx.1, NNReal.coe_nonneg σ])]
    ring
  rw [this]

lemma sig_J {f : ℝ≥0 → ℕ} (hf : IsCadlag f) {s : ℝ≥0} (hE : ∃ r, (s:ℝ) < Jf f r) :
    Jf f (sInf {r | (s:ℝ) < Jf f r}) = s := by
  set σ := sInf {r | (s:ℝ) < Jf f r} with hσ
  have hE' : ({r | (s:ℝ) < Jf f r} : Set ℝ≥0).Nonempty := hE
  have hc := Jf_cont hf
  apply le_antisymm
  · by_contra h
    push Not at h
    have hσpos : 0 < σ := by
      rw [pos_iff_ne_zero]
      intro h0
      rw [h0, Jf_zero] at h
      linarith [s.2]
    have hmem : {r | (s:ℝ) < Jf f r} ∈ 𝓝 σ := (hc.isOpen_preimage _ isOpen_Ioi).mem_nhds h
    obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hmem ⟨0, hσpos⟩
    obtain ⟨c, hlc, hcσ⟩ := exists_between hl
    have := csInf_le (OrderBot.bddBelow _) (hsub ⟨hlc, hcσ.le⟩)
    exact absurd this (not_le.mpr (by rw [← hσ]; exact hcσ))
  · by_contra h
    push Not at h
    have hmem : {r | Jf f r < (s:ℝ)} ∈ 𝓝 σ := (hc.isOpen_preimage _ isOpen_Iio).mem_nhds h
    obtain ⟨w, hw, hsub⟩ := exists_Ico_subset_of_mem_nhds hmem ⟨σ + 1, lt_add_one σ⟩
    obtain ⟨r, hr, hrw⟩ := (csInf_lt_iff (OrderBot.bddBelow _) hE').mp hw
    have hσr : σ ≤ r := csInf_le (OrderBot.bddBelow _) hr
    have h2 : Jf f r < s := hsub ⟨hσr, hrw⟩
    exact lt_asymm hr h2

lemma sig_ne {f : ℝ≥0 → ℕ} (hf : IsCadlag f) {s : ℝ≥0} (hE : ∃ r, (s:ℝ) < Jf f r) :
    f (sInf {r | (s:ℝ) < Jf f r}) ≠ 0 := by
  set σ := sInf {r | (s:ℝ) < Jf f r} with hσ
  have hE' : ({r | (s:ℝ) < Jf f r} : Set ℝ≥0).Nonempty := hE
  intro h0
  obtain ⟨v, hv, hvc⟩ := rc_ev (hf σ).1
  obtain ⟨r, hr, hrv⟩ := (csInf_lt_iff (OrderBot.bddBelow _) hE').mp hv
  have hσr : σ ≤ r := csInf_le (OrderBot.bddBelow _) hr
  have hJ := Jf_shift hf σ (r - σ)
  rw [add_tsub_cancel_of_le hσr, sig_J hf hE] at hJ
  have h0' : Jf (fun u => f (σ + u)) (r - σ) = 0 := by
    unfold Jf
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
    intro x hx
    rw [uIcc_of_le (NNReal.coe_nonneg _)] at hx
    have hxle : x.toNNReal ≤ r - σ := Real.toNNReal_le_iff_le_coe.mpr hx.2
    have hmem : σ + x.toNNReal ∈ Ico σ v := by
      refine ⟨le_add_of_nonneg_right bot_le, ?_⟩
      calc σ + x.toNNReal ≤ σ + (r - σ) := add_le_add_right hxle σ
        _ = r := add_tsub_cancel_of_le hσr
        _ < v := hrv
    simp only
    rw [hvc _ hmem, h0, Nat.cast_zero]
  rw [h0', add_zero] at hJ
  have : (s:ℝ) < Jf f r := hr
  linarith

lemma Xf_shift {f : ℝ≥0 → ℕ} (hf : IsCadlag f) {s : ℝ≥0} (hE : ∃ r, (s:ℝ) < Jf f r)
    (t : ℝ≥0) :
    Xf f (s + t) = Xf (fun u => f (sInf {r | (s:ℝ) < Jf f r} + u)) t := by
  classical
  set σ := sInf {r | (s:ℝ) < Jf f r} with hσ
  set g : ℝ≥0 → ℕ := fun u => f (σ + u) with hg
  have hJσ : Jf f σ = s := sig_J hf hE
  have hset : {r' : ℝ≥0 | ((s + t : ℝ≥0):ℝ) < Jf f r'} =
      (fun r => σ + r) '' {r : ℝ≥0 | (t:ℝ) < Jf g r} := by
    ext r'
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · intro h
      push_cast at h
      have hσr : σ ≤ r' := by
        by_contra hlt
        push Not at hlt
        have := Jf_mono hf hlt.le
        rw [hJσ] at this
        linarith [t.2]
      refine ⟨r' - σ, ?_, add_tsub_cancel_of_le hσr⟩
      have := Jf_shift hf σ (r' - σ)
      rw [add_tsub_cancel_of_le hσr, hJσ] at this
      linarith
    · rintro ⟨r, hr, rfl⟩
      rw [Jf_shift hf, hJσ]
      push_cast
      linarith
  unfold Xf
  by_cases hB : ∃ r, (t:ℝ) < Jf g r
  · have hE' : ∃ r', ((s + t : ℝ≥0):ℝ) < Jf f r' := by
      obtain ⟨r, hr⟩ := hB
      refine ⟨σ + r, ?_⟩
      have : σ + r ∈ {r' : ℝ≥0 | ((s + t : ℝ≥0):ℝ) < Jf f r'} := by
        rw [hset]; exact ⟨r, hr, rfl⟩
      exact this
    have hm := Monotone.map_csInf_of_continuousAt (f := fun r : ℝ≥0 => σ + r)
      (A := {r : ℝ≥0 | (t:ℝ) < Jf g r})
      (continuous_const.add continuous_id).continuousAt
      (fun a b h => add_le_add_right h σ) hB (OrderBot.bddBelow _)
    rw [if_pos hE', if_pos hB, hset, ← hm]
  · have hE' : ¬ ∃ r', ((s + t : ℝ≥0):ℝ) < Jf f r' := by
      rintro ⟨r', hr'⟩
      have : r' ∈ (fun r => σ + r) '' {r : ℝ≥0 | (t:ℝ) < Jf g r} := by
        rw [← hset]; exact hr'
      obtain ⟨r, hr, -⟩ := this
      exact hB ⟨r, hr⟩
    rw [if_neg hE', if_neg hB]

lemma Xf_pos_E {f : ℝ≥0 → ℕ} {s : ℝ≥0} (h : Xf f s ≠ 0) : ∃ r, (s:ℝ) < Jf f r := by
  classical
  by_contra hE
  exact h (by unfold Xf; rw [if_neg hE])

lemma Xf_zero_of {f : ℝ≥0 → ℕ} (hf : IsCadlag f) {s : ℝ≥0} (t : ℝ≥0) (h : Xf f s = 0) :
    Xf f (s + t) = 0 := by
  classical
  by_cases hE : ∃ r, (s:ℝ) < Jf f r
  · unfold Xf at h
    rw [if_pos hE] at h
    exact absurd h (sig_ne hf hE)
  · unfold Xf
    rw [if_neg]
    rintro ⟨r, hr⟩
    push_cast at hr
    exact hE ⟨r, by linarith [t.2]⟩

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

lemma p0_X {Ω : Type*} [MeasurableSpace Ω] (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω)
    (law : PopulationLaws) (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law) (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCad : ∀ᵐ ω ∂P 0, IsCadlag (fun t : ℝ≥0 => Y t ω)) (t : ℝ≥0) (k : ℕ) :
    P 0 {ω | branchingToPoisson Y t ω = k} = if k = 0 then 1 else 0 := by
  classical
  have := hMarkov.1 0
  have hq : ∀ q : ℝ≥0, ∀ᵐ ω ∂(P 0), Y q ω = 0 := fun q => by
    rw [ae_iff_measure_eq (p := fun ω => Y q ω = 0)
      ((measurableSet_singleton 0).preimage (hMeas q)).nullMeasurableSet,
      hMarkov.2.1 0 q 0, zero_absorb hBranching, measure_univ]
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have := hDc.to_subtype
  have hD : ∀ᵐ ω ∂(P 0), ∀ q : D, Y q ω = 0 := ae_all_iff.mpr (fun q => hq q)
  have hX0 : ∀ᵐ ω ∂(P 0), branchingToPoisson Y t ω = 0 := by
    filter_upwards [hCad, hD] with ω hω hDω
    have hzero : ∀ u, Y u ω = 0 := by
      intro u
      obtain ⟨v, huv, hv⟩ := rc_ev (hω u).1
      obtain ⟨q, hqD, hq⟩ := hDd.exists_between huv
      rw [← hv q ⟨hq.1.le, hq.2⟩]
      exact hDω ⟨q, hqD⟩
    rw [btp_eq']
    unfold Xf
    split_ifs <;> simp [hzero]
  split_ifs with hk
  · subst hk
    rw [measure_congr (t := univ) (eventuallyEq_set.mpr ?_), measure_univ]
    filter_upwards [hX0] with ω hω
    simp [hω]
  · rw [measure_congr (t := ∅) (eventuallyEq_set.mpr ?_), measure_empty]
    filter_upwards [hX0] with ω hω
    simp only [hω, mem_empty_iff_false, iff_false]
    exact fun h => hk h.symm


lemma J_const {f : ℝ≥0 → ℕ} {z : ℕ} {r : ℝ≥0} (h : ∀ u ≤ r, f u = z) :
    Jf f r = z * r := by
  unfold Jf
  rw [intervalIntegral.integral_congr (g := fun _ => (z:ℝ)) ?_]
  · simp [intervalIntegral.integral_const, mul_comm]
  · intro x hx
    rw [uIcc_of_le (NNReal.coe_nonneg r)] at hx
    simp only
    rw [h _ (Real.toNNReal_le_iff_le_coe.mpr hx.2)]

lemma J_ge {f : ℝ≥0 → ℕ} (hf : IsCadlag f) {r : ℝ≥0} (h : ∀ u ≤ r, 1 ≤ f u) :
    (r:ℝ) ≤ Jf f r := by
  have : ∫ _ in (0:ℝ)..(r:ℝ), (1:ℝ) ≤ Jf f r := by
    unfold Jf
    refine intervalIntegral.integral_mono_on r.2 intervalIntegrable_const (path_ii hf _ _) ?_
    intro x hx
    exact_mod_cast h _ (Real.toNNReal_le_iff_le_coe.mpr hx.2)
  simpa using this

lemma phi_eq {f : ℝ≥0 → ℕ} (hf : IsCadlag f) {z : ℕ} (hz : 1 ≤ z) {σ : ℝ≥0}
    (hσ : ∀ u < σ, f u = z) {t : ℝ≥0} (hE : ∃ r, (t:ℝ) < Jf f r)
    (hlt : sInf {r | (t:ℝ) < Jf f r} < σ) :
    sInf {r | (t:ℝ) < Jf f r} = t / z ∧ f (sInf {r | (t:ℝ) < Jf f r}) = z := by
  set φ := sInf {r | (t:ℝ) < Jf f r} with hφ
  have hc : ∀ u ≤ φ, f u = z := fun u hu => hσ u (lt_of_le_of_lt hu hlt)
  have h1 := sig_J hf hE
  rw [← hφ, J_const hc] at h1
  refine ⟨?_, hc _ le_rfl⟩
  have hz' : (z:ℝ≥0) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
  rw [eq_div_iff hz']
  apply NNReal.coe_injective
  push_cast
  linear_combination h1

lemma path_main {f : ℝ≥0 → ℕ} (hf : IsCadlag f) {z : ℕ} (hz : 1 ≤ z) (hf0 : f 0 = z)
    {t : ℝ≥0} (ht : 0 < t)
    (habs : ∀ b c, b ≤ c → f b = 0 → f c = 0)
    (hno : ¬ ∃ a b c : ℝ≥0, a < b ∧ b < c ∧ (c:ℝ) ≤ 2 * (t:ℝ) ∧ f a ≠ f b ∧ f b ≠ f c) :
    Xf f t = f (t / z) := by
  classical
  set T : ℝ≥0 := 2 * t with hT
  have hzpos : (0:ℝ≥0) < z := by exact_mod_cast hz
  have haT : t / z ≤ T := by
    calc t / z ≤ t := div_le_self bot_le (by exact_mod_cast hz)
      _ ≤ T := by rw [hT]; exact le_mul_of_one_le_left bot_le one_le_two
  obtain ⟨σ, k, hσT, hzσ, hkσ, hk0⟩ : ∃ (σ : ℝ≥0) (k : ℕ), σ ≤ T ∧ (∀ u < σ, f u = z) ∧
      (∀ u, σ ≤ u → u ≤ T → f u = k) ∧ (k = 0 → ∀ u, σ ≤ u → f u = 0) := by
    by_cases hall : ∀ u ≤ T, f u = z
    · exact ⟨T, z, le_rfl, fun u hu => hall u hu.le, fun u _ h2 => hall u h2,
        fun h => by omega⟩
    · push Not at hall
      have hSne : ({u | u ≤ T ∧ f u ≠ z} : Set ℝ≥0).Nonempty := hall
      set σ := sInf {u | u ≤ T ∧ f u ≠ z} with hσ
      have hσT : σ ≤ T := by
        obtain ⟨u0, hu0T, hu0⟩ := hSne
        exact (csInf_le (OrderBot.bddBelow _) (show u0 ∈ {u | u ≤ T ∧ f u ≠ z} from ⟨hu0T, hu0⟩)).trans hu0T
      have hlow : ∀ u < σ, f u = z := by
        intro u hu
        by_contra hne
        have := csInf_le (OrderBot.bddBelow _) (show u ∈ {u | u ≤ T ∧ f u ≠ z} from
          ⟨(hu.trans_le hσT).le, hne⟩)
        exact absurd hu (not_lt.mpr this)
      have hσne : f σ ≠ z := by
        intro heq
        obtain ⟨v, hv, hvc⟩ := rc_ev (hf σ).1
        obtain ⟨u, huS, huv⟩ := (csInf_lt_iff (OrderBot.bddBelow _) hSne).mp hv
        have := csInf_le (OrderBot.bddBelow _) huS
        exact huS.2 ((hvc u ⟨this, huv⟩).trans heq)
      have hσ0 : 0 < σ := by
        rw [pos_iff_ne_zero]
        intro h
        rw [h] at hσne
        exact hσne hf0
      refine ⟨σ, f σ, hσT, hlow, fun u h1 h2 => ?_, fun h u hu => habs σ u hu h⟩
      rcases h1.lt_or_eq with hlt | heq
      · by_contra hne
        refine hno ⟨0, σ, u, hσ0, hlt, ?_, ?_, fun h => hne h.symm⟩
        · have := NNReal.coe_le_coe.mpr h2
          rw [hT] at this
          push_cast at this
          exact this
        · rw [hf0]; exact Ne.symm hσne
      · rw [heq]
  by_cases hcase : t / z < σ
  · have hfa : f (t / z) = z := hzσ _ hcase
    obtain ⟨r, hr1, hr2⟩ := exists_between hcase
    have hcr : ∀ u ≤ r, f u = z := fun u hu => hzσ u (lt_of_le_of_lt hu hr2)
    have hr : (t:ℝ) < Jf f r := by
      rw [J_const hcr]
      have : t < r * z := (div_lt_iff₀ hzpos).mp hr1
      have := NNReal.coe_lt_coe.mpr this
      push_cast at this
      linarith
    have hE : ∃ r, (t:ℝ) < Jf f r := ⟨r, hr⟩
    have hφ : sInf {r | (t:ℝ) < Jf f r} < σ :=
      lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) hr) hr2
    unfold Xf
    rw [if_pos hE, (phi_eq hf hz hzσ hE hφ).2, hfa]
  · push Not at hcase
    have hfa : f (t / z) = k := hkσ _ hcase haT
    have hnot : ∀ (hE : ∃ r, (t:ℝ) < Jf f r), σ ≤ sInf {r | (t:ℝ) < Jf f r} := by
      intro hE
      by_contra hlt
      push Not at hlt
      have h1 := (phi_eq hf hz hzσ hE hlt).1
      rw [h1] at hlt
      exact absurd hlt (not_lt.mpr hcase)
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hfa, hk]
      unfold Xf
      split_ifs with hE
      · exact absurd (hk0 hk _ (hnot hE)) (sig_ne hf hE)
      · rfl
    · have h1 : ∀ u ≤ T, 1 ≤ f u := by
        intro u hu
        rcases lt_or_ge u σ with h | h
        · rw [hzσ u h]; exact hz
        · rw [hkσ u h hu]; exact hk
      have hJT : (t:ℝ) < Jf f T := by
        have h2 := J_ge hf h1
        have h3 : (t:ℝ) < T := by
          rw [hT]; push_cast; linarith [NNReal.coe_pos.mpr ht]
        linarith
      have hE : ∃ r, (t:ℝ) < Jf f r := ⟨T, hJT⟩
      have hφT : sInf {r | (t:ℝ) < Jf f r} ≤ T := csInf_le (OrderBot.bddBelow _) hJT
      unfold Xf
      rw [if_pos hE, hkσ _ (hnot hE) hφT, hfa]

lemma path_zero {f : ℝ≥0 → ℕ} (hf : IsCadlag f) (hf0 : 1 ≤ f 0) : Xf f 0 = f 0 := by
  classical
  obtain ⟨v, hv, hvc⟩ := rc_ev (hf 0).1
  obtain ⟨r, hr0, hrv⟩ := exists_between hv
  have hc : ∀ u ≤ r, f u = f 0 := fun u hu => hvc u ⟨bot_le, lt_of_le_of_lt hu hrv⟩
  have hr : ((0:ℝ≥0):ℝ) < Jf f r := by
    rw [J_const hc]
    push_cast
    exact mul_pos (by exact_mod_cast hf0) (by exact_mod_cast hr0)
  have hE : ∃ r, ((0:ℝ≥0):ℝ) < Jf f r := ⟨r, hr⟩
  unfold Xf
  rw [if_pos hE, hc _ (csInf_le (OrderBot.bddBelow _) hr)]

lemma path_all {f : ℝ≥0 → ℕ} (hf : IsCadlag f) {z : ℕ} (hz : 1 ≤ z) (hf0 : f 0 = z)
    (t : ℝ≥0) (habs : ∀ b c, b ≤ c → f b = 0 → f c = 0)
    (hno : ¬ ∃ a b c : ℝ≥0, a < b ∧ b < c ∧ (c:ℝ) ≤ 2 * (t:ℝ) ∧ f a ≠ f b ∧ f b ≠ f c) :
    Xf f t = f (t / z) := by
  rcases eq_zero_or_pos t with h | h
  · rw [h, zero_div, path_zero hf (by rw [hf0]; exact hz)]
  · exact path_main hf hz hf0 h habs hno

lemma absorb_ae {Ω : Type*} [MeasurableSpace Ω] (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω)
    (law : PopulationLaws) (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law) (z : ℕ)
    (hCad : ∀ᵐ ω ∂P z, IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∀ᵐ ω ∂P z, ∀ b c : ℝ≥0, b ≤ c → Y b ω = 0 → Y c ω = 0 := by
  have hpair : ∀ s t : ℝ≥0, ∀ᵐ ω ∂P z, Y s ω = 0 → Y (s + t) ω = 0 := by
    intro s t
    have hA : @MeasurableSet Ω (naturalSigma (fun u ω => (Y u ω : ℝ)) s)
        {ω | Y s ω = 0} := by
      have hle : MeasurableSpace.comap (fun ω => (Y s ω : ℝ)) inferInstance ≤
          naturalSigma (fun u ω => (Y u ω : ℝ)) s := by
        unfold naturalSigma PerfCorrMSQ.natFiltr
        exact le_iSup₂ (f := fun (u : ℝ≥0) (_ : u ≤ s) =>
          MeasurableSpace.comap (fun ω => (Y u ω : ℝ)) inferInstance) s le_rfl
      apply hle
      exact ⟨{0}, measurableSet_singleton 0, by ext ω; simp⟩
    have hk : ∀ k : ℕ, k ≠ 0 →
        P z ({ω | Y s ω = 0} ∩ {ω | Y (s + t) ω = k}) = 0 := by
      intro k hk
      rw [hMarkov.2.2 z s t k _ hA]
      refine ENNReal.tsum_eq_zero.mpr fun w => ?_
      by_cases hw : w = 0
      · subst hw
        have h0 : law 0 t k = 0 := by
          have hs := (PMF.apply_eq_one_iff _ _).mp (zero_absorb hBranching t)
          rw [PMF.apply_eq_zero_iff, hs]
          simpa using hk
        rw [h0, mul_zero]
      · have : {ω | Y s ω = 0} ∩ {ω | Y s ω = w} = ∅ := by
          ext ω
          simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
          rintro ⟨h1, h2⟩
          exact hw (h2.symm.trans h1)
        rw [this, measure_empty, zero_mul]
    have hU : {ω | ¬ (Y s ω = 0 → Y (s + t) ω = 0)} =
        ⋃ k : {k : ℕ // k ≠ 0}, ({ω | Y s ω = 0} ∩ {ω | Y (s + t) ω = k}) := by
      ext ω
      simp only [mem_setOf_eq, _root_.not_imp, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨_, h2⟩, h1, rfl⟩
      · rintro ⟨k, h1, h2⟩; exact ⟨h1, by rw [h2]; exact k.2⟩
    rw [ae_iff, hU]
    exact measure_iUnion_null (fun k => hk k k.2)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have := hDc.to_subtype
  have hD : ∀ᵐ ω ∂P z, ∀ q q' : D, (q:ℝ≥0) ≤ q' → Y q ω = 0 → Y q' ω = 0 := by
    refine ae_all_iff.mpr fun q => ae_all_iff.mpr fun q' => ?_
    filter_upwards [hpair q ((q':ℝ≥0) - q)] with ω h hle h0
    rw [← add_tsub_cancel_of_le hle]
    exact h h0
  filter_upwards [hCad, hD] with ω hω hDω b c hbc hb
  rcases hbc.lt_or_eq with hlt | heq
  · obtain ⟨v, hv, hvc⟩ := rc_ev (hω b).1
    obtain ⟨v', hv', hvc'⟩ := rc_ev (hω c).1
    obtain ⟨q, hqD, hq⟩ := hDd.exists_between (lt_min hv hlt)
    obtain ⟨q', hq'D, hq'⟩ := hDd.exists_between hv'
    have h1 : Y q ω = 0 := by
      rw [hvc q ⟨hq.1.le, lt_of_lt_of_le hq.2 (min_le_left _ _)⟩]; exact hb
    have h2 := hDω ⟨q, hqD⟩ ⟨q', hq'D⟩
      (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le hq.2 (min_le_right _ _)) hq'.1.le)) h1
    rw [← hvc' q' ⟨hq'.1.le, hq'.2⟩]
    exact h2
  · rw [← heq]; exact hb

lemma toReal_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A B N D : Set Ω) (hN : μ N = 0) (h : A ⊆ B ∪ (N ∪ D)) :
    (μ A).toReal ≤ (μ B).toReal + (μ D).toReal := by
  have h1 : μ A ≤ μ B + μ D :=
    calc μ A ≤ μ (B ∪ (N ∪ D)) := measure_mono h
      _ ≤ μ B + μ (N ∪ D) := measure_union_le _ _
      _ ≤ μ B + (μ N + μ D) := by gcongr; exact measure_union_le _ _
      _ = μ B + μ D := by rw [hN, zero_add]
  rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h1

end LFG

open LFG in
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
    ∀ z k : ℕ,
      HasDerivWithinAt
        (fun t : ℝ => (P z {ω | branchingToPoisson Y (Real.toNNReal t) ω = k}).toReal)
        (if k = z then (if z = 0 then 0 else -(rate : ℝ))
         else if 1 ≤ z ∧ z ≤ k + 1 then
           (rate : ℝ) * (offspring (k + 1 - z)).toReal
         else 0)
        (Set.Ici 0) 0 := by
  intro z k
  have hProb := hMarkov.1
  rcases Nat.eq_zero_or_pos z with hz | hz
  · subst hz
    have h := fun t : ℝ => p0_X Y P law hBranching hMarkov hMeas (hCadlag 0) t.toNNReal k
    have hc : (fun t : ℝ => (P 0 {ω | branchingToPoisson Y (Real.toNNReal t) ω = k}).toReal)
        = fun _ => (if k = 0 then (1:ℝ≥0∞) else 0).toReal := funext fun t => by rw [h]
    have e : (if k = 0 then (if (0:ℕ) = 0 then (0:ℝ) else -(rate:ℝ)) else
        if 1 ≤ 0 ∧ 0 ≤ k + 1 then (rate:ℝ) * (offspring (k + 1 - 0)).toReal else 0) = 0 := by
      split_ifs <;> simp_all
    rw [hc, e]
    exact hasDerivWithinAt_const _ _ _
  · have hzR : (0:ℝ) < z := by exact_mod_cast hz
    -- the Y-side comparison function
    set q : ℝ → ℝ := fun t => (law z (Real.toNNReal (t / z)) k).toReal with hq_def
    set p : ℝ → ℝ := fun t =>
      (P z {ω | branchingToPoisson Y (Real.toNNReal t) ω = k}).toReal with hp_def
    set Dset : ℝ → Set Ω := fun T => {ω | ∃ a b c : ℝ≥0, a < b ∧ b < c ∧ (c : ℝ) ≤ T ∧
        Y a ω ≠ Y b ω ∧ Y b ω ≠ Y c ω} with hD_def
    set β : ℝ → ℝ := fun T => (P z (Dset T)).toReal with hβ_def
    have hchild := branchingTwoJumpsLittleO Y P law rate hRate offspring hNoNullJumps
      hBranching hMarkov hSemigroup hGenerator hInitial hMeas hCadlag z
    -- derivative of q
    have hF := hGenerator z k
    have hdiv : HasDerivWithinAt (fun t : ℝ => t / z) (1 / z) (Ici 0) 0 := by
      simpa using (hasDerivWithinAt_id (0:ℝ) (Ici 0)).div_const (z:ℝ)
    have hmaps : MapsTo (fun t : ℝ => t / z) (Ici 0) (Ici 0) :=
      fun t ht => div_nonneg ht hzR.le
    have hqd := HasDerivWithinAt.comp_of_eq (0:ℝ) hF hdiv hmaps (by simp)
    -- null set of bad paths
    set N : Set Ω := {ω | ¬ (IsCadlag (fun t : ℝ≥0 => Y t ω) ∧
        (∀ b c : ℝ≥0, b ≤ c → Y b ω = 0 → Y c ω = 0) ∧ Y 0 ω = z)} with hN_def
    have hY0 : ∀ᵐ ω ∂P z, Y 0 ω = z :=
      (ae_iff_measure_eq ((measurableSet_singleton z).preimage (hMeas 0)).nullMeasurableSet).mpr
        (by simp only [mem_singleton_iff, hInitial, measure_univ])
    have hN : P z N = 0 := by
      have hgood : ∀ᵐ ω ∂P z, IsCadlag (fun t : ℝ≥0 => Y t ω) ∧
          (∀ b c : ℝ≥0, b ≤ c → Y b ω = 0 → Y c ω = 0) ∧ Y 0 ω = z := by
        filter_upwards [hCadlag z, absorb_ae Y P law hBranching hMarkov z (hCadlag z), hY0]
          with ω h1 h2 h3 using ⟨h1, h2, h3⟩
      exact ae_iff.mp hgood
    -- pathwise comparison
    have hpath : ∀ t : ℝ, 0 ≤ t → ∀ ω, ω ∉ N → ω ∉ Dset (2 * t) →
        branchingToPoisson Y (Real.toNNReal t) ω = Y (Real.toNNReal (t / z)) ω := by
      intro t ht ω hωN hωD
      simp only [hN_def, mem_setOf_eq, not_not] at hωN
      obtain ⟨hc, habs, h0⟩ := hωN
      rw [btp_eq', path_all hc hz h0 _ habs ?_]
      · congr 1
        rw [Real.toNNReal_div ht, Real.toNNReal_natCast]
      · simpa [Real.coe_toNNReal t ht, hD_def] using hωD
    have hbound : ∀ t : ℝ, 0 ≤ t → |p t - q t| ≤ β (2 * t) := by
      intro t ht
      have hq' : q t = (P z {ω | Y (Real.toNNReal (t / z)) ω = k}).toReal := by
        rw [hq_def, hMarkov.2.1]
      rw [hq', abs_sub_le_iff]
      constructor
      · have := toReal_bound (P z) {ω | branchingToPoisson Y (Real.toNNReal t) ω = k}
          {ω | Y (Real.toNNReal (t / z)) ω = k} N (Dset (2 * t)) hN (by
            intro ω hω
            by_cases h1 : ω ∈ N
            · exact Or.inr (Or.inl h1)
            by_cases h2 : ω ∈ Dset (2 * t)
            · exact Or.inr (Or.inr h2)
            left
            simp only [mem_setOf_eq] at hω ⊢
            rw [← hpath t ht ω h1 h2]; exact hω)
        simp only [hp_def, hβ_def]
        linarith
      · have := toReal_bound (P z) {ω | Y (Real.toNNReal (t / z)) ω = k}
          {ω | branchingToPoisson Y (Real.toNNReal t) ω = k} N (Dset (2 * t)) hN (by
            intro ω hω
            by_cases h1 : ω ∈ N
            · exact Or.inr (Or.inl h1)
            by_cases h2 : ω ∈ Dset (2 * t)
            · exact Or.inr (Or.inr h2)
            left
            simp only [mem_setOf_eq] at hω ⊢
            rw [hpath t ht ω h1 h2]; exact hω)
        simp only [hp_def, hβ_def]
        linarith
    have hβ0 : β (2 * 0) = 0 := by
      have : Dset (2 * 0) = ∅ := by
        ext ω
        simp only [hD_def, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨a, b, c, -, hbc, hc, -⟩
        have : (0:ℝ) < c := by exact_mod_cast bot_le.trans_lt hbc
        linarith
      simp only [hβ_def]
      rw [this, measure_empty, ENNReal.toReal_zero]
    have hpq0 : p 0 - q 0 = 0 := by
      have := hbound 0 le_rfl
      rw [hβ0] at this
      exact abs_nonpos_iff.mp this
    -- the difference is o(t)
    have hr : HasDerivWithinAt (fun t => p t - q t) 0 (Ici 0) 0 := by
      rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
      have h2 : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have : Tendsto (fun t : ℝ => 2 * t) (𝓝 0) (𝓝 (2 * 0)) :=
            (continuous_const.mul continuous_id).tendsto 0
          rw [mul_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          exact mem_Ioi.mpr (mul_pos two_pos ht)
      have hβt : Tendsto (fun t : ℝ => 2 * (β (2 * t) / (2 * t))) (𝓝[>] 0) (𝓝 0) := by
        have := (hchild.comp h2).const_mul 2
        rw [mul_zero] at this
        exact this
      refine squeeze_zero_norm' ?_ hβt
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0:ℝ) < t := ht
      rw [slope_def_field, hpq0, sub_zero, sub_zero, norm_div, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos ht']
      rw [show 2 * (β (2 * t) / (2 * t)) = β (2 * t) / t by field_simp]
      exact div_le_div_of_nonneg_right (hbound t ht'.le) ht'.le
    have hsum := hqd.add hr
    have hzR' : (z:ℝ) ≠ 0 := hzR.ne'
    have hval : (if k = z then (if z = 0 then 0 else -(rate : ℝ))
         else if 1 ≤ z ∧ z ≤ k + 1 then
           (rate : ℝ) * (offspring (k + 1 - z)).toReal
         else 0) = (if k = z then -((rate:ℝ) * z) else if z ≤ k + 1 then
           (rate:ℝ) * z * (offspring (k + 1 - z)).toReal else 0) * (1 / z) + 0 := by
      rw [add_zero]
      split_ifs <;> first | omega | (field_simp; done) | simp_all | (field_simp; ring)
    rw [hval]
    have hfun : p = ((fun t : ℝ => ((law z (Real.toNNReal t)) k).toReal) ∘ fun t => t / z) +
        fun t => p t - q t := by
      funext t
      simp only [Pi.add_apply, Function.comp, hq_def]
      ring
    rw [hfun]
    exact hsum
