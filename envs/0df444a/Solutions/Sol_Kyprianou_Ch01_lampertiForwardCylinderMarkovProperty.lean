-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiForwardCylinderMarkovProperty
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T18:51:11.109051+00:00
-- url     : https://prove2.me/submissions/208c2082-8dfe-45f3-b13d-b73c2f16a64d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardMeasurableAndInitial
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardStrongMarkovShift
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace LFCM

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

end LFCM

open LFCM in
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
    ∀ (y : ℕ) (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (k : ℕ),
      (∀ i, u i ≤ s) →
      P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
          {ω | branchingToPoisson Y (s + t) ω = k}) =
        ∑' z : ℕ, P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
          {ω | branchingToPoisson Y s ω = z}) *
          P z {ω | branchingToPoisson Y t ω = k} := by
  classical
  intro y m u v s t k hu
  have hXae : ∀ r, AEMeasurable (fun ω => branchingToPoisson Y r ω) (P y) := fun r =>
    (lampertiForwardMeasurableAndInitial Y P law rate hRate offspring hNoNullJumps hBranching
      hMarkov hSemigroup hGenerator hInitial hMeas hCadlag y).1 r
  have hnm : ∀ r z, NullMeasurableSet {ω | branchingToPoisson Y r ω = z} (P y) := fun r z =>
    (hXae r).nullMeasurable (measurableSet_singleton z)
  set A := {ω | ∀ i, branchingToPoisson Y (u i) ω = v i} with hAdef
  have hA : NullMeasurableSet A (P y) := by
    have : A = ⋂ i, {ω | branchingToPoisson Y (u i) ω = v i} := by
      ext ω; simp [hAdef]
    rw [this]
    exact NullMeasurableSet.iInter fun i => hnm _ _
  have hdecomp : P y (A ∩ {ω | branchingToPoisson Y (s + t) ω = k}) =
      ∑' z, P y (A ∩ {ω | branchingToPoisson Y (s + t) ω = k} ∩
        {ω | branchingToPoisson Y s ω = z}) := by
    rw [← measure_iUnion₀]
    · congr 1
      ext ω
      simp
    · intro a b hab
      refine Disjoint.aedisjoint (Set.disjoint_left.mpr fun ω h1 h2 => hab ?_)
      exact h1.2.symm.trans h2.2
    · intro z
      exact (hA.inter (hnm _ _)).inter (hnm _ _)
  rw [hdecomp]
  refine tsum_congr fun z => ?_
  have hcad : ∀ᵐ ω ∂(P y), IsCadlag (fun r => Y r ω) := hCadlag y
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · have h0 : ∀ᵐ ω ∂(P y),
        branchingToPoisson Y s ω = 0 → branchingToPoisson Y (s + t) ω = 0 := by
      filter_upwards [hcad] with ω hω
      rw [btp_eq', btp_eq']
      exact Xf_zero_of hω t
    rw [p0_X Y P law hBranching hMarkov hMeas (hCadlag 0) t k]
    split_ifs with hk
    · subst hk
      rw [mul_one]
      refine measure_congr (eventuallyEq_set.mpr ?_)
      filter_upwards [h0] with ω hω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, hω h3⟩, h3⟩
    · rw [mul_zero, measure_congr (t := ∅) (eventuallyEq_set.mpr ?_), measure_empty]
      filter_upwards [h0] with ω hω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, h2⟩, h3⟩
      exact hk (h2.symm.trans (hω h3))
  · have key := lampertiForwardStrongMarkovShift Y P law rate hRate offspring hNoNullJumps
      hBranching hMarkov hSemigroup hGenerator hInitial hMeas hCadlag y m u v s t z k hu hz
    rw [← key]
    refine measure_congr (eventuallyEq_set.mpr ?_)
    filter_upwards [hcad] with ω hω
    simp only [mem_inter_iff, mem_ofPred_eq]
    have hiff : branchingToPoisson Y s ω = z →
        (branchingToPoisson Y (s + t) ω = branchingToPoisson
          (fun r ω' => Y (sInf {r' : ℝ≥0 | (s : ℝ) < branchingOccupation Y r' ω'} + r) ω')
          t ω) := by
      intro hsz
      rw [btp_eq'] at hsz
      have hE := Xf_pos_E (f := fun r => Y r ω) (by rw [hsz]; exact hz.ne')
      rw [btp_eq', btp_eq', Xf_shift hω hE]
      rfl
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, (hiff h3).symm.trans h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, (hiff h3).trans h2⟩, h3⟩
