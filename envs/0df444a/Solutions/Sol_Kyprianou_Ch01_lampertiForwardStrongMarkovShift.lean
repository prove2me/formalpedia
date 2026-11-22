-- Prove2me | solution 1 for Kyprianou.Ch01.lampertiForwardStrongMarkovShift
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-22T19:20:19.609863+00:00
-- url     : https://prove2.me/submissions/0326fccc-ec7d-4876-b46e-f5e15af086a3

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_lampertiForwardMeasurableAndInitial
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace SMS

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


/-! ### Shifted and truncated paths -/

lemma shift_cadlag {f : ℝ≥0 → ℕ} (hf : IsCadlag f) (σ : ℝ≥0) :
    IsCadlag (fun r => f (σ + r)) := by
  intro r
  have hc : Continuous (fun x : ℝ≥0 => σ + x) := continuous_const.add continuous_id
  obtain ⟨hr, l, hl⟩ := hf (σ + r)
  refine ⟨?_, l, ?_⟩
  · exact hr.comp hc.continuousWithinAt (fun x hx => by
      simp only [mem_Ici] at hx ⊢; exact add_le_add_right hx σ)
  · exact hl.comp (hc.continuousWithinAt.tendsto_nhdsWithin (fun x hx => by
      simp only [mem_Iio] at hx ⊢; exact add_lt_add_right hx σ))

lemma trunc_cadlag {f : ℝ≥0 → ℕ} (hf : IsCadlag f) (d : ℝ≥0) :
    IsCadlag (fun u => f (min u d)) := by
  intro u
  have hc : Continuous (fun x : ℝ≥0 => min x d) := continuous_id.min continuous_const
  refine ⟨?_, ?_⟩
  · exact (hf (min u d)).1.comp (f := fun x : ℝ≥0 => min x d) hc.continuousWithinAt (fun x hx => by
      simp only [mem_Ici] at hx ⊢; exact min_le_min_right d hx)
  · by_cases hud : u ≤ d
    · obtain ⟨-, l, hl⟩ := hf u
      refine ⟨l, ?_⟩
      have hev : (fun x => f (min x d)) =ᶠ[𝓝[<] u] f := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        rw [min_eq_left ((le_of_lt hx).trans hud)]
      exact hl.congr' hev.symm
    · push Not at hud
      refine ⟨f d, tendsto_const_nhds.congr' ?_⟩
      have : Ioo d u ∈ 𝓝[<] u := Ioo_mem_nhdsLT hud
      filter_upwards [this] with x hx
      rw [min_eq_right hx.1.le]

lemma Jf_trunc (f : ℝ≥0 → ℕ) {d r : ℝ≥0} (hr : r ≤ d) :
    Jf (fun u => f (min u d)) r = Jf f r := by
  unfold Jf
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le (NNReal.coe_nonneg r)] at hx
  have : x.toNNReal ≤ d := (Real.toNNReal_le_iff_le_coe.mpr hx.2).trans hr
  simp only [min_eq_left this]

lemma sInf_le_of_agree {A1 A2 : Set ℝ≥0} {d : ℝ≥0} (h : ∀ r ≤ d, r ∈ A1 → r ∈ A2)
    (hlt : ∃ r ∈ A1, r < d) : sInf A2 ≤ sInf A1 := by
  obtain ⟨r0, hr0, hr0d⟩ := hlt
  by_contra hcon
  push Not at hcon
  have h1 : sInf A1 < min (sInf A2) d :=
    lt_min hcon (lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) hr0) hr0d)
  obtain ⟨c, hc, hcb⟩ := (csInf_lt_iff (OrderBot.bddBelow _) ⟨r0, hr0⟩).mp h1
  have hc2 : c ∈ A2 := h c ((lt_of_lt_of_le hcb (min_le_right _ _)).le) hc
  have := csInf_le (OrderBot.bddBelow _) hc2
  exact absurd (lt_of_lt_of_le hcb (min_le_left _ _)) (not_lt.mpr this)

/-- Crossing of level `s` strictly before time `c`. -/
def Cr (s : ℝ≥0) (f : ℝ≥0 → ℕ) (c : ℝ≥0) : Prop := ∃ r < c, (s:ℝ) < Jf f r

lemma Cr_trunc (s : ℝ≥0) (f : ℝ≥0 → ℕ) {c d : ℝ≥0} (hc : c ≤ d) :
    Cr s (fun u => f (min u d)) c ↔ Cr s f c := by
  unfold Cr
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, by rwa [Jf_trunc f ((le_of_lt hr).trans hc)] at h⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, by rwa [Jf_trunc f ((le_of_lt hr).trans hc)]⟩

lemma Xf_trunc (f : ℝ≥0 → ℕ) {d s u : ℝ≥0} (hus : u ≤ s) (hcr : Cr s f d) :
    Xf f u = Xf (fun x => f (min x d)) u := by
  classical
  obtain ⟨r0, hr0d, hr0⟩ := hcr
  have hu0 : (u:ℝ) < Jf f r0 := lt_of_le_of_lt (by exact_mod_cast hus) hr0
  have hu0' : (u:ℝ) < Jf (fun x => f (min x d)) r0 := by rwa [Jf_trunc f hr0d.le]
  have hagree : ∀ r ≤ d, (u:ℝ) < Jf f r ↔ (u:ℝ) < Jf (fun x => f (min x d)) r :=
    fun r hr => by rw [Jf_trunc f hr]
  have h12 := sInf_le_of_agree (A1 := {r | (u:ℝ) < Jf f r})
    (A2 := {r | (u:ℝ) < Jf (fun x => f (min x d)) r}) (fun r hr h => (hagree r hr).mp h)
    ⟨r0, hu0, hr0d⟩
  have h21 := sInf_le_of_agree (A1 := {r | (u:ℝ) < Jf (fun x => f (min x d)) r})
    (A2 := {r | (u:ℝ) < Jf f r}) (fun r hr h => (hagree r hr).mpr h)
    ⟨r0, hu0', hr0d⟩
  have heq := le_antisymm h21 h12
  have hσd : sInf {r | (u:ℝ) < Jf f r} < d :=
    lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) hu0) hr0d
  unfold Xf
  rw [if_pos ⟨r0, hu0⟩, if_pos ⟨r0, hu0'⟩, ← heq]
  show f _ = f (min _ d)
  rw [min_eq_left hσd.le]

/-! ### Measurable versions on path space -/

abbrev PathS := ℝ≥0 → ℕ

noncomputable def dn (n : ℕ) (u : ℝ≥0) : ℝ≥0 :=
  (⌈((n:ℝ≥0) + 1) * u⌉₊ : ℝ≥0) / ((n:ℝ≥0) + 1)

lemma joint_dn (n : ℕ) : Measurable (fun p : ℝ≥0 × PathS => p.2 (dn n p.1)) := by
  have hG : Measurable (fun q : PathS × ℕ => q.1 ((q.2 : ℝ≥0) / ((n:ℝ≥0) + 1))) :=
    measurable_from_prod_countable_left (fun k => measurable_pi_apply ((k : ℝ≥0) / ((n:ℝ≥0) + 1)))
  have hk : Measurable (fun p : ℝ≥0 × PathS => (p.2, ⌈((n:ℝ≥0) + 1) * p.1⌉₊)) :=
    measurable_snd.prodMk (Nat.measurable_ceil.comp (measurable_const.mul measurable_fst))
  exact hG.comp hk

open Classical in
noncomputable def hatv (f : PathS) (u : ℝ≥0) : ℕ :=
  if h : ∃ c, ∀ᶠ n in atTop, f (dn n u) = c then h.choose else 0

lemma hat_spec {f : PathS} {u : ℝ≥0} {c : ℕ} (h : ∀ᶠ n in atTop, f (dn n u) = c) :
    hatv f u = c := by
  classical
  have hex : ∃ c, ∀ᶠ n in atTop, f (dn n u) = c := ⟨c, h⟩
  unfold hatv
  rw [dif_pos hex]
  obtain ⟨n, hn1, hn2⟩ := (hex.choose_spec.and h).exists
  exact hn1.symm.trans hn2

lemma hat_meas : Measurable (fun p : ℝ≥0 × PathS => hatv p.2 p.1) := by
  classical
  let ev : ℕ → Set (ℝ≥0 × PathS) := fun c => {p | ∀ᶠ n in atTop, p.2 (dn n p.1) = c}
  have hev : ∀ c, MeasurableSet (ev c) := by
    intro c
    have : ev c = ⋃ N : ℕ, ⋂ n : ℕ, ⋂ _ : N ≤ n, {p | p.2 (dn n p.1) = c} := by
      ext p; simp [ev, eventually_atTop]
    rw [this]
    exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter
      fun _ => measurableSet_eq_fun (joint_dn n) measurable_const
  refine measurable_to_countable' fun c => ?_
  have : (fun p : ℝ≥0 × PathS => hatv p.2 p.1) ⁻¹' {c} =
      ev c ∪ (if c = 0 then (⋃ c', ev c')ᶜ else ∅) := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, mem_union]
    by_cases h : ∃ c', ∀ᶠ n in atTop, p.2 (dn n p.1) = c'
    · obtain ⟨c', hc'⟩ := h
      rw [hat_spec hc']
      have hnot : p ∉ (⋃ c', ev c')ᶜ := by
        simp only [mem_compl_iff, not_not, mem_iUnion]; exact ⟨c', hc'⟩
      constructor
      · rintro rfl; exact Or.inl hc'
      · rintro (h1 | h2)
        · obtain ⟨n, hn1, hn2⟩ := (hc'.and h1).exists
          exact hn1.symm.trans hn2
        · split_ifs at h2 with hc0
          · exact absurd h2 hnot
          · exact absurd h2 (notMem_empty p)
    · have h0 : hatv p.2 p.1 = 0 := by unfold hatv; rw [dif_neg h]
      rw [h0]
      have hn : p ∉ ev c := fun hp => h ⟨c, hp⟩
      have hc : p ∈ (⋃ c', ev c')ᶜ := by
        simp only [mem_compl_iff, mem_iUnion, not_exists]; exact fun c' hp => h ⟨c', hp⟩
      constructor
      · rintro rfl; right; simpa using hc
      · rintro (h1 | h2)
        · exact absurd h1 hn
        · split_ifs at h2 with hc0
          · exact hc0.symm
          · exact absurd h2 (notMem_empty p)
  rw [this]
  refine (hev c).union ?_
  split_ifs
  · exact (MeasurableSet.iUnion hev).compl
  · exact MeasurableSet.empty

lemma hat_eq {f : PathS} (hf : IsCadlag f) : hatv f = f := by
  funext u
  obtain ⟨v, huv, hv⟩ := rc_ev (hf u).1
  exact hat_spec (by filter_upwards [d_ev huv] with n hn using hv _ hn)

noncomputable def Jh (f : PathS) (r : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ x in Ioc (0:ℝ) r, (hatv f x.toNNReal : ℝ≥0∞)

lemma Jh_meas (r : ℝ≥0) : Measurable (fun f : PathS => Jh f r) := by
  have hF : Measurable (fun q : PathS × ℝ => (hatv q.1 q.2.toNNReal : ℝ≥0∞)) :=
    measurable_from_top.comp
      (hat_meas.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
  exact hF.lintegral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) r))

lemma Jh_mono (f : PathS) {r r' : ℝ≥0} (h : r ≤ r') : Jh f r ≤ Jh f r' :=
  lintegral_mono_set (Ioc_subset_Ioc_right (by exact_mod_cast h))

lemma Jh_eq {f : PathS} (hf : IsCadlag f) (r : ℝ≥0) : Jh f r = ENNReal.ofReal (Jf f r) := by
  unfold Jh Jf
  have h1 : (∫ u in (0:ℝ)..(r:ℝ), (f u.toNNReal : ℝ)) = ∫ u in Ioc (0:ℝ) r, (f u.toNNReal : ℝ) :=
    intervalIntegral.integral_of_le r.2
  rw [hat_eq hf, h1, ofReal_integral_eq_lintegral_ofReal (path_ii hf 0 r).1
      (Eventually.of_forall fun _ => Nat.cast_nonneg _)]
  simp only [ENNReal.ofReal_natCast]

lemma cross_iff {f : PathS} (hf : IsCadlag f) (t r : ℝ≥0) :
    (t:ℝ≥0∞) < Jh f r ↔ (t:ℝ) < Jf f r := by
  rw [Jh_eq hf, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff']
  exact ⟨And.left, fun h => ⟨h, lt_of_le_of_lt t.2 h⟩⟩

lemma set_eq_of_cadlag {f : PathS} (hf : IsCadlag f) (t : ℝ≥0) :
    {r | (t:ℝ≥0∞) < Jh f r} = {r | (t:ℝ) < Jf f r} := by
  ext r; exact cross_iff hf t r

open Classical in
noncomputable def Phi (t : ℝ≥0) (f : PathS) : ℕ :=
  if ∃ r, (t:ℝ≥0∞) < Jh f r then hatv f (sInf {r | (t:ℝ≥0∞) < Jh f r}) else 0

noncomputable def Th (t : ℝ≥0) (f : PathS) : ℝ≥0 := sInf {r | (t:ℝ≥0∞) < Jh f r}

lemma Phi_eq {f : PathS} (hf : IsCadlag f) (t : ℝ≥0) : Phi t f = Xf f t := by
  classical
  unfold Phi Xf
  rw [set_eq_of_cadlag hf, hat_eq hf]
  have : (∃ r, (t:ℝ≥0∞) < Jh f r) ↔ ∃ r, (t:ℝ) < Jf f r :=
    exists_congr fun r => cross_iff hf t r
  by_cases h : ∃ r, (t:ℝ) < Jf f r
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]

lemma Th_eq {f : PathS} (hf : IsCadlag f) (t : ℝ≥0) :
    Th t f = sInf {r | (t:ℝ) < Jf f r} := by
  unfold Th; rw [set_eq_of_cadlag hf]

lemma Es_meas (t : ℝ≥0) : MeasurableSet {f : PathS | ∃ r, (t:ℝ≥0∞) < Jh f r} := by
  have : {f : PathS | ∃ r, (t:ℝ≥0∞) < Jh f r} = ⋃ n : ℕ, {f | (t:ℝ≥0∞) < Jh f n} := by
    ext f
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨n, hn⟩ := exists_nat_ge r
      exact ⟨n, hr.trans_le (Jh_mono f hn)⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn⟩
  rw [this]
  exact MeasurableSet.iUnion fun n => measurableSet_lt measurable_const (Jh_meas _)

lemma Th_meas (t : ℝ≥0) : Measurable (Th t) := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  refine measurable_of_Iio fun r => ?_
  have : Th t ⁻¹' Iio r =
      ({f : PathS | ∃ s : ℝ≥0, (t:ℝ≥0∞) < Jh f s} ∩
        ⋃ q ∈ D, ({f : PathS | q < r} ∩ {f | (t:ℝ≥0∞) < Jh f q})) ∪
      ({f : PathS | ∃ s : ℝ≥0, (t:ℝ≥0∞) < Jh f s}ᶜ ∩ {f | 0 < r}) := by
    ext f
    simp only [Th, mem_preimage, mem_Iio, mem_union, mem_inter_iff, mem_iUnion, mem_ofPred_eq,
      mem_compl_iff, exists_prop]
    by_cases hω : ∃ s : ℝ≥0, (t:ℝ≥0∞) < Jh f s
    · simp only [hω, true_and, not_true_eq_false, false_and, or_false]
      rw [csInf_lt_iff (OrderBot.bddBelow _)
        (show ({s : ℝ≥0 | (t:ℝ≥0∞) < Jh f s}).Nonempty from hω)]
      constructor
      · rintro ⟨a, ha, har⟩
        obtain ⟨q, hqD, hq⟩ := hDd.exists_between har
        exact ⟨q, hqD, hq.2, lt_of_lt_of_le ha (Jh_mono f hq.1.le)⟩
      · rintro ⟨q, hqD, hqr, hq⟩
        exact ⟨q, hq, hqr⟩
    · have hempty : {s : ℝ≥0 | (t:ℝ≥0∞) < Jh f s} = ∅ := by
        ext s
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hω ⟨s, h⟩
      simp only [hω, false_and, not_false_eq_true, true_and, false_or, hempty,
        NNReal.sInf_empty]
  rw [this]
  exact ((Es_meas t).inter (MeasurableSet.biUnion hDc fun q _ =>
    (MeasurableSet.const _).inter (measurableSet_lt measurable_const (Jh_meas q)))).union
    ((Es_meas t).compl.inter (MeasurableSet.const _))

lemma Phi_meas (t : ℝ≥0) : Measurable (Phi t) := by
  classical
  have : Phi t = fun f => if (∃ r, (t:ℝ≥0∞) < Jh f r) then hatv f (Th t f) else 0 := by
    funext f; rfl
  rw [this]
  exact Measurable.ite (Es_meas t) (hat_meas.comp ((Th_meas t).prodMk measurable_id))
    measurable_const

def Crh (s c : ℝ≥0) : Set PathS := {f | ∃ r < c, (s:ℝ≥0∞) < Jh f r}

lemma Crh_meas (s c : ℝ≥0) : MeasurableSet (Crh s c) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Crh s c = ⋃ q ∈ D, ({f : PathS | q < c} ∩ {f | (s:ℝ≥0∞) < Jh f q}) := by
    ext f
    simp only [Crh, mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · rintro ⟨r, hrc, hr⟩
      obtain ⟨q, hqD, hq⟩ := hDd.exists_between hrc
      exact ⟨q, hqD, hq.2, lt_of_lt_of_le hr (Jh_mono f hq.1.le)⟩
    · rintro ⟨q, -, hqc, hq⟩; exact ⟨q, hqc, hq⟩
  rw [this]
  exact MeasurableSet.biUnion hDc fun q _ =>
    (MeasurableSet.const _).inter (measurableSet_lt measurable_const (Jh_meas q))

lemma Crh_iff {f : PathS} (hf : IsCadlag f) (s c : ℝ≥0) : f ∈ Crh s c ↔ Cr s f c := by
  unfold Crh Cr
  simp only [mem_ofPred_eq]
  exact exists_congr fun r => and_congr_right fun _ => cross_iff hf s r


/-! ### Natural filtration and the multi-time Markov property -/

section Markov
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

noncomputable abbrev FF (Y : ℝ≥0 → Ω → ℕ) (d : ℝ≥0) : MeasurableSpace Ω :=
  naturalSigma (fun u ω => (Y u ω : ℝ)) d

lemma FF_mono (Y : ℝ≥0 → Ω → ℕ) {d d' : ℝ≥0} (h : d ≤ d') : FF Y d ≤ FF Y d' := by
  unfold FF naturalSigma PerfCorrMSQ.natFiltr
  exact iSup₂_mono' fun u hu => ⟨u, hu.trans h, le_rfl⟩

lemma FF_le (Y : ℝ≥0 → Ω → ℕ) (hMeas : ∀ t, Measurable (Y t)) (d : ℝ≥0) : FF Y d ≤ mΩ := by
  unfold FF naturalSigma PerfCorrMSQ.natFiltr
  exact iSup₂_le fun u _ => (measurable_from_top.comp (hMeas u)).comap_le

lemma FF_meas_Y (Y : ℝ≥0 → Ω → ℕ) {u d : ℝ≥0} (hu : u ≤ d) : Measurable[FF Y d] (Y u) := by
  refine @measurable_to_countable' ℕ Ω _ _ (FF Y d) (Y u) fun c => ?_
  have hle : MeasurableSpace.comap (fun ω => (Y u ω : ℝ)) inferInstance ≤ FF Y d := by
    unfold FF naturalSigma PerfCorrMSQ.natFiltr
    exact le_iSup₂ (f := fun (u : ℝ≥0) (_ : u ≤ d) =>
      MeasurableSpace.comap (fun ω => (Y u ω : ℝ)) inferInstance) u hu
  apply hle
  refine ⟨{(c:ℝ)}, measurableSet_singleton _, ?_⟩
  ext ω; simp

lemma trunc_meas (Y : ℝ≥0 → Ω → ℕ) (d : ℝ≥0) :
    Measurable[FF Y d] (fun ω => (fun u => Y (min u d) ω : PathS)) :=
  @measurable_pi_lambda _ _ _ (FF Y d) _ _ fun u => FF_meas_Y Y (min_le_right u d)

lemma rec_step (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (hM : IsPopulationMarkovPath Y P law) (y : ℕ) (d : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[FF Y d] A) (x : ℕ) (R : Finset ℝ≥0) (w : ℝ≥0 → ℕ) (a : ℝ≥0)
    (ha : ∀ r ∈ R, r < a) :
    P y (A ∩ {ω | Y d ω = x} ∩ {ω | ∀ r ∈ insert a R, Y (d + r) ω = w r}) =
      P y (A ∩ {ω | Y d ω = x} ∩ {ω | ∀ r ∈ R, Y (d + r) ω = w r}) *
        law (if h : R.Nonempty then w (R.max' h) else x)
          (a - (if h : R.Nonempty then R.max' h else 0)) (w a) := by
  classical
  set b : ℝ≥0 := (if h : R.Nonempty then R.max' h else 0) with hb
  set pv : ℕ := (if h : R.Nonempty then w (R.max' h) else x) with hpv
  have hba : b ≤ a := by
    rw [hb]; split_ifs with h
    · exact (ha _ (R.max'_mem h)).le
    · exact bot_le
  have hrb : ∀ r ∈ R, r ≤ b := by
    intro r hr
    rw [hb]; split_ifs with h
    · exact R.le_max' r hr
    · exact absurd ⟨r, hr⟩ h
  set A' := A ∩ {ω | Y d ω = x} ∩ {ω | ∀ r ∈ R, Y (d + r) ω = w r} with hA'def
  have hA' : MeasurableSet[FF Y (d + b)] A' := by
    refine ((FF_mono Y le_self_add _ hA).inter ?_).inter ?_
    · exact FF_meas_Y Y le_self_add (measurableSet_singleton x)
    · have : {ω | ∀ r ∈ R, Y (d + r) ω = w r} = ⋂ r ∈ R, {ω | Y (d + r) ω = w r} := by
        ext; simp
      rw [this]
      exact MeasurableSet.biInter R.countable_toSet fun r hr =>
        FF_meas_Y Y (add_le_add_right (hrb r hr) d) (measurableSet_singleton _)
  have hsub : A' ⊆ {ω | Y (d + b) ω = pv} := by
    intro ω hω
    simp only [mem_ofPred_eq]
    rw [hb, hpv]
    split_ifs with h
    · exact hω.2 _ (R.max'_mem h)
    · simpa using hω.1.2
  have hset : A ∩ {ω | Y d ω = x} ∩ {ω | ∀ r ∈ insert a R, Y (d + r) ω = w r} =
      A' ∩ {ω | Y ((d + b) + (a - b)) ω = w a} := by
    rw [add_assoc, add_tsub_cancel_of_le hba]
    ext ω
    simp only [hA'def, mem_inter_iff, mem_ofPred_eq, Finset.forall_mem_insert]
    tauto
  rw [hset, hM.2.2 y (d + b) (a - b) (w a) A' hA', tsum_eq_single pv]
  · rw [inter_eq_left.mpr hsub]
  · intro z hz
    have : A' ∩ {ω | Y (d + b) ω = z} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and, mem_ofPred_eq]
      intro h1 h2
      exact hz (h2.symm.trans (hsub h1))
    rw [this, measure_empty, zero_mul]

lemma M1_meas (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (hM : IsPopulationMarkovPath Y P law) (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t, Measurable (Y t))
    (y : ℕ) (d : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[FF Y d] A) (x : ℕ)
    (R : Finset ℝ≥0) (w : ℝ≥0 → ℕ) :
    P y (A ∩ {ω | Y d ω = x} ∩ {ω | ∀ r ∈ R, Y (d + r) ω = w r}) =
      P y (A ∩ {ω | Y d ω = x}) * P x {ω | ∀ r ∈ R, Y r ω = w r} := by
  classical
  have key : P y (A ∩ {ω | Y d ω = x} ∩ {ω | ∀ r ∈ R, Y (d + r) ω = w r}) =
      P y (A ∩ {ω | Y d ω = x}) *
        P x (univ ∩ {ω | Y 0 ω = x} ∩ {ω | ∀ r ∈ R, Y (0 + r) ω = w r}) := by
    induction R using Finset.induction_on_max with
    | empty =>
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, setOf_true,
        inter_univ, univ_inter, hInitial x, mul_one]
    | insert a R ha ih =>
      rw [rec_step Y P law hM y d A hA x R w a ha, ih,
        rec_step Y P law hM x 0 univ MeasurableSet.univ x R w a ha, mul_assoc]
  rw [key]
  congr 1
  have := hM.1 x
  have hc : P x {ω | Y 0 ω = x}ᶜ = 0 :=
    (prob_compl_eq_zero_iff ((measurableSet_singleton x).preimage (hMeas 0))).mpr (hInitial x)
  simp only [univ_inter, zero_add]
  rw [inter_comm]
  exact measure_inter_conull hc

end Markov

/-! ### Strong Markov property at the inverse clock for finite cylinders -/

section Strong
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma tend_meas {μ : Measure Ω} [IsFiniteMeasure μ] {S : ℕ → Set Ω} {S0 : Set Ω}
    (hS : ∀ n, NullMeasurableSet (S n) μ) (hS0 : NullMeasurableSet S0 μ)
    (h : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, (ω ∈ S n ↔ ω ∈ S0)) :
    Tendsto (fun n => μ (S n)) atTop (𝓝 (μ S0)) := by
  have := tendsto_lintegral_of_dominated_convergence' (μ := μ)
    (F := fun n => (S n).indicator (1 : Ω → ℝ≥0∞)) (f := S0.indicator 1) 1
    (fun n => aemeasurable_const.indicator₀ (hS n))
    (fun n => Eventually.of_forall fun ω => by
      simp only [Set.indicator, Pi.one_apply]; split_ifs <;> simp)
    (by simp [measure_ne_top])
    (by
      filter_upwards [h] with ω hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hω] with n hn
      by_cases h0 : ω ∈ S0 <;> simp [Set.indicator, h0, hn])
  simpa only [lintegral_indicator_one₀ (hS _), lintegral_indicator_one₀ hS0] using this

lemma cylD_meas (Y : ℝ≥0 → Ω → ℕ) (hMeas : ∀ t, Measurable (Y t)) (d : ℝ≥0)
    (R : Finset ℝ≥0) (w : ℝ≥0 → ℕ) : MeasurableSet {ω | ∀ r ∈ R, Y (d + r) ω = w r} := by
  have : {ω | ∀ r ∈ R, Y (d + r) ω = w r} = ⋂ r ∈ R, {ω | Y (d + r) ω = w r} := by
    ext; simp
  rw [this]
  exact MeasurableSet.biInter R.countable_toSet fun r _ =>
    (hMeas _) (measurableSet_singleton _)

lemma cyl_strong (Y : ℝ≥0 → Ω → ℕ) (P : ℕ → Measure Ω) (law : PopulationLaws)
    (hM : IsPopulationMarkovPath Y P law) (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t, Measurable (Y t)) (y : ℕ)
    (hcad : ∀ᵐ ω ∂P y, IsCadlag (fun t : ℝ≥0 => Y t ω))
    (hX : ∀ r, AEMeasurable (fun ω => branchingToPoisson Y r ω) (P y))
    (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s : ℝ≥0) (z : ℕ)
    (hu : ∀ i, u i ≤ s) (hz : 0 < z) (R : Finset ℝ≥0) (w : ℝ≥0 → ℕ) :
    P y (({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
        {ω | branchingToPoisson Y s ω = z}) ∩
        {ω | ∀ r ∈ R, Y (sInf {r' | (s:ℝ) < Jf (fun x => Y x ω) r'} + r) ω = w r}) =
      P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
        {ω | branchingToPoisson Y s ω = z}) * P z {ω | ∀ r ∈ R, Y r ω = w r} := by
  classical
  have hPy := hM.1 y
  have hPz := hM.1 z
  obtain ⟨E, hEdef⟩ : ∃ E : Set Ω, E = {ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
      {ω | branchingToPoisson Y s ω = z} := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Ω → ℝ≥0, ∀ ω, T ω = sInf {r' | (s:ℝ) < Jf (fun x => Y x ω) r'} :=
    ⟨_, fun _ => rfl⟩
  have hCset : {ω | ∀ r ∈ R, Y (sInf {r' | (s:ℝ) < Jf (fun x => Y x ω) r'} + r) ω = w r} =
      {ω | ∀ r ∈ R, Y (T ω + r) ω = w r} := by
    ext ω; simp only [mem_ofPred_eq, hT]
  rw [← hEdef, hCset]
  set C := {ω | ∀ r ∈ R, Y (T ω + r) ω = w r} with hCdef
  set pz := P z {ω | ∀ r ∈ R, Y r ω = w r} with hpz
  -- basic facts on E
  have hEX : ∀ ω, ω ∈ E ↔ (∀ i, Xf (fun x => Y x ω) (u i) = v i) ∧ Xf (fun x => Y x ω) s = z := by
    intro ω; rw [hEdef]; simp only [mem_inter_iff, mem_ofPred_eq, btp_eq']
  have hEcr : ∀ ω ∈ E, ∃ r, (s:ℝ) < Jf (fun x => Y x ω) r := by
    intro ω hω
    apply Xf_pos_E
    rw [((hEX ω).mp hω).2]; exact hz.ne'
  have hEYT : ∀ ω ∈ E, Y (T ω) ω = z := by
    intro ω hω
    have h2 := ((hEX ω).mp hω).2
    unfold Xf at h2
    rw [if_pos (hEcr ω hω), ← hT] at h2
    exact h2
  have hcr_iff : ∀ ω ∈ E, ∀ c, Cr s (fun x => Y x ω) c ↔ T ω < c := by
    intro ω hω c
    unfold Cr
    rw [hT, csInf_lt_iff (OrderBot.bddBelow _)
      (show ({r' | (s:ℝ) < Jf (fun x => Y x ω) r'} : Set ℝ≥0).Nonempty from hEcr ω hω)]
    constructor
    · rintro ⟨r, hrc, hr⟩; exact ⟨r, hr, hrc⟩
    · rintro ⟨r, hr, hrc⟩; exact ⟨r, hrc, hr⟩
  have hnm : ∀ r z', NullMeasurableSet {ω | branchingToPoisson Y r ω = z'} (P y) := fun r z' =>
    (hX r).nullMeasurable (measurableSet_singleton z')
  have hEnm : NullMeasurableSet E (P y) := by
    have : {ω | ∀ i, branchingToPoisson Y (u i) ω = v i} =
        ⋂ i, {ω | branchingToPoisson Y (u i) ω = v i} := by ext; simp
    rw [hEdef, this]
    exact (NullMeasurableSet.iInter fun i => hnm _ _).inter (hnm _ _)
  -- the grid
  obtain ⟨jn, hjn⟩ : ∃ jn : ℕ → Ω → ℕ, ∀ n ω, jn n ω = ⌊((n:ℝ≥0) + 1) * T ω⌋₊ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨dd, hdd⟩ : ∃ dd : ℕ → ℕ → ℝ≥0, ∀ n j, dd n j = ((j:ℝ≥0) + 1) / ((n:ℝ≥0) + 1) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨ll, hll⟩ : ∃ ll : ℕ → ℕ → ℝ≥0, ∀ n j, ll n j = (j:ℝ≥0) / ((n:ℝ≥0) + 1) :=
    ⟨_, fun _ _ => rfl⟩
  have hn1 : ∀ n : ℕ, (0:ℝ≥0) < (n:ℝ≥0) + 1 := fun n => by positivity
  have hlldd : ∀ n j, ll n j ≤ dd n j := by
    intro n j; rw [hll, hdd]
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (hn1 n).le
  have hjn_iff : ∀ n ω j, jn n ω = j ↔ ll n j ≤ T ω ∧ T ω < dd n j := by
    intro n ω j
    rw [hjn, Nat.floor_eq_iff bot_le, hll, hdd, div_le_iff₀ (hn1 n), lt_div_iff₀ (hn1 n),
      mul_comm (T ω)]
  let τ : ℕ → Ω → ℝ≥0 := fun n ω => dd n (jn n ω)
  have hτ : ∀ n ω, T ω < τ n ω ∧ (τ n ω : ℝ) ≤ T ω + 1 / ((n:ℝ) + 1) := by
    intro n ω
    have h := (hjn_iff n ω (jn n ω)).mp rfl
    refine ⟨h.2, ?_⟩
    have h1 := h.1
    show ((dd n (jn n ω) : ℝ≥0) : ℝ) ≤ T ω + 1 / ((n:ℝ) + 1)
    rw [hll] at h1
    rw [hdd]
    have h1' : ((jn n ω : ℝ≥0) : ℝ) / ((n:ℝ) + 1) ≤ T ω := by exact_mod_cast h1
    push_cast at h1' ⊢
    rw [add_div]
    linarith
  -- events on the grid
  let Enj : ℕ → ℕ → Set Ω := fun n j => E ∩ {ω | jn n ω = j}
  let Ev : ℕ → ℕ → PathS → Prop := fun n j f =>
    (∀ i, Xf f (u i) = v i) ∧ Xf f s = z ∧ Cr s f (dd n j) ∧ ¬ Cr s f (ll n j)
  have hEnj_ev : ∀ n j ω, ω ∈ Enj n j ↔ Ev n j (fun x => Y x ω) := by
    intro n j ω
    simp only [Enj, Ev, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hE, hj⟩
      have hj' := (hjn_iff n ω j).mp hj
      obtain ⟨h1, h2⟩ := (hEX ω).mp hE
      exact ⟨h1, h2, (hcr_iff ω hE _).mpr hj'.2,
        fun h => absurd ((hcr_iff ω hE _).mp h) (not_lt.mpr hj'.1)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      have hE : ω ∈ E := (hEX ω).mpr ⟨h1, h2⟩
      refine ⟨hE, (hjn_iff n ω j).mpr ⟨?_, (hcr_iff ω hE _).mp h3⟩⟩
      by_contra hlt
      push Not at hlt
      exact h4 ((hcr_iff ω hE _).mpr hlt)
  have hEv_trunc : ∀ n j (f : PathS), Ev n j f ↔ Ev n j (fun x => f (min x (dd n j))) := by
    intro n j f
    simp only [Ev]
    rw [Cr_trunc s f le_rfl, Cr_trunc s f (hlldd n j)]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i => ?_, ?_, h3, h4⟩
      · rw [← Xf_trunc f (hu i) h3]; exact h1 i
      · rw [← Xf_trunc f le_rfl h3]; exact h2
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i => ?_, ?_, h3, h4⟩
      · rw [Xf_trunc f (hu i) h3]; exact h1 i
      · rw [Xf_trunc f le_rfl h3]; exact h2
  let H : ℕ → ℕ → Set PathS := fun n j =>
    {g | (∀ i, Phi (u i) g = v i) ∧ Phi s g = z ∧ g ∈ Crh s (dd n j) ∧ g ∉ Crh s (ll n j)}
  have hHmeas : ∀ n j, MeasurableSet (H n j) := by
    intro n j
    have : H n j = (⋂ i, Phi (u i) ⁻¹' {v i}) ∩ Phi s ⁻¹' {z} ∩ Crh s (dd n j) ∩
        (Crh s (ll n j))ᶜ := by
      ext g; simp [H, and_assoc]
    rw [this]
    exact (((MeasurableSet.iInter fun i => Phi_meas _ (measurableSet_singleton _)).inter
      (Phi_meas _ (measurableSet_singleton _))).inter (Crh_meas _ _)).inter (Crh_meas _ _).compl
  have hH_iff : ∀ n j (g : PathS), IsCadlag g → (g ∈ H n j ↔ Ev n j g) := by
    intro n j g hg
    simp only [H, Ev, mem_ofPred_eq, Phi_eq hg, Crh_iff hg]
  let A0 : ℕ → ℕ → Set Ω := fun n j =>
    (fun ω => (fun x => Y (min x (dd n j)) ω : PathS)) ⁻¹' H n j
  have hA0F : ∀ n j, MeasurableSet[FF Y (dd n j)] (A0 n j) :=
    fun n j => trunc_meas Y _ (hHmeas n j)
  have hA0 : ∀ n j, MeasurableSet (A0 n j) := fun n j => FF_le Y hMeas _ _ (hA0F n j)
  have hEnj_ae : ∀ n j, Enj n j =ᵐ[P y] A0 n j := by
    intro n j
    refine eventuallyEq_set.mpr ?_
    filter_upwards [hcad] with ω hω
    rw [hEnj_ev, hEv_trunc]
    exact (hH_iff n j _ (trunc_cadlag hω _)).symm
  have hEnj_nm : ∀ n j, NullMeasurableSet (Enj n j) (P y) := fun n j =>
    (hA0 n j).nullMeasurableSet.congr (hEnj_ae n j).symm
  have hEnj_disj : ∀ n, Pairwise (fun a b => Disjoint (Enj n a) (Enj n b)) := by
    intro n a b hab
    exact Set.disjoint_left.mpr fun ω h1 h2 => hab (h1.2.symm.trans h2.2)
  have hM1 : ∀ n j x, P y (Enj n j ∩ {ω | Y (dd n j) ω = x} ∩
      {ω | ∀ r ∈ R, Y (dd n j + r) ω = w r}) =
      P y (Enj n j ∩ {ω | Y (dd n j) ω = x}) * P x {ω | ∀ r ∈ R, Y r ω = w r} := by
    intro n j x
    rw [measure_congr (((hEnj_ae n j).inter (ae_eq_refl {ω | Y (dd n j) ω = x})).inter
        (ae_eq_refl {ω | ∀ r ∈ R, Y (dd n j + r) ω = w r})),
      measure_congr ((hEnj_ae n j).inter (ae_eq_refl {ω | Y (dd n j) ω = x}))]
    exact M1_meas Y P law hM hInitial hMeas y _ _ (hA0F n j) x R w
  -- decompositions
  let Cn : ℕ → Set Ω := fun n => {ω | ∀ r ∈ R, Y (τ n ω + r) ω = w r}
  have hS1 : ∀ n, E ∩ Cn n = ⋃ j, Enj n j ∩ {ω | ∀ r ∈ R, Y (dd n j + r) ω = w r} := by
    intro n; ext ω
    simp only [Cn, Enj, τ, mem_inter_iff, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨hE, hC⟩; exact ⟨jn n ω, ⟨hE, rfl⟩, hC⟩
    · rintro ⟨j, ⟨hE, hj⟩, hC⟩; exact ⟨hE, by rw [hj]; exact hC⟩
  have hS3 : ∀ n x, E ∩ {ω | Y (τ n ω) ω = x} = ⋃ j, Enj n j ∩ {ω | Y (dd n j) ω = x} := by
    intro n x; ext ω
    simp only [Enj, τ, mem_inter_iff, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨hE, hC⟩; exact ⟨jn n ω, ⟨hE, rfl⟩, hC⟩
    · rintro ⟨j, ⟨hE, hj⟩, hC⟩; exact ⟨hE, by rw [hj]; exact hC⟩
  have hsumJ : ∀ n (K : ℕ → Set Ω), (∀ j, MeasurableSet (K j)) →
      P y (⋃ j, Enj n j ∩ K j) = ∑' j, P y (Enj n j ∩ K j) := by
    intro n K hK
    exact measure_iUnion₀ (fun a b hab => Disjoint.aedisjoint
      ((hEnj_disj n hab).mono inter_subset_left inter_subset_left))
      (fun j => (hEnj_nm n j).inter (hK j).nullMeasurableSet)
  have hsplitX : ∀ (B : Set Ω) (d : ℝ≥0), NullMeasurableSet B (P y) →
      P y B = ∑' x, P y (B ∩ {ω | Y d ω = x}) := by
    intro B d hB
    rw [← measure_iUnion₀]
    · congr 1; ext ω; simp
    · intro a b hab
      exact Disjoint.aedisjoint (Set.disjoint_left.mpr fun ω h1 h2 => hab (h1.2.symm.trans h2.2))
    · intro x; exact hB.inter ((hMeas d) (measurableSet_singleton x)).nullMeasurableSet
  have hcyl : ∀ d, MeasurableSet {ω | ∀ r ∈ R, Y (d + r) ω = w r} :=
    fun d => cylD_meas Y hMeas d R w
  let RHS : ℕ → ℝ≥0∞ := fun n =>
    ∑' x, P y (E ∩ {ω | Y (τ n ω) ω = x}) * P x {ω | ∀ r ∈ R, Y r ω = w r}
  have hRHS : ∀ n, P y (E ∩ Cn n) = RHS n := by
    intro n
    rw [hS1, hsumJ n _ (fun j => hcyl _)]
    have : ∀ j, P y (Enj n j ∩ {ω | ∀ r ∈ R, Y (dd n j + r) ω = w r}) =
        ∑' x, P y (Enj n j ∩ {ω | Y (dd n j) ω = x}) * P x {ω | ∀ r ∈ R, Y r ω = w r} := by
      intro j
      rw [hsplitX _ (dd n j) ((hEnj_nm n j).inter (hcyl _).nullMeasurableSet)]
      refine tsum_congr fun x => ?_
      rw [inter_right_comm, hM1]
    rw [tsum_congr this, ENNReal.tsum_comm]
    refine tsum_congr fun x => ?_
    rw [ENNReal.tsum_mul_right, hS3, hsumJ n (fun j => {ω | Y (dd n j) ω = x})
      (fun j => (hMeas _) (measurableSet_singleton x))]
  -- null measurability
  have hS3nm : ∀ n x, NullMeasurableSet (E ∩ {ω | Y (τ n ω) ω = x}) (P y) := by
    intro n x; rw [hS3]
    exact NullMeasurableSet.iUnion fun j =>
      (hEnj_nm n j).inter ((hMeas _) (measurableSet_singleton x)).nullMeasurableSet
  have hS1nm : ∀ n, NullMeasurableSet (E ∩ Cn n) (P y) := by
    intro n; rw [hS1]
    exact NullMeasurableSet.iUnion fun j => (hEnj_nm n j).inter (hcyl _).nullMeasurableSet
  have hπ : Measurable (fun ω => (fun x => Y x ω : PathS)) := measurable_pi_lambda _ hMeas
  have hCnm : NullMeasurableSet (E ∩ C) (P y) := by
    refine hEnm.inter ?_
    let Ch := {ω | ∀ r ∈ R, hatv (fun x => Y x ω) (Th s (fun x => Y x ω) + r) = w r}
    have hChm : MeasurableSet Ch := by
      have : Ch = ⋂ r ∈ R, {ω | hatv (fun x => Y x ω) (Th s (fun x => Y x ω) + r) = w r} := by
        ext; simp [Ch]
      rw [this]
      exact MeasurableSet.biInter R.countable_toSet fun r _ =>
        measurableSet_eq_fun (hat_meas.comp ((((Th_meas s).comp hπ).add_const r).prodMk hπ))
          measurable_const
    refine hChm.nullMeasurableSet.congr (eventuallyEq_set.mpr ?_)
    filter_upwards [hcad] with ω hω
    simp only [Ch, hCdef, mem_ofPred_eq, hat_eq hω, Th_eq hω, hT]
  -- first limit
  have hL1 : Tendsto (fun n => P y (E ∩ Cn n)) atTop (𝓝 (P y (E ∩ C))) := by
    refine tend_meas hS1nm hCnm ?_
    filter_upwards [hcad] with ω hω
    by_cases hωE : ω ∈ E
    · have hev : ∀ᶠ n in atTop, ∀ r ∈ R, Y (τ n ω + r) ω = Y (T ω + r) ω := by
        refine (Filter.eventually_all_finset R).mpr fun r _ => ?_
        obtain ⟨v', hv', hvc⟩ := rc_ev (hω (T ω + r)).1
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt
          (sub_pos.mpr (show ((T ω + r : ℝ≥0) : ℝ) < v' from hv'))
        filter_upwards [eventually_ge_atTop N] with n hn
        apply hvc
        have h1 := hτ n ω
        constructor
        · exact add_le_add_left h1.1.le r
        · rw [← NNReal.coe_lt_coe]
          push_cast at hN ⊢
          have h2 : 1 / ((n:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) := Nat.one_div_le_one_div hn
          linarith [h1.2]
      filter_upwards [hev] with n hn
      simp only [Cn, hCdef, mem_inter_iff, mem_ofPred_eq, hωE, true_and]
      constructor
      · intro h r hr; rw [← hn r hr]; exact h r hr
      · intro h r hr; rw [hn r hr]; exact h r hr
    · exact Eventually.of_forall fun n => by simp [hωE]
  -- second limit
  let a : ℕ → ℝ≥0∞ := fun n => P y (E ∩ {ω | Y (τ n ω) ω = z})
  have hL2 : Tendsto a atTop (𝓝 (P y E)) := by
    refine tend_meas (fun n => hS3nm n z) hEnm ?_
    filter_upwards [hcad] with ω hω
    by_cases hωE : ω ∈ E
    · obtain ⟨v', hv', hvc⟩ := rc_ev (hω (T ω)).1
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr (show (T ω : ℝ) < v' from hv'))
      filter_upwards [eventually_ge_atTop N] with n hn
      have h1 := hτ n ω
      have hmem : τ n ω ∈ Ico (T ω) v' := by
        refine ⟨h1.1.le, ?_⟩
        rw [← NNReal.coe_lt_coe]
        have h2 : 1 / ((n:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) := Nat.one_div_le_one_div hn
        linarith [h1.2]
      simp only [mem_inter_iff, mem_ofPred_eq, hωE, true_and, hvc _ hmem, hEYT ω hωE]
    · exact Eventually.of_forall fun n => by simp [hωE]
  have hpart : ∀ n, P y E = ∑' x, P y (E ∩ {ω | Y (τ n ω) ω = x}) := by
    intro n
    rw [← measure_iUnion₀]
    · congr 1; ext ω; simp
    · intro a' b hab
      exact Disjoint.aedisjoint (Set.disjoint_left.mpr fun ω h1 h2 => hab (h1.2.symm.trans h2.2))
    · exact fun x => hS3nm n x
  have hlow : ∀ n, a n * pz ≤ RHS n := fun n =>
    ENNReal.le_tsum (f := fun x => P y (E ∩ {ω | Y (τ n ω) ω = x}) *
      P x {ω | ∀ r ∈ R, Y r ω = w r}) z
  have hup : ∀ n, RHS n ≤ a n * pz + (P y E - a n) := by
    intro n
    have hrest : (∑' x, if x = z then 0 else P y (E ∩ {ω | Y (τ n ω) ω = x})) =
        P y E - a n := by
      have hsum := hpart n
      rw [ENNReal.tsum_eq_add_tsum_ite z] at hsum
      exact ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) (by rw [hsum]; convert add_comm (∑' x, if x = z then 0 else P y (E ∩ {ω | Y (τ n ω) ω = x})) (a n))
    show (∑' x, P y (E ∩ {ω | Y (τ n ω) ω = x}) * P x {ω | ∀ r ∈ R, Y r ω = w r}) ≤ _
    rw [ENNReal.tsum_eq_add_tsum_ite z, ← hrest]
    refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun x => ?_)
    split_ifs
    · exact le_rfl
    · have := hM.1 x
      exact mul_le_of_le_one_right bot_le prob_le_one
  have hlim_low : Tendsto (fun n => a n * pz) atTop (𝓝 (P y E * pz)) :=
    ENNReal.Tendsto.mul_const hL2 (Or.inr (measure_ne_top (P z) _))
  have hlim_up : Tendsto (fun n => a n * pz + (P y E - a n)) atTop (𝓝 (P y E * pz)) := by
    have := hlim_low.add (ENNReal.Tendsto.sub tendsto_const_nhds hL2
      (Or.inl (measure_ne_top (P y) E)))
    simpa using this
  have hR : Tendsto RHS atTop (𝓝 (P y E * pz)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlim_low hlim_up hlow hup
  have hL1' : Tendsto RHS atTop (𝓝 (P y (E ∩ C))) := by
    have : (fun n => P y (E ∩ Cn n)) = RHS := funext hRHS
    rw [← this]; exact hL1
  exact tendsto_nhds_unique hL1' hR

end Strong

/-! ### Point cylinders on path space -/

def PC : Set (Set PathS) :=
  {S | ∃ (R : Finset ℝ≥0) (w : ℝ≥0 → ℕ), S = {g | ∀ r ∈ R, g r = w r}}

lemma pc_meas (R : Finset ℝ≥0) (w : ℝ≥0 → ℕ) : MeasurableSet {g : PathS | ∀ r ∈ R, g r = w r} := by
  have : {g : PathS | ∀ r ∈ R, g r = w r} = ⋂ r ∈ R, {g | g r = w r} := by ext; simp
  rw [this]
  exact MeasurableSet.biInter R.countable_toSet fun r _ =>
    measurable_pi_apply r (measurableSet_singleton _)

lemma pc_isPi : IsPiSystem PC := by
  classical
  rintro S ⟨R1, w1, rfl⟩ T ⟨R2, w2, rfl⟩ ⟨g0, hg1, hg2⟩
  refine ⟨R1 ∪ R2, g0, ?_⟩
  ext g
  simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_union]
  constructor
  · rintro ⟨h1, h2⟩ r (hr | hr)
    · rw [h1 r hr, hg1 r hr]
    · rw [h2 r hr, hg2 r hr]
  · intro h
    exact ⟨fun r hr => (h r (Or.inl hr)).trans (hg1 r hr),
      fun r hr => (h r (Or.inr hr)).trans (hg2 r hr)⟩

lemma pc_gen : (inferInstance : MeasurableSpace PathS) = MeasurableSpace.generateFrom PC := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun r => ?_
    refine MeasurableSpace.comap_le_iff_le_map.mpr fun A _ => ?_
    have : (fun g : PathS => g r) ⁻¹' A =
        ⋃ c ∈ A, {g : PathS | ∀ r' ∈ ({r} : Finset ℝ≥0), g r' = (fun _ => c) r'} := by
      ext g; simp
    show MeasurableSet[MeasurableSpace.generateFrom PC] ((fun g : PathS => g r) ⁻¹' A)
    rw [this]
    exact MeasurableSet.biUnion (to_countable A) fun c _ =>
      MeasurableSpace.measurableSet_generateFrom ⟨{r}, fun _ => c, rfl⟩
  · refine MeasurableSpace.generateFrom_le ?_
    rintro S ⟨R, w, rfl⟩
    exact pc_meas R w

end SMS

open SMS in
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
    ∀ (y : ℕ) (m : ℕ) (u : Fin m → ℝ≥0) (v : Fin m → ℕ) (s t : ℝ≥0) (z k : ℕ),
      (∀ i, u i ≤ s) → 0 < z →
      P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
          {ω | branchingToPoisson Y s ω = z} ∩
          {ω | branchingToPoisson
              (fun r ω' => Y (sInf {r' : ℝ≥0 | (s : ℝ) < branchingOccupation Y r' ω'} + r) ω')
              t ω = k}) =
        P y ({ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
          {ω | branchingToPoisson Y s ω = z}) *
          P z {ω | branchingToPoisson Y t ω = k} := by
  classical
  intro y m u v s t z k hu hz
  have hPy := hMarkov.1 y
  have hPz := hMarkov.1 z
  have hX : ∀ r, AEMeasurable (fun ω => branchingToPoisson Y r ω) (P y) := fun r =>
    (lampertiForwardMeasurableAndInitial Y P law rate hRate offspring hNoNullJumps hBranching
      hMarkov hSemigroup hGenerator hInitial hMeas hCadlag y).1 r
  obtain ⟨E, hEdef⟩ : ∃ E : Set Ω, E = {ω | ∀ i, branchingToPoisson Y (u i) ω = v i} ∩
      {ω | branchingToPoisson Y s ω = z} := ⟨_, rfl⟩
  rw [← hEdef]
  have hπ : Measurable (fun ω => (fun x => Y x ω : PathS)) := measurable_pi_lambda _ hMeas
  let Ψ : Ω → PathS := fun ω r => hatv (fun x => Y x ω) (Th s (fun x => Y x ω) + r)
  have hΨ : Measurable Ψ := measurable_pi_lambda _ fun r =>
    hat_meas.comp ((((Th_meas s).comp hπ).add_const r).prodMk hπ)
  have hΨeq : ∀ ω, IsCadlag (fun x => Y x ω) →
      Ψ ω = fun r => Y (sInf {r' : ℝ≥0 | (s : ℝ) < branchingOccupation Y r' ω} + r) ω := by
    intro ω hc
    funext r
    simp only [Ψ, hat_eq hc, Th_eq hc]
    rfl
  let ν1 : Measure PathS := ((P y).restrict E).map Ψ
  let ν2 : Measure PathS := (P y E) • ((P z).map (fun ω => (fun x => Y x ω : PathS)))
  have h1 : ∀ G, MeasurableSet G → ν1 G = P y (Ψ ⁻¹' G ∩ E) := fun G hG => by
    simp only [ν1]; rw [Measure.map_apply hΨ hG, Measure.restrict_apply (hΨ hG)]
  have h2 : ∀ G, MeasurableSet G →
      ν2 G = P y E * P z ((fun ω => (fun x => Y x ω : PathS)) ⁻¹' G) := fun G hG => by
    simp only [ν2]; rw [Measure.smul_apply, Measure.map_apply hπ hG, smul_eq_mul]
  have hν : ν1 = ν2 := by
    have : IsFiniteMeasure ν1 := by simp only [ν1]; infer_instance
    refine ext_of_generate_finite _ pc_gen pc_isPi ?_ ?_
    · rintro S ⟨R, w, rfl⟩
      rw [h1 _ (pc_meas R w), h2 _ (pc_meas R w)]
      have hcs := cyl_strong Y P law hMarkov hInitial hMeas y (hCadlag y) hX m u v s z hu hz R w
      rw [← hEdef] at hcs
      have hpre : (fun ω => (fun x => Y x ω : PathS)) ⁻¹' {g | ∀ r ∈ R, g r = w r} =
          {ω | ∀ r ∈ R, Y r ω = w r} := rfl
      rw [hpre, ← hcs]
      refine measure_congr (eventuallyEq_set.mpr ?_)
      filter_upwards [hCadlag y] with ω hω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      rw [hΨeq ω hω]
      exact and_comm
    · rw [h1 _ MeasurableSet.univ, h2 _ MeasurableSet.univ]; simp
  have hG : MeasurableSet (Phi t ⁻¹' {k}) := Phi_meas t (measurableSet_singleton k)
  have key := congrArg (fun ν : Measure PathS => ν (Phi t ⁻¹' {k})) hν
  rw [h1 _ hG, h2 _ hG] at key
  have e1 : P y (E ∩ {ω | branchingToPoisson
      (fun r ω' => Y (sInf {r' : ℝ≥0 | (s : ℝ) < branchingOccupation Y r' ω'} + r) ω') t ω = k}) =
      P y (Ψ ⁻¹' (Phi t ⁻¹' {k}) ∩ E) := by
    rw [inter_comm]
    refine measure_congr (eventuallyEq_set.mpr ?_)
    filter_upwards [hCadlag y] with ω hω
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    rw [hΨeq ω hω, Phi_eq (shift_cadlag hω _), btp_eq']
  have e2 : P z {ω | branchingToPoisson Y t ω = k} =
      P z ((fun ω => (fun x => Y x ω : PathS)) ⁻¹' (Phi t ⁻¹' {k})) := by
    refine measure_congr (eventuallyEq_set.mpr ?_)
    filter_upwards [hCadlag z] with ω hω
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    rw [Phi_eq hω, btp_eq']
  rw [e1, e2, key]
