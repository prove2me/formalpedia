-- Prove2me | solution 2 for Kyprianou.Ch02.bvLevyPositiveJumpSumMonotonePointwiseV1
-- status  : ACCEPTED   (disprove)
-- author  : @pageman
-- created : 2026-11-24T23:03:33.756275+00:00
-- url     : https://prove2.me/submissions/d990939e-f5dc-4638-84e7-a8c09783429f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Set Function Metric Topology
open scoped NNReal ENNReal Topology
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
Disproof of `bvLevyPositiveJumpSumMonotonePointwiseV1`.

Mathlib sets `∑' f = 0` when `f : ι → ℝ` is not summable. Counterexample:
`Ω = Unit`, `spikeTrain` with a unit spike at `1/2` and unit spikes at
`spikeLoc n = 1 + 1/(n+2)`. Left `a = 1` has tsum `1`; right `b = 2` is not
summable so tsum `0`. Hence `1 ≤ 0` fails.
-/

private noncomputable def spikeLoc (n : ℕ) : ℝ≥0 :=
  ⟨(1 : ℝ) + ((n + 2 : ℝ)⁻¹), by positivity⟩

private lemma spikeLoc_coe (n : ℕ) : (spikeLoc n : ℝ) = (1 : ℝ) + (n + 2 : ℝ)⁻¹ := rfl

private lemma spikeLoc_inj : Injective spikeLoc := by
  intro m n h
  have : (1 : ℝ) + (m + 2 : ℝ)⁻¹ = 1 + (n + 2 : ℝ)⁻¹ :=
    congrArg NNReal.toReal h
  have heq : (m + 2 : ℝ) = (n + 2 : ℝ) := inv_inj.mp (by linarith)
  have : m + 2 = n + 2 := by exact_mod_cast heq
  omega

private lemma spikeLoc_gt_one (n : ℕ) : (1 : ℝ≥0) < spikeLoc n := by
  refine NNReal.coe_lt_coe.mp ?_
  rw [spikeLoc_coe, NNReal.coe_one]
  have : (0 : ℝ) < (n + 2 : ℝ)⁻¹ := inv_pos.mpr (by positivity)
  linarith

private lemma spikeLoc_le_two (n : ℕ) : spikeLoc n ≤ (2 : ℝ≥0) := by
  refine NNReal.coe_le_coe.mp ?_
  rw [spikeLoc_coe, NNReal.coe_ofNat]
  have : (n + 2 : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : (1 : ℕ) ≤ n + 2))
  linarith

private lemma spikeLoc_anti {m n : ℕ} (h : m < n) : spikeLoc n < spikeLoc m := by
  refine NNReal.coe_lt_coe.mp ?_
  rw [spikeLoc_coe, spikeLoc_coe]
  have hlt : (m + 2 : ℝ) < n + 2 := by exact_mod_cast Nat.add_lt_add_right h 2
  have : (n + 2 : ℝ)⁻¹ < (m + 2 : ℝ)⁻¹ := inv_strictAnti₀ (by positivity) hlt
  linarith

private lemma exists_spike_lt (s : ℝ≥0) (hs : (1 : ℝ≥0) < s) : ∃ n, spikeLoc n < s := by
  have hpos : (0 : ℝ) < (s : ℝ) - 1 := by
    have := NNReal.coe_lt_coe.mpr hs
    rw [NNReal.coe_one] at this
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (((s : ℝ) - 1)⁻¹)
  refine ⟨N, NNReal.coe_lt_coe.mp ?_⟩
  rw [spikeLoc_coe]
  have hN' : ((s : ℝ) - 1)⁻¹ < (N : ℝ) + 2 := by linarith
  have hNpos : (0 : ℝ) < N + 2 := by positivity
  have : (N + 2 : ℝ)⁻¹ < (s : ℝ) - 1 := by
    simpa [inv_inv] using (inv_lt_inv₀ hNpos (inv_pos.mpr hpos)).mpr hN'
  linarith

private def isSpike (t : ℝ≥0) : Prop :=
  t = (1 / 2 : ℝ≥0) ∨ ∃ n : ℕ, t = spikeLoc n

private noncomputable def spikeTrain : ℝ≥0 → Unit → ℝ := fun t _ =>
  if isSpike t then (1 : ℝ) else 0

private lemma coe_half : ((1 / 2 : ℝ≥0) : ℝ) = (1 : ℝ) / 2 := by norm_cast

private lemma dist_of_lt {t s : ℝ≥0} (h : t < s) : dist t s = (s : ℝ) - (t : ℝ) := by
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg]
  exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (le_of_lt h))

/-- Left punctured gap with no spikes. -/
private lemma exists_left_spike_gap (s : ℝ≥0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, dist t s < δ → t < s → ¬ isSpike t := by
  classical
  rcases le_or_gt s (1 : ℝ≥0) with hs | hs
  · -- Only possible left spike is `1/2` (all `spikeLoc` exceed `1`).
    rcases le_or_gt s (1 / 2 : ℝ≥0) with hhalf | hhalf
    · refine ⟨1, one_pos, ?_⟩
      intro t _ hts hsp
      rcases hsp with ht | ⟨n, rfl⟩
      · subst t; exact not_lt_of_ge hhalf hts
      · exact not_lt_of_ge (le_trans hs (le_of_lt (spikeLoc_gt_one n))) hts
    · have hpos : (0 : ℝ) < (s : ℝ) - 1 / 2 := by
        have := NNReal.coe_lt_coe.mpr hhalf
        rw [coe_half] at this; linarith
      refine ⟨((s : ℝ) - 1 / 2) / 2, by positivity, ?_⟩
      intro t hdist hts hsp
      rcases hsp with ht | ⟨n, rfl⟩
      · subst t
        have hde := dist_of_lt hhalf
        rw [coe_half] at hde
        linarith [hde, hdist]
      · exact not_lt_of_ge (le_trans hs (le_of_lt (spikeLoc_gt_one n))) hts
  · -- `s > 1`: largest spike below `s` is `spikeLoc (Nat.find _)`; clear a left gap.
    let n0 := Nat.find (exists_spike_lt s hs)
    have hn0 : spikeLoc n0 < s := Nat.find_spec (exists_spike_lt s hs)
    have hmax : ∀ m, spikeLoc m < s → spikeLoc m ≤ spikeLoc n0 := by
      intro m hm
      rcases lt_trichotomy m n0 with hlt | rfl | hgt
      · exact (Nat.find_min (exists_spike_lt s hs) hlt hm).elim
      · exact le_rfl
      · exact le_of_lt (spikeLoc_anti hgt)
    have hpos_gap : (0 : ℝ) < (s : ℝ) - (spikeLoc n0 : ℝ) := by
      have := NNReal.coe_lt_coe.mpr hn0; linarith
    have hpos1 : (0 : ℝ) < (s : ℝ) - 1 := by
      have := NNReal.coe_lt_coe.mpr hs
      rw [NNReal.coe_one] at this; linarith
    refine ⟨min (((s : ℝ) - (spikeLoc n0 : ℝ)) / 2) (((s : ℝ) - 1) / 2), by positivity, ?_⟩
    intro t hdist hts hsp
    have hde := dist_of_lt hts
    have ht_gt_one : (1 : ℝ) < t := by
      have : dist t s < ((s : ℝ) - 1) / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
      rw [hde] at this; linarith
    rcases hsp with ht | ⟨n, rfl⟩
    · subst t
      rw [coe_half] at ht_gt_one; linarith
    · have hle := hmax n hts
      have : dist (spikeLoc n) s < ((s : ℝ) - (spikeLoc n0 : ℝ)) / 2 :=
        lt_of_lt_of_le hdist (min_le_left _ _)
      rw [hde] at this
      have : (s : ℝ) - (spikeLoc n : ℝ) ≥ (s : ℝ) - (spikeLoc n0 : ℝ) := by
        have := NNReal.coe_le_coe.mpr hle; linarith
      linarith

private lemma tendsto_spike_left (s : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => spikeTrain u ()) (nhdsWithin s (Iio s)) (nhds (0 : ℝ)) := by
  obtain ⟨δ, δpos, hδ⟩ := exists_left_spike_gap s
  refine Metric.tendsto_nhds.mpr fun ε εpos => ?_
  refine eventually_nhdsWithin_iff.mpr ?_
  refine Metric.eventually_nhds_iff.mpr ⟨δ, δpos, fun u hu hus => ?_⟩
  have hnot : ¬ isSpike u := hδ u (mem_ball.mp hu) (mem_Iio.mp hus)
  change dist (spikeTrain u ()) 0 < ε
  simp only [spikeTrain, hnot, ite_false, dist_zero_right, norm_zero]
  exact εpos

private lemma limUnder_spike {s : ℝ≥0} (hs : 0 < s) :
    limUnder (nhdsWithin s (Iio s)) (fun u => spikeTrain u ()) = 0 := by
  have : (nhdsWithin s (Iio s)).NeBot := nhdsWithin_Iio_neBot' ⟨0, hs⟩ le_rfl
  exact (tendsto_spike_left s).limUnder_eq

private lemma summand_eq {s : ℝ≥0} (hs : 0 < s) :
    max (spikeTrain s () - limUnder (nhdsWithin s (Iio s)) (fun u => spikeTrain u ())) 0 =
      if isSpike s then (1 : ℝ) else 0 := by
  rw [limUnder_spike hs]
  simp only [spikeTrain, sub_zero]
  split_ifs <;> simp

private lemma spikeLoc_mem_Ioc_two (n : ℕ) :
    spikeLoc n ∈ Ioc (0 : ℝ≥0) (2 : ℝ≥0) :=
  ⟨lt_trans (by positivity : (0 : ℝ≥0) < 1) (spikeLoc_gt_one n), spikeLoc_le_two n⟩

theorem solution :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
        (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (a b : ℝ≥0) (_hab : a ≤ b),
      (∑' s : Ioc (0 : ℝ≥0) a,
          max (X s.1 ω -
            limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => X u ω)) 0) ≤
        ∑' s : Ioc (0 : ℝ≥0) b,
          max (X s.1 ω -
            limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => X u ω)) 0) := by
  intro h
  have hineq :=
    h (Ω := Unit) spikeTrain () (1 : ℝ≥0) (2 : ℝ≥0) (by norm_num : (1 : ℝ≥0) ≤ 2)
  have hleft :
      (∑' s : Ioc (0 : ℝ≥0) (1 : ℝ≥0),
        max (spikeTrain s.1 () -
          limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => spikeTrain u ())) 0) = 1 := by
    have hmem : (1 / 2 : ℝ≥0) ∈ Ioc (0 : ℝ≥0) (1 : ℝ≥0) := ⟨by positivity, by norm_num⟩
    let s0 : Ioc (0 : ℝ≥0) (1 : ℝ≥0) := ⟨_, hmem⟩
    refine (tsum_eq_single s0 ?_).trans ?_
    · intro s hs
      rw [summand_eq s.2.1]
      split_ifs with hsp
      · rcases hsp with h1 | ⟨n, hn⟩
        · exact False.elim (hs (Subtype.ext h1))
        · have : (1 : ℝ≥0) < s.1 := hn ▸ spikeLoc_gt_one n
          exact False.elim ((not_le_of_gt this) s.2.2)
      · rfl
    · rw [summand_eq s0.2.1]
      have : isSpike (s0 : ℝ≥0) := Or.inl rfl
      simp [this]
  have hright :
      (∑' s : Ioc (0 : ℝ≥0) (2 : ℝ≥0),
        max (spikeTrain s.1 () -
          limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => spikeTrain u ())) 0) = 0 := by
    refine tsum_eq_zero_of_not_summable ?_
    intro hg
    let e : ℕ → Ioc (0 : ℝ≥0) (2 : ℝ≥0) := fun n => ⟨spikeLoc n, spikeLoc_mem_Ioc_two n⟩
    have hinj : Injective e := fun m n he => spikeLoc_inj (Subtype.ext_iff.mp he)
    have hcomp := hg.comp_injective hinj
    have hterm : ∀ n,
        ((fun s : Ioc (0 : ℝ≥0) (2 : ℝ≥0) =>
          max (spikeTrain s.1 () -
            limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => spikeTrain u ())) 0) ∘ e) n = 1 := by
      intro n
      change max (spikeTrain (spikeLoc n) () -
          limUnder (nhdsWithin (spikeLoc n) (Iio (spikeLoc n))) (fun u => spikeTrain u ())) 0 = 1
      rw [summand_eq (lt_trans (by positivity : (0 : ℝ≥0) < 1) (spikeLoc_gt_one n))]
      have : isSpike (spikeLoc n) := Or.inr ⟨n, rfl⟩
      simp [this]
    have hsum : Summable fun _ : ℕ => (1 : ℝ) :=
      (summable_congr hterm).mp hcomp
    rw [summable_const_iff] at hsum
    exact one_ne_zero hsum
  rw [hleft, hright] at hineq
  exact absurd hineq (by norm_num)
