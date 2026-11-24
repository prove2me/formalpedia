-- Prove2me | solution 1 for Kyprianou.Ch03.quasiLeft_smallCountableOscillationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:58:54.447057+00:00
-- url     : https://prove2.me/submissions/4096bc41-8ec5-4ece-b373-9fb09b587023

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open Kyprianou.Ch03
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hMeas : ∀ t, Measurable (X t))
    (S : Set NNReal) (hS : S.Countable)
    (eps : Real) (heps : 0 < eps)
    (eta : ENNReal) (heta : 0 < eta) :
    ∃ delta : NNReal, 0 < delta ∧
      MeasurableSet {f : NNReal → Real | ∃ v ∈ S, v < delta ∧ eps / 2 < |f v|} ∧
      Measure.map (fun w t => X t w) P
        {f : NNReal → Real | ∃ v ∈ S, v < delta ∧ eps / 2 < |f v|} ≤ eta := by
  classical
  letI : Countable S := hS.to_subtype
  let delta (n : Nat) : NNReal := 1 / ((n : NNReal) + 1)
  have hp (n : Nat) : 0 < delta n := by
    dsimp [delta]
    positivity
  have hd : Antitone delta := by
    intro i j hij
    dsimp [delta]
    gcongr
  let B (n : Nat) : Set (NNReal → Real) :=
    {f | ∃ v ∈ S, v < delta n ∧ eps / 2 < |f v|}
  have hmB (n : Nat) : MeasurableSet (B n) := by
    have heq : B n = ⋃ v : S,
        {f : NNReal → Real | (v : NNReal) < delta n ∧ eps / 2 < |f v|} := by
      ext f
      simp only [B, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨v, hv, h⟩
        exact ⟨⟨v, hv⟩, h⟩
      · rintro ⟨v, h⟩
        exact ⟨v, v.property, h⟩
    rw [heq]
    apply MeasurableSet.iUnion
    intro v
    by_cases hv : (v : NNReal) < delta n
    · simp only [hv, true_and]
      exact measurableSet_lt measurable_const (measurable_pi_apply (v : NNReal)).abs
    · simp [hv]
  let Y : Omega → (NNReal → Real) := fun w t => X t w
  have hmY : Measurable Y := measurable_pi_lambda _ hMeas
  let E (n : Nat) : Set Omega := Y ⁻¹' B n
  have hmE (n : Nat) : MeasurableSet (E n) := hmY (hmB n)
  have ha : Antitone E := by
    intro i j hij w hw
    obtain ⟨v, hv, hvd, hvx⟩ := hw
    exact ⟨v, hv, lt_of_lt_of_le hvd (hd hij), hvx⟩
  have hnull : P (⋂ n, E n) = 0 := by
    have hset : {w : Omega | ¬ w ∉ ⋂ n, E n} = ⋂ n, E n := by
      ext w
      simp
    rw [← hset]
    apply ae_iff.mp
    filter_upwards [hX.cadlag_ae] with w hc
    change w ∉ ⋂ n, E n
    have hzero : X 0 w = 0 := congrFun hX.start_zero w
    obtain ⟨r, hr, hclose⟩ := Metric.continuousWithinAt_iff.mp (hc 0).1
      (eps / 2) (by linarith)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
    intro hw
    obtain ⟨v, hv, hvd, hvx⟩ := Set.mem_iInter.mp hw n
    have hvr : (v : Real) < r := by
      have hh : (v : Real) < (delta n : Real) := by exact_mod_cast hvd
      exact hh.trans (by simpa [delta] using hn)
    have hdist : dist v 0 < r := by
      simpa [NNReal.dist_eq, abs_of_nonneg v.property] using hvr
    have hmem : v ∈ Set.Ici (0 : NNReal) := by
      exact v.property
    have hlt := hclose (x := v) hmem hdist
    rw [hzero, Real.dist_eq, sub_zero] at hlt
    exact (not_lt_of_ge (le_of_lt hvx)) hlt
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (hmE n).nullMeasurableSet) ha
    ⟨0, measure_ne_top P (E 0)⟩
  rw [hnull] at hlim
  obtain ⟨n, hn⟩ := (eventually_atTop.mp
    (ENNReal.tendsto_nhds_zero.mp hlim eta heta))
  refine ⟨delta n, hp n, hmB n, ?_⟩
  rw [Measure.map_apply hmY (hmB n)]
  exact hn n le_rfl
