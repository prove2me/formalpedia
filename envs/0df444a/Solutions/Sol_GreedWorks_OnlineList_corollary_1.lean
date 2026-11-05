-- Prove2me | solution 1 for GreedWorks.OnlineList.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:57:59.935904+00:00
-- url     : https://prove2.me/submissions/c4a795f4-2b64-4a21-940a-c2222aafe7f3

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_LP
import Definitions.Def_GreedWorks_OnlineTime_Model
import Definitions.Def_GreedWorks_OnlineTime_TimeIndexedLP
import Theorems.Thm_GreedWorks_OnlineList_lemma_2
import Theorems.Thm_GreedWorks_OnlineTime_eq_13_relaxation

open MeasureTheory ProbabilityTheory

namespace GreedOLCor1Aux

variable {M : Type*} [Fintype M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The online-list instance viewed as an online-time instance with all release dates `0`. -/
noncomputable def toTime (I : GreedWorks.OnlineList.StochasticInstance M n Ω) :
    GreedWorks.OnlineTime.StochasticInstance M n Ω where
  Pr := I.Pr
  probability := I.probability
  P := I.P
  measurable := I.measurable
  eligible := I.eligible
  hasMachine := I.hasMachine
  memLp := I.memLp
  meanAtLeastOne := I.meanAtLeastOne
  independentJobs := I.independentJobs
  release := fun _ => 0
  release_monotone := fun _ _ _ => le_rfl
  weight := I.weight
  weight_nonneg := I.weight_nonneg
  Delta := I.Delta
  Delta_nonneg := I.Delta_nonneg
  cvBound := I.cvBound

lemma admissible_toTime (I : GreedWorks.OnlineList.StochasticInstance M n Ω)
    (pol : GreedWorks.OnlineList.Policy M n) (hpol : GreedWorks.OnlineList.IsAdmissible I pol) :
    GreedWorks.OnlineTime.IsAdmissible (toTime I) pol := by
  obtain ⟨hfeas, hna, hint⟩ := hpol
  refine ⟨fun p => ?_, hna, hint⟩
  obtain ⟨h1, h2, h3⟩ := hfeas p
  refine ⟨h1, fun j => by simpa [toTime] using h2 j, fun j k hjk hmk => ?_⟩
  rw [Set.disjoint_iff]
  rintro x ⟨⟨hxj1, hxj2⟩, ⟨hxk1, hxk2⟩⟩
  rcases h3 j k hjk hmk with h | h | h | h
  · have e : GreedWorks.OnlineList.completion pol p j = GreedWorks.OnlineList.start pol p j := by
      simp [GreedWorks.OnlineList.completion, h]
    linarith
  · have e : GreedWorks.OnlineList.completion pol p k = GreedWorks.OnlineList.start pol p k := by
      simp [GreedWorks.OnlineList.completion, h]
    linarith
  · linarith
  · linarith

end GreedOLCor1Aux

open GreedWorks.OnlineList GreedOLCor1Aux in
theorem solution {M : Type*} [Fintype M] [Nonempty M] (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (pol : Policy M n)
    (hpol : IsAdmissible I pol) :
    ∃ y : ProcessingPoint M n,
      IsPrimalFeasible I y ∧
        primalValue I y ≤ (1 + I.Delta / 2) * comparatorCost I pol := by
  obtain ⟨y, ⟨⟨hy0, hyel, -, hys, hys2, hcap, hassign⟩, h5⟩, hval⟩ :=
    GreedWorks.OnlineTime.eq_13_relaxation (toTime I) pol (admissible_toTime I pol hpol)
  have hS : IsStochasticFeasible I y :=
    ⟨⟨hy0, hyel, hys, hys2, hcap, hassign⟩, h5⟩
  have hv : stochasticValue I y ≤ comparatorCost I pol := hval
  obtain ⟨y', hy', hy'v⟩ := lemma_2 n I y hS
  refine ⟨y', hy', le_trans hy'v ?_⟩
  have : 0 ≤ 1 + I.Delta / 2 := by linarith [I.Delta_nonneg]
  exact mul_le_mul_of_nonneg_left hv this
