-- Prove2me | solution 1 for Kyprianou.Ch03.quasiLeft_strictlyEarlierLeftLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:08:26.540467+00:00
-- url     : https://prove2.me/submissions/36c628eb-f63e-4fad-9d85-43b297bcd4c5

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_quasiLeft_stoppingSequenceLimit
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : Omega -> WithTop NNReal)
    (Tn : Nat -> Omega -> WithTop NNReal)
    (timeT : Omega -> NNReal) (timeTn : Nat -> Omega -> NNReal)
    (hTimeT : forall omega, T omega != ⊤ ->
      T omega = (timeT omega : WithTop NNReal))
    (hTimeTn : forall n omega, Tn n omega != ⊤ ->
      Tn n omega = (timeTn n omega : WithTop NNReal))
    (hT : IsStoppingTime F T)
    (hTn : forall n, IsStoppingTime F (Tn n))
    (hIncreasing : ∀ᵐ omega : Omega ∂ P,
      Monotone (fun n => Tn n omega))
    (hLimit : ∀ᵐ omega : Omega ∂ P,
      Tendsto (fun n => Tn n omega) atTop (nhds (T omega))) :
    (∀ᵐ omega : Omega ∂ P, T omega != ⊤ ->
      (forall n, Tn n omega < T omega) ->
      Function.leftLim (fun s : NNReal => X s omega) (timeT omega) =
        X (timeT omega) omega) := by
  have hseq := Kyprianou.Ch03.quasiLeft_stoppingSequenceLimit
    P F X hX hNatural T Tn timeT timeTn hTimeT hTimeTn hT hTn hIncreasing hLimit
  filter_upwards [hseq, hLimit, hX.cadlag_ae] with omega hseqw hconv hcad
  intro hfinite hstrict
  have hfin (n : Nat) : Tn n omega != ⊤ :=
    by simpa using (ne_of_lt (lt_of_lt_of_le (hstrict n) le_top) : Tn n omega ≠ ⊤)
  have heq : (fun n => Tn n omega) =
      (fun n => (timeTn n omega : WithTop NNReal)) :=
    funext (fun n => hTimeTn n omega (hfin n))
  have hc : Tendsto (fun n => (timeTn n omega : WithTop NNReal)) atTop
      (nhds (timeT omega : WithTop NNReal)) := by
    rw [← heq, ← hTimeT omega hfinite]
    exact hconv
  have ha : Tendsto (fun n => timeTn n omega) atTop (nhds (timeT omega)) := by
    exact WithTop.isEmbedding_coe.tendsto_nhds_iff.mpr hc
  have hb (n : Nat) : timeTn n omega < timeT omega := by
    simpa only [hTimeTn n omega (hfin n), hTimeT omega hfinite,
      WithTop.coe_lt_coe] using hstrict n
  have hl : Tendsto (fun n => timeTn n omega) atTop
      (nhdsWithin (timeT omega) (Set.Iio (timeT omega))) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ha, Eventually.of_forall hb⟩
  have hleft := tendsto_leftLim_of_tendsto (hcad (timeT omega)).2
  exact tendsto_nhds_unique (hleft.comp hl) (hseqw hfinite)
