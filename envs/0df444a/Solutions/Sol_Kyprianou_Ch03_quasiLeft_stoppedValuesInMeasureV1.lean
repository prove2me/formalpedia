-- Prove2me | solution 1 for Kyprianou.Ch03.quasiLeft_stoppedValuesInMeasureV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:44:14.595818+00:00
-- url     : https://prove2.me/submissions/c410d1aa-5253-4228-b969-3065c9f92c73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_quasiLeft_uniformStoppedOscillationV1
import Theorems.Thm_Kyprianou_Ch03_quasiLeft_finiteClocksInMeasureV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

open scoped Topology

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
    TendstoInMeasure (P.restrict {omega : Omega | T omega ≠ ⊤})
      (fun n omega => X (timeTn n omega) omega) atTop
      (fun omega => X (timeT omega) omega) := by
  let Q := P.restrict {omega : Omega | T omega ≠ ⊤}
  obtain ⟨hgood, hclock⟩ :=
    Kyprianou.Ch03.quasiLeft_finiteClocksInMeasureV1
      P F X hX hNatural T Tn timeT timeTn hTimeT hTimeTn hT hTn hIncreasing hLimit
  change TendstoInMeasure Q _ atTop _
  rw [tendstoInMeasure_iff_dist]
  intro eps heps
  apply ENNReal.tendsto_nhds_zero.mpr
  intro eta heta
  have hhalf := ENNReal.half_pos (ne_of_gt heta)
  obtain ⟨delta, hd, hosc⟩ :=
    Kyprianou.Ch03.quasiLeft_uniformStoppedOscillationV1 P F X hX hNatural
      eps heps (eta / 2) hhalf
  have hpos : (0 : Real) < (delta : Real) := by exact_mod_cast hd
  have hsmall := ENNReal.tendsto_nhds_zero.mp
    (tendstoInMeasure_iff_dist.mp hclock (delta : Real) hpos) (eta / 2) hhalf
  filter_upwards [hsmall] with n hn
  let B := {omega : Omega | (delta : Real) ≤ dist (timeTn n omega) (timeT omega)}
  let C := {omega : Omega | Tn n omega ≠ ⊤ ∧ ∃ u : NNReal, u < delta ∧
    eps ≤ dist (X (timeTn n omega + u) omega) (X (timeTn n omega) omega)}
  have hsub : Q {omega | eps ≤ dist (X (timeTn n omega) omega)
      (X (timeT omega) omega)} ≤ Q (B ∪ C) := by
    apply measure_mono_ae
    filter_upwards [hgood] with omega h
    intro hw
    by_cases hb : omega ∈ B
    · exact Or.inl hb
    · right
      refine ⟨(h n).1, timeT omega - timeTn n omega, ?_, ?_⟩
      · have hdist : dist (timeTn n omega) (timeT omega) =
            ((timeT omega - timeTn n omega : NNReal) : Real) := by
          rw [dist_comm, NNReal.dist_eq, NNReal.coe_sub (h n).2]
          exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (h n).2))
        have hh : ¬ (delta : Real) ≤ dist (timeTn n omega) (timeT omega) := hb
        rw [hdist] at hh
        exact_mod_cast lt_of_not_ge hh
      · rw [add_tsub_cancel_of_le (h n).2, dist_comm]
        exact hw
  calc
    _ ≤ Q (B ∪ C) := hsub
    _ ≤ Q B + Q C := measure_union_le B C
    _ ≤ eta / 2 + eta / 2 := add_le_add hn
      ((Measure.restrict_apply_le _ _).trans
        (hosc (Tn n) (timeTn n) (hTn n)
          (fun omega h => hTimeTn n omega (by simpa using h))))
    _ = eta := ENNReal.add_halves eta
