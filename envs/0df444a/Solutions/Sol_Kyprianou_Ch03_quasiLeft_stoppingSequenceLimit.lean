-- Prove2me | solution 1 for Kyprianou.Ch03.quasiLeft_stoppingSequenceLimit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:32:22.780526+00:00
-- url     : https://prove2.me/submissions/c7e39c8e-6342-4191-a224-71335f4bdea6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_quasiLeft_stoppedValuesInMeasureV1
import Theorems.Thm_Kyprianou_Ch03_quasiLeft_stoppedValuesPathwiseLimitV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
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
      Tendsto (fun n => X (timeTn n omega) omega)
        atTop (nhds (X (timeT omega) omega))) := by
  have hm := Kyprianou.Ch03.quasiLeft_stoppedValuesInMeasureV1
    P F X hX hNatural T Tn timeT timeTn hTimeT hTimeTn hT hTn hIncreasing hLimit
  have hp := Kyprianou.Ch03.quasiLeft_stoppedValuesPathwiseLimitV1
    P F X hX hNatural T Tn timeT timeTn hTimeT hTimeTn hT hTn hIncreasing hLimit
  obtain ⟨ns, hns, hsub⟩ := hm.exists_seq_tendsto_ae
  have hfin : MeasurableSet {omega : Omega | T omega ≠ ⊤} :=
    (hT.measurable' (measurableSet_singleton (⊤ : WithTop NNReal))).compl
  simp only [bne_iff_ne]
  have hfull : ∀ᵐ omega : Omega ∂ P.restrict {omega : Omega | T omega ≠ ⊤},
      Tendsto (fun n => X (timeTn n omega) omega) atTop (nhds (X (timeT omega) omega)) := by
    filter_upwards [hp, hsub] with omega hex hconv
    obtain ⟨l, hl⟩ := hex
    have heq := tendsto_nhds_unique (hl.comp hns.tendsto_atTop) hconv
    simpa only [heq] using hl
  exact (ae_restrict_iff' hfin).mp hfull
