-- Prove2me | solution 1 for Kyprianou.Ch03.quasiLeft_uniformStoppedOscillationV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:59:57.136979+00:00
-- url     : https://prove2.me/submissions/e2f9d545-78a3-4d20-8809-756cc8a4a843
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_quasiLeft_smallCountableOscillationV1
import Theorems.Thm_Kyprianou_Ch03_quasiLeft_denseShiftOscillationV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedPathV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedRestrictedPathV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open Kyprianou.Ch03
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F) :
    ∀ (epsilon : Real), 0 < epsilon →
    ∀ (eta : ENNReal), 0 < eta →
      ∃ delta : NNReal, 0 < delta ∧
        ∀ (tau : Omega → WithTop NNReal) (finiteTime : Omega → NNReal),
          IsStoppingTime F tau →
          (∀ omega, tau omega ≠ ⊤ → tau omega = (finiteTime omega : WithTop NNReal)) →
          P {omega : Omega | tau omega ≠ ⊤ ∧ ∃ u : NNReal, u < delta ∧
            epsilon ≤ dist (X (finiteTime omega + u) omega) (X (finiteTime omega) omega)} ≤ eta := by
  classical
  intro eps heps eta heta
  have hAdapt : ∀ t : NNReal, Measurable[F t] (X t) := by
    intro t
    apply (comap_measurable (X t)).mono _ le_rfl
    rw [hNatural t]
    exact le_sup_of_le_left (le_iSup₂_of_le t le_rfl le_rfl)
  have hMeas : ∀ t : NNReal, Measurable (X t) :=
    fun t => (hAdapt t).mono (F.le t) le_rfl
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (α := NNReal)
  obtain ⟨delta, hd, hmB, hB⟩ :=
    quasiLeft_smallCountableOscillationV1 P X hX hMeas S hSc eps heps eta heta
  refine ⟨delta, hd, ?_⟩
  intro tau a ht ha
  let D : Set Omega := {w | tau w ≠ ⊤}
  let Z : Omega → (NNReal → Real) := fun w u => X (a w + u) w - X (a w) w
  let B : Set (NNReal → Real) := {f | ∃ v ∈ S, v < delta ∧ eps / 2 < |f v|}
  have hD : MeasurableSet D := ht.measurableSet_eq_top.compl
  obtain ⟨hZm, hLaw⟩ := strongMarkovExtendedRestrictedPathV1 P F X hX hNatural
    (strongMarkovDeterministicRestrictedPathV1 P F X hX hNatural) tau ht a ha
  have hmap : Measure.map Z (P.restrict D) =
      P D • Measure.map (fun w u => X u w) P := by
    simpa [D, Z] using hLaw Set.univ (fun s => by simpa using ht s)
  have hZB : (P.restrict D) (Z ⁻¹' B) ≤ eta := by
    rw [← Measure.map_apply_of_aemeasurable hZm hmB, hmap, Measure.smul_apply]
    change P D * Measure.map (fun w u => X u w) P B ≤ eta
    have hmass : P D ≤ 1 := by
      calc
        P D ≤ P Set.univ := measure_mono (Set.subset_univ D)
        _ = 1 := measure_univ
    exact (mul_le_mul' hmass hB).trans_eq (one_mul eta)
  calc
    _ ≤ P (Z ⁻¹' B ∩ D) := by
      apply measure_mono_ae
      filter_upwards [hX.cadlag_ae] with w hc
      rintro ⟨hw, u, hu, hb⟩
      refine ⟨?_, hw⟩
      exact quasiLeft_denseShiftOscillationV1 (fun t => X t w) hc S hSd
        (a w) delta eps heps u hu hb
    _ = (P.restrict D) (Z ⁻¹' B) := (Measure.restrict_apply' hD).symm
    _ ≤ eta := hZB
