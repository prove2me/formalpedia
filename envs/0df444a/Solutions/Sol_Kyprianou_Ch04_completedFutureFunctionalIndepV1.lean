-- Prove2me | solution 1 for Kyprianou.Ch04.completedFutureFunctionalIndepV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:52:50.142484+00:00
-- url     : https://prove2.me/submissions/56050dcd-bb3f-4bc5-b18b-9934752f7bc5

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedPathV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An a.s. measurable functional of the future increment path is independent of the completed past. -/
theorem solution {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (s : NNReal) (G : (NNReal → ℝ) → E) (hG : Measurable G)
    (W : Ω → E)
    (hW : W =ᵐ[P] fun ω => G (fun u : NNReal => X (s+u) ω - X s ω)) :
    Indep (MeasurableSpace.comap W inferInstance) (F s) P := by
  let Y : Ω → NNReal → ℝ := fun ω u => X (s+u) ω - X s ω
  have hm (t : NNReal) : Measurable (X t) := by
    apply (comap_measurable (X t)).mono _ le_rfl
    refine le_trans ?_ (F.le t)
    rw [hF t]
    exact le_sup_of_le_left (le_iSup₂_of_le t le_rfl le_rfl)
  have hY : Measurable Y := measurable_pi_iff.mpr fun u => (hm _).sub (hm _)
  have hLaw := Kyprianou.Ch03.strongMarkovDeterministicRestrictedPathV1 P F X hX hF s
  have hbase : Measure.map Y P = Measure.map (fun ω u => X u ω) P := by
    simpa [Y] using hLaw univ MeasurableSet.univ
  apply (Indep_iff _ _ P).mpr
  intro A B hA hB
  obtain ⟨C,hC,rfl⟩ := hA
  have hGC : MeasurableSet (G ⁻¹' C) := hG hC
  have heq : W ⁻¹' C =ᵐ[P] Y ⁻¹' (G ⁻¹' C) := by
    filter_upwards [hW] with ω hω
    change (W ω ∈ C) = (G (Y ω) ∈ C)
    rw [hω]
  have heq' : ((W ⁻¹' C) ∩ B : Set Ω) =ᵐ[P] ((Y ⁻¹' (G ⁻¹' C)) ∩ B : Set Ω) := by
    filter_upwards [heq] with ω hω
    change (ω ∈ W ⁻¹' C ∧ ω ∈ B) = (ω ∈ Y ⁻¹' (G ⁻¹' C) ∧ ω ∈ B)
    exact congrArg (fun p : Prop => p ∧ ω ∈ B) hω
  rw [measure_congr heq', measure_congr heq]
  calc
    P (Y ⁻¹' (G ⁻¹' C) ∩ B) = (P.restrict B) (Y ⁻¹' (G ⁻¹' C)) := by
      rw [Measure.restrict_apply (hY hGC)]
    _ = Measure.map Y (P.restrict B) (G ⁻¹' C) :=
      (Measure.map_apply hY hGC).symm
    _ = P B * P (Y ⁻¹' (G ⁻¹' C)) := by
      rw [hLaw B hB, ← hbase, Measure.smul_apply, smul_eq_mul, Measure.map_apply hY hGC]
    _ = _ := mul_comm _ _
