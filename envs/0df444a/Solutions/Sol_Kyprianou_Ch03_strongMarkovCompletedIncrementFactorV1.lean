-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovCompletedIncrementFactorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:29:10.74166+00:00
-- url     : https://prove2.me/submissions/f1256105-3772-4003-892d-ad2102811afa

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_indep_naturalSigma
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_eq_natFiltr
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [mO : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F) :
    ∀ (s t : NNReal), s ≤ t → ∀ (A : Set Omega), MeasurableSet[F s] A →
      ∀ (C : Set Real), MeasurableSet C →
      P (A ∩ {w | X t w - X s w ∈ C}) =
        P A * P {w | X t w - X s w ∈ C} := by
  classical
  have hm : ∀ t : NNReal, Measurable (X t) := by
    intro t
    apply (comap_measurable (X t)).mono _ le_rfl
    refine le_trans ?_ (F.le t)
    rw [hNatural t]
    exact le_sup_of_le_left (le_iSup₂_of_le t le_rfl le_rfl)
  intro s t hst A hA C hC
  let g : Omega → Real := fun w => X t w - X s w
  let N : Set (Set Omega) := {B | ∃ U : Set Omega, @MeasurableSet Omega mO U ∧ P U = 0 ∧ B ⊆ U}
  let G : Set (Set Omega) := {B | MeasurableSet[PerfCorrMSQ.natFiltr X s] B} ∪ N
  have hRaw : Indep (PerfCorrMSQ.natFiltr X s) (MeasurableSpace.comap g inferInstance) P := by
    dsimp [g]
    rw [← Kyprianou.Ch01.naturalSigma_eq_natFiltr]
    exact (Kyprianou.Ch01.levyIncrement_indep_naturalSigma P X hX hm s t hst).symm
  have hGen : F s = MeasurableSpace.generateFrom G := by
    rw [hNatural s]
    change PerfCorrMSQ.natFiltr X s ⊔ MeasurableSpace.generateFrom N = MeasurableSpace.generateFrom G
    apply le_antisymm
    · apply sup_le
      · rw [← @MeasurableSpace.generateFrom_measurableSet Omega (PerfCorrMSQ.natFiltr X s)]
        exact MeasurableSpace.generateFrom_mono Set.subset_union_left
      · exact MeasurableSpace.generateFrom_mono Set.subset_union_right
    · apply MeasurableSpace.generateFrom_le
      rintro B (hB | hB)
      · exact (le_sup_left : PerfCorrMSQ.natFiltr X s ≤ PerfCorrMSQ.natFiltr X s ⊔ MeasurableSpace.generateFrom N) B hB
      · exact (le_sup_right : MeasurableSpace.generateFrom N ≤ _) B
          (MeasurableSpace.measurableSet_generateFrom hB)
  have hPi : IsPiSystem G := by
    intro U hU V hV _
    rcases hU with hU | ⟨W, hW, hW0, hUW⟩
    · rcases hV with hV | ⟨W, hW, hW0, hVW⟩
      · exact Or.inl (MeasurableSet.inter (m := PerfCorrMSQ.natFiltr X s) hU hV)
      · exact Or.inr ⟨W, hW, hW0, Set.inter_subset_right.trans hVW⟩
    · exact Or.inr ⟨W, hW, hW0, Set.inter_subset_left.trans hUW⟩
  have hind : Indep (F s) (MeasurableSpace.comap g inferInstance) P := by
    refine IndepSets.indep (p1 := G)
      (p2 := {B | MeasurableSet[MeasurableSpace.comap g inferInstance] B})
      (F.le s) ((hm t).sub (hm s)).comap_le hPi
      (@MeasurableSpace.isPiSystem_measurableSet Omega (MeasurableSpace.comap g inferInstance)) hGen
      (@MeasurableSpace.generateFrom_measurableSet Omega (MeasurableSpace.comap g inferInstance)).symm ?_
    rw [IndepSets_iff]
    intro U V hU hV
    rcases hU with hU | ⟨W, hW, hW0, hUW⟩
    · exact (Indep_iff (PerfCorrMSQ.natFiltr X s) _ P).mp hRaw U V hU hV
    · have hU0 : P U = 0 := measure_mono_null hUW hW0
      rw [hU0, zero_mul]
      exact measure_mono_null Set.inter_subset_left hU0
  exact (Indep_iff (F s) _ P).mp hind A (g ⁻¹' C) hA
    ((comap_measurable g) hC)
