-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42AvramIndependentIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:43:23.296159+00:00
-- url     : https://prove2.me/submissions/9c34f8a6-3a2b-4e89-af78-9c14341dd587

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Independent future increments yield joint independence on finite partitions. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    ProbabilityTheory.HasIndependentIncrements L.X P := by
  let : IsProbabilityMeasure P := L.isProbability
  intro n t ht
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S A hA
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert k S hk ih =>
    have hkn : k ∉ S := fun h => (lt_irrefl k) (hk k h)
    have htime (i : Fin n) (hi : i ∈ S) : t i.succ ≤ t k.castSucc :=
      ht (by exact_mod_cast Nat.succ_le_of_lt (hk i hi))
    have hMeas : MeasurableSet[F (t k.castSucc)]
        (⋂ i ∈ S, increment L.X (t i.castSucc) (t i.succ) ⁻¹' A i) := by
      apply Finset.measurableSet_biInter
      intro i hi
      have h₁ := (L.adapted (t i.succ)).mono (F.mono (htime i hi)) le_rfl
      have h₂ := (L.adapted (t i.castSucc)).mono
        (F.mono ((ht (Fin.castSucc_le_succ i)).trans (htime i hi))) le_rfl
      exact (h₁.sub h₂) (hA i (Finset.mem_insert_of_mem hi))
    have hNew : MeasurableSet[MeasurableSpace.comap
        (increment L.X (t k.castSucc) (t k.succ)) inferInstance]
        (increment L.X (t k.castSucc) (t k.succ) ⁻¹' A k) :=
      ⟨A k, hA k (Finset.mem_insert_self k S), rfl⟩
    have hInd := (L.indepIncrements (t k.castSucc) (t k.succ)
      (ht (Fin.castSucc_le_succ k)))
    have hEq : (⋂ i ∈ insert k S, increment L.X (t i.castSucc) (t i.succ) ⁻¹' A i) =
        (increment L.X (t k.castSucc) (t k.succ) ⁻¹' A k) ∩
        (⋂ i ∈ S, increment L.X (t i.castSucc) (t i.succ) ⁻¹' A i) := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_insert]
      aesop
    rw [hEq, Finset.prod_insert hkn]
    rw [(Indep_iff _ _ _).mp hInd _ _ hNew hMeas]
    exact congrArg (fun z => P (increment L.X (t k.castSucc) (t k.succ) ⁻¹' A k) * z)
      (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi)))
