-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45DeterministicDriftModelV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:08:23.349977+00:00
-- url     : https://prove2.me/submissions/6d7dcd33-d63b-4a28-baf7-f85140070d4c

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_ito43_ce_linear_indep
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The deterministic unit drift on the trivial probability space has the specified triplet and completed filtration. -/
theorem solution :
    letI m : MeasurableSpace ℕ := ⊥
    let P : Measure ℕ := Measure.dirac 0
    let X : NNReal → ℕ → ℝ := fun t _ => (t : ℝ)
    let tr : LevyKhintchineTriple := ⟨1,0,0,by simp [IsLevyMeasure]⟩
    let F : Filtration NNReal m := ⊥
    IsLevyProcess X P ∧
      (∀ t : NNReal, ∀ ξ : ℝ, charFun (P.map (X t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ)) ∧
      Kyprianou.Ch03.IsCompletedNaturalFiltration P X F := by
  classical
  letI m : MeasurableSpace ℕ := ⊥
  let P : Measure ℕ := Measure.dirac 0
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let X : NNReal → ℕ → ℝ := fun t _ => (t : ℝ)
  let tr : LevyKhintchineTriple := ⟨1,0,0,by simp [IsLevyMeasure]⟩
  letI : SigmaFinite tr.levyMeasure := by dsimp [tr]; infer_instance
  have hX : IsLevyProcess X P := by
    refine ⟨by funext w; rfl, ?_, ?_, ?_⟩
    · exact Kyprianou.Ch04.ito43_ce_linear_indep P
    · intro s h
      have H : increment X s (s+h) = increment X 0 h := by
        funext w
        simp [increment,X,NNReal.coe_add]
      rw [H]
      apply IdentDistrib.refl
      change AEMeasurable (fun _ : ℕ => (h : ℝ) - ((0 : NNReal) : ℝ)) P
      exact measurable_const.aemeasurable
    · filter_upwards [] with w
      intro t
      exact ⟨NNReal.continuous_coe.continuousWithinAt,
        ⟨(t : ℝ),NNReal.continuous_coe.continuousWithinAt⟩⟩
  have htr (t : NNReal) (ξ : ℝ) :
      charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ) := by
    change charFun (P.map (fun _ : ℕ => (t : ℝ))) ξ = _
    rw [Measure.map_const,measure_univ,one_smul,charFun_dirac]
    simp [Kyprianou.Ch01.levyTripleExponent,tr]
    congr 1
    ring
  let F : Filtration NNReal m := ⊥
  have hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F := by
    intro t
    change (⊥ : MeasurableSpace ℕ) = PerfCorrMSQ.natFiltr X t ⊔ _
    apply le_antisymm bot_le
    apply sup_le
    · simp [PerfCorrMSQ.natFiltr, X, MeasurableSpace.comap_const]
    · apply MeasurableSpace.generateFrom_le
      intro A hA
      obtain ⟨B,hB,hz,hsub⟩ := hA
      exact MeasurableSpace.measurableSet_bot_iff.mpr (by
        left
        rcases MeasurableSpace.measurableSet_bot_iff.mp hB with h | h
        · exact subset_empty_iff.mp (h ▸ hsub)
        · rw [h,measure_univ] at hz
          exact (one_ne_zero hz).elim)
  exact ⟨hX,htr,hF⟩
