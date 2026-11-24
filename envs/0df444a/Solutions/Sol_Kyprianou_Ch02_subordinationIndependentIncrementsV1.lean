-- Prove2me | solution 1 for Kyprianou.Ch02.subordinationIndependentIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:11:28.10693+00:00
-- url     : https://prove2.me/submissions/7dfb9b39-aad2-41ae-805a-a0d4d7d75cb4

import Theorems.Thm_Kyprianou_Ch02_subordinationJointCharFactorizationV1
import Theorems.Thm_Kyprianou_Ch02_iIndepFunOfExpProductV1
import Theorems.Thm_Kyprianou_Ch02_subordinatedIncrementCharMixtureV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P) :
    ProbabilityTheory.HasIndependentIncrements (fun t ω => X (τ t ω) ω) P := by
  intro n t ht
  apply Kyprianou.Ch02.iIndepFunOfExpProductV1 P n
  · intro k
    exact (Kyprianou.Ch02.subordinatedIncrementCharMixtureV1 P X τ hX hτ hmon hind
      (t k.castSucc) (t k.succ) (ht (Fin.castSucc_le_succ k)) 0).1
  · intro θ
    simpa [increment] using
      Kyprianou.Ch02.subordinationJointCharFactorizationV1 P X τ hX hτ hmon hind n t ht θ
