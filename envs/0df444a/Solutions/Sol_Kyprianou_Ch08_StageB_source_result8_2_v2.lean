-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:30:48.030802+00:00
-- url     : https://prove2.me/submissions/8fd2fa44-00f8-44cb-8229-02c954cc8a09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_actual_height_law
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_scale_representation
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_left_derivative
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_right_derivative
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_atoms_c1
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution : Kyprianou.Ch08.StageB.sourceCertificate_result8_2 := by
  intro Ω mΩ P hP D ψ W hψ hW q hq
  obtain ⟨n, hLaw⟩ :=
    Kyprianou.Ch08.StageB.source_result8_2_v2_actual_height_law
      P D ψ W hψ hW q hq
  have hScale :=
    Kyprianou.Ch08.StageB.source_result8_2_v2_scale_representation
      P D ψ W hψ hW q hq n hLaw
  have hLeft :=
    Kyprianou.Ch08.StageB.source_result8_2_v2_left_derivative
      P D ψ W q n hLaw hScale
  have hRight :=
    Kyprianou.Ch08.StageB.source_result8_2_v2_right_derivative
      P D ψ W q n hLaw hScale
  have hDerivativeCore :
      ∀ x : ℝ, 0 < x →
        ∃ dLeft dRight : ℝ,
          HasDerivWithinAt (W q) dLeft (Set.Iic x) x ∧
          HasDerivWithinAt (W q) dRight (Set.Ici x) x ∧
          dLeft = (Kyprianou.Ch08.Phi ψ q + (n (Set.Ici x)).toReal) * W q x ∧
          dRight = (Kyprianou.Ch08.Phi ψ q + (n (Set.Ioi x)).toReal) * W q x := by
    intro x hx
    obtain ⟨dLeft, hdLeft, hvalLeft⟩ := hLeft x hx
    obtain ⟨dRight, hdRight, hvalRight⟩ := hRight x hx
    exact ⟨dLeft, dRight, hdLeft, hdRight, hvalLeft, hvalRight⟩
  have hAtomsC1 :=
    Kyprianou.Ch08.StageB.source_result8_2_v2_atoms_c1
      P D ψ W q n hLaw hScale hDerivativeCore
  exact ⟨n, hLaw, hScale, hAtomsC1.1, hAtomsC1.2⟩
