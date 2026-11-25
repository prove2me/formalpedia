-- Prove2me | solution 1 for GlobalTheory.T.hermitian_unitary_group_one_parameter_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:21:34.809276+00:00
-- url     : https://prove2.me/submissions/acc1c8e7-414c-4b9c-a760-d69211199bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianUnitaryGroupOneParameterChart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianUnitaryGroupOneParameterChartStatement
import Theorems.Thm_GlobalTheory_UnitaryGroupChart_unitary_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H → IsUnit H.det →
    ∀ (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d), Function.Injective j →
      (∀ a, a ∉ Set.range j → Z a = 0) → (∀ a, (Z a)ᴴ * H + H * Z a = 0) →
      LinearIndependent ℝ (fun i => Z (j i)) →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) →
      ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ g ∈ V, gᴴ * H * g = H → g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  first | exact @GlobalTheory.UnitaryGroupChart.unitary_chart | exact GlobalTheory.UnitaryGroupChart.unitary_chart | (intros; apply GlobalTheory.UnitaryGroupChart.unitary_chart <;> assumption)
end _root_.GlobalTheory.T
