-- Prove2me | solution 1 for GlobalTheory.UnitaryGroupChart.unitary_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:26:00.814993+00:00
-- url     : https://prove2.me/submissions/07aa4f48-23ce-4679-bce3-d18c6ff3a43d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianUnitaryGroupOneParameterChart
import Theorems.Thm_GlobalTheory_UnitaryGroupChart_chart_matrix

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
noncomputable section
open GlobalTheory GlobalTheory.UnitaryGroupChart
open Filter
namespace GlobalTheory.UnitaryGroupChart
theorem _root_.solution : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H → IsUnit H.det →
    ∀ (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d), Function.Injective j →
      (∀ a, a ∉ Set.range j → Z a = 0) → (∀ a, (Z a)ᴴ * H + H * Z a = 0) →
      LinearIndependent ℝ (fun i => Z (j i)) →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) →
      ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ g ∈ V, gᴴ * H * g = H → g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  intro n H hH hdet d e Z j _ _ hZ hli hsp
  obtain ⟨s, hs1, hs2⟩ := chart_matrix n H hH hdet d e Z j hZ hli hsp
  exact ⟨_, hs2, s, hs1, fun g hg => hg⟩
end GlobalTheory.UnitaryGroupChart
