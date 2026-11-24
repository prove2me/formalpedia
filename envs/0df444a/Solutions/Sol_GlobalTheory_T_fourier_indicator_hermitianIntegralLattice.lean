-- Prove2me | solution 1 for GlobalTheory.T.fourier_indicator_hermitianIntegralLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:13:20.818805+00:00
-- url     : https://prove2.me/submissions/b65d1d4d-f70e-427b-b1f1-06e01c078801

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierIndicatorHermitianIntegralLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierIndicatorHermitianIntegralLatticeStatement
import Theorems.Thm_GlobalTheory_JR_fourB_indicator_intLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) (B : A.L → A.L → ℂ), (∀ y' y, B y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) → IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → ∀ μ : Measure A.L, μ.IsAddHaarMeasure → ∀ y, fourB μ B (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1) y = ((μ {y : A.L | ∀ i, ‖j y i‖ ≤ 1}).toReal : ℂ) * Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1 y := by
  first | exact @GlobalTheory.JR.fourB_indicator_intLattice | exact GlobalTheory.JR.fourB_indicator_intLattice | (intros; apply GlobalTheory.JR.fourB_indicator_intLattice <;> assumption)
end _root_.GlobalTheory.T
