-- Prove2me | solution 1 for GlobalTheory.T.fourier_descendedFunction_eq_partialFourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:25.823231+00:00
-- url     : https://prove2.me/submissions/98d9eb9d-b4b2-44ac-9846-8b10a5e0258c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierDescendedFunctionEqPartialFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierDescendedFunctionEqPartialFourierStatement
import Theorems.Thm_GlobalTheory_JR_fourB_descFn


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → ∀ (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) = A.descFn M Ax j lam α (fourU M ψ f) := by
  first | exact @GlobalTheory.JR.fourB_descFn | exact GlobalTheory.JR.fourB_descFn | (intros; apply GlobalTheory.JR.fourB_descFn <;> assumption)
end _root_.GlobalTheory.T
