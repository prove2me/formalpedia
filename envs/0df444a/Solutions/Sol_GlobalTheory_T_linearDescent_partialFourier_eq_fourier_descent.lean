-- Prove2me | solution 1 for GlobalTheory.T.linearDescent_partialFourier_eq_fourier_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:21:31.118928+00:00
-- url     : https://prove2.me/submissions/75baf5af-40be-4bfe-81a2-a5d7163dcb1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescentStatement
import Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_desc_fourG_eq_fourK_desc


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c)) → ∀ x : A.K × A.K, LinDesc.desc A M hG lam α (fourG M ψ f') x = A.fourK μK ψ (LinDesc.desc A M hG lam α f') x := by
  first | exact @GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc | exact GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc | (intros; apply GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc <;> assumption)
end _root_.GlobalTheory.T
