-- Prove2me | solution 1 for GlobalTheory.T.partialFourier_glOrbit_eq_fourier_etaleKProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:23:20.336315+00:00
-- url     : https://prove2.me/submissions/527cc807-ee91-4261-b67d-c664a990fd94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGlOrbitEqFourierEtaleKProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGlOrbitEqFourierEtaleKProdStatement
import Theorems.Thm_GlobalTheory_JR_LinDesc_fourG_act_pt_eq_fourK


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ f' : Gl r F → ℂ, IsTest f' → ∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c) := by
  first | exact @GlobalTheory.JR.LinDesc.fourG_act_pt_eq_fourK | exact GlobalTheory.JR.LinDesc.fourG_act_pt_eq_fourK | (intros; apply GlobalTheory.JR.LinDesc.fourG_act_pt_eq_fourK <;> assumption)
end _root_.GlobalTheory.T
