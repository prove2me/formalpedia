-- Prove2me | solution 1 for GlobalTheory.T.isLocallyConstantCompactSupport_hyperbolic_operations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:16:09.625635+00:00
-- url     : https://prove2.me/submissions/149ed893-83d5-461f-94b8-2d60b9997176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportHyperbolicOperati
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportHyperbolicOperatiStatement
import Theorems.Thm_GlobalTheory_JR_Hyp_isTest_ops


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (Hyp.rg A g Φ)) ∧ (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun p : A.K × A.K => Φ (p.1, -p.2))) ∧ (∀ (s : A.Kˣ) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (fun p : A.K × A.K => Φ ((s : A.K) * p.1, (s : A.K) * p.2))) ∧ (∀ (h Φ : A.K × A.K → ℂ), IsLocallyConstant h → IsTest Φ → IsTest (fun p => h p * Φ p)) ∧ ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → IsTest (c • Φ + Φ') := by
  first | exact @GlobalTheory.JR.Hyp.isTest_ops | exact GlobalTheory.JR.Hyp.isTest_ops | (intros; apply GlobalTheory.JR.Hyp.isTest_ops <;> assumption)
end _root_.GlobalTheory.T
