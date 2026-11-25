-- Prove2me | solution 1 for GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:43:51.255476+00:00
-- url     : https://prove2.me/submissions/8c1459d7-f215-4d62-b495-b71ac8257a0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyConstantCompactSupportSlicesOperatorApply
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyConstantCompactSupportSlicesOperatorApplyStatement
import Theorems.Thm_P2M_GlobalTheory_slices_test__ca01e1ad2132


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
theorem _root_.solution : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by
  first | exact @GlobalTheory.slices_test' | exact GlobalTheory.slices_test' | (intros; apply GlobalTheory.slices_test' <;> assumption)
end _root_.GlobalTheory.T
