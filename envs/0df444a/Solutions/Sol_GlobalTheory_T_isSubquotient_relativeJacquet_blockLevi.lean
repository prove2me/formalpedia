-- Prove2me | solution 1 for GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:23:40.421997+00:00
-- url     : https://prove2.me/submissions/833c0870-1f42-4a47-8610-52220dda72cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientRelativeJacquetBlockLevi
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientRelativeJacquetBlockLeviStatement
import Theorems.Thm_GlobalTheory_JacStagesExact_isSubquotient_relJacD


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Levi k fun a => Fin (d a)) V)
    (τ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth τ → IsSubquotient σ τ → IsSubquotient (relJacD e' σ) (relJacD e' τ) := by
  first | exact @GlobalTheory.JacStagesExact.isSubquotient_relJacD | exact GlobalTheory.JacStagesExact.isSubquotient_relJacD | (intros; apply GlobalTheory.JacStagesExact.isSubquotient_relJacD <;> assumption)
end _root_.GlobalTheory.T
