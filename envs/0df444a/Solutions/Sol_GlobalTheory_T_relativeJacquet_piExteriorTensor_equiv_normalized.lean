-- Prove2me | solution 1 for GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:35.545045+00:00
-- url     : https://prove2.me/submissions/6999b745-45da-470e-85cb-a64bb212e5b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelativeJacquetPiExteriorTensorEquivNormalized
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelativeJacquetPiExteriorTensorEquivNormalizedStatement
import Theorems.Thm_GlobalTheory_JacStages_relJacD_piTensor_equiv


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
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : Fin s → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    Nonempty ((relJacD e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) := by
  first | exact @GlobalTheory.JacStages.relJacD_piTensor_equiv | exact GlobalTheory.JacStages.relJacD_piTensor_equiv | (intros; apply GlobalTheory.JacStages.relJacD_piTensor_equiv <;> assumption)
end _root_.GlobalTheory.T
