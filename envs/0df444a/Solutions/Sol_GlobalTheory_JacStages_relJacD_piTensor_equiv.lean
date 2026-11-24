-- Prove2me | solution 1 for GlobalTheory.JacStages.relJacD_piTensor_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:09.353337+00:00
-- url     : https://prove2.me/submissions/87e01772-3a52-47dd-b7a1-1fff74ee4497

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelativeJacquetPiExteriorTensorEquivNormalized
import Theorems.Thm_GlobalTheory_JacPiTensor_relJacD_piTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.JacStages
namespace GlobalTheory.JacStages
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : Fin s → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    Nonempty ((relJacD e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) :=
  fun _ _ _ _ _ _ _ _ _ e' _ _ _ ρ => GlobalTheory.JacPiTensor.relJacD_piTensor e' ρ
end GlobalTheory.JacStages
