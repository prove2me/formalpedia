-- Prove2me | solution 1 for GlobalTheory.JacStages.flatHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:51.522702+00:00
-- url     : https://prove2.me/submissions/ac7f4ac6-da80-4b08-9a12-cf7f53b81851

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacStages
variable {s : ℕ} {t : Fin s → ℕ}
namespace GlobalTheory.JacStages
theorem _root_.solution (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] (g : ∀ a b, Γ a b)
    (c : Fin (∑ a, t a)) :
    flatHom Γ g c = g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 := rfl
end GlobalTheory.JacStages
