-- Prove2me | solution 1 for GlobalTheory.JacStages.refinePlace_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:14.678579+00:00
-- url     : https://prove2.me/submissions/ee9d81ea-5ab6-481a-b1f2-8f175396ca59

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
theorem _root_.solution {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (c : Fin (∑ a, t a))
    (i : Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) :
    refinePlace e e' ⟨c, i⟩ =
      e ⟨(finSigmaFinEquiv.symm c).1, e' _ ⟨(finSigmaFinEquiv.symm c).2, i⟩⟩ := rfl
end GlobalTheory.JacStages
