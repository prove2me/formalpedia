-- Prove2me | solution 1 for GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:17.470287+00:00
-- url     : https://prove2.me/submissions/3275bcb0-f67f-4290-a333-dbaf2f6ec936

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIffStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_dual_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (x y : B.A), (∀ z ∈ L, (overExt φ B ψ hψ hσ).herm x y z ∈ (algebraMap K'.O K'.E).range) ↔ (∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) := by
  first | exact @GlobalTheory.UnitLemma.Unr.dual_iff | exact GlobalTheory.UnitLemma.Unr.dual_iff | (intros; apply GlobalTheory.UnitLemma.Unr.dual_iff <;> assumption)
end _root_.GlobalTheory.T
