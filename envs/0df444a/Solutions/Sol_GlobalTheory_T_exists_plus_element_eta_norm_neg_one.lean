-- Prove2me | solution 1 for GlobalTheory.T.exists_plus_element_eta_norm_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:17:05.466807+00:00
-- url     : https://prove2.me/submissions/a360797f-66c7-4d6f-bbff-b201cf34cc33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPlusElementEtaNormNegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPlusElementEtaNormNegOneStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_exists_plus_eta_norm_neg_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (f : B.A), IsIdempotentElem f → f ≠ 0 → (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) → B.σ f = f → ∃ y : B.A, B.Plus y ∧ y * (1 - f) = 1 - f ∧ K.eta (Algebra.norm K.E y) = -1 := by
  first | exact @GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one | exact GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one | (intros; apply GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one <;> assumption)
end _root_.GlobalTheory.T
