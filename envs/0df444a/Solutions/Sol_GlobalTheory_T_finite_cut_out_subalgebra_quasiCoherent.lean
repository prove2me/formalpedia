-- Prove2me | solution 1 for GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:31.899697+00:00
-- url     : https://prove2.me/submissions/9c11d26c-8eb7-484c-b07b-b0dfa9a10da5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteCutOutSubalgebraQuasiCoherent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubmoduleFgOfLocallyLeFgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgLocalizationAwaySpanFinsetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteCutOutSubalgebraQuasiCoherentStatement
import Theorems.Thm_GlobalTheory_QcSub_subMap_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (op U)).hom.IsIntegral) → ∀ {ι : Type} (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → (∀ x : X, ∃ j, x ∈ V j) → ∀ (T : ∀ j, Set (F.obj (op (V j)))), (∀ j, (T j).Finite) → ∀ W : X.Opens, IsAffineOpen W → (subMap F α V T W).Finite := by
  first | exact @GlobalTheory.QcSub.subMap_finite | exact GlobalTheory.QcSub.subMap_finite | (intros; apply GlobalTheory.QcSub.subMap_finite <;> assumption)
end _root_.GlobalTheory.T
