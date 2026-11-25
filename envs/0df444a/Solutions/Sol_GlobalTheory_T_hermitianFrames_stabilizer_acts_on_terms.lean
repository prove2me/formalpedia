-- Prove2me | solution 1 for GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:27.74639+00:00
-- url     : https://prove2.me/submissions/b999fd85-890a-4d00-954a-d9c06f965f22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Theorems.Thm_GlobalTheory_FrameAct_stabiliser_acts_on_terms


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ h ∈ S.St, S.IsTerm d (h • Λ) ∧ S.om d (h • Λ) = S.om d Λ ∧ S.M d (h • Λ) = h • S.M d Λ ∧ S.sat (h • Λ) = h • S.sat Λ ∧ S.Fr d (h • Λ) = h • S.Fr d Λ ∧ S.be d (h • Λ) = S.be d Λ ∧ S.cardI d (h • Λ) = S.cardI d Λ ∧ (S.BBzero d (h • Λ) ↔ S.BBzero d Λ) ∧ (S.TypeBe d (h • Λ) ↔ S.TypeBe d Λ) ∧ (∀ β J βJ, S.InFF β J βJ d (h • Λ) ↔ S.InFF β J βJ d Λ) ∧ ∀ J x x' u s, S.IsMove J d Λ x x' u s ↔ S.IsMove J d (h • Λ) (h x) (h x') (h u) s := by
  first | exact @GlobalTheory.FrameAct.stabiliser_acts_on_terms | exact GlobalTheory.FrameAct.stabiliser_acts_on_terms | (intros; apply GlobalTheory.FrameAct.stabiliser_acts_on_terms <;> assumption)
end _root_.GlobalTheory.T
