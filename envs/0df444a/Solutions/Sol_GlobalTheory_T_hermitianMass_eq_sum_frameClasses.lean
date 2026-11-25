-- Prove2me | solution 1 for GlobalTheory.T.hermitianMass_eq_sum_frameClasses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:54.715804+00:00
-- url     : https://prove2.me/submissions/24ebd26b-6eb6-4c71-98d1-e887a6078eee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMassEqSumFrameClasses
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMassEqSumFrameClassesStatement
import Theorems.Thm_GlobalTheory_HL_mass_eq_sumCls


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ h ∈ S.St, ∀ Λ, S.IsTerm d Λ → P Λ → P (h • Λ)) → S.mass d P = S.sumCls fun C => S.nT d C P := by
  first | exact @GlobalTheory.HL.mass_eq_sumCls | exact GlobalTheory.HL.mass_eq_sumCls | (intros; apply GlobalTheory.HL.mass_eq_sumCls <;> assumption)
end _root_.GlobalTheory.T
