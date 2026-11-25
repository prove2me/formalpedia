-- Prove2me | solution 1 for GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:26:13.126728+00:00
-- url     : https://prove2.me/submissions/895f1a95-a0e7-4e58-9f20-988dbfbfd2f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDataMassEqSumFrameClasses
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDataMassEqSumFrameClassesStatement
import Theorems.Thm_GlobalTheory_HL_sumData_mass_eq_sumCls


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ P : S.Datum → Submodule L.O S.V → Prop, (∀ h ∈ S.St, ∀ d Λ, S.IsTerm d Λ → P d Λ → P d (h • Λ)) → (S.sumData fun d => S.mass d (P d)) = (S.sumCls fun C => S.sumData fun d => S.nT d C (P d)) ∧ ∀ h ∈ S.St, ∀ d C, S.nT d (h • C) (P d) = S.nT d C (P d) := by
  first | exact @GlobalTheory.HL.sumData_mass_eq_sumCls | exact GlobalTheory.HL.sumData_mass_eq_sumCls | (intros; apply GlobalTheory.HL.sumData_mass_eq_sumCls <;> assumption)
end _root_.GlobalTheory.T
