-- Prove2me | solution 1 for GlobalTheory.MoveFine.h_span_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:06:07.255912+00:00
-- url     : https://prove2.me/submissions/9fad5aa3-6a01-42fe-9a70-36a18e679646

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice
import Theorems.Thm_GlobalTheory_MoveFine_h_add_l
import Theorems.Thm_GlobalTheory_MoveFine_h_smul_l
import Theorems.Thm_GlobalTheory_MoveFine_h_zero_l
import Theorems.Thm_GlobalTheory_MoveFine_h_add_r
import Theorems.Thm_GlobalTheory_MoveFine_h_smul_r
import Theorems.Thm_GlobalTheory_MoveFine_h_zero_r

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.MoveFine
theorem _root_.solution (s t : Set S.V) (hst : ∀ x ∈ s, ∀ y ∈ t, S.h x y = 0) :
    ∀ x ∈ Submodule.span E s, ∀ y ∈ Submodule.span E t, S.h x y = 0 := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hst x hx y hy
    | zero => exact h_zero_r S _
    | add a b _ _ ha hb => rw [h_add_r, ha, hb, add_zero]
    | smul c a _ ha => rw [h_smul_r, ha, mul_zero]
  | zero => exact h_zero_l S _
  | add a b _ _ ha hb => rw [h_add_l, ha, hb, add_zero]
  | smul c a _ ha => rw [h_smul_l, ha, mul_zero]
end GlobalTheory.MoveFine
