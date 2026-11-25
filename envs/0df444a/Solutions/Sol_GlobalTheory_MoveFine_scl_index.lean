-- Prove2me | solution 1 for GlobalTheory.MoveFine.scl_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:25.855216+00:00
-- url     : https://prove2.me/submissions/4dbb666a-c929-4317-9145-bfec930b9a48

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
import Theorems.Thm_GlobalTheory_MoveFine_relIndex_scl_ne_zero
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.MoveFine
theorem _root_.solution {W : Type} [AddCommGroup W] [Module E W] (P : Submodule L.O W) (hP : P.FG) (n : ℕ) :
    (scl P.toAddSubgroup (algebraMap F E S.ϖ ^ n)).relIndex P.toAddSubgroup ≠ 0 := by
  obtain ⟨-, -, -, -, -, h1, h2, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  haveI : Finite (L.O ⧸ (Ideal.span {y : L.O | (y : E) = algebraMap F E ((S.ϖ : F) ^ n)})) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [h1]; positivity
  refine relIndex_scl_ne_zero L.O P hP
    (Ideal.span {y : L.O | (y : E) = algebraMap F E ((S.ϖ : F) ^ n)}) _ fun x hx => ?_
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, L.O.one_mem, by rw [mul_one, ← map_pow]; exact hy⟩
  | zero => exact ⟨0, L.O.zero_mem, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨z, hz, e'⟩ := hb
    exact ⟨y + z, L.O.add_mem hy hz, by push_cast; rw [e, e', mul_add]⟩
  | smul c a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    exact ⟨c * y, L.O.mul_mem c.2 hy, by rw [smul_eq_mul]; push_cast; rw [e]; ring⟩
end GlobalTheory.MoveFine
