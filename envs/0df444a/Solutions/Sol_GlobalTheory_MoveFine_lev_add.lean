-- Prove2me | solution 1 for GlobalTheory.MoveFine.lev_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:46:54.214046+00:00
-- url     : https://prove2.me/submissions/2ebf4ddb-6883-47f8-83fc-47e992978f29

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
import Theorems.Thm_GlobalTheory_MoveFine_RR_add
import Theorems.Thm_GlobalTheory_MoveFine_RR_neg
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
namespace GlobalTheory.MoveFine
theorem _root_.solution (g g' : Fin (r + 1) → S.V) (v : S.V) (be be' : Fin (r + 1) → E)
    (hb : ∀ i, S.RR (be i) (be' i)) :
    S.lev g g' (v + (∑ i, be i • g i + ∑ i, be' i • g' i)) = S.lev g g' v := by
  unfold Frames.lev
  congr 1
  ext j
  constructor
  · rintro ⟨al, al', e, h⟩
    refine ⟨fun i => al i + -be i, fun i => al' i + -be' i, ?_, fun i hi => RR_add S (h i hi) (RR_neg S (hb i))⟩
    simp only [add_smul, neg_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [eq_sub_of_add_eq e]; abel
  · rintro ⟨al, al', e, h⟩
    refine ⟨fun i => al i + be i, fun i => al' i + be' i, ?_, fun i hi => RR_add S (h i hi) (hb i)⟩
    simp only [add_smul, Finset.sum_add_distrib]
    rw [e]; abel
end GlobalTheory.MoveFine
