-- Prove2me | solution 1 for GlobalTheory.MoveFine.disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:08:31.017604+00:00
-- url     : https://prove2.me/submissions/cc6b2cf8-a1d2-4bf1-be47-9ba511c555f2

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
theorem _root_.solution (hli : LinearIndependent E (Sum.elim S.f S.f')) (x x' : S.V) (hx : x ∈ S.spanTo S.f (r + 1))
    (hx' : x' ∈ S.spanTo S.f' (r + 1)) (e : x + x' = 0) : x = 0 ∧ x' = 0 := by
  have hd := (linearIndependent_sum.1 hli).2.2
  have h1 : x ∈ Submodule.span E (Set.range (Sum.elim S.f S.f' ∘ Sum.inl)) :=
    Submodule.span_mono (Set.image_subset_range _ _) hx
  have h2 : x' ∈ Submodule.span E (Set.range (Sum.elim S.f S.f' ∘ Sum.inr)) :=
    Submodule.span_mono (Set.image_subset_range _ _) hx'
  have h3 : x = -x' := eq_neg_of_add_eq_zero_left e
  have h4 : x = 0 := Submodule.disjoint_def.1 hd x h1 (h3 ▸ Submodule.neg_mem _ h2)
  exact ⟨h4, by simpa [h4] using e⟩
end GlobalTheory.MoveFine
