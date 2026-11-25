-- Prove2me | solution 1 for GlobalTheory.MatrixIndex.span_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:05.56295+00:00
-- url     : https://prove2.me/submissions/3f862319-482d-4f38-99b4-677fa8644495

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanEqMap
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MatrixIndex
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.MatrixIndex
theorem _root_.solution (L : LocE F E) {n m : ℕ} (y : Fin m → Fin n → E) :
    (Submodule.span L.O (Set.range y)).toAddSubgroup =
      (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup).map
        (Fintype.linearCombination E y).toAddMonoidHom := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
    AddSubgroup.mem_map, AddSubgroup.mem_pi, Set.mem_univ, forall_true_left,
    LinearMap.toAddMonoidHom_coe, Fintype.linearCombination_apply, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (c i).2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => ⟨c i, hc i⟩, rfl⟩
end GlobalTheory.MatrixIndex
