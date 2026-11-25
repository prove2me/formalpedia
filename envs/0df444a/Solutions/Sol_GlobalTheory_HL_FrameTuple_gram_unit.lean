-- Prove2me | solution 1 for GlobalTheory.HL.FrameTuple.gram_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:34:05.93475+00:00
-- url     : https://prove2.me/submissions/e689097f-69ad-423b-bfaf-ea261f56b93c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNondegenerateTupleComplementFixer
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_mem_perp_span
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTuple
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.FrameTuple
theorem _root_.solution (L : LocE F E) [IsArtinianRing E] {n m : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (h : IsHerm L H) (x : Fin m → Fin n → E) (hli : LinearIndependent E x)
    (hd : Disjoint (Submodule.span E (Set.range x)) (perp L H (Submodule.span E (Set.range x)))) :
    IsUnit (gramT L H x).det := by
  have hinj : Function.Injective (Matrix.toLin' (gramT L H x)) := by
    rw [injective_iff_map_eq_zero]
    intro α hα
    have h1 : ∑ i, α i • x i = 0 := by
      refine Submodule.disjoint_def.1 hd _ ((Submodule.mem_span_range_iff_exists_fun E).2 ⟨α, rfl⟩) ?_
      rw [FrameBasic.mem_perp_span L h]
      intro j
      change FrameBasic.hfL L H (x j) _ = 0
      rw [map_sum]
      refine Eq.trans ?_ (congrFun hα j)
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, gramT, Matrix.of_apply, map_smul,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    funext i
    exact Fintype.linearIndependent_iff.1 hli α h1 i
  have hb := IsArtinian.bijective_of_injective_endomorphism _ hinj
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.isUnit_toLin'_iff]
  exact (Module.End.isUnit_iff _).2 hb
end GlobalTheory.HL.FrameTuple
