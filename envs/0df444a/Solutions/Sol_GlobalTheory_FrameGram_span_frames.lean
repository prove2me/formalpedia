-- Prove2me | solution 1 for GlobalTheory.FrameGram.span_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:38.342279+00:00
-- url     : https://prove2.me/submissions/479b6488-0947-4eb6-a7a0-63333bd1ba6d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariant
import Theorems.Thm_GlobalTheory_HL_FrameTri_sub_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameGram
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameGram
theorem _root_.solution {V : Type} [AddCommGroup V] [Module E V] {ι : Type} (g g' : ι → V) (t : F)
    (ht : t ≠ 0) :
    Submodule.span E (Set.range (Sum.elim g fun i => algebraMap F E t⁻¹ • (g' i - g i))) =
      Submodule.span E (Set.range g) ⊔ Submodule.span E (Set.range g') := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
        (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
  · rw [sup_le_iff, Submodule.span_le, Submodule.span_le]
    constructor
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      have e : g' i = algebraMap F E t • (algebraMap F E t⁻¹ • (g' i - g i)) + g i := by
        rw [smul_smul, ← map_mul, mul_inv_cancel₀ ht, map_one, one_smul, sub_add_cancel]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
        (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
end GlobalTheory.FrameGram
