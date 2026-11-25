-- Prove2me | solution 1 for GlobalTheory.IntClsCount.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:41:13.096384+00:00
-- url     : https://prove2.me/submissions/61308454-3de1-45f0-97a7-4aba0321d683

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RmulMul
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
open GlobalTheory GlobalTheory.IntClsCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.IntClsCount
theorem _root_.solution (L : LocE F E) (N : ℕ) :
    ∃ s : Set (Matrix (Fin N) (Fin N) E) → Matrix (Fin N) (Fin N) E,
      ∀ u, ∃ A, IsUni A ∧ IsIntM L A ∧ u = s (coset L u) * A := by
  refine ⟨fun C => if h : ∃ u, C = coset L u then h.choose else 0, fun u => ?_⟩
  have h : ∃ v, coset L u = coset L v := ⟨u, rfl⟩
  simp only [dif_pos h]
  have h1 : u ∈ coset L u := by
    refine ⟨1, ⟨fun i j hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩,
      fun i j => ?_, (mul_one u).symm⟩
    rw [Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem
  exact h.choose_spec.subset h1
end GlobalTheory.IntClsCount
