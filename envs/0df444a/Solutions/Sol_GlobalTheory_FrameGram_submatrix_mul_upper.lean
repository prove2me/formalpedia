-- Prove2me | solution 1 for GlobalTheory.FrameGram.submatrix_mul_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:47.00401+00:00
-- url     : https://prove2.me/submissions/3182b01a-15d8-44cb-b82d-0a1cafdf6590

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariant
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameGram
namespace GlobalTheory.FrameGram
theorem _root_.solution {E : Type} [CommRing E] {N m : ℕ} (hm : m ≤ N) {ι : Type} (f : ι → Fin N)
    (M B : Matrix (Fin N) (Fin N) E) (hB : ∀ i j, j < i → B i j = 0) :
    (M * B).submatrix f (Fin.castLE hm) =
      M.submatrix f (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hm) (Fin.castLE_injective hm) _ _ ?_ fun _ => rfl
  intro i hi
  rw [hB, mul_zero]
  by_contra h
  apply hi
  have h1 : (i : ℕ) ≤ b := not_lt.1 h
  exact ⟨⟨i, by omega⟩, rfl⟩
end GlobalTheory.FrameGram
