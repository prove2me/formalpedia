-- Prove2me | solution 1 for GlobalTheory.HL.Defect.lead_mul_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:05.191891+00:00
-- url     : https://prove2.me/submissions/b1c3bb54-6700-4b1e-bd06-1f7dc0d2720a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Theorems.Thm_GlobalTheory_HL_Defect_submatrix_mul_of_zero
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
omit [TopologicalSpace E]
namespace GlobalTheory.HL.Defect
theorem _root_.solution {N : ℕ} (Z s : Matrix (Fin N) (Fin N) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) (l : Fin (N + 1)) :
    lead (Z * s) l = lead Z l ∧ lead (sᵀ * Z) l = lead Z l := by
  have hl := Nat.lt_succ_iff.mp l.2
  have hd : (s.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (M := s.submatrix (Fin.castLE hl) (Fin.castLE hl))
      (fun i j h => hs.1 _ _ h)]
    simp [hs.2]
  have h0 : ∀ (b : Fin l) (i : Fin N), (l : ℕ) ≤ i → s i (Fin.castLE hl b) = 0 := fun b i h =>
    hs.1 _ _ (show (b : ℕ) < (i : ℕ) from lt_of_lt_of_le b.2 h)
  constructor
  · unfold lead
    rw [submatrix_mul_of_zero hl _ _ fun a b i h => by rw [h0 b i h, mul_zero], Matrix.det_mul, hd,
      mul_one]
  · unfold lead
    rw [submatrix_mul_of_zero hl _ _ fun a b i h => by
      rw [Matrix.transpose_apply, h0 a i h, zero_mul], Matrix.det_mul,
      ← Matrix.transpose_submatrix, Matrix.det_transpose, hd, one_mul]
end GlobalTheory.HL.Defect
