-- Prove2me | solution 1 for GlobalTheory.FrameOver.det_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:52.746372+00:00
-- url     : https://prove2.me/submissions/5c9091c1-b27d-4a4d-ad1d-bc327385eef3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
import Theorems.Thm_GlobalTheory_FrameOver_det_blocks
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_hf_conj
import Theorems.Thm_GlobalTheory_FrameBasic_main
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
open GlobalTheory GlobalTheory.FrameOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameOver
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {r k : ℕ}
    (S : Frames L r k) :
    (Matrix.of fun i j => hf L S.Hm (Sum.elim S.f' S.f i) (Sum.elim S.f S.f' j)).det = S.G := by
  have hU : IsUnit S.Zh.det := (GlobalTheory.FrameBasic.main L r k S).2.2.2.1
  have h1 : (Matrix.of fun i j => hf L S.Hm (Sum.elim S.f' S.f i) (Sum.elim S.f S.f' j)) =
      Matrix.fromBlocks S.Zh.transpose
        (Matrix.single (Fin.last r) (Fin.last r) (-algebraMap F E S.T'))
        (Matrix.single (Fin.last r) (Fin.last r) (-algebraMap F E S.T)) (S.Zh.map L.cj) := by
    ext (i | i) (j | j)
    · rfl
    · simp [S.gram', Matrix.single_apply, eq_comm]
    · simp [S.gram, Matrix.single_apply, eq_comm]
    · exact GlobalTheory.FrameBasic.hf_conj L S.herm.1 _ _
  have hD1 : S.D (Fin.last (r + 1)) = S.Zh.det := rfl
  have hD0 : S.D (Fin.last r).castSucc = (S.Zh.submatrix Fin.castSucc Fin.castSucc).det := rfl
  have hdet : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) E), (A.map L.cj).det = L.cj A.det := fun A =>
    (AlgEquiv.map_det L.cj A).symm
  rw [h1, det_blocks _ _ (by rwa [Matrix.det_transpose]), Frames.G, hD1, hD0,
    ← Matrix.transpose_submatrix, Matrix.submatrix_map, hdet, hdet, Matrix.det_transpose,
    Matrix.det_transpose, map_mul]
  ring
end GlobalTheory.FrameOver
