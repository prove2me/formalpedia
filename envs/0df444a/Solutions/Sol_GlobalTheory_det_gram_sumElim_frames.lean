-- Prove2me | solution 1 for GlobalTheory.det_gram_sumElim_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:03:25.374998+00:00
-- url     : https://prove2.me/submissions/0e8a0591-4965-4d02-90a0-85cef5eec851

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramSumElimSmulSub
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_det_gram_two_frames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
namespace GlobalTheory
section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
private lemma det_transpose_map_cj {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι E) :
    (N.transpose.map M.L.cj).det = M.L.cj N.det := by
  have h1 := RingHom.map_det (M.L.cj : E →+* E) N.transpose
  rw [Matrix.det_transpose] at h1
  exact h1.symm
private lemma castLE_succ_eq_castSucc (r : ℕ) (h : r ≤ r + 1) :
    (Fin.castLE h : Fin r → Fin (r + 1)) = Fin.castSucc := by
  funext i
  rfl
end
end GlobalTheory
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open GlobalTheory
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (P : LocNG.FPair H r) :
    (H.gram (Sum.elim P.A.f P.B.f)).det = (-1) ^ (r + 1) * P.Gv := by
  have diag : ∀ (Fr : LocNG.FrameD H r) (a b : Fin (r + 1)),
      H.h (Fr.f b) (Fr.f a) = Matrix.diagonal
        (fun i => if i = Fin.last r then -algebraMap F E Fr.T else 0) a b := by
    intro Fr a b
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = Fin.last r
      · subst ha
        simp [Fr.h_zz]
      · simp [ha, Fr.h_iso a a (Or.inl ha)]
    · rw [if_neg hab, Fr.h_iso b a ?_]
      by_contra hc
      simp only [not_or, not_not] at hc
      exact hab (hc.2.trans hc.1.symm)
  have hblk : H.gram (Sum.elim P.A.f P.B.f) = Matrix.fromBlocks
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E P.A.T else 0)
      (H.Zhat P.A.f P.B.f)
      ((H.Zhat P.A.f P.B.f).transpose.map M.L.cj)
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E P.B.T else 0) := by
    ext (a | a) (b | b)
    · exact diag P.A a b
    · rfl
    · exact H.h_herm _ _
    · exact diag P.B a b
  rw [hblk, GlobalTheory.det_gram_two_frames, det_transpose_map_cj]
  have hsub : ((H.Zhat P.A.f P.B.f).transpose.map M.L.cj).submatrix Fin.castSucc Fin.castSucc
      = ((H.Zhat P.A.f P.B.f).submatrix Fin.castSucc Fin.castSucc).transpose.map M.L.cj := rfl
  rw [hsub, det_transpose_map_cj]
  congr 1
  simp only [LocNG.FPair.Gv, HermSp.Gdet, HermSp.normE, HermSp.Dl, dif_pos le_rfl,
    dif_pos (Nat.le_succ r), Fin.castLE_rfl, Matrix.submatrix_id_id, castLE_succ_eq_castSucc, map_mul]
end GlobalTheory
