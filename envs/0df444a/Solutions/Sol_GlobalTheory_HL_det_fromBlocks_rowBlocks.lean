-- Prove2me | solution 1 for GlobalTheory.HL.det_fromBlocks_rowBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:01:34.702952+00:00
-- url     : https://prove2.me/submissions/e568ee82-ad84-4298-96a8-c8c12ef410b3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Theorems.Thm_GlobalTheory_HL_fromBlocks_updateRow_eq
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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {R n : Type} [CommRing R] [Fintype n] [DecidableEq n]
    (Z Z' : Matrix n n R) (l : n) (b c : n → R) :
    (Matrix.fromBlocks Z ((0 : Matrix n n R).updateRow l b)
        ((0 : Matrix n n R).updateRow l c) Z').det =
      Z.det * Z'.det - (Z.updateRow l c).det * (Z'.updateRow l b).det := by
  set F : (n ⊕ n → R) → (n ⊕ n → R) → R := fun u v =>
    (((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) u).updateRow (Sum.inr l) v).det with hF
  have hz : (0 : Matrix n n R).updateRow l 0 = 0 := by
    ext i j; simp [Matrix.updateRow_apply]
  have hz0 : ∀ X : Matrix n n R, (X.updateRow l 0).det = 0 := fun X =>
    Matrix.det_eq_zero_of_row_eq_zero l (by simp)
  have add2 : ∀ u v w, F u (v + w) = F u v + F u w := fun u v w => Matrix.det_updateRow_add _ _ _ _
  have add1 : ∀ u v w, F (u + v) w = F u w + F v w := fun u v w => by
    simp only [hF]
    have hne : (Sum.inl l : n ⊕ n) ≠ Sum.inr l := by simp
    rw [Matrix.updateRow_comm _ hne, Matrix.updateRow_comm _ hne, Matrix.updateRow_comm _ hne]
    exact Matrix.det_updateRow_add _ _ _ _
  have swap : ∀ u v, F u v = - F v u := fun u v => by
    simp only [hF]
    have hne : (Sum.inl l : n ⊕ n) ≠ Sum.inr l := by simp
    have : ((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) u).updateRow (Sum.inr l) v =
        (((Matrix.fromBlocks Z 0 0 Z').updateRow (Sum.inl l) v).updateRow (Sum.inr l) u).submatrix
          (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
      ext i j
      by_cases h1 : i = Sum.inl l
      · subst h1; simp [Matrix.updateRow_apply]
      · by_cases h2 : i = Sum.inr l
        · subst h2; simp [Matrix.updateRow_apply]
        · simp [Matrix.updateRow_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, h1, h2]
    rw [this, Matrix.det_permute, Equiv.Perm.sign_swap hne]
    simp
  have val : ∀ a b c d : n → R, F (Sum.elim a b) (Sum.elim c d) =
      (Matrix.fromBlocks (Z.updateRow l a) ((0 : Matrix n n R).updateRow l b)
        ((0 : Matrix n n R).updateRow l c) (Z'.updateRow l d)).det := fun a b c d => by
    simp only [hF, fromBlocks_updateRow_eq]
  have e : ∀ a b : n → R, Sum.elim a b = Sum.elim a (0 : n → R) + Sum.elim (0 : n → R) b := by
    intro a b; ext (i | i) <;> simp
  have h0 := val (Z l) b c (Z' l)
  rw [Matrix.updateRow_eq_self, Matrix.updateRow_eq_self] at h0
  rw [← h0, e (Z l) b, e c (Z' l), add1, add2, add2, swap (Sum.elim 0 b) (Sum.elim c 0)]
  simp only [val, hz, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, hz0,
    Matrix.updateRow_eq_self]
  ring
end GlobalTheory.HL
