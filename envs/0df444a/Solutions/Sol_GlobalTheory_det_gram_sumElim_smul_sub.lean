-- Prove2me | solution 1 for GlobalTheory.det_gram_sumElim_smul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:33:56.439136+00:00
-- url     : https://prove2.me/submissions/4d267b9a-5bf5-462d-ba3a-caef81f15719

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramSumElimSmulSub
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
private lemma hsub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [eq_sub_iff_add_eq, ← H.h_add_left, sub_add_cancel]
private lemma hsub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, hsub_left, map_sub, ← H.h_herm, ← H.h_herm]
private lemma hsmul_right (c : F) (x y : V) :
    H.h x (algebraMap F E c • y) = algebraMap F E c * H.h x y := by
  rw [H.h_herm (algebraMap F E c • y) x, H.h_smul_left, map_mul, AlgEquiv.commutes, ← H.h_herm]
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
theorem _root_.solution {n : ℕ} (f f' : Fin n → V) (c : F) :
    (H.gram (Sum.elim f fun a => algebraMap F E c • (f' a - f a))).det
      = algebraMap F E c ^ (2 * n) * (H.gram (Sum.elim f f')).det := by
  set c' := algebraMap F E c with hc'
  have hcs : ∀ x : E, c • x = algebraMap F E c * x := fun x => Algebra.smul_def c x
  have key : H.gram (Sum.elim f fun a => c' • (f' a - f a)) =
      Matrix.fromBlocks 1 0 (-c' • (1 : Matrix (Fin n) (Fin n) E)) (c' • 1) * H.gram (Sum.elim f f') *
        Matrix.fromBlocks 1 (-c' • (1 : Matrix (Fin n) (Fin n) E)) 0 (c' • 1) := by
    ext (a | a) (b | b) <;>
      simp [HermSp.gram, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, H.h_smul_left,
        hsub_left, hsub_right, hc', hsmul_right, hcs] <;> ring
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_one, Matrix.det_smul, Fintype.card_fin, one_mul, two_mul, pow_add]
  ring
end GlobalTheory
