-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.gramT_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:11:29.845423+00:00
-- url     : https://prove2.me/submissions/6d70d1de-b107-47bc-8cd3-cf10b6db4761

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
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
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
open ValuativeRel
open scoped Pointwise ENNReal Classical
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.ContModel
namespace _root_.GlobalTheory.HL.ContModel
theorem _root_.solution (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    _root_.GlobalTheory.HL.gramT L Hm (_root_.GlobalTheory.HL.rmul x A) =
      _root_.GlobalTheory.HL.cT L A * _root_.GlobalTheory.HL.gramT L Hm x * A := by
  ext a b
  simp only [_root_.GlobalTheory.HL.gramT, _root_.GlobalTheory.HL.rmul, _root_.GlobalTheory.HL.hf,
    _root_.GlobalTheory.HL.cT, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end _root_.GlobalTheory.HL.ContModel
end GlobalTheory.HL.ContModel
