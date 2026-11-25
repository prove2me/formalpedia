-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.relVol_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:29:36.723825+00:00
-- url     : https://prove2.me/submissions/51886316-fa41-4464-871f-0618753ce152

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
open ValuativeRel
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.ContModel
namespace _root_.GlobalTheory.HL.ContModel
theorem _root_.solution {W : Type} [AddCommGroup W]
    {W0 A B : AddSubgroup W} (h : B ≤ A) (hB : B.relIndex W0 ≠ 0) :
    _root_.GlobalTheory.HL.relVol W0 A = B.relIndex A * _root_.GlobalTheory.HL.relVol W0 B := by
  unfold _root_.GlobalTheory.HL.relVol
  have h1 := AddSubgroup.relIndex_inf_mul_relIndex W0 B A
  have h2 := AddSubgroup.relIndex_inf_mul_relIndex B W0 A
  have h3 := AddSubgroup.relIndex_inf_mul_relIndex B A W0
  rw [inf_eq_left.mpr h] at h1 h3
  rw [inf_comm W0 B] at h1
  rw [inf_comm W0 A] at h2
  rw [← h3] at hB ⊢
  have hd : (B.relIndex (A ⊓ W0) : ℝ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hB
  have hα : (A.relIndex W0 : ℝ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hB
  have key : (W0.relIndex B : ℝ) * B.relIndex A = B.relIndex (A ⊓ W0) * W0.relIndex A := by
    exact_mod_cast h1.trans h2.symm
  push_cast
  field_simp
  linear_combination (-1 : ℝ) * key
end _root_.GlobalTheory.HL.ContModel
end GlobalTheory.HL.ContModel
