-- Prove2me | solution 1 for GlobalTheory.DegAsm.pairBd_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:57:16.918846+00:00
-- url     : https://prove2.me/submissions/6b8567bf-64c1-4c18-9e4b-c0abbc03b977

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_PairBdNonneg
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
noncomputable section
open NumberField GlobalTheory.DegCnt
namespace GlobalTheory.DegAsm
open NumberField in
private lemma vInv_nonneg' (K : Type) [Field K] [NumberField K] :
    0 ≤ _root_.Formalism.HermitianLatticesTheory.vInv K := by
  unfold _root_.Formalism.HermitianLatticesTheory.vInv
  positivity
end GlobalTheory.DegAsm
end
end

set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.DegCnt
open GlobalTheory GlobalTheory.DegAsm
open NumberField
namespace GlobalTheory.DegAsm
namespace _root_.GlobalTheory.DegAsm
theorem _root_.solution (K : Type) [Field K] [NumberField K]
    (k g j T x x' : ℕ) : 0 ≤ _root_.GlobalTheory.DegAsm.pairBd K k g j T x x' := by
  have hv := vInv_nonneg' K
  unfold _root_.GlobalTheory.DegAsm.pairBd
  dsimp only
  have hMb : 0 ≤ (20 * ((_root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) * (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^
      (2 * ((_root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) * (6 + _root_.GlobalTheory.DegCnt.cf K)) :=
    Real.rpow_nonneg (by positivity) _
  have hY : 0 ≤ (x : ℝ) * x' * ((T : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K)) ^ 2 := by positivity
  have hxx : 0 ≤ (x : ℝ) * x' := by positivity
  refine mul_nonneg (mul_nonneg (Real.rpow_nonneg hxx _) (Real.rpow_nonneg hY _)) ?_
  refine add_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hMb (by positivity)) ?_))
    (by positivity)
  exact Finset.sum_nonneg fun s _ => by positivity
end _root_.GlobalTheory.DegAsm
end GlobalTheory.DegAsm
