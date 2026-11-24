-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.intO_lift_of_val_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:44.731175+00:00
-- url     : https://prove2.me/submissions/6a17236b-9df2-4348-b53c-13416a7c2ccf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial IsLocalRing
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (K : UQ) (x : K.E) (h : 0 ≤ val K.O x) : ∃ a : K.O, algebraMap K.O K.E a = x := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  unfold val at h
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega
end GlobalTheory.UnitLemma.Unr
