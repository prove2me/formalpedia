-- Prove2me | solution 1 for GroundTheory.LocalField.eq_zero_of_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:35.131534+00:00
-- url     : https://prove2.me/submissions/6140a046-e251-4802-8c72-1634079a295c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
import Theorems.Thm_GroundTheory_LocalField_rootEval_X
import Theorems.Thm_GroundTheory_LocalField_rootEval_C
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.rootEval_X
attribute [local simp] GroundTheory.LocalField.rootEval_C

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {P : Polynomial B}
namespace GroundTheory.LocalField
theorem _root_.solution (hP : P.Monic) {b : B} (hb : ∀ c : B, b * c = 0 → c = 0)
    {z : AdjoinRoot P} (h : AdjoinRoot.of P b * z = 0) : z = 0 := by
  set pb := AdjoinRoot.powerBasis' hP
  have h' : b • z = 0 := by
    rw [Algebra.smul_def]
    exact h
  apply pb.basis.repr.injective
  ext i
  have := congrArg (fun w => pb.basis.repr w i) h'
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
  rw [map_zero, Finsupp.zero_apply]
  exact hb _ this
end GroundTheory.LocalField
