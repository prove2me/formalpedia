-- Prove2me | solution 1 for GlobalTheory.TestLat.Model.valAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:48.441308+00:00
-- url     : https://prove2.me/submissions/20e167c1-b870-42b7-9bf5-da117e7f3305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.TestLat GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
omit [NumberField K]
namespace GlobalTheory.TestLat.Model
theorem _root_.solution (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (c : C) (u : Fin N → K) :
    valAt lam e c u = ∑ i, u (e.symm (c, i)) • bVV K lam i := by
  simp [valAt, Module.Basis.equivFun_symm_apply, LinearMap.funLeft_apply]
end GlobalTheory.TestLat.Model
