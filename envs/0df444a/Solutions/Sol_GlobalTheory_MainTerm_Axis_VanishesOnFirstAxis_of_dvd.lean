-- Prove2me | solution 1 for GlobalTheory.MainTerm.Axis.VanishesOnFirstAxis.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:41:57.035989+00:00
-- url     : https://prove2.me/submissions/fd1ef0fd-d21f-435c-b4e1-8de024224501

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
import Theorems.Thm_GlobalTheory_MainTerm_Axis_VanishesOnFirstAxis_mul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.MainTerm GlobalTheory.MainTerm.Axis
variable {C : Type} [Field C] {ι ι' : Type}
namespace GlobalTheory.MainTerm.Axis
namespace VanishesOnFirstAxis
theorem _root_.solution {F G : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (hd : F ∣ G) : VanishesOnFirstAxis G := by
  obtain ⟨K, rfl⟩ := hd
  rw [mul_comm]
  exact h.mul_left K
end VanishesOnFirstAxis
end GlobalTheory.MainTerm.Axis
