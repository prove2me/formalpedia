-- Prove2me | solution 1 for GlobalTheory.HCA.SolFunc.continuous_extLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:54:03.847796+00:00
-- url     : https://prove2.me/submissions/dcab5c7a-cd45-43db-8078-9a05634b7ec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.HCA GlobalTheory.HCA.SolFunc
variable {d : ℕ}
namespace GlobalTheory.HCA.SolFunc
theorem _root_.solution {U : Set (E d)} (S : Submodule ℂ (U →ᵇ ℂ)) (x : E d) :
    Continuous fun u : S => extLin S u x := by
  by_cases hx : x ∈ U
  · have : (fun u : S => extLin S u x) = fun u : S => (u : U →ᵇ ℂ) ⟨x, hx⟩ := by
      funext u; simp [extLin, ext0, hx]
    rw [this]
    exact (BoundedContinuousFunction.evalCLM ℂ (⟨x, hx⟩ : U)).continuous.comp continuous_subtype_val
  · have : (fun u : S => extLin S u x) = fun _ => 0 := by
      funext u; simp [extLin, ext0, hx]
    rw [this]; exact continuous_const
end GlobalTheory.HCA.SolFunc
