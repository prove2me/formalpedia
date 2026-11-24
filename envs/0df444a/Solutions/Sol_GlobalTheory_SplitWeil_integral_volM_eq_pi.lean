-- Prove2me | solution 1 for GlobalTheory.SplitWeil.integral_volM_eq_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:35.826828+00:00
-- url     : https://prove2.me/submissions/5529a46e-6834-4fce-89c7-feec25148734

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Theorems.Thm_GlobalTheory_SplitWeil_map_curry_symm_pi_pi
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]
omit [BorelSpace k] [DecidableEq a] [DecidableEq b]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ x ∂(volM ν b a) = ∫ y, Φ (Matrix.of (Function.curry y)) ∂(Measure.pi fun _ : b × a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  rw [← map_curry_symm_pi_pi ν, (MeasurableEquiv.curry b a k).symm.measurableEmbedding.integral_map]
  rfl
end GlobalTheory.SplitWeil
