-- Prove2me | solution 1 for GlobalTheory.StepData.volNat_stabLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:25.096246+00:00
-- url     : https://prove2.me/submissions/8f9ec990-2e6a-4374-8972-b4103b14c4c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_volN_stabLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
  (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
namespace GlobalTheory.StepData
theorem _root_.solution [ν.IsAddHaarMeasure] (b : GL (n ⊕ Fin c) k) : volNat ν b (stabLat b) = 1 :=
  div_self (volN_stabLat ν b).ne'
end GlobalTheory.StepData
