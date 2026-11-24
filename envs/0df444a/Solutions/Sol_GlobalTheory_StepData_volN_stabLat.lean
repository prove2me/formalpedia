-- Prove2me | solution 1 for GlobalTheory.StepData.volN_stabLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:04.87989+00:00
-- url     : https://prove2.me/submissions/91a56741-a3dd-4ed8-9996-70fb8fd197b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_isOpen_isCompact_conj
import Theorems.Thm_GlobalTheory_StepData_volN_ne_zero_ne_top


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
theorem _root_.solution [ν.IsAddHaarMeasure] (b : GL (n ⊕ Fin c) k) :
    0 < (volN ν n c 1 ((stabLat b).subgroupOf (N k n c 1))).toReal := by
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj b SplitFlip.isOpen_KO SplitFlip.isCompact_KO
  obtain ⟨h3, h4⟩ := volN_ne_zero_ne_top ν 1 h1 h2
  exact ENNReal.toReal_pos h3 h4
end GlobalTheory.StepData
