-- Prove2me | solution 1 for GlobalTheory.StepData.xi_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:02.50731+00:00
-- url     : https://prove2.me/submissions/91bbc48f-66fa-4ca0-88f2-d84bca257b77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_volNat_Cgrp_pos

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
theorem _root_.solution [ν.IsAddHaarMeasure] {J : Subgroup (GL (n ⊕ Fin c) k)}
    (ho : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (hc : IsCompact (J : Set (GL (n ⊕ Fin c) k)))
    (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) :
    xi ψ ν μ Φ J b h' h = 0 ↔ flat ψ ν μ Φ h' h = 0 := by
  have := (volNat_Cgrp_pos ν ho hc b h).ne'
  simp [funext_iff, xi, this]
end GlobalTheory.StepData
