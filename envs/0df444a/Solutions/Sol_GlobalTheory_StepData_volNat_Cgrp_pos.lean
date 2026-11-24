-- Prove2me | solution 1 for GlobalTheory.StepData.volNat_Cgrp_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:54.378932+00:00
-- url     : https://prove2.me/submissions/121fb2d3-fba4-447f-b26a-63a23346d695

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_volN_stabLat
import Theorems.Thm_GlobalTheory_StepData_volN_Cgrp

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
    (b h : GL (n ⊕ Fin c) k) : 0 < volNat ν b (Cgrp J h) :=
  div_pos (ENNReal.toReal_pos (volN_Cgrp ν ho hc h).1 (volN_Cgrp ν ho hc h).2) (volN_stabLat ν b)
end GlobalTheory.StepData
