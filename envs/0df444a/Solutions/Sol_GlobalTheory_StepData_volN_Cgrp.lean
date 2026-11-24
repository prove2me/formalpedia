-- Prove2me | solution 1 for GlobalTheory.StepData.volN_Cgrp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:22.517896+00:00
-- url     : https://prove2.me/submissions/c37b1dd8-5543-4508-8785-51488d0be095

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
theorem _root_.solution [ν.IsAddHaarMeasure] {J : Subgroup (GL (n ⊕ Fin c) k)} (ho : IsOpen (J : Set (GL (n ⊕ Fin c) k)))
    (hc : IsCompact (J : Set (GL (n ⊕ Fin c) k))) (h : GL (n ⊕ Fin c) k) :
    volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) ≠ 0 ∧ volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) ≠ ⊤ := by
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj h ho hc
  have e : (Cgrp J h).subgroupOf (N k n c 1) = (J.comap (MulAut.conj h⁻¹).toMonoidHom).subgroupOf (N k n c 1) := by
    ext u
    exact ⟨fun H => H.2, fun H => ⟨(le_sup_right : N k n c 1 ≤ R k n c 1) u.2, H⟩⟩
  rw [e]
  exact volN_ne_zero_ne_top ν 1 h1 h2
end GlobalTheory.StepData
