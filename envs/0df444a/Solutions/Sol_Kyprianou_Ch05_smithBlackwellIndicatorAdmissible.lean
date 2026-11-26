-- Prove2me | solution 1 for Kyprianou.Ch05.smithBlackwellIndicatorAdmissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:59:37.149844+00:00
-- url     : https://prove2.me/submissions/ab754443-b028-431f-ba37-fed41c798d2a

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The indicator of the half-open interval [0,y) is measurable, bounded on the positive half-line, nonincreasing there and integrable there, as required by Smith's Theorem A(a). -/
theorem solution
    (y : Real) (hy : 0 < y) :
    let psi : Real → Real := (Set.Ico 0 y).indicator (fun _ => 1)
    Measurable psi ∧ (∃ C : Real, ∀ v : Real, 0 ≤ v → |psi v| ≤ C) ∧
      AntitoneOn psi (Set.Ioi 0) ∧ IntegrableOn psi (Set.Ioi 0) := by
  dsimp only
  let psi : Real → Real := (Set.Ico 0 y).indicator (fun _ => 1)
  change Measurable psi ∧ (∃ C : Real, ∀ v : Real, 0 ≤ v → |psi v| ≤ C) ∧
    AntitoneOn psi (Set.Ioi 0) ∧ IntegrableOn psi (Set.Ioi 0)
  refine ⟨measurable_const.indicator measurableSet_Ico, ?_, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    intro v hv
    by_cases h : v ∈ Set.Ico (0 : Real) y <;> simp [psi, h]
  · intro a ha b hb hab
    by_cases h : b ∈ Set.Ico (0 : Real) y
    · have h' : a ∈ Set.Ico (0 : Real) y := ⟨ha.le, hab.trans_lt h.2⟩
      simp [psi, h, h']
    · by_cases h' : a ∈ Set.Ico (0 : Real) y <;> simp [psi, h, h']
  · apply Integrable.integrableOn
    apply (integrable_indicator_iff measurableSet_Ico).2
    apply integrableOn_const
    all_goals simp [Real.volume_Ico]
