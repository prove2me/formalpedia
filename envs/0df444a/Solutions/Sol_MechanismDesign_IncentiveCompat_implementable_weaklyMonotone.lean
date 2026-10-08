-- Prove2me | solution 1 for MechanismDesign.IncentiveCompat.implementable_weaklyMonotone
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T05:21:12.472317+00:00
-- url     : https://prove2.me/submissions/e158b7b0-e2ab-42f5-86cf-f9a62ba98341

import Definitions.Def_MechanismDesign_IncentiveCompat_Model
set_option autoImplicit false
open MechanismDesign.IncentiveCompat

theorem solution {A Θ : Type*} [Nonempty Θ] (u : A → Θ → ℝ) (q : Θ → A)
    (hq : Implementable u q) : WeaklyMonotone u q := by
  obtain ⟨t,ht⟩ := hq
  intro x y
  have hxy := ht x y
  have hyx := ht y x
  dsimp [IsIC] at *
  linarith
