-- Prove2me | solution 1 for MechanismDesign.IncentiveCompat.weaklyMonotone_monotoneWRT
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T05:21:13.711669+00:00
-- url     : https://prove2.me/submissions/3eaaade8-592e-4349-b898-7e1502822633

import Definitions.Def_MechanismDesign_IncentiveCompat_Model
set_option autoImplicit false
open MechanismDesign.IncentiveCompat

theorem solution {A Θ : Type*} [Nonempty Θ] (u : A → Θ → ℝ)
    (R : A → A → Prop) (hR : IsCompleteTransitive R) (q : Θ → A)
    (hq : WeaklyMonotone u q) : MonotoneWRT u R q := by
  intro x y hxy
  by_contra hnot
  have hrev : R (q y) (q x) := (hR.1 (q x) (q y)).resolve_left hnot
  have hh := hxy.1 (q y) (q x) ⟨hrev,hnot⟩
  have hw := hq x y
  linarith
