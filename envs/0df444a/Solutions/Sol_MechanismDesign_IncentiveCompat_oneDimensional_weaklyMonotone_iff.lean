-- Prove2me | solution 1 for MechanismDesign.IncentiveCompat.oneDimensional_weaklyMonotone_iff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T05:21:15.109735+00:00
-- url     : https://prove2.me/submissions/7c55cc9d-09ff-4ea2-bfa5-b55e10d2522d

import Definitions.Def_MechanismDesign_IncentiveCompat_Model
set_option autoImplicit false
open MechanismDesign.IncentiveCompat

theorem solution {A Θ : Type*} [Nonempty Θ] (u : A → Θ → ℝ)
    (R : A → A → Prop) (hR : IsCompleteTransitive R)
    (h1 : OneDimensional u R) (q : Θ → A) :
    WeaklyMonotone u q ↔ MonotoneWRT u R q := by
  constructor
  · intro hq x y hxy
    by_contra hnot
    have hrev : R (q y) (q x) := (hR.1 (q x) (q y)).resolve_left hnot
    have hh := hxy.1 (q y) (q x) ⟨hrev,hnot⟩
    have hw := hq x y
    linarith
  · intro hq
    have hordered (x y : Θ) (hxy : HigherType u R x y) (hr : R (q x) (q y)) :
        u (q x) y - u (q y) y ≤ u (q x) x - u (q y) x := by
      by_cases hrev : R (q y) (q x)
      · exact (hxy.2 (q x) (q y) ⟨hr,hrev⟩).1.ge
      · exact (hxy.1 (q x) (q y) ⟨hr,hrev⟩).le
    intro x y
    by_cases heq : x = y
    · subst y
      exact le_refl _
    rcases h1 x y heq with hxy | hyx
    · exact hordered x y hxy (hq x y hxy)
    · have h := hordered y x hyx (hq y x hyx)
      linarith
