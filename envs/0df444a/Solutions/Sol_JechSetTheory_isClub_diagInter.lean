-- Prove2me | solution 1 for JechSetTheory.isClub_diagInter
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T05:44:58.500238+00:00
-- url     : https://prove2.me/submissions/2bc8d0a8-be4d-4498-a4d9-848a4132bfa3

import Definitions.Def_JechStationary

open Cardinal Order Set JechSetTheory

theorem solution (k : Cardinal) (hk : k.IsRegular) (hk₀ : ℵ₀ < k)
    (X : Below k → Set (Below k)) (hX : ∀ a, IsClub (X a)) :
    IsClub (diagInter X) := by
  classical
  have hcof : Order.cof (Below k) = k := by
    show Order.cof k.ord.ToType = k
    rw [Ordinal.cof_toType, hk.cof_ord]
  have hα : ℵ₀ < Order.cof (Below k) := by rw [hcof]; exact hk₀
  have hD : ∀ y : Below k, IsClub (⋂ b : Iio y, X b) := fun y =>
    IsClub.iInter hα.ne' (by rw [Cardinal.lift_id, Cardinal.lift_id, hcof]; exact mk_Iio_toType_ord_lt y)
      fun b => hX b
  refine ⟨fun d hd hne _ x hx => ?_, fun a => ?_⟩
  · show ∀ a < x, x ∈ X a
    intro a hax
    obtain ⟨z, hzd, haz⟩ : ∃ z ∈ d, a < z := by
      by_contra hcon
      push Not at hcon
      exact absurd (hx.2 hcon) (not_le.mpr hax)
    apply (hX a).isLUB_mem (t := {y ∈ d | a < y})
      (fun y hy => (hd hy.1 : ∀ c < y, y ∈ X c) a hy.2) ⟨z, hzd, haz⟩
    refine ⟨fun y hy => hx.1 hy.1, fun b hb => hx.2 fun y hy => ?_⟩
    rcases lt_or_ge a y with h | h
    · exact hb ⟨hy, h⟩
    · exact h.trans (haz.le.trans (hb ⟨hzd, haz⟩))
  · choose f hf using fun y : Below k => (hD y).isCofinal y
    let g : ℕ → Below k := fun n => Nat.rec a (fun _ IH => f IH) n
    have hmono : Monotone g := monotone_nat_of_le_succ fun n => (hf (g n)).2
    have hg : BddAbove (range g) := by
      refine .of_not_isCofinal fun hg ↦ (cof_le hg).not_gt (hα.trans_le' ?_)
      simpa using mk_range_le_lift (f := g)
    obtain ⟨δ, hδ, hδmin⟩ := (wellFounded_lt (α := Below k)).has_min (upperBounds (range g)) hg
    have hlub : IsLUB (range g) δ := ⟨hδ, fun c hc => not_lt.1 (hδmin c hc)⟩
    refine ⟨δ, ?_, hδ ⟨0, rfl⟩⟩
    show ∀ b < δ, δ ∈ X b
    intro b hb
    obtain ⟨m, hbm⟩ : ∃ m, b < g m := by
      by_contra hcon
      push Not at hcon
      exact absurd (hlub.2 (fun _ ⟨j, hj⟩ => hj ▸ hcon j)) (not_le.mpr hb)
    apply (hX b).isLUB_mem (t := range fun n => g (n + m + 1)) _ (range_nonempty _)
    · refine ⟨?_, fun c hc => hlub.2 ?_⟩
      · rintro _ ⟨n, rfl⟩; exact hδ ⟨n + m + 1, rfl⟩
      · rintro _ ⟨j, rfl⟩; exact (hmono (by omega : j ≤ j + m + 1)).trans (hc ⟨j, rfl⟩)
    · rintro _ ⟨n, rfl⟩
      have h1 : g (n + m + 1) ∈ ⋂ c : Iio (g (n + m)), X c := (hf _).1
      exact mem_iInter.1 h1 ⟨b, lt_of_lt_of_le hbm (hmono (by omega))⟩
