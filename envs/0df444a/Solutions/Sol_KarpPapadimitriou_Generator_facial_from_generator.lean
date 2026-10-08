-- Prove2me | solution 1 for KarpPapadimitriou.Generator.facial_from_generator
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:17:29.324604+00:00
-- url     : https://prove2.me/submissions/c2e5c20b-6ab2-433d-9946-d287ab57f3d5

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Oracle

open KarpPapadimitriou.Generator

private lemma generated_facial (C : COP) (gen : Oracle C)
    (hgen : IsGenerator C gen) : IsFacialDescription C (FG C gen) := by
  constructor
  · intro a ha
    exact ha.1
  · intro z hz x
    constructor
    · intro hx f g hfg
      obtain ⟨_, p, hp⟩ := hfg
      have hv := (hgen z hz p).2 f g hp |>.2
      have hs : ((fun y : Fin (C.n z) → ℤ => fun j => (y j : ℚ)) '' C.S z) ⊆
          {y | dotQ f y ≤ (g : ℚ)} := by
        rintro y ⟨a, ha, rfl⟩
        have hh := hv a ha
        change dotQ f (fun j => (a j : ℚ)) ≤ (g : ℚ)
        simp only [dotQ, dotZ] at hh ⊢
        exact_mod_cast hh
      have hc : Convex ℚ {y : Fin (C.n z) → ℚ | dotQ f y ≤ (g : ℚ)} := by
        apply convex_halfSpace_le
        exact ⟨by intros; simp [dotQ, mul_add, Finset.sum_add_distrib],
          by intros; simp [dotQ, Finset.mul_sum, mul_left_comm]⟩
      exact convexHull_min hs hc hx
    · intro hx
      cases he : gen z x with
      | none => exact (hgen z hz x).1.mp he
      | some fg =>
        have hv := (hgen z hz x).2 fg.1 fg.2 he |>.1
        exact (not_lt_of_ge (hx fg.1 fg.2 ⟨hz, x, he⟩) hv).elim

theorem solution (C : COP) (gen : Oracle C)
    (hgen : IsGenerator C gen) : IsFacialDescription C (FG C gen) := generated_facial C gen hgen

#print axioms solution
