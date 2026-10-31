-- Prove2me | solution 1 for MNatOps.Monotone.thm3_induction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:41:58.401536+00:00
-- url     : https://prove2.me/submissions/658458a5-947f-42bf-b1eb-022f5f9c5459

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model
import Theorems.Thm_MNatOps_Monotone_exchange_step

open MNatOps.Monotone in
theorem solution {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (hG : SSQMNatConcave G)
    (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (s s' : Fin m → ℤ) (hss : s ≤ s')
    (a : Fin n → ℤ) (ha : a ∈ optSet G l u s) (haf : G (Sum.elim s a) ≠ ⊥)
    (hs' : s' ∈ finiteParams G l u) :
    ∀ r : ℕ, r ≤ n → ∃ a'' ∈ optSet G l u s', a'' ∈ lowerOrthant a r := by
  obtain ⟨b, hb, hbf⟩ := hs'
  -- every optimal solution at s' has the same (finite) value
  have hfin : ∀ a' ∈ optSet G l u s', G (Sum.elim s' a') ≠ ⊥ := by
    intro a' ha' h
    have := ha'.2 b hb.1
    rw [h] at this
    exact hbf (le_bot_iff.mp this)
  intro r
  induction r with
  | zero =>
    intro _
    exact ⟨b, hb, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ r ih =>
    intro hr
    obtain ⟨c, hc, hcl⟩ := ih (by omega)
    set i : Fin n := ⟨r, by omega⟩ with hi_def
    -- descend on the r-th coordinate, one unit step at a time
    have main : ∀ N : ℕ, ∀ a' ∈ optSet G l u s', a' ∈ lowerOrthant a r →
        a' i - a i ≤ (N : ℤ) → ∃ a'' ∈ optSet G l u s', a'' ∈ lowerOrthant a (r + 1) := by
      intro N
      induction N with
      | zero =>
        intro a' ha' hl hd
        refine ⟨a', ha', fun k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
        · exact hl k hk
        · have : k = i := Fin.ext hk
          subst this; push_cast at hd; omega
      | succ N ihN =>
        intro a' ha' hl hd
        by_cases hle : a' i ≤ a i
        · refine ⟨a', ha', fun k hk => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
          · exact hl k hk
          · have : k = i := Fin.ext hk
            subst this; exact hle
        · rw [not_le] at hle
          obtain ⟨j, hj, hopt', -, hlo⟩ :=
            exchange_step G hG l u s s' hss a ha haf a' ha' (hfin a' ha') i hle
          apply ihN (a' - dir i j) hopt' (hlo hl)
          have hji : j ≠ some i := by
            intro h; have := hj i h; omega
          have : dir i j i = 1 := by
            cases j with
            | none => simp [dir, DiscreteConvex.MConvexFunctions.CharVec]
            | some j =>
              have : i ≠ j := fun h => hji (by rw [h])
              simp [dir, DiscreteConvex.MConvexFunctions.CharVec, this]
          simp only [Pi.sub_apply, this]
          push_cast at hd ⊢; omega
    exact main (c i - a i).toNat c hc hcl (Int.self_le_toNat _)
