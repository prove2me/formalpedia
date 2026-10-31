-- Prove2me | solution 1 for MNatOps.Monotone.thm3_second_half
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:41:59.174046+00:00
-- url     : https://prove2.me/submissions/9f398c0a-27ec-44bd-9449-34e45253d52b

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model
import Theorems.Thm_MNatOps_Monotone_exchange_step

open MNatOps.Monotone in
theorem solution {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (hG : SSQMNatConcave G)
    (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (s s' : Fin m → ℤ) (hss : s ≤ s')
    (hs : s ∈ finiteParams G l u)
    (a' : Fin n → ℤ) (ha' : a' ∈ optSet G l u s') (ha'f : G (Sum.elim s' a') ≠ ⊥) :
    ∃ a ∈ optSet G l u s, a' ≤ a := by
  obtain ⟨b, hb, hbf⟩ := hs
  have hfin : ∀ a ∈ optSet G l u s, G (Sum.elim s a) ≠ ⊥ := by
    intro a ha h
    have := ha.2 b hb.1
    rw [h] at this
    exact hbf (le_bot_iff.mp this)
  -- upper orthant: a'_k ≤ a_k for the first r coordinates
  have ind : ∀ r : ℕ, r ≤ n → ∃ a ∈ optSet G l u s, ∀ k : Fin n, k.val < r → a' k ≤ a k := by
    intro r
    induction r with
    | zero => intro _; exact ⟨b, hb, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ r ih =>
      intro hr
      obtain ⟨c, hc, hcl⟩ := ih (by omega)
      set i : Fin n := ⟨r, by omega⟩ with hi_def
      -- ascend on the r-th coordinate, one unit step at a time
      have main : ∀ N : ℕ, ∀ a ∈ optSet G l u s, (∀ k : Fin n, k.val < r → a' k ≤ a k) →
          a' i - a i ≤ (N : ℤ) →
          ∃ a'' ∈ optSet G l u s, ∀ k : Fin n, k.val < r + 1 → a' k ≤ a'' k := by
        intro N
        induction N with
        | zero =>
          intro a ha hl hd
          refine ⟨a, ha, fun k hk => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
          · exact hl k hk
          · have : k = i := Fin.ext hk
            subst this; push_cast at hd; omega
        | succ N ihN =>
          intro a ha hl hd
          by_cases hle : a' i ≤ a i
          · refine ⟨a, ha, fun k hk => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
            · exact hl k hk
            · have : k = i := Fin.ext hk
              subst this; exact hle
          · rw [not_le] at hle
            obtain ⟨j, hj, -, hopt, -⟩ :=
              exchange_step G hG l u s s' hss a ha (hfin a ha) a' ha' ha'f i hle
            have hji : j ≠ some i := by
              intro h; have := hj i h; omega
            apply ihN (a + dir i j) hopt
            · intro k hk
              have hki : k ≠ i := by
                intro h; have : k.val = r := by rw [h]
                omega
              have := hl k hk
              cases j with
              | none => simp [dir, DiscreteConvex.MConvexFunctions.CharVec, hki]; omega
              | some j =>
                by_cases hkj : k = j
                · subst hkj; have := hj k rfl
                  simp [dir, DiscreteConvex.MConvexFunctions.CharVec, hki]; omega
                · simp [dir, DiscreteConvex.MConvexFunctions.CharVec, hki, hkj]; omega
            · have : dir i j i = 1 := by
                cases j with
                | none => simp [dir, DiscreteConvex.MConvexFunctions.CharVec]
                | some j =>
                  have : i ≠ j := fun h => hji (by rw [h])
                  simp [dir, DiscreteConvex.MConvexFunctions.CharVec, this]
              simp only [Pi.add_apply, this]
              push_cast at hd ⊢; omega
      exact main (a' i - c i).toNat c hc hcl (Int.self_le_toNat _)
  obtain ⟨a, h1, h2⟩ := ind n le_rfl
  exact ⟨a, h1, fun k => h2 k k.isLt⟩
