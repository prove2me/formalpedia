-- Prove2me | solution 1 for ModularCurve.nuTwo_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d59301e0-cb4b-5c54-bde9-90b7921c1fc7

import Definitions.Def_ModularCurve_GenusNumerics
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nuTwo_prime

open ModularCurve

theorem solution {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    nuTwo p = if p % 4 = 1 then 2 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq_iff : ∀ {s x : ZMod p}, s ^ 2 + 1 = 0 → (x ^ 2 + 1 = 0 ↔ x = s ∨ x = -s) := by
    intro s x hs
    constructor
    · intro hx
      have hfac : (x - s) * (x + s) = 0 := by linear_combination hx - hs
      rcases mul_eq_zero.mp hfac with hd | hd
      · exact Or.inl (by linear_combination hd)
      · exact Or.inr (by linear_combination hd)
    · rintro (rfl | rfl)
      · exact hs
      · linear_combination hs
  have hne_neg : ∀ {s : ZMod p}, s ^ 2 + 1 = 0 → s ≠ -s := by
    intro s hs hcontra
    have h2s : (2 : ZMod p) * s = 0 := by linear_combination hcontra
    rcases mul_eq_zero.mp h2s with h2 | hs0
    · have hcast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hcast
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    · have hs_ne : s ≠ 0 := by
        rintro rfl
        exact one_ne_zero (α := ZMod p) (by linear_combination hs)
      exact hs_ne hs0
  by_cases h1 : p % 4 = 1
  · rw [if_pos h1]
    obtain ⟨s, hs⟩ : IsSquare (-1 : ZMod p) :=
      ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    have hs2 : s ^ 2 + 1 = 0 := by linear_combination -hs
    have hns2 : (-s) ^ 2 + 1 = 0 := by linear_combination hs2
    show Nat.card {x : ZMod p // x ^ 2 + 1 = 0} = 2
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨s, hs2⟩, ⟨-s, hns2⟩, ?_, ?_⟩
    · simp only [ne_eq, Subtype.mk.injEq]
      exact hne_neg hs2
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.mk.injEq]
      exact (hsq_iff hs2).mp hx
  · rw [if_neg h1]
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hns : ¬IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]
      omega
    have hempty : IsEmpty {x : ZMod p // x ^ 2 + 1 = 0} := by
      refine ⟨fun z => ?_⟩
      obtain ⟨x, hx⟩ := z
      exact hns ⟨x, by linear_combination -hx⟩
    exact @Nat.card_of_isEmpty _ hempty

end S_ModularCurve_nuTwo_prime
end P2MW
export P2MW.S_ModularCurve_nuTwo_prime (solution)
