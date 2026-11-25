-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.relIndex_unitsOneAdd_inf_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:17.515153+00:00
-- url     : https://prove2.me/submissions/0107388c-a0b8-4701-b619-8ae38fb4e4db

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
import Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_levelHom_eq_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.SenTateChar
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge.SenTateChar
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (R : Subgroup ℤ_[p]ˣ) {c : ℤ_[p]ˣ}
    (hcR : c ∈ R) (hc : c ∈ unitsOneAdd p k) (hc' : c ∉ unitsOneAdd p (k + 1)) :
    (unitsOneAdd p (k + 1) ⊓ R).relIndex (unitsOneAdd p k ⊓ R) = p := by
  set S := unitsOneAdd p k ⊓ R
  let φ : S →* Multiplicative (ZMod p) :=
    (levelHom p k hk).comp (Subgroup.inclusion inf_le_left)
  have hker : φ.ker = (unitsOneAdd p (k + 1) ⊓ R).subgroupOf S := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change levelHom p k hk _ = 1 ↔ _
    rw [levelHom_eq_one_iff]
    exact ⟨fun h => ⟨h, u.2.2⟩, fun h => h.1⟩
  have hrange : φ.range = ⊤ := by
    have hne : φ ⟨c, hc, hcR⟩ ≠ 1 := by
      change levelHom p k hk _ ≠ 1
      rw [Ne, levelHom_eq_one_iff]
      exact hc'
    have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have := Subgroup.eq_bot_or_eq_top_of_prime_card φ.range (hp := ⟨by rw [hcard]; exact hp.out⟩)
    rcases this with h | h
    · exact absurd (h ▸ φ.mem_range.2 ⟨_, rfl⟩ : φ ⟨c, hc, hcR⟩ ∈ (⊥ : Subgroup _))
        (by rw [Subgroup.mem_bot]; exact hne)
    · exact h
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
end GroundTheory.PAdicHodge.SenTateChar
