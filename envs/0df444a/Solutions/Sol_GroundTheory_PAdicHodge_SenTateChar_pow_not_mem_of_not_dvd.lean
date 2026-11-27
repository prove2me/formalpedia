-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.pow_not_mem_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:59.942607+00:00
-- url     : https://prove2.me/submissions/814db199-e190-44e0-859d-d59d23a5e73b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
import Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_levelHom_apply
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
theorem _root_.solution {s : ℕ} (hs : 1 ≤ s) {a : ℤ_[p]ˣ} (ha : a ∈ unitsOneAdd p s)
    (ha' : a ∉ unitsOneAdd p (s + 1)) {m : ℕ} (hm : ¬ p ∣ m) :
    a ^ m ∈ unitsOneAdd p s ∧ a ^ m ∉ unitsOneAdd p (s + 1) := by
  refine ⟨pow_mem ha m, fun h => ?_⟩
  have h1 : levelHom p s hs (⟨a, ha⟩ ^ m) = 1 := (levelHom_eq_one_iff hs _).2 (by simpa using h)
  have h2 : levelHom p s hs ⟨a, ha⟩ ≠ 1 := fun h' => ha' ((levelHom_eq_one_iff hs _).1 h')
  rw [map_pow, levelHom_apply, ← ofAdd_nsmul, ← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq,
    nsmul_eq_mul] at h1
  rw [levelHom_apply, ← ofAdd_zero, Ne, EmbeddingLike.apply_eq_iff_eq] at h2
  have hm' : (m : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  exact h2 ((mul_eq_zero.1 h1).resolve_left hm')
end GroundTheory.PAdicHodge.SenTateChar
