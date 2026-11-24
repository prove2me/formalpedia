-- Prove2me | solution 1 for GlobalTheory.ddChar_exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:53.269322+00:00
-- url     : https://prove2.me/submissions/d90fc756-e2ff-4c86-86d4-779412a9ea77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
import Theorems.Thm_GlobalTheory_ddChar_crt
import Theorems.Thm_GlobalTheory_ddChar_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]
namespace GlobalTheory
theorem _root_.solution [Finite R]
    (h : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 4 ≤ Nat.card (R ⧸ 𝔪)) :
    ∃ u : Rˣ, IsUnit ((u : R) - 1) := by
  have key : ∀ m : MaximalSpectrum R, ∃ c : R, c ∉ m.asIdeal ∧ c - 1 ∉ m.asIdeal := by
    intro m
    have h4 := h m.asIdeal m.isMaximal
    by_contra hno
    push Not at hno
    have hsurj : Function.Surjective
        (fun b : Bool => if b then (1 : R ⧸ m.asIdeal) else 0) := by
      intro y
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      by_cases hc : c ∈ m.asIdeal
      · exact ⟨false, by simp [Ideal.Quotient.eq_zero_iff_mem.2 hc]⟩
      · refine ⟨true, ?_⟩
        have h1 := hno c hc
        simp only [if_true]
        rw [eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk m.asIdeal), ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem]
        exact h1
    have := Nat.card_le_card_of_surjective _ hsurj
    simp at this
    omega
  choose f hf using key
  obtain ⟨t, ht⟩ := ddChar_crt f
  have hnot : ∀ (c : R) (m : MaximalSpectrum R), c - f m ∈ m.asIdeal → f m ∉ m.asIdeal → c ∉ m.asIdeal :=
    fun c m h1 h2 h3 => h2 (by simpa using m.asIdeal.sub_mem h3 h1)
  have htu : IsUnit t := ddChar_isUnit fun m => hnot t m (ht m) (hf m).1
  refine ⟨htu.unit, ddChar_isUnit fun m hm => (hf m).2 ?_⟩
  have : (t - 1) - (t - f m) = f m - 1 := by ring
  rw [← this]
  exact m.asIdeal.sub_mem (by simpa using hm) (ht m)
end GlobalTheory
