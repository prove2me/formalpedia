-- Prove2me | solution 1 for GlobalTheory.ddChar_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:55.793829+00:00
-- url     : https://prove2.me/submissions/40354d9b-e5d8-44ff-aad6-a0f4f7edf645

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
theorem _root_.solution [Finite R] {v w b : R} (h : w * v + b = 1) :
    ∃ t : R, IsUnit (v + t * b) := by
  have key : ∀ m : MaximalSpectrum R, ∃ c : R, v + c * b ∉ m.asIdeal := by
    intro m
    by_cases hb : b ∈ m.asIdeal
    · refine ⟨0, fun hv => m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
      have : w * v + b ∈ m.asIdeal := m.asIdeal.add_mem (m.asIdeal.mul_mem_left _ (by simpa using hv)) hb
      rwa [h] at this
    · obtain ⟨y, i, hi, hyi⟩ := m.isMaximal.exists_inv hb
      refine ⟨(1 - v) * y, fun hmem => m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
      have e : (1 : R) = (v + (1 - v) * y * b) + (1 - v) * i := by linear_combination (v - 1) * hyi
      rw [e]
      exact m.asIdeal.add_mem hmem (m.asIdeal.mul_mem_left _ hi)
  choose f hf using key
  obtain ⟨t, ht⟩ := ddChar_crt f
  refine ⟨t, ddChar_isUnit fun m hm => hf m ?_⟩
  have : v + f m * b = (v + t * b) - (t - f m) * b := by ring
  rw [this]
  exact m.asIdeal.sub_mem hm (m.asIdeal.mul_mem_right _ (ht m))
end GlobalTheory
