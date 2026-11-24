-- Prove2me | solution 1 for GlobalTheory.WittGaussMul.exists_first_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:36.985155+00:00
-- url     : https://prove2.me/submissions/d0b30202-0976-41a3-8e9c-790802251acb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormMul
import Theorems.Thm_GlobalTheory_WittGaussMul_exists_lt_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.WittGaussMul
namespace GlobalTheory.WittGaussMul
theorem _root_.solution (f : ℕ → ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hf : ∀ n, f n ≤ r ^ n) (hpos : 0 < ⨆ n, f n) :
    ∃ i, f i = (⨆ n, f n) ∧ ∀ k < i, f k < ⨆ n, f n := by
  classical
  have hb : BddAbove (Set.range f) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hf n).trans (pow_le_one₀ hr0.le hr1.le)⟩
  have hle : ∀ n, f n ≤ ⨆ n, f n := fun n => le_ciSup hb n
  have hex : ∃ i, f i = ⨆ n, f n := by
    by_contra hne
    push Not at hne
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hpos hr1
    obtain ⟨c, -, hcB, hc⟩ := exists_lt_bound f _ hpos M
      (fun k _ => lt_of_le_of_ne (hle k) (hne k))
    have : (⨆ n, f n) ≤ max c (r ^ M) := by
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n M with h | h
      · exact le_max_of_le_left (hc n h)
      · exact le_max_of_le_right ((hf n).trans (pow_le_pow_of_le_one hr0.le hr1.le h))
    exact absurd (max_lt hcB hM) (not_lt.mpr this)
  exact ⟨Nat.find hex, Nat.find_spec hex,
    fun k hk => lt_of_le_of_ne (hle k) (Nat.find_min hex hk)⟩
end GlobalTheory.WittGaussMul
