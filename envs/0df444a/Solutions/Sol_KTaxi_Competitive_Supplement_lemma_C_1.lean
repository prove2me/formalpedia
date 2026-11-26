-- Prove2me | solution 1 for KTaxi.Competitive.Supplement.lemma_C_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-26T22:08:28.561328+00:00
-- url     : https://prove2.me/submissions/0d572e75-0d59-4a75-964b-529fd0109e42
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KTaxi_Competitive_Supplement_Memoryless
import Theorems.Thm_LefebvreVariations_ktaxi_discrepancy_upper_bound

set_option autoImplicit false

open scoped ENNReal NNReal


open KTaxi.Competitive.Supplement

private lemma mc_cons (A : MemorylessPolicy) (X : Multiset ℝ) (q : ℝ × ℝ) (qs : List (ℝ × ℝ)) :
    memorylessCost A X (q :: qs) =
      ∑' a : ℝ, A.law X q a * (edist a q.1 + memorylessCost A ((X.erase a).cons q.2) qs) := by
  rw [memorylessCost]

private lemma locations_const (x : ℝ) : locations (fun _ => x) = x ::ₘ x ::ₘ 0 := by
  simp [locations, List.ofFn_succ]
  rfl

private lemma lower (A : MemorylessPolicy) (x y : ℝ) : edist x y ≤ discrepancy A x y := by
  have hfree : Free x y [(y, y)] := ⟨fun _ => 1, by simp [scheduleCost]⟩
  refine le_trans ?_ (le_iSup_of_le ⟨[(y, y)], hfree⟩ le_rfl)
  rw [mc_cons, locations_const]
  have hsupp : ∀ a : ℝ, a ≠ x → A.law (x ::ₘ x ::ₘ 0) (y, y) a = 0 := by
    intro a ha
    by_contra h
    have := A.supported _ _ a (by simp) h
    simp [ha] at this
  rw [tsum_eq_single x (fun a ha => by rw [hsupp a ha, zero_mul])]
  have hone : A.law (x ::ₘ x ::ₘ 0) (y, y) x = 1 := by
    rw [← PMF.tsum_coe (A.law (x ::ₘ x ::ₘ 0) (y, y)),
      tsum_eq_single x (fun a ha => hsupp a ha)]
  rw [hone, one_mul]
  simp [memorylessCost]

theorem solution (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (ρ β : ℝ≥0)
    (hρ : 1 ≤ ρ) (hcomp : ObliviousCompetitive A x₀ ρ β) :
    ∀ x y : ℝ, edist x y ≤ discrepancy A x y ∧
      discrepancy A x y ≤ (ρ : ℝ≥0∞) * edist x y :=
  fun x y => ⟨lower A x y, LefebvreVariations.ktaxi_discrepancy_upper_bound A x₀ ρ β hρ hcomp x y⟩
