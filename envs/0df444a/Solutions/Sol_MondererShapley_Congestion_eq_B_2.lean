-- Prove2me | solution 1 for MondererShapley.Congestion.eq_B_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:00:47.087208+00:00
-- url     : https://prove2.me/submissions/23f21f10-f90f-41f3-8036-f573e0f6cab8

import Mathlib
import Definitions.Def_MondererShapley_Congestion_FacilityConstruction

open MondererShapley.Congestion

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (Y i)] (P : (∀ i, Y i) → ℝ) (m : ∀ i, Y i) :
    (⋂ i, stratFac i (m i)) ∩ M1 Y = {epsOf m} ∧
      vecSum (xn P) (⋂ i, stratFac i (m i)) = P m := by
  classical
  have hinj : Function.Injective (epsOf (Y := Y)) := by
    intro a b hab
    funext i
    have h := congrFun (congrFun hab i) (a i)
    simpa [epsOf] using h.symm
  have he : epsOf m ∈ ⋂ i, stratFac i (m i) := by simp [stratFac, epsOf]
  have hs : (⋂ i, stratFac i (m i)) ∩ M1 Y = {epsOf m} := by
    ext e
    constructor
    · rintro ⟨h, a, rfl⟩
      have ha : a = m := by
        funext i
        have hi := Set.mem_iInter.mp h i
        exact (of_decide_eq_true hi).symm
      simp [ha]
    · rintro rfl
      exact ⟨he, m, rfl⟩
  refine ⟨hs, ?_⟩
  have hx : xn P (epsOf m) = P m := by
    unfold xn
    split_ifs with h
    · rw [hinj h.choose_spec.symm]
    · exact False.elim (h ⟨m, rfl⟩)
  unfold vecSum
  rw [show (∑ᶠ j ∈ ⋂ i, stratFac i (m i), xn P j) =
      ∑ᶠ j ∈ ({epsOf m} : Set (Facility Y)), xn P j from ?_]
  · simpa using hx
  · apply finsum_congr
    intro e
    by_cases h : e ∈ ⋂ i, stratFac i (m i)
    · by_cases h1 : e ∈ M1 Y
      · have : e = epsOf m := Set.mem_singleton_iff.mp (hs ▸ ⟨h, h1⟩)
        subst e
        simp [he]
      · have hz : xn P e = 0 := by
          unfold xn
          split_ifs with hh
          · exact False.elim (h1 ⟨hh.choose, hh.choose_spec.symm⟩)
          · rfl
        have hn : e ≠ epsOf m := by rintro rfl; exact h1 ⟨m, rfl⟩
        simp [h, hn, hz]
    · have hn : e ≠ epsOf m := by rintro rfl; exact h he
      simp [h, hn]

#print axioms solution
