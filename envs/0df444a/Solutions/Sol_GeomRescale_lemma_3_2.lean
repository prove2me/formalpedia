-- Prove2me | solution 1 for GeomRescale.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:22:32.307211+00:00
-- url     : https://prove2.me/submissions/a8c97844-3808-4fb8-ba69-3cddaea1e663

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_enlarge

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

open GeomRescale in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (μ : ℝ) (hμ : max 0 (-f Finset.univ) ≤ μ) :
    Submodular (enlarge f μ) ∧
      ((0 : Fin n → ℝ) ∈ baseB (enlarge f μ) → ∀ S, -μ ≤ f S) ∧
      ∀ μ' : ℝ, μ ≤ μ' → baseB (enlarge f μ) ⊆ baseB (enlarge f μ') := by
  have hμ0 : 0 ≤ μ := le_trans (le_max_left _ _) hμ
  have hμ1 : -f Finset.univ ≤ μ := le_trans (le_max_right _ _) hμ
  have hg0 : ∀ m, enlarge f m ∅ = 0 := fun m => if_pos (Or.inl rfl)
  have hgu : ∀ m, enlarge f m Finset.univ = 0 := fun m => if_pos (Or.inr rfl)
  have hgp : ∀ m U, U ≠ ∅ → U ≠ Finset.univ → enlarge f m U = f U + m :=
    fun m U h1 h2 => if_neg (not_or.mpr ⟨h1, h2⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro S T
    by_cases hS0 : S = ∅
    · rw [hS0, Finset.empty_union, Finset.empty_inter, hg0] <;> linarith
    by_cases hT0 : T = ∅
    · rw [hT0, Finset.union_empty, Finset.inter_empty, hg0] <;> linarith
    by_cases hSu : S = Finset.univ
    · rw [hSu, Finset.union_eq_left.2 (Finset.subset_univ T),
        Finset.inter_eq_right.2 (Finset.subset_univ T), hgu] <;> linarith
    by_cases hTu : T = Finset.univ
    · rw [hTu, Finset.union_eq_right.2 (Finset.subset_univ S),
        Finset.inter_eq_left.2 (Finset.subset_univ S), hgu] <;> linarith
    rw [hgp μ S hS0 hSu, hgp μ T hT0 hTu]
    have hST := hsub S T
    have hU0 : S ∪ T ≠ ∅ := fun h => hS0 (Finset.union_eq_empty.mp h).1
    have hIu : S ∩ T ≠ Finset.univ := by
      intro h
      apply hSu
      refine Finset.eq_univ_of_forall (fun x => ?_)
      have hx := Finset.mem_univ x
      rw [← h] at hx
      exact (Finset.mem_inter.mp hx).1
    by_cases hUu : S ∪ T = Finset.univ
    · rw [hUu, hgu]
      rw [hUu] at hST
      by_cases hI0 : S ∩ T = ∅
      · rw [hI0, hg0]; rw [hI0, hf0] at hST; linarith
      · rw [hgp μ _ hI0 hIu]; linarith
    · rw [hgp μ _ hU0 hUu]
      by_cases hI0 : S ∩ T = ∅
      · rw [hI0, hg0]; rw [hI0, hf0] at hST; linarith
      · rw [hgp μ _ hI0 hIu]; linarith
  · rintro ⟨h1, -⟩ S
    have h := h1 S
    have hx : xsum (0 : Fin n → ℝ) S = 0 := by simp [xsum]
    rw [hx] at h
    by_cases hS0 : S = ∅
    · rw [hS0, hf0]; linarith
    by_cases hSu : S = Finset.univ
    · rw [hSu]; linarith
    rw [hgp μ S hS0 hSu] at h
    linarith
  · intro μ' hμμ' x hx
    obtain ⟨h1, h2⟩ := hx
    refine ⟨fun U => le_trans (h1 U) ?_, ?_⟩
    · unfold enlarge
      split_ifs <;> linarith
    · rw [h2, hgu, hgu]
