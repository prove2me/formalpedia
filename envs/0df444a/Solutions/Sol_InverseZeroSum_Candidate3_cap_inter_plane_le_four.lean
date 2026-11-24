-- Prove2me | solution 1 for InverseZeroSum.Candidate3.cap_inter_plane_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:18.742002+00:00
-- url     : https://prove2.me/submissions/cd9c85b0-cd29-4376-ac87-92252c6ee308

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planePointT_injective
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_eq_image
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_planeCoord_cap_le_four
public import Theorems.Thm_InverseZeroSum_Candidate3_planePointT_sum_zero_of_coord
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {A : Finset F3T} (hA : IsCapT A) (p : PlaneIdx) :
    (A ∩ planeSetT p).card ≤ 4 := by
  classical
  let Q : Finset PlaneCoord :=
    Finset.univ.filter (fun q => planePointT p q ∈ A)
  have hQcap :
      ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q,
        a ≠ b → a ≠ c → b ≠ c → a + b + c ≠ 0 := by
    intro a ha b hb c hc hab hac hbc hzero
    have haA : planePointT p a ∈ A := (Finset.mem_filter.mp ha).2
    have hbA : planePointT p b ∈ A := (Finset.mem_filter.mp hb).2
    have hcA : planePointT p c ∈ A := (Finset.mem_filter.mp hc).2
    have hab' : planePointT p a ≠ planePointT p b :=
      (planePointT_injective p).ne hab
    have hac' : planePointT p a ≠ planePointT p c :=
      (planePointT_injective p).ne hac
    have hbc' : planePointT p b ≠ planePointT p c :=
      (planePointT_injective p).ne hbc
    exact (hA _ haA _ hbA _ hcA hab' hac' hbc')
      (planePointT_sum_zero_of_coord p a b c hzero)
  have hImage :
      Q.image (planePointT p) = A ∩ planeSetT p := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, hqQ, rfl⟩ := Finset.mem_image.mp hx
      have hqA : planePointT p q ∈ A := (Finset.mem_filter.mp hqQ).2
      refine Finset.mem_inter.mpr ⟨hqA, ?_⟩
      rw [planeSetT_eq_image p]
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
    · intro hx
      have hxA : x ∈ A := (Finset.mem_inter.mp hx).1
      have hxP : x ∈ planeSetT p := (Finset.mem_inter.mp hx).2
      rw [planeSetT_eq_image p] at hxP
      obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hxP
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hxA⟩, rfl⟩
  calc
    (A ∩ planeSetT p).card = (Q.image (planePointT p)).card := by
      rw [hImage]
    _ = Q.card := Finset.card_image_of_injective Q (planePointT_injective p)
    _ ≤ 4 := planeCoord_cap_le_four Q hQcap
end InverseZeroSum.Candidate3
