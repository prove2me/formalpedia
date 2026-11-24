-- Prove2me | solution 1 for InverseZeroSum.Candidate3.nine_cap_plane_card_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:44.819627+00:00
-- url     : https://prove2.me/submissions/16739e32-8066-4ebb-b1ab-9e890b1caf7e

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_cap_inter_plane_le_four
public import Theorems.Thm_InverseZeroSum_Candidate3_pair_plane_countT
public import Theorems.Thm_InverseZeroSum_Candidate3_pair_planes_coverT
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {A : Finset F3T} (hA : IsCapT A)
    (hcard : A.card = 9) (H : PlaneIdx) :
    (A ∩ planeSetT H).card ≠ 2 := by
  classical
  intro hAH2
  obtain ⟨a, b, haH, hbH, hab⟩ :=
    Finset.one_lt_card_iff.mp
      (show 1 < (A ∩ planeSetT H).card by omega)
  have haA : a ∈ A := (Finset.mem_inter.mp haH).1
  have hbA : b ∈ A := (Finset.mem_inter.mp hbH).1
  have haP : a ∈ planeSetT H := (Finset.mem_inter.mp haH).2
  have hbP : b ∈ planeSetT H := (Finset.mem_inter.mp hbH).2
  let P : Finset F3T := {a, b}
  have hPcard : P.card = 2 := by simp [P, hab]
  have hPsubA : P ⊆ A := by
    intro x hx
    have hx' : x = a ∨ x = b := by simpa [P] using hx
    rcases hx' with rfl | rfl
    · exact haA
    · exact hbA
  let Rset : Finset F3T := A \ P
  have hRcard : Rset.card = 7 := by
    dsimp [Rset]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hPsubA, hcard, hPcard]
  let T : Finset PlaneIdx :=
    Finset.univ.filter
      (fun p => onPlaneTB p a = true ∧ onPlaneTB p b = true)
  have hTcard : T.card = 4 := by
    simpa [T] using pair_plane_countT a b hab
  have hHa : onPlaneTB H a = true := (Finset.mem_filter.mp haP).2
  have hHb : onPlaneTB H b = true := (Finset.mem_filter.mp hbP).2
  have hHT : H ∈ T := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ H, hHa, hHb⟩
  have hRplane :
      ∀ p ∈ T, (Rset ∩ planeSetT p).card ≤ 2 := by
    intro p hp
    have hpab := (Finset.mem_filter.mp hp).2
    have haPlane : a ∈ planeSetT p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hpab.1⟩
    have hbPlane : b ∈ planeSetT p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ b, hpab.2⟩
    have hPsub : P ⊆ A ∩ planeSetT p := by
      intro x hx
      have hx' : x = a ∨ x = b := by simpa [P] using hx
      rcases hx' with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨haA, haPlane⟩
      · exact Finset.mem_inter.mpr ⟨hbA, hbPlane⟩
    have heq :
        Rset ∩ planeSetT p = (A ∩ planeSetT p) \ P := by
      ext x
      simp [Rset, P, and_assoc, and_left_comm, and_comm]
    have h4p := cap_inter_plane_le_four hA p
    rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr hPsub, hPcard]
    omega
  have hPsubH : P ⊆ A ∩ planeSetT H := by
    intro x hx
    have hx' : x = a ∨ x = b := by simpa [P] using hx
    rcases hx' with rfl | rfl
    · exact haH
    · exact hbH
  have hRH : (Rset ∩ planeSetT H).card = 0 := by
    have heqH :
        Rset ∩ planeSetT H = (A ∩ planeSetT H) \ P := by
      ext x
      simp [Rset, P, and_assoc, and_left_comm, and_comm]
    rw [heqH, Finset.card_sdiff, Finset.inter_eq_left.mpr hPsubH, hAH2, hPcard]
  have hRsubset :
      Rset ⊆ T.biUnion (fun p => Rset ∩ planeSetT p) := by
    intro z hz
    obtain ⟨p, hpa, hpb, hpz⟩ := pair_planes_coverT a b z hab
    exact Finset.mem_biUnion.mpr
      ⟨p,
        Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpa, hpb⟩,
        Finset.mem_inter.mpr
          ⟨hz, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hpz⟩⟩⟩
  have hRle :
      Rset.card ≤ ∑ p ∈ T, (Rset ∩ planeSetT p).card :=
    (Finset.card_le_card hRsubset).trans Finset.card_biUnion_le
  have hTEraseCard : (T.erase H).card = 3 := by
    rw [Finset.card_erase_of_mem hHT, hTcard]
  have hOther :
      (∑ p ∈ T.erase H, (Rset ∩ planeSetT p).card) ≤ 6 := by
    calc
      (∑ p ∈ T.erase H, (Rset ∩ planeSetT p).card)
          ≤ ∑ _p ∈ T.erase H, 2 := by
            exact Finset.sum_le_sum
              (fun p hp => hRplane p (Finset.mem_of_mem_erase hp))
      _ = 6 := by simp [hTEraseCard]
  have hsumSplit :
      (∑ p ∈ T, (Rset ∩ planeSetT p).card) =
        (∑ p ∈ T.erase H, (Rset ∩ planeSetT p).card) +
          (Rset ∩ planeSetT H).card := by
    exact (Finset.sum_erase_add T
      (fun p => (Rset ∩ planeSetT p).card) hHT).symm
  have hsumLe :
      (∑ p ∈ T, (Rset ∩ planeSetT p).card) ≤ 6 := by
    rw [hsumSplit, hRH, Nat.add_zero]
    exact hOther
  omega
end InverseZeroSum.Candidate3
