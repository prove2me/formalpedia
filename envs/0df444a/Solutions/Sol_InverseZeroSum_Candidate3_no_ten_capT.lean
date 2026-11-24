-- Prove2me | solution 1 for InverseZeroSum.Candidate3.no_ten_capT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:04.514513+00:00
-- url     : https://prove2.me/submissions/7306f873-4bfe-4236-8fe9-0144e18adcd0

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_cap_inter_plane_le_four
public import Theorems.Thm_InverseZeroSum_Candidate3_horizontalSliceT_eq_inter
public import Theorems.Thm_InverseZeroSum_Candidate3_horizontalSliceT_card_le_four
public import Theorems.Thm_InverseZeroSum_Candidate3_card_eq_sum_horizontalSliceT
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
theorem _root_.solution {A : Finset F3T} (hA : IsCapT A) (hcard : A.card = 10) : False := by
  classical
  have hSlice4 : ∀ c : Fin 3, (horizontalSliceT A c).card ≤ 4 :=
    fun c => horizontalSliceT_card_le_four hA c
  obtain ⟨c, _hc_mem, hc_lt⟩ :=
    Finset.exists_card_fiber_lt_of_card_lt_mul
      (f := thirdCoordT) (s := A) (t := (Finset.univ : Finset (Fin 3))) (n := 4)
      (by simp [hcard])
  have hc_lt4 : (horizontalSliceT A c).card < 4 := by
    simpa [horizontalSliceT, thirdCoordT] using hc_lt
  have hc_le3 : (horizontalSliceT A c).card ≤ 3 := by omega
  have hc_ge2 : 2 ≤ (horizontalSliceT A c).card := by
    by_contra hnot
    have hc_le1 : (horizontalSliceT A c).card ≤ 1 := by omega
    have hrest :
        (∑ d ∈ (Finset.univ : Finset (Fin 3)).erase c,
          (horizontalSliceT A d).card) ≤ 8 := by
      calc
        (∑ d ∈ (Finset.univ : Finset (Fin 3)).erase c,
            (horizontalSliceT A d).card)
            ≤ ∑ _d ∈ (Finset.univ : Finset (Fin 3)).erase c, 4 := by
              exact Finset.sum_le_sum (fun d _hd => hSlice4 d)
        _ = 8 := by simp
    have hdecomp :
        A.card =
          (∑ d ∈ (Finset.univ : Finset (Fin 3)).erase c,
            (horizontalSliceT A d).card) +
          (horizontalSliceT A c).card := by
      calc
        A.card = ∑ d ∈ (Finset.univ : Finset (Fin 3)),
            (horizontalSliceT A d).card := by
              simpa using card_eq_sum_horizontalSliceT A
        _ =
            (∑ d ∈ (Finset.univ : Finset (Fin 3)).erase c,
              (horizontalSliceT A d).card) +
            (horizontalSliceT A c).card :=
              (Finset.sum_erase_add (Finset.univ : Finset (Fin 3))
                (fun d => (horizontalSliceT A d).card) (Finset.mem_univ c)).symm
    rw [hcard] at hdecomp
    omega
  obtain ⟨a, b, haS, hbS, hab⟩ :=
    Finset.one_lt_card_iff.mp (show 1 < (horizontalSliceT A c).card by omega)
  have haA : a ∈ A := (Finset.mem_filter.mp haS).1
  have hbA : b ∈ A := (Finset.mem_filter.mp hbS).1
  let H : PlaneIdx := horizontalPlaneT c
  have haH : a ∈ planeSetT H := by
    have hmem : a ∈ A ∩ planeSetT (horizontalPlaneT c) := by
      rw [← horizontalSliceT_eq_inter A c]
      exact haS
    simpa [H] using (Finset.mem_inter.mp hmem).2
  have hbH : b ∈ planeSetT H := by
    have hmem : b ∈ A ∩ planeSetT (horizontalPlaneT c) := by
      rw [← horizontalSliceT_eq_inter A c]
      exact hbS
    simpa [H] using (Finset.mem_inter.mp hmem).2
  let P : Finset F3T := {a, b}
  have hPcard : P.card = 2 := by simp [P, hab]
  have hPsubA : P ⊆ A := by
    intro x hx
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haA
    · exact hbA
  let Rset : Finset F3T := A \ P
  have hRcard : Rset.card = 8 := by
    dsimp [Rset]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hPsubA, hcard, hPcard]
  let T : Finset PlaneIdx :=
    Finset.univ.filter
      (fun p => onPlaneTB p a = true ∧ onPlaneTB p b = true)
  have hTcard : T.card = 4 := by
    simpa [T] using pair_plane_countT a b hab
  have hHa : onPlaneTB H a = true := (Finset.mem_filter.mp haH).2
  have hHb : onPlaneTB H b = true := (Finset.mem_filter.mp hbH).2
  have hHT : H ∈ T := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ H, hHa, hHb⟩
  have hRplane :
      ∀ p ∈ T, (Rset ∩ planeSetT p).card ≤ 2 := by
    intro p hp
    have hpab := (Finset.mem_filter.mp hp).2
    have haP : a ∈ planeSetT p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hpab.1⟩
    have hbP : b ∈ planeSetT p :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ b, hpab.2⟩
    have hPsub : P ⊆ A ∩ planeSetT p := by
      intro x hx
      have hx' : x = a ∨ x = b := by simpa [P] using hx
      rcases hx' with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨haA, haP⟩
      · exact Finset.mem_inter.mpr ⟨hbA, hbP⟩
    have heq :
        Rset ∩ planeSetT p = (A ∩ planeSetT p) \ P := by
      ext x
      simp [Rset, P, and_assoc, and_left_comm, and_comm]
    have h4p := cap_inter_plane_le_four hA p
    rw [heq, Finset.card_sdiff, Finset.inter_eq_left.mpr hPsub, hPcard]
    omega
  have hRH : (Rset ∩ planeSetT H).card ≤ 1 := by
    have hPsubH : P ⊆ A ∩ planeSetT H := by
      intro x hx
      have hx' : x = a ∨ x = b := by simpa [P] using hx
      rcases hx' with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨haA, haH⟩
      · exact Finset.mem_inter.mpr ⟨hbA, hbH⟩
    have heqH :
        Rset ∩ planeSetT H = (A ∩ planeSetT H) \ P := by
      ext x
      simp [Rset, P, and_assoc, and_left_comm, and_comm]
    have hAH3 : (A ∩ planeSetT H).card ≤ 3 := by
      have h := hc_le3
      rw [horizontalSliceT_eq_inter A c] at h
      simpa [H] using h
    rw [heqH, Finset.card_sdiff, Finset.inter_eq_left.mpr hPsubH, hPcard]
    omega
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
      (∑ p ∈ T, (Rset ∩ planeSetT p).card) ≤ 7 := by
    rw [hsumSplit]
    omega
  omega
end InverseZeroSum.Candidate3
