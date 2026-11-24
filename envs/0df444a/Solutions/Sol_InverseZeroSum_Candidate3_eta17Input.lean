-- Prove2me | solution 1 for InverseZeroSum.Candidate3.eta17Input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:29.638873+00:00
-- url     : https://prove2.me/submissions/a8db32f9-8c80-4372-9e09-cf0397adc964

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_three_nsmul_G
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_capT_card_le_nine
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution : Eta17Input := by
  classical
  intro R
  by_contra hcontra
  have hFree : ShortFree R := by
    intro I hI
    exact hcontra ⟨I, hI⟩
  let f : Fin 17 → F3T :=
    fun i => finiteModelEquiv (R i : G)
  let support : Finset F3T :=
    (Finset.univ : Finset (Fin 17)).image f

  have hZeroNot : (0 : F3T) ∉ support := by
    intro h0
    have h0' :
        (0 : F3T) ∈ (Finset.univ : Finset (Fin 17)).image f := by
      simpa [support] using h0
    obtain ⟨i, _hi, hfi⟩ := Finset.mem_image.mp h0'
    have hG0 : (R i : G) = 0 := by
      apply finiteModelEquiv.injective
      simpa [f] using hfi
    exact (R i).property hG0

  have hCap : IsCapT support := by
    intro x hx y hy z hz hxy hxz hyz hxyz
    have hx' : x ∈ (Finset.univ : Finset (Fin 17)).image f := by
      simpa [support] using hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx'
    have hy' : y ∈ (Finset.univ : Finset (Fin 17)).image f := by
      simpa [support] using hy
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy'
    have hz' : z ∈ (Finset.univ : Finset (Fin 17)).image f := by
      simpa [support] using hz
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hz'
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hxy rfl
    have hik : i ≠ k := by
      intro hik
      subst k
      exact hxz rfl
    have hjk : j ≠ k := by
      intro hjk
      subst k
      exact hyz rfl
    have hGsum : (R i : G) + (R j : G) + (R k : G) = 0 := by
      apply finiteModelEquiv.injective
      simpa [f] using hxyz
    have hIcard : ({i, j, k} : Finset (Fin 17)).card = 3 := by
      simp [hij, hik, hjk]
    have hpos : posSum R ({i, j, k} : Finset (Fin 17)) = 0 := by
      simpa [posSum, hij, hik, hjk, add_assoc] using hGsum
    exact (hFree _) ⟨Finset.card_pos.mp (by omega), by omega, hpos⟩

  have hNoPair :
      ∀ x ∈ support, ∀ y ∈ support, x + y ≠ 0 := by
    have hSelf :
        ∀ x : F3T, x ≠ 0 → x + x ≠ 0 := by
      decide
    intro x hx y hy hxy
    have hx' : x ∈ (Finset.univ : Finset (Fin 17)).image f := by
      simpa [support] using hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx'
    have hy' : y ∈ (Finset.univ : Finset (Fin 17)).image f := by
      simpa [support] using hy
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy'
    have hfi0 : f i ≠ 0 := by
      intro h0
      have hz : (0 : F3T) ∈ support := by
        change (0 : F3T) ∈ (Finset.univ : Finset (Fin 17)).image f
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h0⟩
      exact hZeroNot hz
    have hij : i ≠ j := by
      intro hij
      subst j
      exact (hSelf (f i) hfi0) hxy
    have hGsum : (R i : G) + (R j : G) = 0 := by
      apply finiteModelEquiv.injective
      simpa [f] using hxy
    have hIcard : ({i, j} : Finset (Fin 17)).card = 2 := by
      simp [hij]
    have hpos : posSum R ({i, j} : Finset (Fin 17)) = 0 := by
      simpa [posSum, hij, add_comm] using hGsum
    exact (hFree _) ⟨Finset.card_pos.mp (by omega), by omega, hpos⟩

  let cap0 : Finset F3T := insert 0 support
  have hCap0 : IsCapT cap0 := by
    intro a ha b hb c hc hab hac hbc hsum
    simp only [cap0, Finset.mem_insert] at ha hb hc
    rcases ha with rfl | ha
    · have hbS : b ∈ support := by
        rcases hb with hb0 | hbS
        · exact False.elim (hab hb0.symm)
        · exact hbS
      have hcS : c ∈ support := by
        rcases hc with hc0 | hcS
        · exact False.elim (hac hc0.symm)
        · exact hcS
      apply hNoPair b hbS c hcS
      simpa using hsum
    · rcases hb with rfl | hb
      · have hcS : c ∈ support := by
          rcases hc with hc0 | hcS
          · exact False.elim (hbc hc0.symm)
          · exact hcS
        apply hNoPair a ha c hcS
        simpa using hsum
      · rcases hc with rfl | hc
        · apply hNoPair a ha b hb
          simpa [add_assoc] using hsum
        · exact hCap a ha b hb c hc hab hac hbc hsum

  have hCap0Card : cap0.card ≤ 9 :=
    capT_card_le_nine hCap0
  have hSupportLe : support.card ≤ 8 := by
    have hCard : cap0.card = support.card + 1 := by
      simp [cap0, hZeroNot, Nat.add_comm]
    rw [hCard] at hCap0Card
    omega

  have hFiber :
      ∀ x ∈ support,
        ((Finset.univ : Finset (Fin 17)).filter (fun i => f i = x)).card ≤ 2 := by
    intro x _hx
    let fiber : Finset (Fin 17) :=
      (Finset.univ : Finset (Fin 17)).filter (fun i => f i = x)
    have hfiber_eq :
        fiber =
          (Finset.univ : Finset (Fin 17)).filter (fun i => f i = x) := rfl
    rw [← hfiber_eq]
    by_contra hle
    have h3 : 3 ≤ fiber.card := by omega
    obtain ⟨I, hI_sub, hIcard⟩ :=
      Finset.exists_subset_card_eq (s := fiber) (n := 3) h3
    have hconst :
        ∀ i ∈ I, (R i : G) = finiteModelEquiv.symm x := by
      intro i hi
      have hiFiber : i ∈ fiber := hI_sub hi
      have hfix : f i = x := (Finset.mem_filter.mp hiFiber).2
      have hback := congrArg finiteModelEquiv.symm hfix
      simpa [f] using hback
    have hsum : posSum R I = 0 := by
      unfold posSum
      calc
        (∑ i ∈ I, (R i : G)) =
            ∑ _i ∈ I, finiteModelEquiv.symm x := by
              exact Finset.sum_congr rfl (fun i hi => hconst i hi)
        _ = I.card • finiteModelEquiv.symm x := by simp
        _ = 0 := by
          rw [hIcard]
          simpa using
            three_nsmul_G (finiteModelEquiv.symm x)
    exact (hFree I) ⟨Finset.card_pos.mp (by omega), by omega, hsum⟩

  have hMaps :
      ∀ i ∈ (Finset.univ : Finset (Fin 17)), f i ∈ support := by
    intro i hi
    change f i ∈ (Finset.univ : Finset (Fin 17)).image f
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hBound :=
    Finset.card_le_mul_card_image_of_maps_to hMaps 2 hFiber
  have hBound' : 17 ≤ 2 * support.card := by
    simpa using hBound
  omega
end InverseZeroSum.Candidate3
