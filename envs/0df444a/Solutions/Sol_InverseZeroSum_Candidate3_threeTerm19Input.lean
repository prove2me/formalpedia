-- Prove2me | solution 1 for InverseZeroSum.Candidate3.threeTerm19Input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:22.827664+00:00
-- url     : https://prove2.me/submissions/31388bed-dfdf-4f73-a565-b7920b49be68

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
theorem _root_.solution : ThreeTerm19Input := by
  classical
  intro R
  by_contra hcontra
  have hNo :
      ∀ I : Finset (Fin 19), I.card = 3 → posSum R I ≠ 0 := by
    intro I hIcard hzero
    exact hcontra ⟨I, hIcard, hzero⟩
  let f : Fin 19 → F3T :=
    fun i => finiteModelEquiv (R i : G)
  let support : Finset F3T :=
    (Finset.univ : Finset (Fin 19)).image f
  have hCap : IsCapT support := by
    intro x hx y hy z hz hxy hxz hyz hxyz
    have hx' : x ∈ (Finset.univ : Finset (Fin 19)).image f := by
      simpa [support] using hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx'
    have hy' : y ∈ (Finset.univ : Finset (Fin 19)).image f := by
      simpa [support] using hy
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy'
    have hz' : z ∈ (Finset.univ : Finset (Fin 19)).image f := by
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
    have hIcard : ({i, j, k} : Finset (Fin 19)).card = 3 := by
      simp [hij, hik, hjk]
    have hpos : posSum R ({i, j, k} : Finset (Fin 19)) = 0 := by
      simpa [posSum, hij, hik, hjk, add_assoc] using hGsum
    exact (hNo _ hIcard) hpos
  have hFiber :
      ∀ x ∈ support,
        ((Finset.univ : Finset (Fin 19)).filter (fun i => f i = x)).card ≤ 2 := by
    intro x _hx
    let fiber : Finset (Fin 19) :=
      (Finset.univ : Finset (Fin 19)).filter (fun i => f i = x)
    have hfiber_eq :
        fiber =
          (Finset.univ : Finset (Fin 19)).filter (fun i => f i = x) := rfl
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
    exact (hNo I hIcard) hsum
  have hMaps :
      ∀ i ∈ (Finset.univ : Finset (Fin 19)), f i ∈ support := by
    intro i hi
    change f i ∈ (Finset.univ : Finset (Fin 19)).image f
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hBound :=
    Finset.card_le_mul_card_image_of_maps_to hMaps 2 hFiber
  have hBound' : 19 ≤ 2 * support.card := by
    simpa using hBound
  have hSupport10 : 10 ≤ support.card := by omega
  have hSupport9 : support.card ≤ 9 := capT_card_le_nine hCap
  omega
end InverseZeroSum.Candidate3
