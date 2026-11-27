-- Prove2me | solution 1 for MohP3.indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:17.96905+00:00
-- url     : https://prove2.me/submissions/4df18108-149b-406c-bcc7-0fa42d0764b2

module
public import Mathlib
public import Definitions.Def_MohP3_Independence
public import Theorems.Thm_MohP3_comp_X8_ne_zero
public import Theorems.Thm_MohP3_dvd8_ntd
public import Theorems.Thm_MohP3_vv_ne_zero
public import Theorems.Thm_MohP3_ntd_vv
public import Theorems.Thm_MohP3_oo_mod_inj

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3
namespace MohP3
theorem _root_.solution (p : Fin 8 → ℚ[X]) (hs : ∑ i, (p i).comp (X^8) * vv i = 0) :
    ∀ i, p i = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hcon
  set w : Fin 8 → ℚ[X] := fun i => (p i).comp (X^8) * vv i with hw
  set S : Finset (Fin 8) := Finset.univ.filter (fun i => p i ≠ 0) with hSdef
  have hS : S.Nonempty := ⟨i0, by simp [hSdef, hi0]⟩
  have hwne : ∀ i ∈ S, w i ≠ 0 := by
    intro i hi
    simp [hSdef] at hi
    exact mul_ne_zero (comp_X8_ne_zero hi) (vv_ne_zero i)
  have hntd : ∀ i ∈ S, (w i).natTrailingDegree % 8 = oo i % 8 := by
    intro i hi
    simp [hSdef] at hi
    rw [hw]
    simp only
    rw [Polynomial.natTrailingDegree_mul (comp_X8_ne_zero hi) (vv_ne_zero i), ntd_vv]
    obtain ⟨k, hk⟩ := dvd8_ntd hi
    omega
  obtain ⟨m, hmS, hmin⟩ := S.exists_min_image (fun i => (w i).natTrailingDegree) hS
  set d := (w m).natTrailingDegree with hd
  have key : (∑ i, w i).coeff d = (w m).coeff d := by
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single m]
    · intro b _ hbm
      by_cases hb : b ∈ S
      · have h1 : d ≤ (w b).natTrailingDegree := hmin b hb
        have h2 : (w b).natTrailingDegree ≠ d := fun he =>
          hbm (oo_mod_inj (by rw [← hntd b hb, ← hntd m hmS, he]))
        exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (lt_of_le_of_ne h1 (Ne.symm h2))
      · have : p b = 0 := by simpa [hSdef] using hb
        simp [hw, this]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  rw [hs] at key
  simp at key
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr (hwne m hmS)) key.symm
end MohP3
