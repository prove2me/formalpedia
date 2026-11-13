-- Prove2me | solution 1 for HararySachs.Hyper.charPoly_coeff_top
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T18:47:20.557264+00:00
-- url     : https://prove2.me/submissions/f74f2da7-6607-421b-bfd2-ec16c1d490a0

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Theorems.Thm_MvResultant_isWeightedHomogeneous_block
import Theorems.Thm_MvResultant_blockDegree_le
import Theorems.Thm_MvResultant_blockDegree_ge
import Theorems.Thm_HararySachs_Hyper_charPoly_coeff_of_blockHomogeneous

open HararySachs.Hyper

theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = k)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) :
    (charPoly (k := k) E res).coeff (n * (k - 1) ^ (n - 1)) = 1 := by
  have hD : ∀ j : Fin n, 1 ≤ (fun _ : Fin n => k - 1) j := fun _ => by simp only; omega
  -- each block degree of the resultant is exactly `(k - 1) ^ (n - 1)`
  have hδ : ∀ i : Fin n, res.IsWeightedHomogeneous
      (fun v : ResVar n (fun _ => k - 1) => if v.1 = i then 1 else 0) ((k - 1) ^ (n - 1)) := by
    intro i
    obtain ⟨δ, h⟩ := MvResultant.isWeightedHomogeneous_block res hres i
    have h1 := MvResultant.blockDegree_le hD res hres i δ h
    have h2 := MvResultant.blockDegree_ge hD res hres i δ h
    have hp : ∏ j ∈ Finset.univ.erase i, (fun _ : Fin n => k - 1) j = (k - 1) ^ (n - 1) := by
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    rw [hp] at h1 h2
    rwa [show δ = (k - 1) ^ (n - 1) by omega] at h
  -- top coefficient from block-homogeneity and the normalisation of the resultant
  exact charPoly_coeff_of_blockHomogeneous n k E res _ hδ hres.2.1
