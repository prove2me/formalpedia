-- Prove2me | solution 1 for MohP3.arithRank_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:29.506261+00:00
-- url     : https://prove2.me/submissions/0a58665f-571e-4827-bca0-aefa41e7f935

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_sigma_x
public import Theorems.Thm_MohP3_sigma_y
public import Theorems.Thm_MohP3_sigma_z
public import Theorems.Thm_MohP3_height_P
public import Theorems.Thm_MohP3_P_isPrime
public import Theorems.Thm_MohP3_P_radical
public import Theorems.Thm_MohP3_arithRank_le
public import Theorems.Thm_MohP3_height_le_arithRank
public import Theorems.Thm_MohP3_iota_C
public import Theorems.Thm_MohP3_iota_X
public import Theorems.Thm_MohP3_iota_ofNat
public import Theorems.Thm_MohP3_radical_Q
public import Theorems.Thm_MohP3_rho_C
public import Theorems.Thm_MohP3_rho_x
public import Theorems.Thm_MohP3_rho_y
public import Theorems.Thm_MohP3_rho_z
attribute [local simp] MohP3.iota_C
attribute [local simp] MohP3.iota_X
attribute [local simp] MohP3.iota_ofNat
attribute [local simp] MohP3.rho_C
attribute [local simp] MohP3.rho_x
attribute [local simp] MohP3.rho_y
attribute [local simp] MohP3.rho_z


attribute [local simp] MohP3.sigma_x
attribute [local simp] MohP3.sigma_y
attribute [local simp] MohP3.sigma_z

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
open scoped Classical
namespace MohP3
theorem _root_.solution : arithRank P = 2 := by
  refine le_antisymm ?_ ?_
  · refine le_trans (arithRank_le ({H1, H2} : Finset R) ?_) ?_
    · have hQ : Ideal.span ((({H1, H2} : Finset R) : Finset R) : Set R) = Q := by
        simp [Q]
      rw [hQ, radical_Q, P_radical]
    · have : ({H1, H2} : Finset R).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      exact_mod_cast this
  · calc (2 : ℕ∞) = P.height := height_P.symm
      _ ≤ arithRank P := height_le_arithRank P P_isPrime
end MohP3
