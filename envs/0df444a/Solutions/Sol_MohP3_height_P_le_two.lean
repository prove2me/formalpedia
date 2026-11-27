-- Prove2me | solution 1 for MohP3.height_P_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:33:35.40786+00:00
-- url     : https://prove2.me/submissions/4a1170f6-af25-439b-9a47-f0506f1b1e69

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_P_mem_minimalPrimes_Q
public import Theorems.Thm_MohP3_iota_C
public import Theorems.Thm_MohP3_iota_X
public import Theorems.Thm_MohP3_iota_ofNat
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



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
open scoped Classical
namespace MohP3
theorem _root_.solution : P.height ≤ 2 := by
  have hQ : Q = Ideal.span ((({H1, H2} : Finset R) : Finset R) : Set R) := by
    simp [Q]
  have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    (p := P) (s := ({H1, H2} : Finset R)) (by rw [← hQ]; exact P_mem_minimalPrimes_Q)
  refine h.trans ?_
  have : ({H1, H2} : Finset R).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  exact_mod_cast this
end MohP3
