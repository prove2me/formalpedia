-- Prove2me | solution 1 for MohP3.two_le_height_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:36.420823+00:00
-- url     : https://prove2.me/submissions/4e56c7d4-23c0-4d5e-9a74-0ea190cbcce7

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_Psurf_isPrime
public import Theorems.Thm_MohP3_Psurf_lt_P
public import Theorems.Thm_MohP3_bot_lt_Psurf
public import Theorems.Thm_MohP3_P_isPrime


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : 2 ≤ P.height := by
  haveI := P_isPrime
  haveI := Psurf_isPrime
  haveI : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal R).height + 1 ≤ Psurf.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime bot_lt_Psurf
  have h2 : Psurf.height + 1 ≤ P.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime Psurf_lt_P
  have hbot : (⊥ : Ideal R).height = 0 := Ideal.height_bot
  calc (2 : ℕ∞) = (⊥ : Ideal R).height + 1 + 1 := by rw [hbot]; rfl
    _ ≤ Psurf.height + 1 := by gcongr
    _ ≤ P.height := h2
end MohP3
