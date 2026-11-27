-- Prove2me | solution 1 for MohP3.two_le_height_Ppoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:29.404811+00:00
-- url     : https://prove2.me/submissions/661d445e-5aca-47f2-9397-3417d69b3517

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_PsurfK_isPrime
public import Theorems.Thm_MohP3_PsurfK_lt_Ppoly
public import Theorems.Thm_MohP3_bot_lt_PsurfK
public import Theorems.Thm_MohP3_Ppoly_isPrime


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution : 2 ≤ (Ppoly k).height := by
  haveI := Ppoly_isPrime k
  haveI := PsurfK_isPrime k
  haveI : (⊥ : Ideal (Rk k)).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal (Rk k)).height + 1 ≤ (PsurfK k).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_PsurfK k)
  have h2 : (PsurfK k).height + 1 ≤ (Ppoly k).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime (PsurfK_lt_Ppoly k)
  have hbot : (⊥ : Ideal (Rk k)).height = 0 := Ideal.height_bot
  calc (2 : ℕ∞) = (⊥ : Ideal (Rk k)).height + 1 + 1 := by rw [hbot]; rfl
    _ ≤ (PsurfK k).height + 1 := by gcongr
    _ ≤ (Ppoly k).height := h2
end MohP3
