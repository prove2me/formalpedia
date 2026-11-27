-- Prove2me | solution 1 for MohP3.FormalLocal.two_le_height_Pk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:42:09.76724+00:00
-- url     : https://prove2.me/submissions/e328a81a-36c6-4c0e-8140-b6c5393cc9d9

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_Pk_isPrime
public import Theorems.Thm_MohP3_FormalLocal_Psurfk_isPrime
public import Theorems.Thm_MohP3_FormalLocal_Psurfk_lt_Pk
public import Theorems.Thm_MohP3_FormalLocal_bot_lt_Psurfk

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : 2 ≤ (Pk k).height := by
  haveI := Pk_isPrime k
  haveI := Psurfk_isPrime k
  haveI : (⊥ : Ideal (Sk k)).IsPrime := Ideal.isPrime_bot
  have h2 : (Psurfk k).height + 1 ≤ (Pk k).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime (Psurfk_lt_Pk k)
  have h1 : (⊥ : Ideal (Sk k)).height + 1 ≤ (Psurfk k).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_Psurfk k)
  have hbot : (⊥ : Ideal (Sk k)).height = 0 := Ideal.height_bot
  calc (2 : ℕ∞) = (⊥ : Ideal (Sk k)).height + 1 + 1 := by rw [hbot]; rfl
    _ ≤ (Psurfk k).height + 1 := by gcongr
    _ ≤ (Pk k).height := h2
end MohP3.FormalLocal
