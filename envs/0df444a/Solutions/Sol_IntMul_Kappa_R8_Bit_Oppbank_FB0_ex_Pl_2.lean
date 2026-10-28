-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.FB0_ex_Pl
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:40:33.838638+00:00
-- url     : https://prove2.me/submissions/9fa54cc0-4889-46ee-b8a6-60adc99a85d6

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_flagBasis
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped Kronecker
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.ProjB
open IntMul.Kappa.R8.Bit.Oppbank.NetFB

theorem solution :
    ∃ (S : Matrix (Fin 529) Pr23 ℚ) (Sinv : Matrix Pr23 (Fin 529) ℚ),
      S * Sinv = 1 ∧ Sinv * S = 1 ∧
        (∀ p ∈ Lab0,
          AuxE (h := 19) (S * ((1 : M23) ⊗ₖ (1 - vecMulVec p.1 p.2)) * Sinv) ∧
            AuxE (h := 19) (S * ((1 - vecMulVec p.1 p.2) ⊗ₖ (1 : M23)) * Sinv)) ∧
        (∀ p ∈ Lab0, ∀ A ∈ Pis0Pl,
          SideE (h := 19) (S * (A ⊗ₖ vecMulVec p.1 p.2) * Sinv) A.rank ∧
            SideE (h := 19) (S * (vecMulVec p.1 p.2 ⊗ₖ A) * Sinv) A.rank) ∧
        (∀ p₁ ∈ Lab0, ∀ p₂ ∈ Lab0,
          DataE (h := 19)
            (S * ((1 - vecMulVec p₁.1 p₁.2) ⊗ₖ (1 - vecMulVec p₂.1 p₂.2)) * Sinv)) :=
  flagBasis Lab0 hLab0 Pis0Pl hPis0Pl
