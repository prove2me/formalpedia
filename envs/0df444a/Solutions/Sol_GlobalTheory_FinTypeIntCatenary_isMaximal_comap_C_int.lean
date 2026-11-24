-- Prove2me | solution 1 for GlobalTheory.FinTypeIntCatenary.isMaximal_comap_C_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:52.035632+00:00
-- url     : https://prove2.me/submissions/ae4d5744-22f8-47eb-a650-2980db0fcce2

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeightMaximalLePrimeAddDim
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_isJacobsonRing_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinTypeIntCatenary
open ReciprocityTheory.CA
namespace GlobalTheory.FinTypeIntCatenary
theorem _root_.solution (N : ℕ) (𝔑 : Ideal (MvPolynomial (Fin N) ℤ)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : ℤ →+* MvPolynomial (Fin N) ℤ)).IsMaximal := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have hi := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑
  letI := Ideal.Quotient.field 𝔑
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi
    (⊥ : Ideal (MvPolynomial (Fin N) ℤ ⧸ 𝔑))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this
end GlobalTheory.FinTypeIntCatenary
