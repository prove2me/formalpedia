-- Prove2me | solution 1 for GlobalTheory.idealHilbertPoly_sup_of_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:07.116978+00:00
-- url     : https://prove2.me/submissions/50273799-b760-4ce5-b8f1-f0a5098fecd2

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_idealHilbertPoly_eq_sup_add_colon

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
variable [Finite ι]
namespace GlobalTheory
theorem _root_.solution {P : Ideal (MvPolynomial ι k)} [hP : P.IsPrime]
    (hI : P.IsHomogeneous (homogeneousSubmodule ι k)) {f : MvPolynomial ι k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hfP : f ∉ P) :
    idealHilbertPoly (P ⊔ Ideal.span {f}) = idealHilbertPoly P -
      (idealHilbertPoly P).comp (Polynomial.X - Polynomial.C (d : ℚ)) := by
  have h := idealHilbertPoly_eq_sup_add_colon hI hf
  have e : Submodule.colon P {f} = P := by
    ext g
    rw [Submodule.mem_colon_singleton, smul_eq_mul, hP.mul_mem_iff_mem_or_mem]
    simp [hfP]
  rw [e] at h
  linear_combination -h
end GlobalTheory
