-- Prove2me | solution 1 for GlobalTheory.CuspGL.LogDeriv.pow_mul_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:45:25.4638+00:00
-- url     : https://prove2.me/submissions/f6d97fed-c1e0-4ec1-9d40-c0a84712d9ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveMulEqVonMangoldtConvolution
import Theorems.Thm_GlobalTheory_CuspGL_LogDeriv_conv_eq_sum
import Theorems.Thm_GlobalTheory_CuspGL_conv_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.LogDeriv
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL.LogDeriv
theorem _root_.solution (q : ℂ) (a b : F[X] → ℂ) {P : F[X]} (hP : P.Monic) :
    q ^ P.natDegree * conv a b P =
      conv (fun D => q ^ D.natDegree * a D) (fun D => q ^ D.natDegree * b D) P := by
  rw [conv_eq_sum _ _ hP, conv_eq_sum _ _ hP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  rw [← h3, h1.natDegree_mul h2, pow_add]
  ring
end GlobalTheory.CuspGL.LogDeriv
