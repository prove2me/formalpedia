-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dblock.CentreBlocks.aeval_sub_aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:51.979077+00:00
-- url     : https://prove2.me/submissions/a82f9f9f-fcc3-4796-95c0-b4eeb7e0f101

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdeal
import Theorems.Thm_GlobalTheory_CompanionTheory_Dblock_CentreBlocks_pow_sub_pow_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dblock GlobalTheory.CompanionTheory.Dblock.CentreBlocks
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks
theorem _root_.solution (β D : Module.End ℂ V) (Wn I : Submodule ℂ V)
    (hβ : ∀ F ∈ I, β F ∈ I) (hD : ∀ F ∈ Wn, D F ∈ Wn) (hDβ : ∀ F ∈ Wn, D F - β F ∈ I)
    (p : ℂ[X]) : ∀ F ∈ Wn, (aeval β p) F - (aeval D p) F ∈ I := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro F hF
    have := I.add_mem (hp F hF) (hq F hF)
    simp only [map_add, LinearMap.add_apply]
    convert this using 1
    abel
  | monomial n c =>
    intro F hF
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [← smul_sub]
    exact I.smul_mem c (pow_sub_pow_mem β D Wn I hβ hD hDβ n F hF)
end GlobalTheory.CompanionTheory.Dblock.CentreBlocks
