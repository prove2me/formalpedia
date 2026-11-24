-- Prove2me | solution 1 for GlobalTheory.SubstCoeff.continuous_coeff_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:06:15.031816+00:00
-- url     : https://prove2.me/submissions/2520fe48-581f-4ca2-8beb-6a08508483cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Theorems.Thm_GlobalTheory_SubstCoeff_continuous_coeff_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.SubstCoeff
variable {σ : Type}
namespace GlobalTheory.SubstCoeff
theorem _root_.solution {Y κ : Type} [TopologicalSpace Y] (s : Finset κ) (f : κ → Y → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, Continuous fun y => coeff m (f q y)) (m : σ →₀ ℕ) :
    Continuous fun y => coeff m (∏ q ∈ s, f q y) := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty =>
    simp only [Finset.prod_empty, coeff_one]
    exact continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact continuous_coeff_mul _ _ (hf a (Finset.mem_insert_self a s))
      (fun m' => ih (fun q hq => hf q (Finset.mem_insert_of_mem hq)) m') m
end GlobalTheory.SubstCoeff
