-- Prove2me | solution 1 for GlobalTheory.T.matrixFamilyBilateralSubstitution_scalar_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:44.868235+00:00
-- url     : https://prove2.me/submissions/c851de90-59fa-4866-b444-152476f39010

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionScalarMonomial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionScalarMonomialStatement
import Theorems.Thm_GlobalTheory_CompactHowe_substF_scalar_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ), GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  first | exact @GlobalTheory.CompactHowe.substF_scalar_monomial | exact GlobalTheory.CompactHowe.substF_scalar_monomial | (intros; apply GlobalTheory.CompactHowe.substF_scalar_monomial <;> assumption)
end _root_.GlobalTheory.T
