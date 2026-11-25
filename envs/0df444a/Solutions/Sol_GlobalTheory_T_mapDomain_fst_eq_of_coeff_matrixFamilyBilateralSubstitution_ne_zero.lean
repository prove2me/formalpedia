-- Prove2me | solution 1 for GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:39.364082+00:00
-- url     : https://prove2.me/submissions/e81d3867-c485-4246-a83a-cdc69b68653f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapDomainFstEqOfCoeffMatrixFamilyBilateralSubstiStatement
import Theorems.Thm_GlobalTheory_CompactHowe_mapDomain_fst_eq_of_coeff_substF_ne_zero


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
theorem _root_.solution : ∀ {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ), MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) ≠ 0 → Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  first | exact @GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | (intros; apply GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero <;> assumption)
end _root_.GlobalTheory.T
