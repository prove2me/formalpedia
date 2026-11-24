-- Prove2me | solution 1 for GlobalTheory.T.exists_formal_branches_of_separable_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:48.234192+00:00
-- url     : https://prove2.me/submissions/fbe491f0-69f7-4223-ac28-14e77cfc1ed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReductionStatement
import Theorems.Thm_GlobalTheory_branches_of_unramified_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℂ)) (c : Fin D → ℂ), P.Monic → (P.map (MvPolynomial.eval c)).Separable → ∃ (n : ℕ) (φ : Fin n → (AdjoinRoot P →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)), (∀ u, (∀ j, φ j u = 0) → u = 0) ∧ ∀ j i, φ j (AdjoinRoot.of P (MvPolynomial.X i)) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  first | exact @GlobalTheory.branches_of_unramified_point | exact GlobalTheory.branches_of_unramified_point | (intros; apply GlobalTheory.branches_of_unramified_point <;> assumption)
end _root_.GlobalTheory.T
