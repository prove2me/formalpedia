-- Prove2me | solution 1 for GlobalTheory.T.partialZeta_totallyReal_at_most_simple_pole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:31:50.143035+00:00
-- url     : https://prove2.me/submissions/2ad3478e-4a13-47eb-8d17-f425431ec6c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialZetaTotallyRealAtMostSimplePole
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialZetaTotallyRealAtMostSimplePoleStatement
import Theorems.Thm_GlobalTheory_ZetaPole_zeta_simple_pole


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (C C' : ClassGroup (NumberField.RingOfIntegers F)) (Z Z' : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C' Z' → (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)) → ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ ∀ s : ℂ, s ≠ 1 → Z s = R s / (s - 1) := by
  first | exact @GlobalTheory.ZetaPole.zeta_simple_pole | exact GlobalTheory.ZetaPole.zeta_simple_pole | (intros; apply GlobalTheory.ZetaPole.zeta_simple_pole <;> assumption)
end _root_.GlobalTheory.T
