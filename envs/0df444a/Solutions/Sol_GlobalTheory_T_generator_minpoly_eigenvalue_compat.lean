-- Prove2me | solution 1 for GlobalTheory.T.generator_minpoly_eigenvalue_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:21:47.68355+00:00
-- url     : https://prove2.me/submissions/aba0925f-1d21-45b5-bbc7-62c867ade799

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeneratorMinpolyEigenvalueCompat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeneratorMinpolyEigenvalueCompatStatement
import Theorems.Thm_GlobalTheory_spanEquivariant_minpoly_eigen_transfer


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (V : Type 1) [AddCommGroup V] [Module ℂ V] (P : E →+ V),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (b : E) (T : Module.End ℂ V), (∀ x, T (P x) = P (b * x)) →
    IntermediateField.adjoin ℚ {b} = ⊤ →
    Polynomial.aeval T ((minpoly ℚ b).map (algebraMap ℚ ℂ)) = 0 ∧
    ∀ (σ : E →+* ℂ) (a : E) (S : Module.End ℂ V), (∀ x, S (P x) = P (a * x)) → ∀ y, T y = σ b • y → S y = σ a • y := by
  first | exact @GlobalTheory.spanEquivariant_minpoly_eigen_transfer | exact GlobalTheory.spanEquivariant_minpoly_eigen_transfer | (intros; apply GlobalTheory.spanEquivariant_minpoly_eigen_transfer <;> assumption)
end _root_.GlobalTheory.T
