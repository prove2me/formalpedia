-- Prove2me | solution 1 for GlobalTheory.T.doubledRowTestFunction_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:15:19.584802+00:00
-- url     : https://prove2.me/submissions/00f47f3c-0128-4330-a807-0e87d8306c76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionPropertiesStatement
import Theorems.Thm_GlobalTheory_Phase_Doubling_doubling


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n g : ℕ) (φ : Matrix (Fin n) (Fin g) ℚ → ℂ), (PV φ → PV (dup φ)) ∧ (φ ≠ 0 → dup φ ≠ 0) ∧ (IsSB φ → IsSB (dup φ)) ∧ (∀ u : ℂ, dup (u • φ) = u ^ 2 • dup φ) ∧ ∀ τ ∈ Siegel (Fin g), blk n τ ∈ Siegel (Fin n × Fin g) ∧ (IsSB φ → ∀ ζ : Fin 2 → Fin n × Fin g → ℂ, thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i))) ∧ ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  first | exact @GlobalTheory.Phase.Doubling.doubling | exact GlobalTheory.Phase.Doubling.doubling | (intros; apply GlobalTheory.Phase.Doubling.doubling <;> assumption)
end _root_.GlobalTheory.T
