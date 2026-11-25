-- Prove2me | solution 1 for GlobalTheory.T.hermitianTheta_summable_and_determines_testFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:51.10523+00:00
-- url     : https://prove2.me/submissions/a1fbbca9-ed99-44fc-b0ae-16cd4a870b5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Theorems.Thm_GlobalTheory_SW_thH_summable_and_inj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → ∀ Z ∈ Hn Ψ N, (∀ z z', Summable fun x => ‖φ x * cexp (2 * π * I * expo Ψ x Z z z')‖) ∧ ∀ ψ, IsSB ψ → (∀ z z', thH Ψ φ Z z z' = thH Ψ ψ Z z z') → φ = ψ := by
  first | exact @GlobalTheory.SW.thH_summable_and_inj | exact GlobalTheory.SW.thH_summable_and_inj | (intros; apply GlobalTheory.SW.thH_summable_and_inj <;> assumption)
end _root_.GlobalTheory.T
