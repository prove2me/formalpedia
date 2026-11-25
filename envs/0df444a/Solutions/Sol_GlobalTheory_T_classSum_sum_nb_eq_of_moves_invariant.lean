-- Prove2me | solution 1 for GlobalTheory.T.classSum_sum_nb_eq_of_moves_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:34:04.135135+00:00
-- url     : https://prove2.me/submissions/0334fa2d-9bc8-4347-b07b-98ef99912dec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNbStatement
import Theorems.Thm_GlobalTheory_SW_classSum_nb


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
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n M q : ℕ) (P : Ideal (𝓞 E)), 0 < M → GoodPrime M q P → ∀ f : Lt E n → ℂ, (∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' → f Λ' = f Λ) → ((q : ℂ) - 1) * classSum M (fun Λ => ∑ᶠ Λ' ∈ Nb M P Λ, f Λ') = ((q : ℂ) ^ n - 1) * classSum M f := by
  first | exact @GlobalTheory.SW.classSum_nb | exact GlobalTheory.SW.classSum_nb | (intros; apply GlobalTheory.SW.classSum_nb <;> assumption)
end _root_.GlobalTheory.T
