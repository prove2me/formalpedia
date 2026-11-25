-- Prove2me | solution 1 for GlobalTheory.T.wQ_characterization_and_mul_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:00.545068+00:00
-- url     : https://prove2.me/submissions/7a4bb2c6-8d42-483a-8143-ffc72b608e16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactorStatement
import Theorems.Thm_GlobalTheory_Ex_SymLift_normalising_factor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ), Odd k → ∀ p p' : N.QT k, (∀ w : Oˣ, w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧ w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b)) ∧ N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') ∧ N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p := by
  first | exact @GlobalTheory.Ex.SymLift.normalising_factor | exact GlobalTheory.Ex.SymLift.normalising_factor | (intros; apply GlobalTheory.Ex.SymLift.normalising_factor <;> assumption)
end _root_.GlobalTheory.T
