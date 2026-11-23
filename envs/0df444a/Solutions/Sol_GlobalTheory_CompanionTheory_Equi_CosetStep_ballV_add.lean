-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.ballV_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:45.7728+00:00
-- url     : https://prove2.me/submissions/2168ef7c-4fe3-403e-8d28-13044ee83c5e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetStep
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Equi.CosetStep
theorem _root_.solution {v : HeightOneSpectrum (𝓞 F)} {k : ℕ} {a b : Fv F v}
    (ha : a ∈ ballV v k) (hb : b ∈ ballV v k) : a + b ∈ ballV v k := by
  show Valued.v (a + b) ≤ _
  exact (Valuation.map_add _ a b).trans (max_le ha hb)
end GlobalTheory.CompanionTheory.Equi.CosetStep
