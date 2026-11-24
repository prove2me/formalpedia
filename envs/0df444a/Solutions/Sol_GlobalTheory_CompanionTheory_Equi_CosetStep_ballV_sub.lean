-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.ballV_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:25.663288+00:00
-- url     : https://prove2.me/submissions/6594faa6-3b88-4183-81db-c7d6d2b15e75

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
    (ha : a ∈ ballV v k) (hb : b ∈ ballV v k) : a - b ∈ ballV v k := by
  show Valued.v (a - b) ≤ _
  exact (Valuation.map_sub _ a b).trans (max_le ha hb)
end GlobalTheory.CompanionTheory.Equi.CosetStep
