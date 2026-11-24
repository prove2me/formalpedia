-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.mem_pow_of_val_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:42.08195+00:00
-- url     : https://prove2.me/submissions/c1b2a0a8-b7c9-48bb-8bfc-32ee08f126cc

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {y : 𝓞 F} {k : ℕ}
    (hy : v.valuation F (algebraMap (𝓞 F) F y) ≤ WithZero.exp (-(k : ℤ))) :
    y ∈ v.asIdeal ^ k := by
  rw [HeightOneSpectrum.valuation_of_algebraMap] at hy
  exact (v.intValuation_le_pow_iff_mem y k).1 hy
end GlobalTheory.CompanionTheory.Equi.CosetStep
