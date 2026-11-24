-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:29.538245+00:00
-- url     : https://prove2.me/submissions/1041241b-51fc-4737-b4c0-09f66f425576

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
theorem _root_.solution {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a : F}
    (ha : LocMem I w a) : LocMem I w (-a) := by
  obtain ⟨s, hs, y, hy, hsy⟩ := ha
  refine ⟨s, hs, -y, I.neg_mem hy, ?_⟩
  push_cast
  rw [mul_neg, hsy]
end GlobalTheory.CompanionTheory.Equi.CosetStep
