-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:46.475208+00:00
-- url     : https://prove2.me/submissions/7e033c62-29af-417d-a9d7-ea55f919734b

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
theorem _root_.solution {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : LocMem I w a) (hb : LocMem I w b) : LocMem I w (a + b) := by
  obtain ⟨s, hs, y, hy, hsy⟩ := ha
  obtain ⟨t, ht, z, hz, htz⟩ := hb
  refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, t * y + s * z,
    I.add_mem (I.mul_mem_left _ hy) (I.mul_mem_left _ hz), ?_⟩
  push_cast
  linear_combination (t : F) * hsy + (s : F) * htz
end GlobalTheory.CompanionTheory.Equi.CosetStep
