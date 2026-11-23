-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.exists_mem_pow_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:05.12324+00:00
-- url     : https://prove2.me/submissions/44d00b0e-6a81-492b-8576-67a6c895854b

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
theorem _root_.solution {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (k : ℕ) :
    ∃ e ∈ v.asIdeal ^ k, e ∉ w.asIdeal := by
  by_contra h
  push_neg at h
  have hle : v.asIdeal ^ k ≤ w.asIdeal := fun e he => h e he
  have hvw : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hle
  exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hvw).symm)
end GlobalTheory.CompanionTheory.Equi.CosetStep
