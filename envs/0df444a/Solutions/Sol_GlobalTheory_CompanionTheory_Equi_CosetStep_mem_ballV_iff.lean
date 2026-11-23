-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.mem_ballV_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:26.35604+00:00
-- url     : https://prove2.me/submissions/fdb71733-25d3-495d-8b1c-842ea8b9b358

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (t : F) :
    algebraMap F (Fv F v) t ∈ ballV v k ↔ v.valuation F t ≤ WithZero.exp (-(k : ℤ)) := by
  show Valued.v (algebraMap F (Fv F v) t) ≤ _ ↔ _
  rw [show Valued.v (algebraMap F (Fv F v) t) = v.valuation F t by
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v t
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t
      | rfl]
end GlobalTheory.CompanionTheory.Equi.CosetStep
