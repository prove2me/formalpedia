-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.isUnit_det_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:11.113345+00:00
-- url     : https://prove2.me/submissions/d778d394-d43f-4066-b2ab-6767732f4eb2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open PI.BesselMapUniq (psiGen)
variable {k r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
theorem _root_.solution {h : Mat k r} (hh : h ∈ UH (Hpk k r)) (hH : IsUnit (Hpk k r).det) :
    IsUnit h.det := by
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh
  have := congrArg Matrix.det hU
  rw [Matrix.det_mul] at this
  exact isUnit_of_mul_isUnit_right (this ▸ hH)
end GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
