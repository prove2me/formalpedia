-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap.measurable_mulP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:26.212686+00:00
-- url     : https://prove2.me/submissions/98cc6682-085b-4852-b3bb-224c10f08e82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap
open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU IsOrthProjOnto InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
namespace GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap
theorem _root_.solution {k r : ℕ} : Measurable (mulP (k := k) (r := r)) := by
  unfold mulP
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  fun_prop
end GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap
