-- Prove2me | solution 1 for GlobalTheory.BesselPeriodCompare.fdeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:58:09.70869+00:00
-- url     : https://prove2.me/submissions/7e2e1711-fae1-4d85-8029-2e1b5c72d9db

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SymmetricMeasureL2NormEqResolutionL2

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
open GlobalTheory GlobalTheory.BesselPeriodCompare
open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open Formalism.FourierDecayAlt.B2 (IsClosedSubgroup mulM invM)
open Formalism.FourierDecayAlt.P.B2x1
open GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient (Mat leviW IsClosedMatGroup)
variable {k r : ℕ}
namespace GlobalTheory.BesselPeriodCompare
theorem _root_.solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure (Mt k r))
    (σ : Mat k r → (H →L[ℂ] H)) (w : H)
    (hm : AEStronglyMeasurable (fun x : Mt k r => ⟪w, σ (Matrix.of x) w⟫_ℂ) μ) :
    PI.BesselPeriodGGP.fdegH μ σ w = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt μ σ w := by
  unfold PI.BesselPeriodGGP.fdegH GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.coefNormSq
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (hm.norm.pow 2)]
  congr 3
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
end GlobalTheory.BesselPeriodCompare
