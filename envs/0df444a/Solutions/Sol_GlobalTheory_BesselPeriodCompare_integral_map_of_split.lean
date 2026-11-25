-- Prove2me | solution 1 for GlobalTheory.BesselPeriodCompare.integral_map_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:09.750929+00:00
-- url     : https://prove2.me/submissions/b62ee660-919f-4c97-a2b4-ae77b558f227

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_continuous_split
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_split_mul
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_ae_prod
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_map_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mulM_cont


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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) (f : Mt k r → E) :
    ∫ s, f s ∂((μW.prod μN).map mulM) = ∫ p, f (mulM p) ∂(μW.prod μN) := by
  have hm : Measurable (mulM : Mt k r × Mt k r → Mt k r) := mulM_cont.measurable
  by_cases hf : AEStronglyMeasurable f ((μW.prod μN).map mulM)
  · exact integral_map hm.aemeasurable hf
  · rw [integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable]
    intro h
    apply hf
    rw [← map_split hW hN] at h
    refine (h.comp_measurable continuous_split.measurable).congr ?_
    have hc : Continuous fun s : Mt k r => mulM (split k r s) := mulM_cont.comp continuous_split
    have : ∀ᵐ s ∂((μW.prod μN).map mulM), mulM (split k r s) = s := by
      refine (ae_map_iff hm.aemeasurable (isClosed_eq hc continuous_id).measurableSet).mpr ?_
      filter_upwards [ae_prod hW hN] with p hp
      exact congrArg mulM (split_mul hp.1 hp.2)
    filter_upwards [this] with s hs
    exact congrArg f hs
end GlobalTheory.BesselPeriodCompare
