-- Prove2me | solution 1 for GlobalTheory.BesselPeriodCompare.period_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:29.645792+00:00
-- url     : https://prove2.me/submissions/580741cd-33ef-449b-bc5f-e384627ad179

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_haar_unique
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_haar_of_compact
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_closedS
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_ae_prod
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_haar_prod
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_integral_map_of_split
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_star_psiGen
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_closedW
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FormalDegreeHaarQuotient_twist_mul


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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW μN μS : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN)
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn (Sset k r z) μS) :
    ∃ t : ℝ, 0 < t ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (c : Fin r → ℂ)
      (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Wp →L[ℂ] Wp)) (w v : H),
      GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.period k r z c σ π μS w v =
        t • ∫ p : Mt k r × Mt k r,
          (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ *
            star (PI.BesselPeriodGGP.psiGen k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
          ∂(μW.prod μN) := by
  obtain ⟨t, t0, t1, e⟩ := haar_unique (closedS hz) (haar_of_compact (closedS hz).closed hS)
    (haar_prod hz hW hN)
  refine ⟨t.toReal, ENNReal.toReal_pos t0 t1, fun H _ _ Wp _ _ c σ π w v => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.period
  rw [e, integral_smul_measure, integral_map_of_split hW hN]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_prod hW hN] with p hp
  have h := (GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.twist_mul c π hp.1 hp.2
    ((Formalism.FourierDecayAlt.P.B2x3.closedW k r z).unit _ hp.1)).2
  rw [star_psiGen, ← smul_smul, ← h]
  rfl
end GlobalTheory.BesselPeriodCompare
