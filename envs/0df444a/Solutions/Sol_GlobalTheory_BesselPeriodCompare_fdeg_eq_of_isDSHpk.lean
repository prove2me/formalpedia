-- Prove2me | solution 1 for GlobalTheory.BesselPeriodCompare.fdeg_eq_of_isDSHpk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:52:49.000562+00:00
-- url     : https://prove2.me/submissions/b0b9ea73-369a-4d4f-983c-95a415f601f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_fdeg_eq
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_continuousOn_of_isDSHpk
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_closedG


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
theorem _root_.solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {μ : Measure (Mt k r)}
    (hμ : μ {x | Matrix.of x ∉ UH (Hpk k r)} = 0) (w : H) :
    PI.BesselPeriodGGP.fdegH μ σ w = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt μ σ w := by
  apply fdeg_eq
  have hG := Formalism.FourierDecayAlt.P.B2x2.closedG k r
  have hr : μ.restrict (amb (UH (Hpk k r))) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ)
  rw [← hr]
  have hc : ContinuousOn (fun x : Mt k r => ⟪w, σ (Matrix.of x) w⟫_ℂ) (amb (UH (Hpk k r))) :=
    continuousOn_const.inner (continuousOn_of_isDSHpk hσ w)
  exact hc.aestronglyMeasurable (amb_closed hG).measurableSet
end GlobalTheory.BesselPeriodCompare
