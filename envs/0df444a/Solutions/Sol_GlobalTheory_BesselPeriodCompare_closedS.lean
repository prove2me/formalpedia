-- Prove2me | solution 1 for GlobalTheory.BesselPeriodCompare.closedS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:01.18668+00:00
-- url     : https://prove2.me/submissions/91afdab4-b827-4929-83f4-33b08177a44d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_uinv_eq
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_continuous_split
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_split_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_closedN
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_closedW
import Theorems.Thm_Formalism_QuantumDeterminants_sGroup


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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : IsClosedSubgroup (Sset k r z) := by
  obtain ⟨h1, h2, h3⟩ := Formalism.QuantumDeterminants.sGroup k r z hz
  have hW := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have hN := Formalism.FourierDecayAlt.P.B2x2.closedN k r
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · rintro a ⟨h, hh, n, hn, rfl⟩
    rw [Matrix.det_mul]
    exact (hW.unit h hh).mul (hN.unit n hn)
  · have e : Sset k r z = split k r ⁻¹' (amb (UWset k r z) ×ˢ amb (Nset k r)) := by
      ext s
      constructor
      · rintro ⟨h, hh, n, hn, rfl⟩
        show split k r (h * n) ∈ amb (UWset k r z) ×ˢ amb (Nset k r)
        rw [split_mul hh hn]
        exact ⟨hh, hn⟩
      · rintro ⟨hh, hn⟩
        have hh' : leviW k r s ∈ UWset k r z := hh
        refine ⟨_, hh', uinv k r (leviW k r s) * s, hn, ?_⟩
        rw [uinv_eq hh'.1, Matrix.mul_nonsing_inv_cancel_left _ _ (hW.unit _ hh')]
    rw [e]
    exact ((amb_closed hW).prod (amb_closed hN)).preimage continuous_split
end GlobalTheory.BesselPeriodCompare
