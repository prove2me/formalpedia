-- Prove2me | solution 1 for GlobalTheory.BesselPeriodCompare.isHCParam_of_interlaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:08.724957+00:00
-- url     : https://prove2.me/submissions/095360e0-3e7f-44db-b425-0c7bec88793c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_node
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_node
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_node
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_node



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
theorem _root_.solution {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hi : GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.Interlaces r k lam u)
    (hp : GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.Parity r k lam u) : Formalism.QuantumDeterminants.IsHCParam u := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have hlt : i.val < j.val := hij
    have hj := j.isLt
    have h1 := hi.1 i
    have h2 := hi.2 (j.val - 1) (by omega)
    have e : (⟨j.val - 1 + 1, by omega⟩ : Fin k) = j := Fin.ext (by simp only; omega)
    rw [e] at h2
    have h3 := hl.1.antitone (a := ⟨i.val, by omega⟩) (b := ⟨j.val - 1, by omega⟩)
      (by simp only [Fin.le_def]; omega)
    linarith
  · obtain ⟨m, hm⟩ := hl.2 0
    obtain ⟨j, hj⟩ := hp 0 a
    refine ⟨m - j + r, ?_⟩
    push_cast at hm ⊢
    linarith
end GlobalTheory.BesselPeriodCompare
