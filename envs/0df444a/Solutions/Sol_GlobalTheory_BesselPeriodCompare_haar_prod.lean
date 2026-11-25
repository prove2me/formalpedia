-- Prove2me | solution 1 for GlobalTheory.BesselPeriodCompare.haar_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:53:09.418795+00:00
-- url     : https://prove2.me/submissions/a5e0a1f4-b033-41e0-84de-27faf6f77c94

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
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_continuous_uinv
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_continuous_split
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_closedS
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_ae_prod
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_map_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_closedW
import Theorems.Thm_Formalism_QuantumDeterminants_uWNormal
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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) :
    PI.BesselPeriodGGP.IsHaarOn (Sset k r z) ((μW.prod μN).map mulM) := by
  have := hW.1
  have := hN.1
  have cW := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have hm : Measurable (mulM : Mt k r × Mt k r → Mt k r) := mulM_cont.measurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SigmaFinite.of_map _ continuous_split.measurable.aemeasurable
      (by rw [map_split hW hN]; infer_instance)
  · intro h
    rw [Measure.map_eq_zero_iff hm.aemeasurable] at h
    have h' := congrArg (fun m : Measure (Mt k r × Mt k r) => m (Set.univ ×ˢ Set.univ)) h
    simp only [Measure.prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
      Measure.measure_univ_eq_zero] at h'
    exact h'.elim hW.2.1 hN.2.1
  · rw [← ae_iff]
    refine (ae_map_iff hm.aemeasurable (amb_closed (closedS hz)).measurableSet).mpr ?_
    filter_upwards [ae_prod hW hN] with p hp
    exact ⟨_, hp.1, _, hp.2, rfl⟩
  · rintro s ⟨h, hh, n, hn, rfl⟩
    let g : Mt k r → Mt k r → Mt k r := fun a x => lmulM (uinv k r (Matrix.of a) * n * Matrix.of a) x
    have hg : Continuous (Function.uncurry g) :=
      ((((continuous_uinv (k := k) (r := r)).comp continuous_fst).matrix_mul continuous_const).matrix_mul
        continuous_fst).matrix_mul continuous_snd
    have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
    have hp : MeasurePreserving (fun p : Mt k r × Mt k r => (lmulM h p.1, g p.1 p.2))
        (μW.prod μN) (μW.prod μN) := by
      refine MeasurePreserving.skew_product ⟨(lmulM_cont h).measurable, hW.2.2.2 h hh⟩ hg.measurable ?_
      filter_upwards [h1] with a ha
      refine hN.2.2.2 _ ?_
      have := (Formalism.QuantumDeterminants.uWNormal k r z hz _ (cW.inv_mem _ ha) n hn).1
      rwa [Matrix.nonsing_inv_nonsing_inv _ (cW.unit _ ha), ← uinv_eq ha.1] at this
    conv_rhs => rw [← hp.map_eq]
    rw [Measure.map_map (lmulM_cont _).measurable hm, Measure.map_map hm hp.measurable]
    refine Measure.map_congr ?_
    filter_upwards [ae_prod hW hN] with p hp
    show h * n * (Matrix.of p.1 * Matrix.of p.2) =
      h * Matrix.of p.1 * (uinv k r (Matrix.of p.1) * n * Matrix.of p.1 * Matrix.of p.2)
    rw [uinv_eq hp.1.1]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (cW.unit _ hp.1)]
end GlobalTheory.BesselPeriodCompare
