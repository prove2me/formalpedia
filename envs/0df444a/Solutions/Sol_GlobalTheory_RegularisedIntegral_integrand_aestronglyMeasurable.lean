-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.integrand_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:10.807304+00:00
-- url     : https://prove2.me/submissions/43c059ab-8676-4f5c-b50e-e34b0f26bd1a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haarG
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_sgs_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_ae_strongly_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_two_sided_translate
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hsInner_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inSS_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_sgs_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_sgs_eq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RegularisedIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {α : ℝ}
namespace GlobalTheory.RegularisedIntegral
theorem _root_.solution (H : SqIntegrable D α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) :
    AEStronglyMeasurable (fun g : Mt k r => hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g))) D.μG := by
  have hxy := inSS_mem D hp
  have hAt : AEStronglyMeasurable (fun g : Mt k r => A (sgs p (Matrix.of g))) D.μG := by
    simp only [sgs_eq]
    exact admissible_ae_strongly_measurable (admissible_two_sided_translate H.1 hA (WeylGroupFacts.uh_inv hxy.1) hxy.2) D.haarG
  have h1 : AEStronglyMeasurable (fun g : Mt k r => Sd D p (A (sgs p (Matrix.of g)))) D.μG :=
    (Sd D p).continuous.comp_aestronglyMeasurable hAt
  exact hsInner_continuous.comp_aestronglyMeasurable (h1.prodMk (admissible_ae_strongly_measurable hB D.haarG))
end GlobalTheory.RegularisedIntegral
