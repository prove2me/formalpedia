-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.coef_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:15:50.109677+00:00
-- url     : https://prove2.me/submissions/064aeee8-e5be-48a3-879e-8643a7d6ec44

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_GlobalTheory_RegularisedIntegral_SqIntegrable_integrable
import Theorems.Thm_GlobalTheory_RegularisedIntegral_integrand_aestronglyMeasurable
import Theorems.Thm_GlobalTheory_RegularisedIntegral_integrand_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haarG
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Sd_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_conj_product_mem_unitary_group
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_conjugated_pair_continuous_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hsInner_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_norm_product_continuous_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_haar_ae


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (hB : admitted α cB B) : ContinuousOn (Ph D A B) {p | D.inSS p} := by
  intro p₀ hp₀
  show ContinuousWithinAt (fun p => ∫ g : Mt k r, hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g)) ∂D.μG)
    {p | D.inSS p} p₀
  refine continuousWithinAt_of_dominated
    (bound := fun g : Mt k r => (Module.finrank ℂ Wq : ℝ) * (cA * (normProductOfPair p₀ + 1) ^ α * cB) *
      (gN (Matrix.of g : Mat k r) ^ (-α) * gN (Matrix.of g : Mat k r) ^ (-α))) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact integrand_aestronglyMeasurable H hA hB hp
  · have hN : ∀ᶠ p in 𝓝[{p | D.inSS p}] p₀, normProductOfPair p < normProductOfPair p₀ + 1 :=
      (norm_product_continuous_on D p₀ hp₀).tendsto.eventually_lt_const (lt_add_one _)
    filter_upwards [self_mem_nhdsWithin, hN] with p hp hNp
    filter_upwards [haar_ae D.haarG] with g hg
    exact integrand_norm_le H hA hB hp hg hNp.le
  · exact (SqIntegrable.integrable H).const_mul _
  · filter_upwards [haar_ae D.haarG] with g hg
    have h1 : ContinuousWithinAt (fun p : SS k r => A (sgs p (Matrix.of g))) {p | D.inSS p} p₀ :=
      (hA.1.comp (conjugated_pair_continuous_on D (Matrix.of g)) (fun p hp => conj_product_mem_unitary_group D hp hg)) p₀ hp₀
    have h2 : ContinuousWithinAt (fun p : SS k r => Sd D p (A (sgs p (Matrix.of g)))) {p | D.inSS p} p₀ :=
      (Sd_continuousOn D p₀ hp₀).clm_apply h1
    exact hsInner_continuous.continuousAt.comp_continuousWithinAt (h2.prodMk continuousWithinAt_const)
end GlobalTheory.RegularisedIntegral
