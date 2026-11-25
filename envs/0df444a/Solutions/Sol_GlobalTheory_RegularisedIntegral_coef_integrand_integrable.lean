-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.coef_integrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:02.280558+00:00
-- url     : https://prove2.me/submissions/9e051dc0-8bf5-4bc4-a111-942c4577a11f

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_ae
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
theorem _root_.solution (H : SqIntegrable D α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : admitted α cA A) (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) :
    Integrable (fun g : Mt k r => hsInner (rho D p A (Matrix.of g)) (B (Matrix.of g))) D.μG := by
  refine (H.integrable.const_mul ((Module.finrank ℂ Wq : ℝ) * (cA * normProductOfPair p ^ α * cB))).mono'
    (integrand_aestronglyMeasurable H hA hB hp) ?_
  filter_upwards [haar_ae D.haarG] with g hg
  exact integrand_norm_le H hA hB hp hg le_rfl
end GlobalTheory.RegularisedIntegral
