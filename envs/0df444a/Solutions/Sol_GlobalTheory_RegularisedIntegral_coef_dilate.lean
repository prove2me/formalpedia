-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.coef_dilate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:41:31.076442+00:00
-- url     : https://prove2.me/submissions/3446e7c3-7557-42a6-a9e5-629c42614df7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haarG
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Sd_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_rho_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_sgs_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_dilation_unipotent_weyl_measure
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


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
theorem _root_.solution (_H : SqIntegrable D α) (A B : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : D.inSS p) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Ph D A B (dilation₂ (x, y) p) =
      Ph D (fun g => A (aDil k r x * g * (aDil k r y)⁻¹)) (fun g => B (aDil k r x * g * (aDil k r y)⁻¹)) p := by
  have hax := aDil_mem k r hx
  have hay := aDil_inv_mem k r hy
  have mpL : MeasurePreserving (lmulM (aDil k r x)) D.μG D.μG :=
    ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarG.left _ hax⟩
  have mpR : MeasurePreserving (rmulF (aDil k r y)⁻¹) D.μG D.μG :=
    ⟨(continuous_right_multiplication_map _).measurable, D.haarG.right _ hay⟩
  have eL : MeasurableEmbedding (lmulM (k := k) (r := r) (aDil k r x)) :=
    (BesselUnitaryEquiv.lmulE _ (WeylGroupFacts.isUnit_of_uh hax)).measurableEmbedding
  have eR : MeasurableEmbedding (rmulF (aDil k r y)⁻¹) :=
    (rightMulMeasurableEquiv _ (WeylGroupFacts.isUnit_of_uh hay)).measurableEmbedding
  unfold Ph
  rw [← (mpR.comp mpL).integral_comp (eR.comp eL)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have e : (Matrix.of ((rmulF (aDil k r y)⁻¹ ∘ lmulM (aDil k r x)) g) : Mat k r) =
      aDil k r x * Matrix.of g * (aDil k r y)⁻¹ := rfl
  show hsInner (rho D (dilation₂ (x, y) p) A (Matrix.of ((rmulF (aDil k r y)⁻¹ ∘ lmulM (aDil k r x)) g)))
      (B (Matrix.of ((rmulF (aDil k r y)⁻¹ ∘ lmulM (aDil k r x)) g))) =
    hsInner (rho D p (fun g => A (aDil k r x * g * (aDil k r y)⁻¹)) (Matrix.of g))
      (B (aDil k r x * Matrix.of g * (aDil k r y)⁻¹))
  rw [e, rho_eq, rho_eq, sgs_dil P.dilation_unipotent_weyl_measure D hp hx hy, Sd_dil]
end GlobalTheory.RegularisedIntegral
