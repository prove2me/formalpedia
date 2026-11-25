-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.leibnizL_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:50:30.584092+00:00
-- url     : https://prove2.me/submissions/884b0d1e-7728-4819-b14c-d696b786bd36

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_GlobalTheory_RegularisedIntegral_coef_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_dil_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_left_derivative
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_of_succ_left_order
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_dil_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_dilationAction_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_dilation_unipotent_measure


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
theorem _root_.solution (H : SqIntegrable D α) {m : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA 0 m A) (hB : AdmW α cB 0 m B) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => QL D q.1 m A B q.2.1 q.2.2) ({p | D.inSS p} ×ˢ Quad) := by
  induction m generalizing A B with
  | zero =>
    have h1 := coef_continuousOn H (admissible_of_weighted hA) (admissible_of_weighted hB)
    have h2 : ContinuousOn (fun q : SS k r × (ℝ × ℝ) => dilation₂ q.2 q.1) ({p | D.inSS p} ×ˢ Quad) :=
      (dilationAction_continuousOn k r).mono (Set.prod_mono (Set.subset_univ _) le_rfl)
    refine h1.comp h2 ?_
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    exact dil_inSS P.dilation_unipotent_measure D hp ht.1 ht.2
  | succ m ih => exact (ih (admissibleWeight_left_derivative hA) (admissibleWeight_of_succ_left_order hB)).add (ih (admissibleWeight_of_succ_left_order hA) (admissibleWeight_left_derivative hB))
end GlobalTheory.RegularisedIntegral
