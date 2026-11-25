-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.sqIntegrable_of_threshold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:26.31344+00:00
-- url     : https://prove2.me/submissions/e0483996-9a09-4a7c-85f3-400ba6bb4abb

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2_AB_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haarG
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_matrix_norm_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_norm_power_integrable_sharp


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
omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
namespace GlobalTheory.RegularisedIntegral
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (hα : AB k r ≤ α) : SqIntegrable D α := by
  have h0 : 0 ≤ α := le_trans (P.B2.AB_nonneg k r) hα
  refine ⟨h0, ?_⟩
  have hfin := norm_power_integrable_sharp k r D.μG α D.haarG hα
  have hm : Measurable fun g : Mt k r => gN (Matrix.of g : Mat k r) ^ (-α) :=
    (show Continuous fun g : Mt k r => gN (Matrix.of g : Mat k r) from gN_continuous).measurable.pow_const _
  have hnn : ∀ g : Mt k r, 0 ≤ gN (Matrix.of g : Mat k r) ^ (-α) := fun g => Real.rpow_nonneg (gN_nonneg _) _
  have hI : Integrable (fun g : Mt k r => gN (Matrix.of g : Mat k r) ^ (-α)) D.μG :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)).2 hfin⟩
  refine hI.mono' (hm.mul hm).aestronglyMeasurable ?_
  filter_upwards [haar_ae D.haarG] with g hg
  rw [Real.norm_of_nonneg (mul_nonneg (hnn g) (hnn g))]
  exact mul_le_of_le_one_right (hnn g)
    (Real.rpow_le_one_of_one_le_of_nonpos (matrix_norm_ge_one k r _ hg) (by linarith))
end GlobalTheory.RegularisedIntegral
