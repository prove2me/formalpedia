-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.integrand_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:34.99298+00:00
-- url     : https://prove2.me/submissions/b80da2dc-bfba-4491-9690-bf07b57c97a2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_norm_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_two_sided_translate
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hilbert_schmidt_integrand_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inSS_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv


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
    (hB : admitted α cB B) {p : SS k r} (hp : D.inSS p) {g : Mat k r} (hg : g ∈ GV k r) {M : ℝ} (hM : normProductOfPair p ≤ M) :
    ‖hsInner (rho D p A g) (B g)‖ ≤
      (Module.finrank ℂ Wq : ℝ) * (cA * M ^ α * cB) * (gN g ^ (-α) * gN g ^ (-α)) := by
  have hxy := inSS_mem D hp
  have hcA := admissible_constant_nonneg hA
  have hcB := admissible_constant_nonneg hB
  have h1 := admissible_norm_bound (admissible_two_sided_translate H.1 hA (WeylGroupFacts.uh_inv hxy.1) hxy.2) hg
  rw [Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hxy.1)] at h1
  have h2 := admissible_norm_bound hB hg
  have h3 : (gN (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r) *
      gN (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)⁻¹) ^ α ≤ M ^ α :=
    Real.rpow_le_rpow (mul_nonneg (gN_nonneg _) (gN_nonneg _)) hM H.1
  have hg0 : 0 ≤ gN g ^ (-α) := Real.rpow_nonneg (gN_nonneg g) _
  have hM0 : 0 ≤ M ^ α := le_trans (Real.rpow_nonneg (mul_nonneg (gN_nonneg _) (gN_nonneg _)) _) h3
  refine (hilbert_schmidt_integrand_bound D A B hp g).trans ?_
  calc (Module.finrank ℂ Wq : ℝ) * (‖A ((Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)⁻¹ * g *
        (Matrix.of p.2.2 * Matrix.of p.2.1))‖ * ‖B g‖)
      ≤ (Module.finrank ℂ Wq : ℝ) * ((cA * M ^ α * gN g ^ (-α)) * (cB * gN g ^ (-α))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (h1.trans ?_) h2 (norm_nonneg _) (by positivity))
          (by positivity)
        gcongr
    _ = _ := by ring
end GlobalTheory.RegularisedIntegral
