-- Prove2me | solution 1 for GlobalTheory.RealWeil.SchrFamily.seminorm_rhoSch_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:58:50.336131+00:00
-- url     : https://prove2.me/submissions/cce46855-06a1-47fa-9ff0-6332375e88c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
import Theorems.Thm_GlobalTheory_RealWeil_SchrFamily_seminorm_rhoSch_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.SchrFamily
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil.SchrFamily
theorem _root_.solution (g : Sch l) (k m : ℕ) :
    ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (rhoSch w g) ≤ C * (1 + ‖w‖) ^ N := by
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_rhoSch_sub_le (SchwartzMap.seminorm ℂ k m)
    ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_seminorm (k, m))
  set p := SchwartzMap.seminorm ℂ k m (E := EuclideanSpace ℝ l) (F := ℂ) with hpdef
  set c := ‖pCLM l‖ + ‖qCLM l‖ with hcdef
  set N := 3 + M₁ + M₂ + M₃ with hN
  have hq1 : 0 ≤ q₁ g := apply_nonneg _ _
  have hq2 : 0 ≤ q₂ g := apply_nonneg _ _
  have hq3 : 0 ≤ q₃ g := apply_nonneg _ _
  have hp : 0 ≤ p g := apply_nonneg _ _
  refine ⟨(1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g), N, fun w => ?_⟩
  have hc : 0 ≤ c := by positivity
  have hw := norm_nonneg w
  set X := (1 + c) * (1 + ‖w‖) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hpw : ‖pPart w‖ ≤ ‖pCLM l‖ * ‖w‖ := (pCLM l).le_opNorm w
  have hqw : ‖qPart w‖ ≤ ‖qCLM l‖ * ‖w‖ := (qCLM l).le_opNorm w
  have hpn := norm_nonneg (pCLM l)
  have hqn := norm_nonneg (qCLM l)
  have ha : 1 + ‖pPart w‖ ≤ X := by rw [hX]; nlinarith
  have hb' : 1 + ‖qPart w‖ ≤ X := by rw [hX]; nlinarith
  have ha' : ‖pPart w‖ ≤ X := by linarith
  have hb'' : ‖qPart w‖ ≤ X := by linarith
  have hk : ‖qPart w‖ + |⟪pPart w, qPart w⟫ / 2| ≤ 2 * X ^ 2 := by
    have h1 : |⟪pPart w, qPart w⟫| ≤ ‖pPart w‖ * ‖qPart w‖ := abs_real_inner_le_norm _ _
    have h2 : ‖pPart w‖ * ‖qPart w‖ ≤ X * X := mul_le_mul ha' hb'' (norm_nonneg _) (by linarith)
    rw [abs_div, abs_two]
    nlinarith
  have hsub : p (rhoSch w g) ≤ p (rhoSch w g - g) + p g := by
    simpa using map_add_le_add p (rhoSch w g - g) g
  calc p (rhoSch w g) ≤ p (rhoSch w g - g) + p g := hsub
    _ ≤ (2 * X ^ 2) * X ^ M₁ * (X * X ^ M₃ * q₃ g + q₁ g) + X * X ^ M₂ * q₂ g + p g := by
        refine add_le_add ((hb w g).trans ?_) le_rfl
        gcongr
    _ = 2 * X ^ (3 + M₁ + M₃) * q₃ g + 2 * X ^ (2 + M₁) * q₁ g + X ^ (1 + M₂) * q₂ g + 1 * p g := by ring
    _ ≤ 2 * X ^ N * q₃ g + 2 * X ^ N * q₁ g + X ^ N * q₂ g + X ^ N * p g := by
        have e1 : X ^ (3 + M₁ + M₃) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e2 : X ^ (2 + M₁) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e3 : X ^ (1 + M₂) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e4 : (1 : ℝ) ≤ X ^ N := one_le_pow₀ hX1
        have f1 := mul_le_mul_of_nonneg_right e1 hq3
        have f2 := mul_le_mul_of_nonneg_right e2 hq1
        have f3 := mul_le_mul_of_nonneg_right e3 hq2
        have f4 := mul_le_mul_of_nonneg_right e4 hp
        nlinarith
    _ = (1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g) * (1 + ‖w‖) ^ N := by
        rw [hX, mul_pow]; ring
end GlobalTheory.RealWeil.SchrFamily
