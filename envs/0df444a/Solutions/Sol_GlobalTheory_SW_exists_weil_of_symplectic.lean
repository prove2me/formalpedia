-- Prove2me | solution 1 for GlobalTheory.SW.exists_weil_of_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:38.160362+00:00
-- url     : https://prove2.me/submissions/a5edf3ac-3e0a-4740-9acb-11077501590a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandarStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplectic
import Theorems.Thm_GlobalTheory_SW_exists_weil_mul
import Theorems.Thm_GlobalTheory_T_exists_unitary_siegelThetaTransformationLaw_standardJ
import Theorems.Thm_GlobalTheory_T_siegelTheta_transformation_siegelParabolic
import Theorems.Thm_P2M_GlobalTheory_T_symplectic_eq_parabolic_J_parabolic_J_parabolic__6343b5708f56


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution :
    ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧ TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  intro κ ι _ _ _ σ hκ hσ
  obtain ⟨p₁, h₁, p₂, h₂, p₃, h₃, l₁, l₂, l₃, rfl⟩ := GlobalTheory.T.symplectic_eq_parabolic_J_parabolic_J_parabolic' ι σ hσ
  have hJ : Matrix.J ι ℚ ∈ Matrix.symplecticGroup ι ℚ := SymplecticGroup.J_mem ι ℚ
  have w₁ := GlobalTheory.T.siegelTheta_transformation_siegelParabolic κ ι p₁ hκ h₁ l₁
  have w₂ := GlobalTheory.T.siegelTheta_transformation_siegelParabolic κ ι p₂ hκ h₂ l₂
  have w₃ := GlobalTheory.T.siegelTheta_transformation_siegelParabolic κ ι p₃ hκ h₃ l₃
  have wJ := GlobalTheory.T.exists_unitary_siegelThetaTransformationLaw_standardJ κ ι hκ
  have a₁ := mul_mem h₁ hJ
  have a₂ := mul_mem a₁ h₂
  have a₃ := mul_mem a₂ hJ
  exact exists_weil_mul a₃ h₃
    (exists_weil_mul a₂ hJ (exists_weil_mul a₁ h₂ (exists_weil_mul h₁ hJ w₁ wJ) w₂) wJ) w₃
end GlobalTheory.SW
