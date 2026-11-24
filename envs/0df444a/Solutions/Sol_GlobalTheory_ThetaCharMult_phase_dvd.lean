-- Prove2me | solution 1 for GlobalTheory.ThetaCharMult.phase_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:48:22.322832+00:00
-- url     : https://prove2.me/submissions/f695f972-5bcc-421f-b766-9afc0cf000b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
import Theorems.Thm_GlobalTheory_ThetaCharMult_sp_rel_int
import Theorems.Thm_GlobalTheory_ThetaCharMult_dvd_mulVec
import Theorems.Thm_GlobalTheory_ThetaCharMult_dvd_dot_left
import Theorems.Thm_GlobalTheory_ThetaCharMult_dvd_dot_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ThetaCharMult
variable {g : ℕ}
namespace GlobalTheory.ThetaCharMult
theorem _root_.solution {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (hB : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₁₂ᵀ i j) (hC : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₂₁ᵀ i j)
    (n n' : Fin g → ℤ) :
    (8 : ℤ) ∣ n ⬝ᵥ n' - (γ.toBlocks₁₁ᵀ *ᵥ n + γ.toBlocks₂₁ᵀ *ᵥ n') ⬝ᵥ
      (γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n') := by
  have e : (γ.toBlocks₁₁ᵀ *ᵥ n) ⬝ᵥ (γ.toBlocks₂₂ᵀ *ᵥ n') =
      n ⬝ᵥ n' + (γ.toBlocks₁₂ᵀ *ᵥ n) ⬝ᵥ (γ.toBlocks₂₁ᵀ *ᵥ n') := by
    rw [mulVec_transpose, mulVec_transpose γ.toBlocks₁₂, ← dotProduct_mulVec, ← dotProduct_mulVec,
      mulVec_mulVec, mulVec_mulVec, sp_rel_int hγ, add_mulVec, one_mulVec, dotProduct_add]
  have d1 := dvd_dot_left (dvd_mulVec hB n) (γ.toBlocks₂₁ᵀ *ᵥ n')
  have d2 := dvd_dot_right (dvd_mulVec hB n) (γ.toBlocks₁₁ᵀ *ᵥ n)
  have d3 := dvd_dot_left (dvd_mulVec hC n') (γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n')
  rw [add_dotProduct, dotProduct_add, e]
  omega
end GlobalTheory.ThetaCharMult
