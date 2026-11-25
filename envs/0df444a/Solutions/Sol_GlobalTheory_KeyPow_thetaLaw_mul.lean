-- Prove2me | solution 1 for GlobalTheory.KeyPow.thetaLaw_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:45:59.702315+00:00
-- url     : https://prove2.me/submissions/d326675f-cb71-4943-a8e6-d28c18aa1d7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaLawMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_det_jAut_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_expArg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_isUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sp_A
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_zAct_mul
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KeyPow
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace GlobalTheory.KeyPow
theorem _root_.solution : ∀ (g : ℕ) (sp sq : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (n n' m m' k k' : Fin g → ℤ), sp ∈ Matrix.symplecticGroup (Fin g) ℤ → sq ∈ Matrix.symplecticGroup (Fin g) ℤ → GlobalTheory.KeyPow.ThetaLaw g sq n n' m m' → GlobalTheory.KeyPow.ThetaLaw g sp m m' k k' → GlobalTheory.KeyPow.ThetaLaw g (sp * sq) n n' k k' := by
  intro g x y n n' m m' k k' hx hy Hy Hx
  obtain ⟨c₁, hc₁, h₁⟩ := Hy
  obtain ⟨c₂, hc₂, h₂⟩ := Hx
  refine ⟨c₂ * c₁, by rw [mul_pow, hc₁, hc₂, _root_.one_mul], fun τ hτ z => ?_⟩
  have hjy := jAut_isUnit hy hτ
  have hτ₂ := spAct_mem hy hτ
  have hjx := jAut_isUnit hx hτ₂
  rw [spAct_mul x y τ hjy, zAct_mul x y τ hjy z, h₂ _ hτ₂, h₁ τ hτ z, det_jAut_mul x y τ hjy,
    expArg_mul x y τ hjy hjx (sp_A hy hτ.1 hjy) z, eC_add]
  ring
end GlobalTheory.KeyPow
