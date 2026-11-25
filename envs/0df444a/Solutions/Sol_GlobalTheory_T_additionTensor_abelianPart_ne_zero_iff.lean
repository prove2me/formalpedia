-- Prove2me | solution 1 for GlobalTheory.T.additionTensor_abelianPart_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:13:54.633476+00:00
-- url     : https://prove2.me/submissions/d70dc85b-ff23-400e-8607-afc7c14317ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionTensorAbelianPartNeZeroIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionTensorAbelianPartNeZeroIffStatement
import Theorems.Thm_GlobalTheory_addB_tensor_ne_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by
  first | exact @GlobalTheory.addB_tensor_ne_zero_iff | exact GlobalTheory.addB_tensor_ne_zero_iff | (intros; apply GlobalTheory.addB_tensor_ne_zero_iff <;> assumption)
end _root_.GlobalTheory.T
