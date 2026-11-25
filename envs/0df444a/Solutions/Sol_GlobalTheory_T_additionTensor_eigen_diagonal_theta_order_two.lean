-- Prove2me | solution 1 for GlobalTheory.T.additionTensor_eigen_diagonal_theta_order_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:03:22.003377+00:00
-- url     : https://prove2.me/submissions/d0ac8f01-aac2-4f9f-9da8-46e897e985e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionTensorEigenDiagonalThetaOrderTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionTensorEigenDiagonalThetaOrderTwoStatement
import Theorems.Thm_GlobalTheory_AddEig_main
import Theorems.Thm_GlobalTheory_SectionsProduct_main
import Theorems.Thm_GlobalTheory_ThetaLin_main


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
theorem _root_.solution : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' u u' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → ∀ θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p), θ.pt ^ 2 = 1 → (∀ i, IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t i).sec (u i).sec ∧ IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t' i).sec (u' i).sec) → ∃ r : F, ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  first | exact @GlobalTheory.AddEig.main | exact GlobalTheory.AddEig.main | (intros; apply GlobalTheory.AddEig.main <;> assumption)
end _root_.GlobalTheory.T
