-- Prove2me | solution 1 for GlobalTheory.T.section_lin_comb_fiber_product_separated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:38:49.493549+00:00
-- url     : https://prove2.me/submissions/f65523b0-1bcb-41e1-9d78-aa40c6d294e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Theorems.Thm_GlobalTheory_SectionsProduct_main


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Over (Spec (CommRingCat.of F))) [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁.left ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂.left ⟶ Z)) (ε₂ : K₂ → ℤ), (∀ v : LB.Sec (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim (fun k => (fst Y₁ Y₂).left ≫ φ₁ k) (fun k => (snd Y₁ Y₂).left ≫ φ₂ k)) (Sum.elim ε₁ ε₂)), ∃ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), ∀ (T : Scheme.{0}) (r : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J → sval v r z J = ∑ i, sval (a i) (r ≫ (fst Y₁ Y₂).left) z J * sval (b i) (r ≫ (snd Y₁ Y₂).left) z J) ∧ ∀ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), (∀ c : Fin n → F, (∀ j, ∑ i, resTop _ (scal Y₁.hom (c i)) * (a i).f j = 0) → c = 0) → (∀ (z : (Y₁ ⊗ Y₂).left) (J), Good L z J → ∑ i, sval (a i) (fst Y₁ Y₂).left z J * sval (b i) (snd Y₁ Y₂).left z J = 0) → ∀ i j, (b i).f j = 0 := by
  first | exact @GlobalTheory.SectionsProduct.main | exact GlobalTheory.SectionsProduct.main | (intros; apply GlobalTheory.SectionsProduct.main <;> assumption)
end _root_.GlobalTheory.T
