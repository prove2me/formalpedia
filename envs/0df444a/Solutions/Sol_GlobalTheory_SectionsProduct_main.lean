-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:25:34.534294+00:00
-- url     : https://prove2.me/submissions/8e1d7a78-0e44-4781-b694-0ee111567da9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_GlobalTheory_SectionsProduct_exists_sum
import Theorems.Thm_GlobalTheory_SectionsProduct_eq_zero_of_sum
import Theorems.Thm_GlobalTheory_SectionsProduct_isSeparated_of_hom

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
open TensorProduct TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.SectionsProduct
open GlobalTheory.KuennethOne
variable {B Y T S X₁ X₂ W : Scheme.{0}} {L : LB B} {K : Type} [Fintype K]
variable {p : W ⟶ X₁} {q : W ⟶ X₂} {i₁ : X₁ ⟶ S} {i₂ : X₂ ⟶ S} (H : IsPullback p q i₁ i₂)
variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (X₁ ⟶ B)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (X₂ ⟶ B)) (ε₂ : K₂ → ℤ)
namespace GlobalTheory.SectionsProduct
theorem _root_.solution : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Over (Spec (CommRingCat.of F))) [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁.left ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂.left ⟶ Z)) (ε₂ : K₂ → ℤ), (∀ v : LB.Sec (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim (fun k => (fst Y₁ Y₂).left ≫ φ₁ k) (fun k => (snd Y₁ Y₂).left ≫ φ₂ k)) (Sum.elim ε₁ ε₂)), ∃ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), ∀ (T : Scheme.{0}) (r : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J → sval v r z J = ∑ i, sval (a i) (r ≫ (fst Y₁ Y₂).left) z J * sval (b i) (r ≫ (snd Y₁ Y₂).left) z J) ∧ ∀ (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), (∀ c : Fin n → F, (∀ j, ∑ i, resTop _ (scal Y₁.hom (c i)) * (a i).f j = 0) → c = 0) → (∀ (z : (Y₁ ⊗ Y₂).left) (J), Good L z J → ∑ i, sval (a i) (fst Y₁ Y₂).left z J * sval (b i) (snd Y₁ Y₂).left z J = 0) → ∀ i j, (b i).f j = 0 := by
  intro F _ Z L hL Y₁ Y₂ _ _ _ _ K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂
  have H : IsPullback (fst Y₁ Y₂).left (snd Y₁ Y₂).left Y₁.hom Y₂.hom := IsPullback.of_hasPullback _ _
  let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  have hS : IsField Γ(Spec (CommRingCat.of F), ⊤) := e.toMulEquiv.isField (Field.toIsField F)
  have := QuasiCompact.compactSpace_of_compactSpace Y₁.hom
  have := QuasiCompact.compactSpace_of_compactSpace Y₂.hom
  have := isSeparated_of_hom Y₁.hom
  have := isSeparated_of_hom Y₂.hom
  refine ⟨exists_sum H φ₁ ε₁ φ₂ ε₂ hL hS, fun n a b ha => eq_zero_of_sum H φ₁ ε₁ φ₂ ε₂ hL hS a b fun c hc => ?_⟩
  have := ha (fun i => e (c i)) fun j => by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hc j)
    exact congrArg (fun t => resTop _ (Y₁.hom.appTop.hom t) * (a i).f j) (e.symm_apply_apply (c i))
  exact funext fun i => e.injective ((congrFun this i).trans (map_zero e).symm)
end GlobalTheory.SectionsProduct
