-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.exists_grpObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:59:41.742779+00:00
-- url     : https://prove2.me/submissions/f9ef53de-2719-41a9-aa39-9c2a144f9aa7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GeneratorLaw
namespace GlobalTheory.GeneratorLaw
theorem _root_.solution {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C] {G B : C}
    [GrpObj B] [IsCommMonObj B] (q : G ⟶ B) (P : C → Type) [∀ W, CommGroup (P W)]
    (n : ∀ {W : C}, (W ⟶ G) → P W) (v : ∀ {W : C}, (W ⟶ B) → (W ⟶ B) → P W)
    (ext : ∀ {W : C} (x y : W ⟶ G), x ≫ q = y ≫ q → n x = n y → x = y)
    (v₁ : ∀ {W : C} (x : W ⟶ B), v x 1 = 1) (v₂ : ∀ {W : C} (x y : W ⟶ B), v x y = v y x)
    (v₃ : ∀ {W : C} (x y w : W ⟶ B), v (x * y) w * v x y = v x (y * w) * v y w)
    (m : G ⊗ G ⟶ G) (m₁ : ∀ {W : C} (x y : W ⟶ G), (lift x y ≫ m) ≫ q = (x ≫ q) * (y ≫ q))
    (m₂ : ∀ {W : C} (x y : W ⟶ G), n (lift x y ≫ m) = n x * n y * (v (x ≫ q) (y ≫ q))⁻¹)
    (e : 𝟙_ C ⟶ G) (e₁ : ∀ W : C, (toUnit W ≫ e) ≫ q = 1) (e₂ : ∀ W : C, n (toUnit W ≫ e) = 1)
    (j : G ⟶ G) (j₁ : ∀ {W : C} (x : W ⟶ G), (x ≫ j) ≫ q = (x ≫ q)⁻¹)
    (j₂ : ∀ {W : C} (x : W ⟶ G), n (x ≫ j) = (n x)⁻¹ * v (x ≫ q)⁻¹ (x ≫ q)) :
    ∃ _ : GrpObj G, IsCommMonObj G ∧ μ[G] = m ∧ η[G] = e := by
  have comm : ∀ {W : C} (x y : W ⟶ G), lift x y ≫ m = lift y x ≫ m := fun x y =>
    ext _ _ (by rw [m₁, m₁, mul_comm]) (by rw [m₂, m₂, v₂, mul_comm (n x)])
  have mo : ∀ {W : C} (x : W ⟶ G), lift x (toUnit W ≫ e) ≫ m = x := fun x =>
    ext _ _ (by rw [m₁, e₁, _root_.mul_one]) (by rw [m₂, e₁, e₂, v₁]; simp)
  have as : ∀ {W : C} (x y w : W ⟶ G), lift (lift x y ≫ m) w ≫ m = lift x (lift y w ≫ m) ≫ m := fun x y w =>
    ext _ _ (by rw [m₁, m₁, m₁, m₁, _root_.mul_assoc]) (by
      rw [m₂, m₂, m₂, m₂, m₁, m₁, eq_mul_inv_of_mul_eq (v₃ (x ≫ q) (y ≫ q) (w ≫ q))]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  have li : ∀ {W : C} (x : W ⟶ G), lift (x ≫ j) x ≫ m = toUnit W ≫ e := fun x =>
    ext _ _ (by rw [m₁, j₁, e₁, inv_mul_cancel]) (by
      rw [m₂, j₂, j₁, e₂, mul_right_comm (n x)⁻¹]; simp)
  letI : GrpObj G :=
    { one := e
      mul := m
      one_mul := by
        have h : e ▷ G = lift (toUnit _ ≫ e) (λ_ G).hom := by
          ext
          · simp [toUnit_unique (fst (𝟙_ C) G) (toUnit _)]
          · simp [leftUnitor_hom]
        rw [h, comm, mo]
      mul_one := by
        have h : G ◁ e = lift (ρ_ G).hom (toUnit _ ≫ e) := by
          ext
          · simp [rightUnitor_hom]
          · simp [toUnit_unique (snd G (𝟙_ C)) (toUnit _)]
        rw [h, mo]
      mul_assoc := by
        have h₁ : m ▷ G = lift (lift (fst _ _ ≫ fst G G) (fst _ _ ≫ snd G G) ≫ m) (snd (G ⊗ G) G) := by
          ext <;> simp [← comp_lift]
        have h₂ : (α_ G G G).hom ≫ G ◁ m =
            lift (fst _ _ ≫ fst G G) (lift (fst _ _ ≫ snd G G) (snd (G ⊗ G) G) ≫ m) := by
          ext
          · simp
          · simp only [Category.assoc, whiskerLeft_snd, lift_snd]
            rw [← Category.assoc]
            congr 1
            ext <;> simp
        rw [← Category.assoc, h₁, h₂, as]
      inv := j
      left_inv := by simpa using li (𝟙 G)
      right_inv := by rw [comm]; simpa using li (𝟙 G) }
  refine ⟨inferInstance, ?_, rfl, rfl⟩
  rw [isCommMonObj_iff_isMulCommutative]
  exact fun W => ⟨⟨fun x y => comm x y⟩⟩
end GlobalTheory.GeneratorLaw
