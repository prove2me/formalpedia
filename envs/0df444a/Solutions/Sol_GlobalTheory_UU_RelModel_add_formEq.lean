-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.add_formEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:52.943301+00:00
-- url     : https://prove2.me/submissions/ab0e9916-bd82-449b-b4ce-9303055f7b2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight

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
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU.RelModel
theorem _root_.solution (a b : D.X) (U : Type) [CommGroup U] (h : ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ k, h (addφ D a b k) ^ addε k =
      (∏ k, h ((lift (toUnit _) (fst D.P.A D.P.A)).left ≫ famφT D (𝟙_ _) (a + b) k) ^ DegPre.famε 2 k) *
      (∏ k, h ((lift (toUnit _) (snd D.P.A D.P.A)).left ≫ famφT D (𝟙_ _) (a - b) k) ^ DegPre.famε 2 k) *
      (∏ k, h ((lift (toUnit _) (fst D.P.A D.P.A * snd D.P.A D.P.A)).left ≫ famφT D (𝟙_ _) a k) ^ DegPre.famε 1 k)⁻¹ *
      (∏ k, h ((lift (toUnit _) (fst D.P.A D.P.A * (snd D.P.A D.P.A)⁻¹)).left ≫ famφT D (𝟙_ _) b k) ^ DegPre.famε 1 k)⁻¹ := by
  have key : ∀ (p : D.P.A ⊗ D.P.A ⟶ D.P.A) (χ : D.X) (n : ℕ),
      ∏ k, h ((lift (toUnit _) p).left ≫ famφT D (𝟙_ _) χ k) ^ DegPre.famε n k =
        h p.left ^ ((n : ℤ) - 1) * h (p * (toUnit _ ≫ D.c χ)).left * (h (toUnit _ ≫ D.c χ).left)⁻¹ *
          h (toUnit (D.P.A ⊗ D.P.A) ≫ η[D.P.A]).left := fun p χ n => by
    have e1 : lift (toUnit _) p ≫ snd (𝟙_ _) D.P.A = p := lift_snd _ _
    have e3 : ∀ q : 𝟙_ _ ⟶ D.P.A, lift (toUnit _) p ≫ toUnit (𝟙_ _ ⊗ D.P.A) ≫ q = toUnit _ ≫ q := fun q => by
      rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    have e2 : lift (toUnit _) p ≫ padd D.P.A (snd (𝟙_ _) D.P.A) (toUnit _ ≫ D.c χ) = p * (toUnit _ ≫ D.c χ) := by
      show _ ≫ (snd (𝟙_ _) D.P.A * (toUnit _ ≫ D.c χ)) = _
      rw [MonObj.comp_mul, e1, e3]
    rw [Fin.prod_univ_four]
    show h (lift (toUnit _) p ≫ snd (𝟙_ _) D.P.A).left ^ ((n : ℤ) - 1) *
      h (lift (toUnit _) p ≫ padd D.P.A (snd (𝟙_ _) D.P.A) (toUnit _ ≫ D.c χ)).left ^ (1 : ℤ) *
      h (lift (toUnit _) p ≫ toUnit (𝟙_ _ ⊗ D.P.A) ≫ D.c χ).left ^ (-1 : ℤ) *
      h (lift (toUnit _) p ≫ toUnit (𝟙_ _ ⊗ D.P.A) ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [e1, e2, e3, e3, zpow_one, zpow_one, zpow_neg_one]
  rw [key, key, key, key]
  simp only [Fin.prod_univ_succ, addφ, addε, Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_eq_empty,
    Finset.prod_empty, Fin.prod_univ_zero]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
  norm_num
  abel
end GlobalTheory.UU.RelModel
