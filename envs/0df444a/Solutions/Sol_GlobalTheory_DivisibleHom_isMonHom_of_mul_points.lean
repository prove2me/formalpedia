-- Prove2me | solution 1 for GlobalTheory.DivisibleHom.isMonHom_of_mul_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:58.108907+00:00
-- url     : https://prove2.me/submissions/d335f1c7-0b02-47ca-800a-ca952600a0a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DivisibleHom
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.DivisibleHom
namespace _root_.GlobalTheory.DivisibleHom
theorem _root_.solution {G H : Over S} [GrpObj G] [GrpObj H] (e : G ⟶ H)
    (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h
    simpa using h
  have hG : (η : 𝟙_ (Over S) ⟶ G) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hH : (η : 𝟙_ (Over S) ⟶ H) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h := mul (G ⊗ G) (fst G G) (snd G G)
  rw [Hom.mul_def, lift_fst_snd, Category.id_comp, Hom.mul_def] at h
  have ht : lift (fst G G ≫ e) (snd G G ≫ e) = e ⊗ₘ e := by ext <;> simp
  refine ⟨?_, ?_⟩
  · rw [hG, hH, hone]
  · rw [h, ht]
end _root_.GlobalTheory.DivisibleHom
end GlobalTheory.DivisibleHom
