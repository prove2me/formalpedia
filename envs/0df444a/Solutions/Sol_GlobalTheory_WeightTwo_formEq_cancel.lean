-- Prove2me | solution 1 for GlobalTheory.WeightTwo.formEq_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:55.765637+00:00
-- url     : https://prove2.me/submissions/4c38e900-2b86-426a-80da-6a583bd1532e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecFinsum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
open GlobalTheory GlobalTheory.WeightTwo
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace GlobalTheory.WeightTwo
theorem _root_.solution (k l : ℕ) (α β : D.X) :
    FormEq (Sum.elim (fun a => (D.P.A ◁ g.pG).left ≫ Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
        (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i) a)
        (fun a => (snd D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.Oφ g.pG β a))
      (Sum.elim (Sum.elim (DegPre.famε k) (DegPre.famε l)) Oinvε)
      (Sum.elim (fun i => (fst D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.famφB α i)
        (fun _ : Unit => (snd D.P.A _ ≫ g.pG).left))
      (Sum.elim (DegPre.famε k) (fun _ => (l : ℤ))) := by
  intro U _ h
  have e₁ : (D.P.A ◁ g.pG).left ≫ (fst D.P.A D.P.A).left = (fst D.P.A _).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have e₂ : (D.P.A ◁ g.pG).left ≫ (snd D.P.A D.P.A).left = (snd D.P.A _).left ≫ g.pG.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  have f₀ : g.pG.left ≫ D.famφB β 0 = g.pG.left := Category.comp_id _
  have f₁ : g.pG.left ≫ D.famφB β 1 = D.Oφ g.pG β 0 := by
    change (g.pG ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c β)).left = (padd D.P.A g.pG (toUnit _ ≫ D.c β)).left
    congr 1
    simp only [padd, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
  have f₂ : g.pG.left ≫ D.famφB β 2 = D.Oφ g.pG β 1 := by
    change (g.pG ≫ toUnit _ ≫ D.c β).left = (toUnit _ ≫ D.c β).left
    rw [comp_toUnit_assoc]
  have f₃ : g.pG.left ≫ D.famφB β 3 = D.Oφ g.pG β 3 := by
    change (g.pG ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
    rw [comp_toUnit_assoc]
  have f₄ : D.Oφ g.pG β 2 = g.pG.left := rfl
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, reassoc_of% e₁, reassoc_of% e₂,
    Finset.univ_unique, Finset.prod_singleton]
  rw [_root_.mul_assoc]
  congr 1
  rw [Fin.prod_univ_four, Fin.prod_univ_four, f₀, f₁, f₂, f₃, f₄, Over.comp_left _ _ _ (snd D.P.A _) g.pG]
  generalize h (_ ≫ g.pG.left) = a
  generalize h (_ ≫ D.Oφ g.pG β 0) = b
  generalize h (_ ≫ D.Oφ g.pG β 1) = c
  generalize h (_ ≫ D.Oφ g.pG β 3) = d
  change a ^ ((l : ℤ) - 1) * b ^ (1 : ℤ) * c ^ (-1 : ℤ) * d ^ (1 : ℤ) *
    (b ^ (-1 : ℤ) * c ^ (1 : ℤ) * a ^ (1 : ℤ) * d ^ (-1 : ℤ)) = a ^ (l : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module
end GlobalTheory.WeightTwo
