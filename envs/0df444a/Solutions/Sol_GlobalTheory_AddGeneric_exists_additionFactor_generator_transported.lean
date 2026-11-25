-- Prove2me | solution 1 for GlobalTheory.AddGeneric.exists_additionFactor_generator_transported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:12.057637+00:00
-- url     : https://prove2.me/submissions/f6264536-22fa-4011-8cad-3ce9a022c768

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsAdditionFactorGeneratorTransported
import Theorems.Thm_GlobalTheory_AddGeneric_exists_additionFactor_generator_value
import Theorems.Thm_GlobalTheory_CubTransport_exists_pmaps
import Theorems.Thm_GlobalTheory_DegPull_exists_pmaps
import Theorems.Thm_GlobalTheory_DegPull_pmaps_val
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_mul


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
open GlobalTheory GlobalTheory.AddGeneric
namespace GlobalTheory.AddGeneric
theorem _root_.solution {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G)
    {A : Over S'} [GrpObj A] [IsCommMonObj A] {Φ : A.left ⟶ G.left} (hw : Φ ≫ G.hom = A.hom ≫ f)
    (mul : ∀ (T : Over S') (x y : T ⟶ A), toBase hw (x * y) = toBase hw x * toBase hw y)
    {L' : LB A.left} (hL' : L'.IsLB) (u : LB.Iso L' (P.L.L.pull Φ)) (hu : PGen u) {Y : Over S'} (p q s d : Y ⟶ A)
    (hs : s = p * q) (hd : d = p * q⁻¹) :
    ∃ a : LB.Gen (LB.LinComb L' (K := Fin 4) ![p.left, q.left, s.left, d.left] ![2, 2, -1, -1]), a.IsGen ∧
      ∀ (T : Over S') (ρ : T ⟶ Y) (z : T.left) (J J'), Good P.L.L z J → Good L' z J' →
        ∀ W : (T ⟶ A) → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw u x.left z (J (x.left ≫ Φ)) (J' x.left)) →
        @id (T.left.presheaf.stalk z)ˣ (kap0 P.c P.sym (T := Over.mk (T.hom ≫ f)) z J (toBase hw (ρ ≫ p)) (toBase hw (ρ ≫ q))) =
          W (ρ ≫ p) ^ 2 * W (ρ ≫ q) ^ 2 * (W ((ρ ≫ p) * (ρ ≫ q)))⁻¹ * (W ((ρ ≫ p) * (ρ ≫ q)⁻¹))⁻¹ *
            val a ρ.left z J' := by
  subst hs hd
  obtain ⟨t, ht, hv⟩ := exists_additionFactor_generator_value P (toBase hw p) (toBase hw q)
  have hψ : ∀ k : Fin 4, ![p.left, q.left, (p * q).left, (p * q⁻¹).left] k ≫ Φ = 𝟙 Y.left ≫
      ![(toBase hw p).left, (toBase hw q).left, (toBase hw p * toBase hw q).left,
        (toBase hw p * (toBase hw q)⁻¹).left] k := by
    intro k
    rw [Category.id_comp]
    have e : toBase hw (p * q⁻¹) = toBase hw p * (toBase hw q)⁻¹ :=
      (mul _ _ _).trans (congrArg _ (map_inv (toBaseHom mul Y) q))
    rw [← e, ← mul]
    fin_cases k <;> rfl
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps hu P.L.isLB hL' (𝟙 Y.left) hψ t ht
  refine ⟨a, ha, fun T ρ z J J' hJ hJ' W hW => ?_⟩
  have e₁ := DegPull.pmaps_val hψ H ρ.left z hJ hJ'
  let ρ' : Over.mk (T.hom ≫ f) ⟶ Over.mk (Y.hom ≫ f) := Over.homMk ρ.left (by
    show ρ.left ≫ Y.hom ≫ f = T.hom ≫ f
    rw [← Category.assoc, Over.w ρ])
  have e₂ := hv _ ρ' z J hJ
  have e₃ : ∀ x : Y ⟶ A, ρ' ≫ toBase hw x = toBase hw (ρ ≫ x) := fun x =>
    Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [e₃, e₃] at e₂
  rw [Category.comp_id] at e₁
  refine e₂.symm.trans (e₁.trans (congrArg (· * val a ρ.left z J') ?_))
  rw [← GrpObj.comp_inv, ← MonObj.comp_mul, ← MonObj.comp_mul, ← zpow_neg_one (W _), ← zpow_neg_one (W _),
    ← zpow_natCast (W _), ← zpow_natCast (W _), hW, hW, hW, hW, Fin.prod_univ_four]
  rfl
end GlobalTheory.AddGeneric
