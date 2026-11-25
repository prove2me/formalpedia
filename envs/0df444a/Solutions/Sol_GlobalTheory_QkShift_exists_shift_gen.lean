-- Prove2me | solution 1 for GlobalTheory.QkShift.exists_shift_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:51:30.151618+00:00
-- url     : https://prove2.me/submissions/e83dc120-ac4e-4aaa-94cf-1659b00239c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsShiftGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_powGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.QkShift
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.QkShift
theorem _root_.solution (n : ℕ) (g : GtPtF D F) (z : D.X) (b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = g.b * cP D _ z)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε n))) (hw : w.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b') (DegPre.lineε n)), w₂.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (y : Z) (J), Good D.P.L y J →
        val w₂ r y J = val w r y J *
          (val (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) (r ≫ jFK (R := R) F) y J *
            val (GeneratorPullback.powGen D.P.L _ _ D.rigK n) (r ≫ jFK (R := R) F) y J) * val (g.s z) r y J ^ n := by
  subst hb
  obtain ⟨w₂, h₂, v₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F (g.b * cP D _ z)) (ε' := DegPre.lineε n)
    (fun U _ h => by
      have a₁ : ∀ χ, jFK (R := R) F ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (n : ℤ) * h g.b.left ^ (-(n : ℤ)) * _ *
        (h (cP D _ z * g.b).left ^ ((n : ℤ) * -1) * h (cP D _ z).left ^ ((n : ℤ) * 1) * h g.b.left ^ ((n : ℤ) * 1) *
          h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((n : ℤ) * -1)) =
        h (1 : TF (R := R) F ⟶ D.P.A).left ^ (n : ℤ) * h (g.b * cP D _ z).left ^ (-(n : ℤ))
      rw [mul_comm g.b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ w (LB.pullGen D.P.L _ _
      (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) (GeneratorPullback.powGen D.P.L _ _ D.rigK n)) (jFK (R := R) F)))
      (GeneratorPullback.powGen D.P.L _ _ (g.s z) n))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hw (pullGen_isGen _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen z) n)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) n)) _)) (powGen_isGen _ _ _ _ (g.isGen z) n))
  refine ⟨w₂, h₂, fun Z r y J hJ => (v₂ Z r y J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (val_mul hJ _ _ _)))) ?_))⟩
  exact map_pow _ _ _
end GlobalTheory.QkShift
