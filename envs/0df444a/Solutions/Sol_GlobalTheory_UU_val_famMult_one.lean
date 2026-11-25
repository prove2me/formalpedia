-- Prove2me | solution 1 for GlobalTheory.UU.val_famMult_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:57:28.948621+00:00
-- url     : https://prove2.me/submissions/4d9fffb0-fef1-45ad-9277-e98e47f6e6c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FamFEOneOfPsiRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_val_famMult
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv


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
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu α : D.X) :
    val (DegPre.famMult D F 1 mu α) σ.left z J * val (D.psi α) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (mu + α)) (σ.left ≫ jFK (R := R) F) z J := by
  have e : val (D.tau mu α) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (mu + α)) (σ.left ≫ jFK (R := R) F) z J * (val (D.psi mu) (σ.left ≫ jFK (R := R) F) z J)⁻¹ *
        (val (D.psi α) (σ.left ≫ jFK (R := R) F) z J)⁻¹ * (val D.rigK (σ.left ≫ jFK (R := R) F) z J)⁻¹ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) 1) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi mu) (σ.left ≫ jFK (R := R) F) z J := congrArg (gm _ z _) (pow_one _)
  have p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK 1) (σ.left ≫ jFK (R := R) F) z J =
      val D.rigK (σ.left ≫ jFK (R := R) F) z J := congrArg (gm _ z _) (pow_one _)
  rw [val_famMult σ hJ, e, p₁, p₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.UU
