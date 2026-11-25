-- Prove2me | solution 1 for GlobalTheory.ExpansionTotal.exists_famPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:06:42.526587+00:00
-- url     : https://prove2.me/submissions/894e60ea-b5c5-4587-ac6f-8bd2a893473d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecLinOfSecScal
import Theorems.Thm_GlobalTheory_ExpansionTotal_globalFns
import Theorems.Thm_GlobalTheory_ExpansionTotal_toBK_fst
import Theorems.Thm_GlobalTheory_ExpansionTotal_toBK_prB
import Theorems.Thm_P2M_GlobalTheory_ExpansionTotal_fam__eq_971ca53a3ce1
import Theorems.Thm_GlobalTheory_ExpansionTotal_trF_toBK
import Theorems.Thm_GlobalTheory_FieldBaseChange_sval_pullOver
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_val_famMult
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExpansionTotal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)
namespace GlobalTheory.ExpansionTotal
theorem _root_.solution (hθ : θ.left ≫ jFK (R := R) F' = jFK (R := R) F) (k : ℕ) (S : Fam D F' k) : ∃ S' : Fam D F k,
    ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (S'.s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := by
  have hp : (toBK θ D).left ≫ (DegPre.BF D F').hom =
      (DegPre.BF D F).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) :=
    (Over.w _).trans ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm))
  let s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)) := fun α =>
    pullOver D.P.L (DegPre.famε k) hp (famφ_eq θ D α) (S.s α)
  have hs : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := fun α Z r z J hJ =>
    sval_pullOver hp (famφ_eq θ D α) (S.s α) r hJ
  refine ⟨⟨s, fun mu α u hu hc => (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩, hs⟩
  have e₁ := (gen_fe globalFns k mu α).2 u hu hc _ (𝟙 _) y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F') globalFns k mu α
  have e₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (S.fe mu α u' hu' hc') _ (toBK θ D).left y J hJ
  rw [hv' u' hu' hc' _ (toBK θ D) y J hJ, ← Over.comp_left, ← trF_toBK, Over.comp_left] at e₂
  rw [Over.id_left] at e₁
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, Category.id_comp, Category.id_comp, e₂, e₁]
  have a : (toBK θ D ≫ fst _ _).left ≫ jFK (R := R) F' =
      (𝟙 (DegPre.BF D F) ≫ fst _ _).left ≫ jFK (R := R) F := by
    rw [toBK_fst, Category.id_comp, Over.comp_left, Category.assoc, hθ]
  rw [val_famMult _ hJ, val_famMult _ hJ, a, uVal, uVal, toBK_prB, comp_cP, comp_cP, comp_cP, comp_cP,
    Category.id_comp (DegPre.prB D F)]
end GlobalTheory.ExpansionTotal
