-- Prove2me | solution 1 for GlobalTheory.PhiSpec.generic_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:59.641855+00:00
-- url     : https://prove2.me/submissions/9f9d1975-d36e-48b3-91b4-bcf4baec1028

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
import Theorems.Thm_GlobalTheory_PhiSpec_trT_fst
import Theorems.Thm_GlobalTheory_PhiSpec_trT_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_of_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_uVal_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PhiSpec
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
variable {D}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.PhiSpec
theorem _root_.solution {k : ℕ} (gp : GtPt D T) (ρ : TF (R := R) F ⟶ T) (p : QkPt D F k)
    (hp : GtPt.IsPullF F ρ.left gp p.g)
    (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k)))
    (ν : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (hν : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      val ν r z J = val w (r ≫ ρ.left) z J)
    (s s₂ : Fam D F k) (g g₂ : ∀ α, SecT D T k α) (H : PhiVal p ν s.s s₂.s) (HT : PhiT p.y gp w g g₂)
    (hs : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s.s α)
      (fun i => (snd T D.P.A).left ≫ D.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.P.A).left 1) (β : D.X) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D F β) (DegPre.famε k) (s₂.s β)
      (fun i => (snd T D.P.A).left ≫ D.famφB β i) (DegPre.famε k) (g₂ β) (ρ ▷ D.P.A).left 1 := by
  refine SectionScalarValuation.secScal_of_sval D.P.isLB fun y J hJ => ?_
  have hb : ρ ≫ gp.b = p.g.b := Over.OverMorphism.ext hp.1.symm
  have e₁ := H (β - p.y) β (sub_add_cancel _ _) _ (𝟙 _) y J hJ
  have e₂ := HT (β - p.y) β (sub_add_cancel _ _) _ (ρ ▷ D.P.A) y J hJ
  have e₃ := SectionScalarValuation.secScal_sval (hs (β - p.y)) (DegPre.trPt D F p.g.b).left y hJ
  have t : ρ ▷ D.P.A ≫ trT D gp.b = DegPre.trPt D F p.g.b ≫ ρ ▷ D.P.A := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, trT_fst, Category.assoc, whiskerRight_fst, ← Category.assoc, tr_fst]
    · rw [Category.assoc, trT_snd, MonObj.comp_mul, whiskerRight_snd, Category.assoc, whiskerRight_snd, tr_pr,
        ← Category.assoc, whiskerRight_fst, Category.assoc, hb]
  have u : uT D k (β - p.y) gp.b (ρ ▷ D.P.A) y J = uVal D F k (β - p.y) p.g.b (𝟙 _) y J := by
    rw [uVal_id, uT, ← Category.assoc, whiskerRight_fst, Category.assoc, hb, whiskerRight_snd]
  have v₁ := (val_corr hJ (hp.2 (β - p.y)) (fst (TF (R := R) F) D.P.A).left).trans (val_pull hJ _ _ _)
  have v₂ := hν _ (fst (TF (R := R) F) D.P.A).left y J hJ
  rw [t, u, whiskerRight_fst] at e₂
  rw [Category.id_comp, Category.id_comp, val_mul hJ, v₁, v₂, ← e₃] at e₁
  rw [Category.id_comp]
  exact e₂.trans e₁.symm
end GlobalTheory.PhiSpec
