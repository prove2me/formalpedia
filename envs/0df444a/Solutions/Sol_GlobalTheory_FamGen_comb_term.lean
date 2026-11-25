-- Prove2me | solution 1 for GlobalTheory.FamGen.comb_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:12:25.552559+00:00
-- url     : https://prove2.me/submissions/13ea60a2-a32b-4a6c-aff5-fdeb3b2f64bc

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
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRepresentativesModNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FamEqOnClassOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntegralDegenerationFamilyBaseChangeExtensionFie
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanPullDegeneration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanGenerateValuationRings
import Theorems.Thm_GlobalTheory_FamGen_constVal_mul
import Theorems.Thm_GlobalTheory_IntegralCoord_lin_of_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_lin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamGen
open GlobalTheory.FamSpan GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FamGen
theorem _root_.solution {S : Type} [CommRing S] (σ : R →+* S) (ιF : S →+* F)
    (ρ : TF (R := R) F ⟶ Over.mk (specOf σ)) (hρ : ρ.left = specOf ιF) (k : ℕ) (α : D.X) {m : ℕ}
    (b g : Fin m → D.SecB k α)
    (hb : IsSecBasis (T := Over.mk (specOf σ)) (A := D.P.A) _ (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε k)
      (b i) (snd (Over.mk (specOf σ)) D.P.A).left))
    (r : Fin m → R) (hr : ∀ i, IsUnit (σ (r i)))
    (hg : ∀ i j, (g i).f j = resTop _ (scal D.P.A.hom (r i)) * (b i).f j)
    (G : Fin m → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (hG : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (G i) (D.famφB α)
      (DegPre.famε k) (g i) (DegPre.prB D F).left 1)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (sg : LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k)))
    (hsg : GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) s
      (fun i => (snd (Over.mk (specOf σ)) D.P.A).left ≫ D.famφB α i) (DegPre.famε k) sg (ρ ▷ D.P.A).left 1) :
    ∃ c : Fin m → S, ∀ j, s.f j = ∑ i, resTop _ (DVR.gF D F (ιF (c i))) * (G i).f j := by
  obtain ⟨c, hc, -⟩ := hb sg
  choose u hu using fun i => (hr i).exists_left_inv
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i,
    IntegralCoord.lin_of_sval D.P.isLB _ G fun y J hJ => ?_⟩
  have a₁ : (𝟙 _ ≫ (ρ ▷ D.P.A).left) ≫ (snd (Over.mk (specOf σ)) D.P.A).left = 𝟙 _ ≫ (DegPre.prB D F).left := by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_snd]
  have a₂ : (𝟙 _ ≫ (ρ ▷ D.P.A).left) ≫ (fst (Over.mk (specOf σ)) D.P.A).left =
      (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) ≫ specOf ιF := by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hρ, Category.assoc]
  have a₃ : (𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) ≫ specOf ιF) ≫ specOf σ := by
    rw [← a₂, ← a₁]
    simp only [Category.assoc]
    rw [Over.w (snd (Over.mk (specOf σ)) D.P.A)]
    exact congrArg _ (congrArg _ (Over.w (fst (Over.mk (specOf σ)) D.P.A)).symm)
  rw [← secScal_sval hsg _ y hJ]
  refine (sval_lin (fun i => scal (fst (Over.mk (specOf σ)) D.P.A).left
    ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i))) _ (fun j => (hc j).trans (Finset.sum_congr rfl fun i _ =>
      congrArg₂ (· * ·) (congrArg _ (congrArg _ (Iso.hom_inv_id_apply _ _).symm)) rfl)) _ y hJ).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  have e₃ : sval (g i) (𝟙 _ ≫ (DegPre.prB D F).left) y J =
      gs (𝟙 _ ≫ (DegPre.prB D F).left) y ⊤ (scal D.P.A.hom (r i)) * sval (b i) (𝟙 _ ≫ (DegPre.prB D F).left) y J := by
    have hm := hJ.mem (D.famφB α) (𝟙 _ ≫ (DegPre.prB D F).left)
    exact (congrArg (gs _ y _) (hg i _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hm _) rfl))
  have e₄ : gs (𝟙 _) y ⊤ (DVR.gF D F (ιF ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i))) =
      constVal (𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left) y
        (ιF ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (c i) * u i)) :=
    gs_scal (fst (TF (R := R) F) D.P.A).left _ y _
  rw [sval_pullSec _ _ _ _ _ y hJ, a₁, ← secScal_sval (hG i) _ y hJ, e₃, e₄, gs_scal, gs_scal, a₂, a₃,
    constVal_specMap, constVal_specMap, constVal_specMap, ← _root_.mul_assoc, ← constVal_mul, ← map_mul,
    _root_.mul_assoc _ (u i), hu, _root_.mul_one]
end GlobalTheory.FamGen
