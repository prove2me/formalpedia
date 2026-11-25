-- Prove2me | solution 1 for GlobalTheory.FamSpan.exists_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:30:15.100918+00:00
-- url     : https://prove2.me/submissions/7add27cc-37e3-4f5e-a4e0-b0e6159581a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRepresentativesModNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FamEqOnClassOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanPullDegeneration
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamSpan
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
namespace GlobalTheory.FamSpan
theorem _root_.solution (hD : IsPullDeg φ D D') (T : Over (Spec (CommRingCat.of R)))
    (a : (TF (R := R') (FractionRing R')).left ≅ T.left)
    (ha : a.hom ≫ T.hom = (TF (R := R') (FractionRing R')).hom ≫ specOf φ) :
    ∃ e : (DegPre.BF D' (FractionRing R')).left ≅ (T ⊗ D.P.A).left,
      e.hom ≫ (fst T D.P.A).left = (fst (TF (R := R') (FractionRing R')) D'.P.A).left ≫ a.hom ∧
      e.hom ≫ (snd T D.P.A).left = (DegPre.prB D' (FractionRing R')).left ≫
        (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  have P₁ : IsPullback (fst (TF (R := R') (FractionRing R')) D'.P.A).left (DegPre.prB D' (FractionRing R')).left
      (TF (R := R') (FractionRing R')).hom D'.P.A.hom := IsPullback.of_hasPullback _ _
  have P₂ : IsPullback (fst T D.P.A).left (snd T D.P.A).left T.hom D.P.A.hom := IsPullback.of_hasPullback _ _
  have P₃ := P₁.paste_vert (pull_grp hD).1.flip
  have P₄ : IsPullback ((fst (TF (R := R') (FractionRing R')) D'.P.A).left ≫ a.hom)
      ((DegPre.prB D' (FractionRing R')).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) T.hom D.P.A.hom :=
    P₃.of_iso (Iso.refl _) a (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simpa using ha.symm) (by simp)
  exact ⟨P₄.isoIsPullback _ _ P₂, P₄.isoIsPullback_hom_fst _ _ P₂, P₄.isoIsPullback_hom_snd _ _ P₂⟩
end GlobalTheory.FamSpan
