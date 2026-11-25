-- Prove2me | solution 1 for GlobalTheory.PhiSpec.secMaps_of_sval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:47.863204+00:00
-- url     : https://prove2.me/submissions/a20dcd2b-2270-4176-9f0d-8d7f00c63ddc

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
import Theorems.Thm_GlobalTheory_PhiSpec_gs_of_charts
import Theorems.Thm_GlobalTheory_PhiSpec_liftB_fam
import Theorems.Thm_GlobalTheory_PhiSpec_fam_comm
import Theorems.Thm_GlobalTheory_PhiPull_liftB_fam
import Theorems.Thm_P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_fam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {T : Over (Spec (CommRingCat.of R))} {F : Type} [Field F] [Algebra (FractionRing R') F]
  (hD : IsPullDeg φ D D') {h : (TF (R := R') F).left ⟶ T.left} (hT : (TF (R := R') F).hom ≫ spMap φ = h ≫ T.hom)
  {Θ : (DegPre.BF D' F).left ⟶ (T ⊗ D.P.A).left}
  (hΘ₁ : Θ ≫ (fst T D.P.A).left = (fst (TF (R := R') F) D'.P.A).left ≫ h)
  (hΘ₂ : Θ ≫ (snd T D.P.A).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}
include hΘ₂
namespace GlobalTheory.PhiSpec
theorem _root_.solution {k : ℕ} (x : D'.X) (s : SecT D T k (hD.xe x))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k)))
    (H : ∀ (T' : Over (Spec (CommRingCat.of R'))) (ρ : T' ⟶ DegPre.BF D' F) (z : T'.left) (J J'),
      Good D.P.L z J → Good D'.P.L z J' → ∀ (Ω : (T' ⟶ D'.P.A) → (T'.left.presheaf.stalk z)ˣ),
      (Ω = fun x => gw hD.w x.left z (J (x.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' x.left)) →
      @Eq (T'.left.presheaf.stalk z) (sval s (liftB hT hΘ₁ ρ).left z J)
      ((Ω (ρ ≫ DegPre.prB D' F) ^ ((k : ℤ) - 1) * Ω (cP D' T' x * (ρ ≫ DegPre.prB D' F)) * (Ω (cP D' T' x))⁻¹ *
        Ω 1).val * sval s' ρ.left z J')) : SecMaps hD Θ x s s' := by
  intro Z r z p q hp hq
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  let ρ : Over.mk (r ≫ (DegPre.BF D' F).hom) ⟶ DegPre.BF D' F := Over.homMk r rfl
  have e := H _ ρ z J J' hJ hJ' _ rfl
  have pr := prod_fam D' F ρ x k (fun q => gw hD.w q z (J (q ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (J' q))
  refine gs_of_charts ((isGen_iff hD.w).1 hD.w_gen) (fam_comm hD hT hΘ₁ hΘ₂ x) s s' r z hp hq
    (p' := fun κ => J ((r ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (q' := fun κ => J' (r ≫ DegPre.famφ D' F x κ))
    (fun κ => hJ ((r ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) (fun κ => hJ' (r ≫ DegPre.famφ D' F x κ)) ?_
  refine (sval_of s (liftB hT hΘ₁ ρ).left z J _
    (fun κ => congrArg J (liftB_fam hD hT hΘ₁ hΘ₂ ρ x κ))).symm.trans (e.trans ?_)
  exact congrArg₂ (· * ·) (congrArg Units.val pr.symm) rfl
end GlobalTheory.PhiSpec
