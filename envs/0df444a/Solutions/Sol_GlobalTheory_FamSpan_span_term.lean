-- Prove2me | solution 1 for GlobalTheory.FamSpan.span_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:42:12.172243+00:00
-- url     : https://prove2.me/submissions/63fc64ad-576f-49ec-b461-c3558b5ada97

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
import Theorems.Thm_GlobalTheory_FamSpan_span_sec
import Theorems.Thm_P2M_GlobalTheory_FamSpan_fam_B_comm_3ace86c881b8
import Theorems.Thm_GlobalTheory_FamSpan_base_eq
import Theorems.Thm_GlobalTheory_FamSpan_exists_iso
import Theorems.Thm_GlobalTheory_IntegralCoord_specMap_appTop
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


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
theorem _root_.solution (hD : IsPullDeg φ D D') (k : ℕ) (x : D'.X) {m : ℕ} (b g : Fin m → D.SecB k (hD.xe x))
    (hb : IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ))))
      (A := D.P.A) _ (fun i => DVR.pullSec D.P.L (D.famφB (hD.xe x)) (DegPre.famε k) (b i)
        (snd (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ)))) D.P.A).left))
    (r : Fin m → R) (hr : ∀ i, algebraMap R' (FractionRing R') (φ (r i)) ≠ 0)
    (hg : ∀ i j, (g i).f j = resTop _ (scal D.P.A.hom (r i)) * (b i).f j) (g' : Fin m → D'.SecB k x)
    (hg' : ∀ i (y : (DegPre.BF D' (FractionRing R')).left) J J', Good D.P.L y J → Good D'.P.L y J' →
      sval (g i) ((𝟙 _ ≫ (DegPre.prB D' (FractionRing R')).left) ≫
        (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) y J =
      (fac hD.w (D'.famφB x) (DegPre.famε k) (𝟙 _ ≫ (DegPre.prB D' (FractionRing R')).left) y J J').val *
        sval (g' i) (𝟙 _ ≫ (DegPre.prB D' (FractionRing R')).left) y J')
    (G : Fin m → LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' (FractionRing R') x) (DegPre.famε k)))
    (hG : ∀ i, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') x) (DegPre.famε k) (G i) (D'.famφB x)
      (DegPre.famε k) (g' i) (DegPre.prB D' (FractionRing R')).left 1)
    (s : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' (FractionRing R') x) (DegPre.famε k))) :
    ∃ c : Fin m → FractionRing R', ∀ j, s.f j = ∑ i, resTop _ (DVR.gF D' (FractionRing R') (c i)) * (G i).f j := by
  obtain ⟨e, e₁, e₂⟩ := exists_iso hD
    (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ)))) (Iso.refl _)
    ((Category.id_comp _).trans (base_eq φ).symm)
  replace e₁ := e₁.trans (Category.comp_id _)
  obtain ⟨c, hc⟩ := span_sec ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB (famφB_comm hD x) _
    (DegPre.prB D' (FractionRing R')).left e.inv e.hom e.hom_inv_id (by rw [← e₂, e.inv_hom_id_assoc])
    (DVR.GC.famφ_eq D' (FractionRing R') x) b g
    (fun c => (fst (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ)))) D.P.A).left.appTop.hom c)
    (fun s => (hb s).exists) (fun i => scal D.P.A.hom (r i)) hg g' hg' G hG
    (fun i => DVR.gF D' (FractionRing R') (algebraMap R' (FractionRing R') (φ (r i)))⁻¹) (fun i => by
      have q : (DegPre.prB D' (FractionRing R')).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.P.A.hom =
          (fst (TF (R := R') (FractionRing R')) D'.P.A).left ≫
            Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp φ)) := by
        rw [← Category.assoc, ← e₂, ← e₁, Category.assoc, Category.assoc, Over.w]
        exact congrArg _ (Over.w _).symm
      have q' : ((DegPre.prB D' (FractionRing R')).left ≫
          (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).appTop.hom (scal D.P.A.hom (r i)) =
          DVR.gF D' (FractionRing R') (algebraMap R' (FractionRing R') (φ (r i))) := by
        have := congrArg (fun t => t.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (r i))) q
        refine Eq.trans this ?_
        refine congrArg (fst (TF (R := R') (FractionRing R')) D'.P.A).left.appTop.hom ?_
        refine (IntegralCoord.specMap_appTop _ _).trans (congrArg _ (congrArg _ ?_))
        exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) (r i)
      rw [q', ← map_mul, inv_mul_cancel₀ (hr i), map_one]) s
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R'))).hom.hom (c i) *
    (algebraMap R' (FractionRing R') (φ (r i)))⁻¹, fun j => (hc j).trans (Finset.sum_congr rfl fun i _ => ?_)⟩
  refine congrArg₂ (· * ·) (congrArg _ ?_) rfl
  rw [map_mul]
  refine congrArg₂ (· * ·) ?_ rfl
  have := congrArg (fun t => t.appTop.hom (c i)) e₁
  refine Eq.trans this ?_
  exact congrArg (fst (TF (R := R') (FractionRing R')) D'.P.A).left.appTop.hom
    (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R'))) (c i)).symm
end GlobalTheory.FamSpan
