-- Prove2me | solution 1 for GlobalTheory.SS.TorOpen.exists_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:11:47.261254+00:00
-- url     : https://prove2.me/submissions/a0d20fcb-2446-4a98-8616-c37d5247b872

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMultiplicativeGroupOpenNonvanishingPolynom
import Theorems.Thm_GlobalTheory_SS_TorOpen_isIso_univPt_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.TorOpen
open GlobalTheory.SplitTorus ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
namespace GlobalTheory.SS.TorOpen
theorem _root_.solution (k L : Type) [CommRing k] [CommRing L] [Algebra k L]
    (ψ : AddMonoidAlgebra k (ULift.{0} ℤ) →+* L)
    (h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ))) (h2 : ψ.comp (algebraMap k _) = algebraMap k _)
    (t : L) (h3 : ψ (AddMonoidAlgebra.single (ULift.up 1) 1) = t) :
    ∃ jj : algOver k L ⟶ Gm (Sp k), IsOpenImmersion jj.left ∧ ∀ x y z : L →ₐ[k] k,
      (algOverHom x ≫ jj) * (algOverHom y ≫ jj) = algOverHom z ≫ jj → x t * y t = z t := by
  have hs : Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap k _))) ≫ 𝟙 (Sp k) =
      spMap (algebraMap k L) := by
    rw [h2]; exact Category.comp_id _
  let jj : algOver k L ⟶ Gm (Sp k) :=
    ptOf (A := CommRingCat.of k) (B := CommRingCat.of L) (𝟙 (Sp k)) ψ hs
  refine ⟨jj, ?_, fun x y z h => ?_⟩
  · have := isIso_univPt_left k (ULift.{0} ℤ)
    exact IsOpenImmersion.comp (Spec.map (CommRingCat.ofHom ψ))
      (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left
  · have key : ∀ w : L →ₐ[k] k,
        pull (B := CommRingCat.of k) (s := spMap (algebraMap k k)) (algOverHom w ≫ jj)
          (chi _ (ULift.up 1)) = w t := by
      intro w
      have hs' : Spec.map (CommRingCat.ofHom (((w : L →+* k).comp ψ).comp (algebraMap k _))) ≫ 𝟙 (Sp k) =
          spMap (algebraMap k k) := by
        rw [RingHom.comp_assoc, h2, w.comp_algebraMap]; exact Category.comp_id _
      have e : algOverHom w ≫ jj = ptOf (A := CommRingCat.of k) (B := CommRingCat.of k) (𝟙 (Sp k))
          ((w : L →+* k).comp ψ) hs' := by
        ext1
        change Spec.map (CommRingCat.ofHom (w : L →+* k)) ≫ Spec.map (CommRingCat.ofHom ψ) ≫
            (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left =
          Spec.map (CommRingCat.ofHom ((w : L →+* k).comp ψ)) ≫
            (univPt (A := CommRingCat.of k) (ULift.{0} ℤ) (𝟙 (Sp k))).left
        rw [← Category.assoc, ← Spec.map_comp]
        rfl
      rw [e, pull_ptOf, ev_chi]
      exact congrArg w h3
    rw [← key, ← key, ← key, ← h]
    exact (pull_mul_chi (B := CommRingCat.of k) (s := spMap (algebraMap k k)) _ _ _).symm
end GlobalTheory.SS.TorOpen
