-- Prove2me | solution 1 for GlobalTheory.SemiRigid.ext_of_geometric_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:26:43.218196+00:00
-- url     : https://prove2.me/submissions/8fab837a-29d9-4a97-b949-ed806f3b5837

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Theorems.Thm_P2M_GlobalTheory_range_subset_range_equalizer___aeb7241b0453


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SemiRigid
open SplitTorus
variable {S : Scheme.{0}}
namespace GlobalTheory.SemiRigid
theorem _root_.solution {Z Y : Over S} [IsReduced Z.left] [IsSeparated Y.hom] {f g : Z ⟶ Y}
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S),
      (Over.pullback p).map f = (Over.pullback p).map g) : f = g := by
  have : Surjective (equalizer.ι f.left g.left) := ⟨fun z ↦ by
    let k := S.residueField (Z.hom z)
    let p : Spec (.of (AlgebraicClosure k)) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫
        S.fromSpecResidueField (Z.hom z)
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback Z.hom p) z
      default (Scheme.fromSpecResidueField_apply (Z.hom z) _).symm
    refine range_subset_range_equalizer_ι (pullback.fst Z.hom p) ?_ ⟨y, hy⟩
    have := congrArg (·.left ≫ pullback.fst Y.hom p) (h _ p)
    exact (pullback.lift_fst _ _ _).symm.trans (this.trans (pullback.lift_fst _ _ _))⟩
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated Y.hom
    ((Over.w f).trans (Over.w g).symm) (equalizer.ι f.left g.left) (equalizer.condition _ _))
end GlobalTheory.SemiRigid
