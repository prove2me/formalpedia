-- Prove2me | solution 1 for GlobalTheory.geometricallyConnected_of_isPullback_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:58.10199+00:00
-- url     : https://prove2.me/submissions/5a4bd17d-b426-4324-8618-759ed282fa5d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
theorem _root_.solution {X Y X' Y' : Scheme.{0}}
    {a : X' ⟶ X} {p : X' ⟶ Y'} {q : X ⟶ Y} {s : Y' ⟶ Y} (h : IsPullback a p q s)
    [Surjective s] [GeometricallyConnected p] : GeometricallyConnected q := by
  refine ⟨fun K _ t Z fst snd hZ => ?_⟩
  obtain ⟨z, -⟩ := (pullback.snd s t).surjective (Nonempty.some inferInstance)
  let e := (pullback s t).fromSpecResidueField z
  let u := e ≫ pullback.fst s t
  let v := e ≫ pullback.snd s t
  have huv : v ≫ t = u ≫ s := by simp only [u, v, Category.assoc, pullback.condition]
  have hbig : IsPullback (pullback.fst snd v ≫ fst) (pullback.snd snd v) q (u ≫ s) :=
    huv ▸ (IsPullback.of_hasPullback snd v).paste_horiz hZ
  have hsmall := IsPullback.of_right
    (h₁₁ := h.lift (pullback.fst snd v ≫ fst) (pullback.snd snd v ≫ u)
      (by simpa only [Category.assoc] using hbig.w))
    (by simpa using hbig) (by simp) h
  have hc : ConnectedSpace ↥(pullback snd v) :=
    GeometricallyConnected.geometrically_connectedSpace u _ _ hsmall
  have hv : Surjective v := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact (pullback.fst snd v).surjective.connectedSpace (pullback.fst snd v).continuous
end GlobalTheory
