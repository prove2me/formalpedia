-- Prove2me | solution 1 for GlobalTheory.SemiAbelianCompare.geometricallyConnected_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:31.18479+00:00
-- url     : https://prove2.me/submissions/4e5bbbff-6c13-4660-ad7e-0f90b953775b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_GroupRingConst_powChar_apply
import Theorems.Thm_GlobalTheory_GroupRingConst_pt_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GroupRingConst.powChar_apply
attribute [local simp] GlobalTheory.GroupRingConst.pt_single
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G
open GlobalTheory GlobalTheory.SemiAbelianCompare
namespace GlobalTheory.SemiAbelianCompare
theorem _root_.solution {X Y X' Y' : Scheme.{u}}
    {a : X' ⟶ X} {p : X' ⟶ Y'} {q : X ⟶ Y} {s : Y' ⟶ Y} (h : IsPullback a p q s)
    [Surjective s] [GeometricallyConnected p] : GeometricallyConnected q := by
  refine ⟨fun k _ y Z fst snd hZ => ?_⟩
  obtain ⟨w⟩ : Nonempty ↥(pullback y s) := by
    obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨w, -⟩ := (pullback.fst y s).surjective pt
    exact ⟨w⟩
  let r := (pullback y s).fromSpecResidueField w
  let b := r ≫ pullback.fst y s
  let x := r ≫ pullback.snd y s
  have hbx : b ≫ y = x ≫ s := by simp only [b, x, Category.assoc, pullback.condition]
  have hb : Surjective b := ⟨fun z => ⟨_, Subsingleton.elim (b (default : PrimeSpectrum _)) z⟩⟩
  have big : IsPullback (pullback.fst snd b ≫ fst) (pullback.snd snd b) q (x ≫ s) :=
    hbx ▸ (IsPullback.of_hasPullback snd b).paste_horiz hZ
  have sq : IsPullback (h.lift (pullback.fst snd b ≫ fst) (pullback.snd snd b ≫ x)
      (big.w.trans (Category.assoc _ _ _).symm)) (pullback.snd snd b) p x :=
    IsPullback.of_right (by rw [h.lift_fst]; exact big) (h.lift_snd _ _ _) h
  have : ConnectedSpace ↥(pullback snd b) :=
    GeometricallyConnected.geometrically_connectedSpace (f := p) x _ _ sq
  exact (pullback.fst snd b).surjective.connectedSpace (pullback.fst snd b).continuous
end GlobalTheory.SemiAbelianCompare
