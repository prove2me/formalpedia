-- Prove2me | solution 1 for GlobalTheory.StalkLimit.exists_spread
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:16:09.864065+00:00
-- url     : https://prove2.me/submissions/e1afe876-83ee-42f5-8227-9dfe26175915

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_P2M_GlobalTheory_StalkLimit_cone___fst_b63b7be6912f
import Theorems.Thm_GlobalTheory_StalkLimit_nonempty_isLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.StalkLimit
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
variable {S X : Scheme.{u}} (x : S) (p : X ⟶ S)
variable {x p} {X' : Scheme.{u}} {φ : X' ⟶ X} {p' : X' ⟶ Spec (S.presheaf.stalk x)}
namespace GlobalTheory.StalkLimit
theorem _root_.solution [QuasiCompact p] [QuasiSeparated p] (h : IsPullback φ p' p (S.fromSpecStalk x))
    {Y : Scheme.{u}} (q : Y ⟶ S) [LocallyOfFinitePresentation q] (a : X' ⟶ Y) (ha : a ≫ q = φ ≫ p) :
    ∃ (V : S.Opens) (_ : x ∈ V) (_ : IsAffineOpen V) (w : X' ⟶ pullback p V.ι) (g : pullback p V.ι ⟶ Y),
      w ≫ pullback.fst p V.ι = φ ∧ w ≫ g = a ∧ g ≫ q = pullback.fst p V.ι ≫ p := by
  obtain ⟨hc⟩ := nonempty_isLimit h
  have hcpt : ∀ V : AffNhd x, CompactSpace ((diagram x p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have hqs : ∀ V : AffNhd x, QuasiSeparatedSpace ((diagram x p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p V.1.ι)).mp inferInstance
  let t : diagram x p ⟶ (Functor.const (AffNhd x)).obj S :=
    { app := fun V => pullback.fst p V.1.ι ≫ p
      naturality := fun V W i => by
        dsimp
        rw [Category.comp_id, ← Category.assoc, diagram_map_fst] }
  have ht : (cone h).π ≫ t = (Functor.const _).map (a ≫ q) := by
    apply NatTrans.ext
    funext V
    simp only [NatTrans.comp_app, Functor.const_map_app, t]
    rw [← Category.assoc, cone_π_fst, ha]
  obtain ⟨V, g, hg₁, hg₂⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (diagram x p) t q (cone h) hc a ht
  exact ⟨V.1, V.2.1, V.2.2, (cone h).π.app V, g, cone_π_fst h V, hg₁, hg₂⟩
end GlobalTheory.StalkLimit
