-- Prove2me | solution 1 for GlobalTheory.GeneratorFunctor.isRepresentable_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:44:32.247371+00:00
-- url     : https://prove2.me/submissions/e927cade-ba4b-471c-8c24-3216c1a77f59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections

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
open GlobalTheory
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GeneratorFunctor
theorem _root_.solution (F : Scheme.{0}ᵒᵖ ⥤ Type)
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) {J : Type} (X : J → Scheme.{0})
    (x : ∀ j, F.obj (op (X j))) (W : ∀ (_ : J) (Z : Scheme.{0}), F.obj (op Z) → Z.Opens)
    (hW : ∀ j (Z : Scheme.{0}) (y : F.obj (op Z)) (Z' : Scheme.{0}) (a : Z' ⟶ Z),
      Set.range a ⊆ (W j Z y : Set Z) ↔ ∃ g : Z' ⟶ X j, F.map g.op (x j) = F.map a.op y)
    (inj : ∀ j (Z : Scheme.{0}) (g g' : Z ⟶ X j), F.map g.op (x j) = F.map g'.op (x j) → g = g')
    (cov : ∀ (Z : Scheme.{0}) (y : F.obj (op Z)) (z : Z), ∃ j, z ∈ W j Z y) :
    F.IsRepresentable := by
  let F' : Sheaf Scheme.zariskiTopology.{0} (Type) := ⟨F, (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩
  let f : ∀ j, yoneda.obj (X j) ⟶ F'.1 := fun j => yonedaEquiv.symm (x j)
  have hfa : ∀ j (Z : Scheme.{0}) (g : Z ⟶ X j), (f j).app (op Z) g = F.map g.op (x j) :=
    fun j Z g => rfl
  have hι : ∀ j (Z : Scheme.{0}) (y : F.obj (op Z)),
      ∃ g : (W j Z y).toScheme ⟶ X j, F.map g.op (x j) = F.map (W j Z y).ι.op y :=
    fun j Z y => (hW j Z y _ _).1 (by simp)
  have hf : ∀ j, IsOpenImmersion.presheaf (f j) := by
    intro j
    refine MorphismProperty.relative.of_exists fun Z g => ?_
    obtain ⟨y, rfl⟩ := yonedaEquiv.symm.surjective g
    obtain ⟨c, hc⟩ := hι j Z y
    refine ⟨(W j Z y).toScheme, yoneda.map c, (W j Z y).ι, ?_, inferInstance⟩
    refine IsPullback.of_forall_isPullback_app fun T => ?_
    obtain ⟨T⟩ := T
    rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext (a : T ⟶ _)
      change F.map (a ≫ c).op (x j) = F.map (a ≫ (W j Z y).ι).op y
      simp only [op_comp, Functor.map_comp_apply, hc]
    · rintro (a : T ⟶ _) (a' : T ⟶ _) ⟨-, h⟩
      exact (cancel_mono (W j Z y).ι).1 h
    · rintro (g : T ⟶ _) (a : T ⟶ _) h
      replace h : F.map g.op (x j) = F.map a.op y := h
      have hr := (hW j Z y T a).2 ⟨g, h⟩
      let l := IsOpenImmersion.lift (W j Z y).ι a (by simpa using hr)
      have hl : l ≫ (W j Z y).ι = a := IsOpenImmersion.lift_fac _ _ _
      refine ⟨l, inj j T _ _ ?_, hl⟩
      change F.map (l ≫ c).op (x j) = _
      rw [h, ← hl]
      simp only [op_comp, Functor.map_comp_apply, hc]
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    refine ⟨fun {Z} y => ?_⟩
    rw [Scheme.mem_grothendieckTopology_iff]
    refine ⟨Z.openCoverOfIsOpenCover (fun j => W j Z y) ?_, ?_⟩
    · exact eq_top_iff.2 fun z _ => Opens.mem_iSup.2 (cov Z y z)
    · rintro _ _ ⟨j⟩
      obtain ⟨c, hc⟩ := hι j Z y
      refine ⟨(Sigma.ι (fun j => yoneda.obj (X j)) j).app _ c, ?_⟩
      refine Eq.trans ?_ hc
      exact congrArg (fun φ : yoneda.obj (X j) ⟶ F'.1 => φ.app (op (W j Z y).toScheme) c)
        (Sigma.ι_desc f j)
  exact Scheme.LocalRepresentability.isRepresentable hf
end GlobalTheory.GeneratorFunctor
