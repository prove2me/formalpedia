-- Prove2me | solution 1 for GlobalTheory.PointQuot.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:13.407575+00:00
-- url     : https://prove2.me/submissions/5e660314-b634-48a1-9e17-2315640b1760

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
import Theorems.Thm_GlobalTheory_PointQuot_constPt_desc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.PointQuot
variable {S : Scheme.{0}}
namespace GlobalTheory.PointQuot
theorem _root_.solution {I : Type} {A Z : Over S} (x : I → (𝟙_ (Over S) ⟶ A)) [Mono (constDesc x)]
    (g : Z ⟶ A)
    (h : ∀ z : Z.left, ∃ V : Z.left.Opens, z ∈ V ∧ ∃ c : I, openι Z V ≫ g = toUnit _ ≫ x c) :
    ∃ f : Z ⟶ constObj S I, f ≫ constDesc x = g := by
  choose V hV c hc using h
  have hcov : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    exact fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hV z⟩
  have : Mono (constDesc x).left := Over.mono_left_of_mono _
  let 𝒰 := Z.left.openCoverOfIsOpenCover V hcov
  let φ : ∀ z, 𝒰.X z ⟶ (constObj S I).left := fun z =>
    (toUnit (openObj Z (V z)) ≫ constPt S (c z)).left
  have hφ : ∀ z, φ z ≫ (constDesc x).left = 𝒰.f z ≫ g.left := fun (z : Z.left) => by
    have : (toUnit (openObj Z (V z)) ≫ constPt S (c z)) ≫ constDesc x = openι Z (V z) ≫ g := by
      rw [Category.assoc, constPt_desc]
      exact (hc z).symm
    exact congrArg CommaMorphism.left this
  have hcomp : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ φ a = pullback.snd _ _ ≫ φ b := fun a b => by
    rw [← cancel_mono (constDesc x).left, Category.assoc, Category.assoc, hφ, hφ,
      pullback.condition_assoc]
  have key : 𝒰.glueMorphisms φ hcomp ≫ (constDesc x).left = g.left :=
    𝒰.hom_ext _ _ fun z => by rw [𝒰.ι_glueMorphisms_assoc, hφ]
  exact ⟨Over.homMk (𝒰.glueMorphisms φ hcomp) (by
    rw [← Over.w (constDesc x), ← Category.assoc, key, Over.w]), Over.OverMorphism.ext key⟩
end GlobalTheory.PointQuot
