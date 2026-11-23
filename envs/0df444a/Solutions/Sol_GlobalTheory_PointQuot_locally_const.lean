-- Prove2me | solution 1 for GlobalTheory.PointQuot.locally_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:36.823287+00:00
-- url     : https://prove2.me/submissions/c59edd0f-049a-43ab-a416-218ee4728e70

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints

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
theorem _root_.solution {I : Type} {Z : Over S} (f : Z ⟶ constObj S I) (z : Z.left) :
    ∃ V : Z.left.Opens, z ∈ V ∧ ∃ c : I, openι Z V ≫ f = toUnit _ ≫ constPt S c := by
  obtain ⟨c, y, hy'⟩ : ∃ (c : I) (y : S), Sigma.ι (fun _ : I => S) c y = f.left z :=
    (sigmaOpenCover fun _ : I ↦ S).exists_eq (f.left z)
  let V : Z.left.Opens := f.left ⁻¹ᵁ (Sigma.ι (fun _ : I => S) c).opensRange
  have hr : Set.range (V.ι ≫ f.left) ⊆ Set.range (Sigma.ι (fun _ : I => S) c) := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact v.2
  have hl := IsOpenImmersion.lift_fac (Sigma.ι (fun _ : I => S) c) (V.ι ≫ f.left) hr
  let l : openObj Z V ⟶ 𝟙_ (Over S) :=
    Over.homMk (IsOpenImmersion.lift (Sigma.ι (fun _ : I => S) c) (V.ι ≫ f.left) hr) (by
      change _ ≫ 𝟙 S = V.ι ≫ Z.hom
      have e₁ : Sigma.ι (fun _ : I => S) c ≫ (constObj S I).hom = 𝟙 S :=
        Sigma.ι_desc (f := fun _ : I => S) (fun _ => 𝟙 S) c
      rw [← Over.w f, ← e₁]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (constObj S I).hom) hl).trans (Category.assoc _ _ _)))
  refine ⟨V, ⟨y, hy'⟩, c, ?_⟩
  rw [toUnit_unique (toUnit _) l]
  exact Over.OverMorphism.ext hl.symm
end GlobalTheory.PointQuot
