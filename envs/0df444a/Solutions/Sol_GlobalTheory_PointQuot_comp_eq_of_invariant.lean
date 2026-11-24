-- Prove2me | solution 1 for GlobalTheory.PointQuot.comp_eq_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:10.995849+00:00
-- url     : https://prove2.me/submissions/196a4473-6cac-46b6-8c9c-d1cede90c0c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
import Theorems.Thm_GlobalTheory_PointQuot_hom_ext_local
import Theorems.Thm_GlobalTheory_PointQuot_locally_const_desc

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
theorem _root_.solution {I : Type} {A B Y : Over S} [GrpObj A] [GrpObj B]
    (x : I → (𝟙_ (Over S) ⟶ A)) (q : A ⟶ B) [IsMonHom q]
    (hker : IsPullback (constDesc x) (toUnit _) q η[B]) (f : A ⟶ Y)
    (hf : ∀ c, ((toUnit A ≫ x c) * 𝟙 A) ≫ f = f) {Z : Over S} (g g' : Z ⟶ A)
    (h : g ≫ q = g' ≫ q) : g ≫ f = g' ≫ f := by
  have h1 : (g / g') ≫ q = toUnit Z ≫ η[B] := by
    rw [GrpObj.div_comp, h, div_self', Hom.one_def]
  refine hom_ext_local _ _ fun z => ?_
  obtain ⟨V, hV, c, hc⟩ := locally_const_desc x (hker.lift (g / g') (toUnit Z) h1) z
  refine ⟨V, hV, ?_⟩
  rw [hker.lift_fst, GrpObj.comp_div, div_eq_iff_eq_mul] at hc
  rw [← Category.assoc, hc]
  conv_rhs => rw [← hf c, ← Category.assoc, ← Category.assoc, MonObj.comp_mul, Category.comp_id,
    ← Category.assoc, toUnit_unique (_ ≫ toUnit A) (toUnit _)]
end GlobalTheory.PointQuot
