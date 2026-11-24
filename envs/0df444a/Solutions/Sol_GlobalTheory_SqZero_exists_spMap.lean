-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_spMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:12.758012+00:00
-- url     : https://prove2.me/submissions/3c0327c5-9471-4beb-b875-44c5a6448e34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one')
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {X : Over (Spec (CommRingCat.of R))} {A A₀ B : Type} [CommRing A] [Algebra R A]
  [CommRing A₀] [Algebra R A₀] [CommRing B] [Algebra R B]
namespace GlobalTheory.SqZero
theorem _root_.solution (f : sp (R₀ := R) A ⟶ sp B) : ∃ φ : B →ₐ[R] A, f = spMap φ := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap R B) ≫ Spec.preimage f.left) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [Spec.map_comp, Spec.map_preimage]
    exact Over.w f
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  refine ⟨⟨(Spec.preimage f.left).hom, fun r => RingHom.congr_fun e' r⟩, Over.OverMorphism.ext ?_⟩
  exact (Spec.map_preimage f.left).symm
end GlobalTheory.SqZero
