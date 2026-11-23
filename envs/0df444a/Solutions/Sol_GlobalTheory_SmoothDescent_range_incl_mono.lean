-- Prove2me | solution 1 for GlobalTheory.SmoothDescent.range_incl_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:28.657752+00:00
-- url     : https://prove2.me/submissions/bde2359b-85a2-4091-92bf-d0e36f99710b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SmoothDescent
open TensorProduct
variable {A R B₁ C₁ : Type} [CommRing A] [CommRing R] [CommRing B₁] [CommRing C₁] [Algebra A R]
  [Algebra A B₁] [Algebra A C₁]
namespace GlobalTheory.SmoothDescent
theorem _root_.solution {S T : Subalgebra A R} (h : S ≤ T) :
    (incl C₁ S).range ≤ (incl C₁ T).range := by
  have e : incl C₁ S = (incl C₁ T).comp
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A C₁)) :=
    Algebra.TensorProduct.ext' fun _ _ => rfl
  rw [e]
  exact AlgHom.range_comp_le_range _ _
end GlobalTheory.SmoothDescent
