-- Prove2me | solution 1 for GlobalTheory.SmoothDescent.incl_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:16.5009+00:00
-- url     : https://prove2.me/submissions/41d3297f-2d02-450e-9c0c-587a87def189

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
theorem _root_.solution (S : Subalgebra A R) (s : S) (c : C₁) :
    incl C₁ S (s ⊗ₜ c) = (s : R) • ((1 : R) ⊗ₜ[A] c) := by
  simp [incl, TensorProduct.smul_tmul']
end GlobalTheory.SmoothDescent
