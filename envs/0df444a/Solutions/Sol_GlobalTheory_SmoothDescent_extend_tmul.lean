-- Prove2me | solution 1 for GlobalTheory.SmoothDescent.extend_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:16.052488+00:00
-- url     : https://prove2.me/submissions/77f72c52-a29f-4237-98d7-61bee8cfdd5c

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
theorem _root_.solution (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) (s : S) (b : B₁) :
    extend S ψ (s ⊗ₜ b) = s • ψ b := by
  simp [extend, Algebra.smul_def]
end GlobalTheory.SmoothDescent
