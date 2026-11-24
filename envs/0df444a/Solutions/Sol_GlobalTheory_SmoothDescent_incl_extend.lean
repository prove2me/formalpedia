-- Prove2me | solution 1 for GlobalTheory.SmoothDescent.incl_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:28:41.37944+00:00
-- url     : https://prove2.me/submissions/32d895ba-5548-4ccf-ba9b-a55cf088b5d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Theorems.Thm_GlobalTheory_SmoothDescent_incl_tmul
import Theorems.Thm_GlobalTheory_SmoothDescent_incl_smul
import Theorems.Thm_GlobalTheory_SmoothDescent_extend_tmul

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
theorem _root_.solution (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁)
    (ψ : B₁ →ₐ[A] S ⊗[A] C₁) (h : ∀ b, incl C₁ S (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    incl C₁ S (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => rw [extend_tmul, incl_smul, h, incl_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
end GlobalTheory.SmoothDescent
