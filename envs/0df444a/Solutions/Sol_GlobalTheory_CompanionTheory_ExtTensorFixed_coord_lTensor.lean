-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExtTensorFixed.coord_lTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:30:01.83384+00:00
-- url     : https://prove2.me/submissions/165e9555-7474-4a3a-84a1-8ddd6f3b830d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalFixedTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExtTensorFixed
variable {G H V W X ι : Type} [DecidableEq ι] [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
namespace GlobalTheory.CompanionTheory.ExtTensorFixed
theorem _root_.solution (b : Module.Basis ι ℂ X) (f : W →ₗ[ℂ] W) (y : X ⊗[ℂ] W) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (f.lTensor X y) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b y i) := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hx, hy]
  | tmul x w => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
end GlobalTheory.CompanionTheory.ExtTensorFixed
