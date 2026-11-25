-- Prove2me | solution 1 for GlobalTheory.PadicOrderAction.liftInt_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:43:09.471688+00:00
-- url     : https://prove2.me/submissions/3395cba7-babf-4445-a683-a091b8e712ea

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicEndApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PadicOrderAction
namespace GlobalTheory.PadicOrderAction
theorem _root_.solution {A B C : Type} [CommRing A] [CommRing B] [Ring C] (φ : A →+* C) (ψ : B →+* C)
    (h : ∀ a b, φ a * ψ b = ψ b * φ a) (a : A) (b : B) : liftInt φ ψ h (a ⊗ₜ[ℤ] b) = φ a * ψ b :=
  Algebra.TensorProduct.lift_tmul φ.toIntAlgHom ψ.toIntAlgHom h a b
end GlobalTheory.PadicOrderAction
