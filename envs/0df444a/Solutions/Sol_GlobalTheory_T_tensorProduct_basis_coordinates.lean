-- Prove2me | solution 1 for GlobalTheory.T.tensorProduct_basis_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:36.571799+00:00
-- url     : https://prove2.me/submissions/c9b9a156-aadd-47bb-8445-45288e08c1b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorProductBasisCoordinates
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorProductBasisCoordinatesStatement
import Theorems.Thm_GlobalTheory_tensorBasisCoords


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (B : Type) [CommRing B] [Algebra F B] (V : Type) [AddCommGroup V] [Module F V] (n : Type) [Fintype n] [DecidableEq n] (b : Basis n F V), ∃ e : V ⊗[F] B ≃ₗ[F] (n → B), (∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x) ∧ (∀ y : n → B, e.symm y = ∑ i, b i ⊗ₜ[F] y i) ∧ ∀ (r : V →ₗ[F] V) (f : B →ₗ[F] B) (y : V ⊗[F] B), e (TensorProduct.map r f y) = ((LinearMap.toMatrix b b r).map (algebraMap F B)).mulVec (fun i => f (e y i)) := by
  first | exact @GlobalTheory.tensorBasisCoords | exact GlobalTheory.tensorBasisCoords | (intros; apply GlobalTheory.tensorBasisCoords <;> assumption)
end _root_.GlobalTheory.T
