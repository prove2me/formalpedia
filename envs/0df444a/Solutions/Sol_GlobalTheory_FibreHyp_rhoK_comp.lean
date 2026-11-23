-- Prove2me | solution 1 for GlobalTheory.FibreHyp.rhoK_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:18.025499+00:00
-- url     : https://prove2.me/submissions/9f20715c-3aca-403c-bee1-e486836ea0dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.FibreHyp
variable {A : Type} [CommRing A] {σ : Type} (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k]
namespace GlobalTheory.FibreHyp
theorem _root_.solution : (rhoK f g k).toRingHom =
    (algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k)).comp (Ideal.Quotient.mk (Ik f k)) := rfl
end GlobalTheory.FibreHyp
