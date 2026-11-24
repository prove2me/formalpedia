-- Prove2me | solution 1 for GlobalTheory.norm_tensorProduct_map_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:13.809356+00:00
-- url     : https://prove2.me/submissions/a854b3ee-6cfe-4edd-bcd8-f966433f165b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormTensorProductMapLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L]
    [Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L) :
    Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by
  classical
  let e := Module.finBasis R L
  let b := Algebra.TensorProduct.basis B e
  let σ := Algebra.TensorProduct.map f (AlgHom.id R L)
  have hrepr : ∀ z : B ⊗[R] L, ∀ i, b.repr (σ z) i = f (b.repr z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [σ, b, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hb : ∀ j, σ (b j) = b j := by
    intro j
    simp [σ, b, Algebra.TensorProduct.basis_apply]
  have hmat : Algebra.leftMulMatrix b (σ w) = (Algebra.leftMulMatrix b w).map f := by
    ext i j
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      ← hb j, ← map_mul, hb j, hrepr]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, hmat]
  exact (AlgHom.map_det f _).symm
end GlobalTheory
