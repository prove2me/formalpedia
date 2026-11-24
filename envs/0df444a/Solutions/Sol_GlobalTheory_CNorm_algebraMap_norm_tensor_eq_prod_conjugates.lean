-- Prove2me | solution 1 for GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:58.608643+00:00
-- url     : https://prove2.me/submissions/27e77947-b926-463b-8053-868f5929f9cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AlgebraMapNormTensorEqProdConjugates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped WithZero TensorProduct
namespace GlobalTheory.CNorm
namespace _root_.GlobalTheory.CNorm
theorem _root_.solution (F E K : Type) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [CommRing K] [Algebra F K] (y : K ⊗[F] E) :
    algebraMap K (K ⊗[F] E) (Algebra.norm K y) =
      ∏ g : E ≃ₐ[F] E, Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y := by
  classical
  set G := E ≃ₐ[F] E
  have hcard : Fintype.card G = Module.finrank F E := by
    rw [← IsGalois.card_aut_eq_finrank F E, Nat.card_eq_fintype_card]
  let b : Module.Basis G F E := (Module.finBasis F E).reindex (Fintype.equivFinOfCardEq hcard).symm
  let b' : Module.Basis G K (K ⊗[F] E) := Algebra.TensorProduct.basis K b
  set A := Algebra.leftMulMatrix b' y with hA
  let P : Matrix G G E := fun g j => g (b j)
  have hP : P.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
    have hj : ∀ j, ∑ g, v g * g (b j) = 0 := fun j => by
      simpa [Matrix.vecMul, dotProduct, P] using congrFun hv j
    have hx : ∀ x : E, ∑ g, v g * g x = 0 := fun x => by
      calc ∑ g, v g * g x = ∑ g, v g * g (∑ j, b.repr x j • b j) := by rw [b.sum_repr]
        _ = ∑ j, b.repr x j • ∑ g, v g * g (b j) := by
          simp only [map_sum, Algebra.smul_def, map_mul, AlgEquiv.commutes, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun g _ => by rw [AlgEquiv.commutes]; ring
        _ = 0 := by simp [hj]
    have hli := (linearIndependent_monoidHom E E).comp
      (fun g : G => (g : E ≃* E).toMonoidHom) (fun g₁ g₂ h => by
        ext x; exact DFunLike.congr_fun h x)
    have := Fintype.linearIndependent_iff.mp hli v (by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply]
      exact hx x)
    exact hv0 (funext this)
  let P' : Matrix G G (K ⊗[F] E) := P.map Algebra.TensorProduct.includeRight
  have key : Matrix.diagonal
      (fun g : G => Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y) * P'
      = P' * A.map (algebraMap K (K ⊗[F] E)) := by
    ext g j
    have h1 : y * b' j = ∑ i, A i j • b' i := by
      simpa [A, Algebra.leftMulMatrix_eq_repr_mul] using (b'.sum_repr (y * b' j)).symm
    have h2 := congrArg (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E)) h1
    simp only [map_mul, map_sum, b', Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.smul_def,
      AlgHom.commutes] at h2
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    change _ * (1 ⊗ₜ[F] (g : E →ₐ[F] E) (b j)) =
      ∑ i, (1 ⊗ₜ[F] (g : E →ₐ[F] E) (b i)) * algebraMap K (K ⊗[F] E) (A i j)
    rw [h2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdet := congrArg Matrix.det key
  have hAdet : (A.map (algebraMap K (K ⊗[F] E))).det = algebraMap K (K ⊗[F] E) A.det :=
    (RingHom.map_det _ _).symm
  have hPdet : P'.det = Algebra.TensorProduct.includeRight P.det :=
    (RingHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).toRingHom P).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hAdet, hA,
    ← Algebra.norm_eq_matrix_det] at hdet
  have hu : IsUnit P'.det := by
    rw [hPdet]; exact (isUnit_iff_ne_zero.mpr hP).map _
  exact (hu.mul_left_cancel (by rw [mul_comm]; exact hdet)).symm
end _root_.GlobalTheory.CNorm
end GlobalTheory.CNorm
