-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:23.693406+00:00
-- url     : https://prove2.me/submissions/776e1cc5-c7d3-473f-b594-c36c3d029824

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IntFac
namespace GlobalTheory.CompanionTheory.IntFac
theorem _root_.solution (A : Type) [CommRing A] [Algebra ℂ A] (F : A[X])
    (h : ∀ u : ℂ, IsIntegral ℂ (F.eval (algebraMap ℂ A u))) (k : ℕ) :
    IsIntegral ℂ (F.coeff k) := by
  classical
  set N := F.natDegree + 1 with hN
  by_cases hk : k < N
  swap
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact isIntegral_zero
  let φ := algebraMap ℂ A
  let v : Fin N → ℂ := fun j => ((j : ℕ) : ℂ)
  have hv : Function.Injective v := fun a b hab => Fin.ext (by simpa only [v, Nat.cast_inj] using hab)
  let V := Matrix.vandermonde v
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
  let c : Fin N → A := fun j => F.coeff j
  let y : Fin N → A := fun i => F.eval (φ (v i))
  have hy : Matrix.mulVec (V.map φ) c = y := by
    funext i
    simp only [y, Matrix.mulVec, dotProduct, Matrix.map_apply, V, Matrix.vandermonde_apply, c]
    rw [eval_eq_sum_range' (Nat.lt_succ_self _),
      ← Fin.sum_univ_eq_sum_range (fun j => F.coeff j * φ (v i) ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_pow, mul_comm]
  have hc : c = Matrix.mulVec (V⁻¹.map φ) y := by
    rw [← hy, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec]
  have hmem : Matrix.mulVec (V⁻¹.map φ) y ⟨k, hk⟩ ∈ integralClosure ℂ A := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (h _)
  have hck : F.coeff k = c ⟨k, hk⟩ := rfl
  rw [hck, hc]
  exact hmem
end GlobalTheory.CompanionTheory.IntFac
