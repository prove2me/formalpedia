-- Prove2me | solution 1 for GlobalTheory.SimAlg.gram_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:53.231254+00:00
-- url     : https://prove2.me/submissions/913300bd-80f2-4307-8058-bfdc9fabdd93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg
namespace GlobalTheory.SimAlg
theorem _root_.solution {Λ : Type} [AddCommGroup Λ] (b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ)
    (hb : ∀ x, x ≠ 0 → 0 < b x x) (φ : Module.End ℤ Λ) (e : Λ) (d : ℕ)
    (hd : ∀ P : ℤ[X], P ≠ 0 → P.degree < d → aeval φ P e ≠ 0) (c : Fin d → ℤ) (hc : c ≠ 0) :
    0 < c ⬝ᵥ (Matrix.of fun i j : Fin d => b ((φ ^ (i : ℕ)) e) ((φ ^ (j : ℕ)) e)) *ᵥ c := by
  have h1 : aeval φ (∑ i : Fin d, C (c i) * X ^ (i : ℕ)) e = ∑ i : Fin d, c i • (φ ^ (i : ℕ)) e := by
    simp [map_sum, LinearMap.sum_apply, Module.End.intCast_apply]
  have h2 : (∑ i : Fin d, C (c i) * X ^ (i : ℕ) : ℤ[X]) ≠ 0 := by
    intro h
    apply hc
    ext k
    have := congrArg (fun p : ℤ[X] => p.coeff k) h
    simp only [finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero, Fin.val_inj] at this
    simpa using this
  have h3 := hb _ (hd _ h2 (degree_sum_fin_lt c))
  rw [h1] at h3
  refine h3.trans_eq ?_
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, dotProduct, mulVec,
    Finset.mul_sum, Matrix.of_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.SimAlg
