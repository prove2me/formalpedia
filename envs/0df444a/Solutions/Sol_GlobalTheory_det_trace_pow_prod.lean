-- Prove2me | solution 1 for GlobalTheory.det_trace_pow_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:57.058799+00:00
-- url     : https://prove2.me/submissions/e61ee2cc-80a6-4e7e-ae59-a3a1ab6ecd4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Theorems.Thm_GlobalTheory_TraceDetSplit_det_aeval
import Theorems.Thm_GlobalTheory_TraceDetSplit_det_trace_monic
import Theorems.Thm_GlobalTheory_TraceDetSplit_charpoly_leftMul_basis
import Theorems.Thm_GlobalTheory_TraceDetSplit_trace_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory.TraceDetSplit
namespace GlobalTheory
theorem _root_.solution : ∀ (E A₁ A₂ : Type) [Field E] [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) (a b : ℕ) (u : Module.Basis (Fin a) E A₁) (w : Module.Basis (Fin b) E A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → ∃ ε : E, ε * ε = 1 ∧ (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂) ((g₁, g₂) ^ (k : ℕ) * Fin.addCases (fun i => (u i, 0)) (fun j => (0, w j)) l)).det = ε * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly * (Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)).det * (Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)).det := by
  intro E A₁ A₂ _ _ _ _ _ _ _ g₁ g₂ a b u w _
  classical
  have hdeg₁ : (LinearMap.mulLeft E g₁).charpoly.natDegree = a := by
    rw [LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis u, Fintype.card_fin]
  have hCH : aeval g₁ (LinearMap.mulLeft E g₁).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g₁)
    have h2 : aeval (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₁).charpoly =
        Algebra.lmul E A₁ (aeval g₁ (LinearMap.mulLeft E g₁).charpoly) :=
      Polynomial.aeval_algHom_apply (Algebra.lmul E A₁) g₁ _
    rw [h2] at h
    simpa using LinearMap.congr_fun h 1
  let q : Fin (a + b) → E[X] := fun k =>
    if (k : ℕ) < a then X ^ (k : ℕ) else X ^ ((k : ℕ) - a) * (LinearMap.mulLeft E g₁).charpoly
  have hd : ∀ k, (q k).natDegree = k := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp [q, hk]
    · simp only [q, hk, if_false]
      rw [(monic_X_pow _).natDegree_mul (LinearMap.charpoly_monic _), natDegree_X_pow, hdeg₁]
      omega
  have hm : ∀ k, (q k).Monic := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp only [q, hk, if_true]
      exact monic_X_pow _
    · simp only [q, hk, if_false]
      exact (monic_X_pow _).mul (LinearMap.charpoly_monic _)
  refine ⟨(-1) ^ (a * b), by rw [← mul_pow, neg_one_mul, neg_neg, one_pow], ?_⟩
  rw [det_trace_monic (g₁, g₂) _ q hd hm]
  let M := Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
    (aeval (g₁, g₂) (q k) * Fin.addCases (fun i => ((u i, 0) : A₁ × A₂)) (fun j => (0, w j)) l)
  let T₁ := Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)
  let T₂ := Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)
  let S := Matrix.of fun k l : Fin b =>
    Algebra.trace E A₂ (g₂ ^ (k : ℕ) * aeval g₂ (LinearMap.mulLeft E g₁).charpoly * w l)
  have hblock : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks T₁ (Matrix.of fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)) 0 S := by
    ext (i | i) (l | l)
    · simp [M, T₁, q, Algebra.trace_prod_apply, aeval_prod_apply]
    · simp [M]
    · simp [M, q, Algebra.trace_prod_apply, aeval_prod_apply, hCH]
    · simp [M, S, q, Algebra.trace_prod_apply, aeval_prod_apply, mul_assoc]
  have hS : S = T₂ * Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly) :=
    trace_mul_eq (fun k : Fin b => g₂ ^ (k : ℕ)) _ w
  have hres : (Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly)).det =
      (-1) ^ (b * a) * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly := by
    rw [← Polynomial.aeval_algHom_apply, det_aeval _ _ (LinearMap.charpoly_monic _),
      charpoly_leftMul_basis, hdeg₁]
  calc M.det = (M.submatrix finSumFinEquiv finSumFinEquiv).det :=
        (Matrix.det_submatrix_equiv_self _ _).symm
    _ = T₁.det * S.det := by rw [hblock, Matrix.det_fromBlocks_zero₂₁]
    _ = _ := by
      rw [hS, Matrix.det_mul, hres]
      ring
end GlobalTheory
