-- Prove2me | solution 1 for GlobalTheory.det_frobenius_sub_pow_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:51:14.747213+00:00
-- url     : https://prove2.me/submissions/cce074bd-9b9e-4c6e-9f8c-64d610322b0b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupport
import Theorems.Thm_GlobalTheory_DetPowDegree_Good_mono
import Theorems.Thm_GlobalTheory_DetPowDegree_Good_sub
import Theorems.Thm_GlobalTheory_DetPowDegree_Good_pow
import Theorems.Thm_GlobalTheory_DetPowDegree_Good_X_inl
import Theorems.Thm_GlobalTheory_DetPowDegree_Good_C_mul_X_inr
import Theorems.Thm_GlobalTheory_DetPowDegree_C_mem_freeIdeal
import Theorems.Thm_GlobalTheory_DetPowDegree_X_inr_mem_freeIdeal
import Theorems.Thm_GlobalTheory_DetPowDegree_Good_of_mem
import Theorems.Thm_GlobalTheory_DetPowDegree_C_dvd_expand_sub_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPolynomial
open GlobalTheory
open DetPowDegree
namespace GlobalTheory
theorem _root_.solution :
  (∀ (l i E n₀ s : ℕ), l.Prime → 1 ≤ i → ∀ ψ : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ,
    ψ = (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) ^ (l ^ i) - MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ)).det -
      MvPolynomial.rename Sum.inl (cayDet n₀ ℤ) ^ (l ^ i) →
    ∀ m ∈ (ψ ^ s).support, (∑ q, m (Sum.inr q)) ≤ n₀ * s ∧ (∑ q, m (Sum.inl q)) + l ^ i * ∑ q, m (Sum.inr q) = n₀ * l ^ i * s ∧
      (l : ℤ) ^ (E * (∑ q, m (Sum.inr q)) + (s - ∑ q, m (Sum.inr q))) ∣ MvPolynomial.coeff m (ψ ^ s)) := by
  intro l i E n₀ s hl _ ψ hψ
  set f : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ :=
    MvPolynomial.rename Sum.inl (cayDet n₀ ℤ) with hf
  have hfdet : f = (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) :
      MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ)).det := by
    rw [hf, cayDet, AlgHom.map_det]
    congr 1
    ext b c : 2
    simp [Matrix.mvPolynomialX]
  have h0 : Good (l : ℤ) (l ^ i) E n₀ (n₀ * l ^ i) 0 ψ := by
    rw [hψ]
    refine Good.sub ?_ ?_
    · have := Good.det (l := (l : ℤ)) (L := l ^ i) (E := E) (n := 1) (d := l ^ i)
        (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) ^ (l ^ i) - MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ))
        (fun b c => by
          refine Good.sub ?_ (Good.C_mul_X_inr _)
          have := (Good.X_inl (l := (l : ℤ)) (L := l ^ i) (E := E) (b, c)).pow (l ^ i)
          simp only [zero_mul, one_mul] at this
          exact this.mono zero_le_one)
      rwa [mul_one] at this
    · have := (Good.det (l := (l : ℤ)) (L := l ^ i) (E := E) (n := 0) (d := 1)
        (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) :
          MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ))
        (fun b c => Good.X_inl _)).pow (l ^ i)
      rw [← hfdet] at this
      simp only [mul_zero, zero_mul, mul_one] at this
      exact this.mono (Nat.zero_le _)
  have hmem : ψ ∈ freeIdeal (Fin n₀ × Fin n₀) (l : ℤ) := by
    have h2 : expand (l ^ i) f - f ^ (l ^ i) ∈ freeIdeal (Fin n₀ × Fin n₀) (l : ℤ) :=
      Ideal.mem_of_dvd _ (C_dvd_expand_sub_pow l i hl f) C_mem_freeIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h2 ⊢
    rw [← h2, hψ, map_sub, map_sub]
    congr 1
    rw [hfdet, AlgHom.map_det, RingHom.map_det, RingHom.map_det]
    congr 1
    ext b c
    have h3 := Ideal.Quotient.eq_zero_iff_mem.2
      (X_inr_mem_freeIdeal (l := (l : ℤ)) (b, c))
    simp only [RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      expand_X, map_sub, map_mul, h3, mul_zero, sub_zero]
  have h1 := (h0.of_mem hmem).pow s
  rw [one_mul] at h1
  intro m hm
  exact h1 m (mem_support_iff.1 hm)
end GlobalTheory
