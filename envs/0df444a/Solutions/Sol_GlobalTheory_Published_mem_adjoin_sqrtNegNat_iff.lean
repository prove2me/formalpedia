-- Prove2me | solution 1 for GlobalTheory.Published.mem_adjoin_sqrtNegNat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:40:06.709822+00:00
-- url     : https://prove2.me/submissions/f57a278c-80f9-4c5e-b902-9d3f8b0a04d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
import Theorems.Thm_GlobalTheory_Published_sqrtNegNat_sq
import Theorems.Thm_GlobalTheory_Published_ComplexMultiplicationJSt_finrank_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
namespace GlobalTheory.Published
section Reduction
variable {F : Type} [Field F] [NumberField F]
end Reduction
section Lattice
variable {p : ℕ} {K : Type} [Field K] [NumberField K]
variable [Algebra K ℂ]
private theorem algebraMap_rat_ne_sqrtNegNat (hp : 0 < p) (q : ℚ) : algebraMap ℚ ℂ q ≠ sqrtNegNat p := by
  intro hq
  have h1 := sqrtNegNat_sq p
  rw [← hq, eq_ratCast] at h1
  have h3 : ((q ^ 2 : ℚ) : ℂ) = ((-(p : ℚ) : ℚ) : ℂ) := by
    push_cast
    exact h1
  have h4 := Rat.cast_injective h3
  have h5 : (0 : ℚ) < p := by exact_mod_cast hp
  nlinarith [sq_nonneg q]
private theorem finrank_adjoin_sqrtNegNat_eq_two (hp : 0 < p) : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ = 2 := by
  have hint : IsIntegral ℚ (sqrtNegNat p) :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (p : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, by
      simp [sqrtNegNat_sq]⟩
  rw [IntermediateField.adjoin.finrank hint]
  have hle : (minpoly ℚ (sqrtNegNat p)).natDegree ≤ 2 := by
    have hd := minpoly.degree_le_of_ne_zero ℚ (sqrtNegNat p)
      (Polynomial.X_pow_add_C_ne_zero two_pos (p : ℚ)) (by simp [sqrtNegNat_sq])
    rw [Polynomial.degree_X_pow_add_C two_pos] at hd
    exact Polynomial.natDegree_le_of_degree_le hd
  have hne : (minpoly ℚ (sqrtNegNat p)).natDegree ≠ 1 := by
    intro h1
    obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact algebraMap_rat_ne_sqrtNegNat hp q hq
  have hpos := minpoly.natDegree_pos hint
  omega
end Lattice
section Consequences
variable {p : ℕ}
variable {F : IntermediateField ℚ ℂ} {A : WeierstrassCurve F}
end Consequences
section Model
end Model
end GlobalTheory.Published
end

set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {p : ℕ} {K : Type} [Field K] [NumberField K]
variable [Algebra K ℂ]
namespace GlobalTheory.Published
theorem _root_.solution (hp : 0 < p) (h2 : Module.finrank ℚ K = 2) {x : K}
    (hx : x ^ 2 = -(p : K)) (z : ℂ) :
    z ∈ ℚ⟮sqrtNegNat p⟯ ↔ ∃ y : K, algebraMap K ℂ y = z := by
  let φ : K →ₐ[ℚ] ℂ := (algebraMap K ℂ).toRatAlgHom
  have hxs : sqrtNegNat p ^ 2 = φ x ^ 2 := by
    rw [sqrtNegNat_sq, ← map_pow, hx, map_neg, map_natCast]
  have hsE : sqrtNegNat p ∈ φ.fieldRange := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxs with h | h
    · exact AlgHom.mem_fieldRange.mpr ⟨x, h.symm⟩
    · exact AlgHom.mem_fieldRange.mpr ⟨-x, by rw [map_neg, h]⟩
  have hle : ℚ⟮sqrtNegNat p⟯ ≤ φ.fieldRange := IntermediateField.adjoin_simple_le_iff.mpr hsE
  have hE : Module.finrank ℚ φ.fieldRange = 2 := by
    rw [← h2]
    exact (AlgEquiv.ofInjectiveField φ).toLinearEquiv.finrank_eq.symm
  have : FiniteDimensional ℚ φ.fieldRange := Module.finite_of_finrank_pos (by omega)
  have heq : ℚ⟮sqrtNegNat p⟯ = φ.fieldRange :=
    IntermediateField.eq_of_le_of_finrank_eq hle (by rw [hE, finrank_adjoin_sqrtNegNat_eq_two hp])
  rw [heq]
  exact AlgHom.mem_fieldRange
end GlobalTheory.Published
