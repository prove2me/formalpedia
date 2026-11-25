-- Prove2me | solution 1 for GlobalTheory.Published.exists_isIntegersLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:10:24.438278+00:00
-- url     : https://prove2.me/submissions/f4b15713-265f-4359-ba1c-1509f6f337f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
import Theorems.Thm_GlobalTheory_Published_sqrtNegNat_sq
import Theorems.Thm_GlobalTheory_Published_isTotallyComplex_of_sq_eq_neg
import Theorems.Thm_GlobalTheory_Published_isIntegersLattice_iff
import Theorems.Thm_GlobalTheory_Published_exists_isIdealLattice

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
theorem _root_.solution (hp : 0 < p) : ∃ L, IsIntegersLattice p L := by
  have hint : IsIntegral ℚ (sqrtNegNat p) :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (p : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, by
      simp [sqrtNegNat_sq]⟩
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat p⟯ := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField ℚ⟮sqrtNegNat p⟯ := ⟨⟩
  let x : ℚ⟮sqrtNegNat p⟯ := ⟨sqrtNegNat p, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hx : x ^ 2 = -(p : ℚ⟮sqrtNegNat p⟯) := by
    apply Subtype.ext
    simp [x, sqrtNegNat_sq]
  have : IsTotallyComplex ℚ⟮sqrtNegNat p⟯ := isTotallyComplex_of_sq_eq_neg hp hx
  obtain ⟨L, hL⟩ := exists_isIdealLattice (finrank_adjoin_sqrtNegNat_eq_two hp) 1
  exact ⟨L, (isIntegersLattice_iff hp (finrank_adjoin_sqrtNegNat_eq_two hp) hx L).mpr hL⟩
end GlobalTheory.Published
