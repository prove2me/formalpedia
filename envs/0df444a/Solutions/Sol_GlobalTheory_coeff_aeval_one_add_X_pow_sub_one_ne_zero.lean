-- Prove2me | solution 1 for GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:53.425805+00:00
-- url     : https://prove2.me/submissions/477aa832-a2c6-4bd0-a661-aa8fc35c4236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoeffAevalOneAddXPowSubOneNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped BigOperators
namespace GlobalTheory
private lemma one_add_X_pow_prime_pow_sub_one {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l]
    (m : ℕ) : (1 + Polynomial.X : Polynomial k) ^ (l ^ m) - 1 = Polynomial.X ^ (l ^ m) := by
  rw [add_pow_char_pow, one_pow, add_sub_cancel_left]
private lemma coeff_zero_aeval_of_coeff_zero_eq_zero {k σ : Type} [Field k] (g : σ → Polynomial k)
    (hg : ∀ q, (g q).coeff 0 = 0) (p : MvPolynomial σ k) :
    (MvPolynomial.aeval g p).coeff 0 = p.coeff 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p q hp =>
    classical
    rw [map_mul, MvPolynomial.aeval_X, Polynomial.mul_coeff_zero, hg, mul_zero,
      MvPolynomial.coeff_mul_X']
    simp
end GlobalTheory
end

set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by
  intro k σ _ _ l M _ _ D u n e hu hD hlt
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hgX : ∀ q, ((1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) = Polynomial.X ^ (l ^ e q) :=
    fun q => one_add_X_pow_prime_pow_sub_one l (e q)
  simp only [hgX]

  have hideal : ∀ r ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)),
      (Polynomial.X : Polynomial k) ^ (l ^ M) ∣
        MvPolynomial.aeval (fun q => (Polynomial.X : Polynomial k) ^ (l ^ e q)) r := by
    intro r hr
    have hle : Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) ≤
        Ideal.comap (MvPolynomial.aeval (fun q => (Polynomial.X : Polynomial k) ^ (l ^ e q)))
          (Ideal.span {(Polynomial.X : Polynomial k) ^ (l ^ M)}) := by
      rw [Ideal.span_le]
      rintro _ ⟨q, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow, MvPolynomial.aeval_X, ← pow_mul, pow_mul',
        Ideal.mem_span_singleton]
      exact dvd_pow_self _ (pow_pos hl _).ne'
    exact Ideal.mem_span_singleton.mp (hle hr)
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)),
      D = u * ∏ q, MvPolynomial.X q ^ n q + r := ⟨_, hD, by ring⟩
  rw [map_add, Polynomial.coeff_add, (Polynomial.X_pow_dvd_iff.mp (hideal r hr)) _ hlt, add_zero,
    map_mul, map_prod]
  simp only [map_pow, MvPolynomial.aeval_X, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ q, l ^ e q * n q = ∑ q, n q * l ^ e q :=
    Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [hsum, Polynomial.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, coeff_zero_aeval_of_coeff_zero_eq_zero _ _ u]
  · exact hu
  · intro q
    rw [Polynomial.coeff_X_pow, if_neg (pow_pos hl _).ne]
end GlobalTheory
