-- Prove2me | solution 1 for OAI.QuarticPowerFree.medium_degree_dyadic_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T15:07:21.76204+00:00
-- url     : https://prove2.me/submissions/3abadb17-acc7-4611-9530-10c9ad284608

import Mathlib
import Definitions.Def_OAIB3Qp000
import Theorems.Thm_OAI_QuarticPowerFree_norm_generic_threshold_uniform
import Theorems.Thm_OAI_QuarticPowerFree_physical_affine_count

section
-- module Solutions.OAIB3_Qpf.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_Sieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Asymptotics
open scoped Topology
namespace QuarticPowerFree

open Polynomial

theorem resultant_derivative_ne_zero (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    f.resultant f.derivative ≠ 0 := by
  have h := Polynomial.resultant_ne_zero _ _ hf.separable
  rw [Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.resultant_map_map] at h
  intro hz
  apply h
  rw [hz]
  rfl

theorem derivative_not_dvd_of_good (f : Polynomial ℤ) (hdeg : f.natDegree ≠ 0)
    {p : ℕ} (hp : ¬ (p : ℤ) ∣ f.resultant f.derivative) {a : ℤ}
    (ha : (p : ℤ) ∣ f.eval a) : ¬ (p : ℤ) ∣ f.derivative.eval a := by
  obtain ⟨u, v, _, _, h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f
    f.derivative le_rfl le_rfl (Or.inl hdeg)
  have he := congrArg (Polynomial.eval a) h
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at he
  intro hd
  apply hp
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left ha (u.eval a)) (dvd_mul_of_dvd_left hd (v.eval a))

open scoped BigOperators Count

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_HilbertSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open scoped BigOperators

open scoped BigOperators
open MvPolynomial

theorem mem_weightedMonomials {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) (T : ℝ) (a : σ →₀ ℕ) :
    a ∈ weightedMonomials ω T ↔ monomialWeight ω a ≤ T := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ?_,ha⟩
    intro i
    change a i ≤ ⌊T/ω i⌋₊
    apply Nat.le_floor
    apply (le_div_iff₀ (hω i)).mpr
    have hi := Finset.single_le_sum
      (fun j _ => mul_nonneg (hω j).le (Nat.cast_nonneg (a j))) (Finset.mem_univ i)
    simpa only [mul_comm (a i : ℝ)] using hi.trans ha

theorem weightedMonomials_mono {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) {S T : ℝ} (h : S ≤ T) :
    weightedMonomials ω S ⊆ weightedMonomials ω T := by
  intro a ha
  exact (mem_weightedMonomials ω hω T a).mpr
    (((mem_weightedMonomials ω hω S a).mp ha).trans h)

end

open scoped BigOperators
open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_WeightedHypersurfaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open MvPolynomial
open scoped BigOperators

theorem weightedLift_monomial {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) :
    weightedLift w (monomial m r) =
      Polynomial.C (monomial m r) * Polynomial.X ^ (Finsupp.weight w m) := by
  classical
  simp only [weightedLift, eval₂Hom_monomial, RingHom.comp_apply]
  simp only [Finsupp.prod, mul_pow, ← map_pow, Finset.prod_mul_distrib,
    ← map_prod]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  · rw [monomial_eq, Finsupp.prod]
  · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]

theorem weightedLift_coeff {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) (t : ℕ) :
    (weightedLift w p).coeff t = weightedHomogeneousComponent w t p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [weightedLift_monomial, Polynomial.coeff_C_mul_X_pow]
    ext s
    by_cases hs : m = s
    · subst s
      split_ifs <;> simp_all [coeff_weightedHomogeneousComponent, coeff_monomial, eq_comm]
    · split_ifs <;> simp_all [coeff_weightedHomogeneousComponent, coeff_monomial]
  | add p q hp hq => simp [map_add, Polynomial.coeff_add, hp, hq]

theorem weightedLift_eval_one {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) : (weightedLift w p).eval 1 = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r => simp [weightedLift_monomial]
  | add p q hp hq => simp [map_add, hp, hq]

theorem weightedLift_injective {σ R : Type*} [CommSemiring R] (w : σ → ℕ) :
    Function.Injective (weightedLift (R := R) w) := by
  intro p q h
  simpa only [weightedLift_eval_one] using congrArg (Polynomial.eval 1) h

theorem weightedLift_natDegree {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) :
    (weightedLift w p).natDegree = weightedTotalDegree w p := by
  classical
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro t ht
    rw [weightedLift_coeff]
    exact weightedHomogeneousComponent_eq_zero t p ht
  · unfold weightedTotalDegree
    apply Finset.sup_le
    intro m hm
    have hc : (weightedLift w p).coeff (Finsupp.weight w m) ≠ 0 := by
      rw [weightedLift_coeff]
      intro he
      have h := congrArg (fun polynomial => polynomial.coeff m) he
      simp [coeff_weightedHomogeneousComponent, mem_support_iff.mp hm] at h
    exact Polynomial.le_natDegree_of_ne_zero hc

theorem weightedTotalDegree_mul_exact {σ R : Type*} [CommSemiring R] [IsDomain R]
    (w : σ → ℕ) (p q : MvPolynomial σ R) (hp : p ≠ 0) (hq : q ≠ 0) :
    weightedTotalDegree w (p * q) = weightedTotalDegree w p + weightedTotalDegree w q := by
  rw [← weightedLift_natDegree, map_mul, Polynomial.natDegree_mul]
  · rw [weightedLift_natDegree, weightedLift_natDegree]
  · intro h
    apply hp
    apply weightedLift_injective w
    simpa using h
  · intro h
    apply hq
    apply weightedLift_injective w
    simpa using h

theorem weightedSpace_finite {σ K : Type*} [Finite σ] [CommSemiring K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (T : ℕ) :
    Module.Finite K (weightedSpace (K := K) w T) := by
  have := (Finsupp.finite_of_nat_weight_le w hw T).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport K _)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ComplexValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open Polynomial Matrix
open scoped BigOperators

namespace QuarticPowerFree.ComplexValues

theorem denominator_value_dvd_resultant (A B : ℤ[X])
    (hB : B.natDegree ≠ 0) {s : ℤ} (hs : B.eval s ∣ A.eval s) :
    B.eval s ∣ A.resultant B := by
  obtain ⟨u, v, _, _, h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant A B
    le_rfl le_rfl (Or.inr hB)
  have he := congrArg (Polynomial.eval s) h
  simp only [eval_add, eval_mul, eval_C] at he
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left hs _) (dvd_mul_right _ _)

theorem card_fibre_eval_le (B : ℤ[X]) (hB : 0 < B.natDegree)
    (S : Finset ℤ) (q : ℤ) :
    (S.filter (fun s => B.eval s = q)).card ≤ B.natDegree := by
  have hnz : B - C q ≠ 0 := by
    intro hz
    have hh := congrArg Polynomial.natDegree hz
    rw [natDegree_sub_C, natDegree_zero] at hh
    omega
  have hh : (S.filter (fun s => B.eval s = q)).val ⊆ (B - C q).roots := by
    intro s hs
    have he := (Finset.mem_filter.mp hs).2
    exact Polynomial.mem_roots hnz |>.mpr (by simp [he])
  simpa only [natDegree_sub_C] using Polynomial.card_le_degree_of_subset_roots hh

theorem mem_signedDivisors {r q : ℤ} (hr : r ≠ 0) (hq : q ∣ r) :
    q ∈ signedDivisors r := by
  have hn : q.natAbs ∈ r.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hq, Int.natAbs_ne_zero.mpr hr⟩
  rcases le_total 0 q with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨_, hn, by simp [abs_of_nonneg h]⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, hn, by simp [abs_of_nonpos h]⟩)

theorem card_signedDivisors_le (r : ℤ) :
    (signedDivisors r).card ≤ 2 * r.natAbs.divisors.card := by
  exact (Finset.card_union_le _ _).trans (by
    have h₁ := Finset.card_image_le (s := r.natAbs.divisors) (f := fun n => (n : ℤ))
    have h₂ := Finset.card_image_le (s := r.natAbs.divisors) (f := fun n => -(n : ℤ))
    omega)

theorem rational_values_card_le_divisors (A B : ℤ[X])
    (hB : 0 < B.natDegree) (hres : A.resultant B ≠ 0) (S : Finset ℤ) :
    (S.filter (fun s => B.eval s ∣ A.eval s)).card ≤
      2 * B.natDegree * (A.resultant B).natAbs.divisors.card := by
  classical
  let T := S.filter (fun s => B.eval s ∣ A.eval s)
  have himage : T.image B.eval ⊆ signedDivisors (A.resultant B) := by
    intro q hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    exact mem_signedDivisors hres (denominator_value_dvd_resultant A B
      (Nat.ne_zero_of_lt hB) (Finset.mem_filter.mp hs).2)
  calc
    T.card = ∑ q ∈ T.image B.eval, (T.filter (fun s => B.eval s = q)).card :=
      (Finset.card_eq_sum_card_image B.eval T)
    _ ≤ ∑ q ∈ T.image B.eval, B.natDegree := by
      apply Finset.sum_le_sum
      intro q _
      exact card_fibre_eval_le B hB T q
    _ = (T.image B.eval).card * B.natDegree := by simp
    _ ≤ (signedDivisors (A.resultant B)).card * B.natDegree :=
      Nat.mul_le_mul_right _ (Finset.card_le_card himage)
    _ ≤ (2 * (A.resultant B).natAbs.divisors.card) * B.natDegree :=
      Nat.mul_le_mul_right _ (card_signedDivisors_le _)
    _ = 2 * B.natDegree * (A.resultant B).natAbs.divisors.card := by ring

theorem rational_function_interpolation_cross {F : Type*} [Field F]
    (A B A₁ B₁ : F[X]) (S : Finset F)
    (hA : A₁.natDegree ≤ A.natDegree) (hB : B₁.natDegree ≤ B.natDegree)
    (hcard : A.natDegree + B.natDegree < S.card)
    (heval : ∀ s ∈ S, A₁.eval s * B.eval s = A.eval s * B₁.eval s) :
    A₁ * B = A * B₁ := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S
  · intro s hs
    simpa only [eval_sub, eval_mul, sub_eq_zero] using heval s hs
  · have hd := Polynomial.natDegree_sub_le (A₁ * B) (A * B₁)
    have h₁ := Polynomial.natDegree_mul_le (p := A₁) (q := B)
    have h₂ := Polynomial.natDegree_mul_le (p := A) (q := B₁)
    exact lt_of_le_of_lt (hd.trans (max_le (by omega) (by omega))) hcard

theorem rational_function_interpolation_unique {F : Type*} [Field F]
    (A B A₁ B₁ : F[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (hB : B₁.natDegree ≤ B.natDegree) (heq : A₁ * B = A * B₁) :
    ∃ c : F, A₁ = C c * A ∧ B₁ = C c * B := by
  have hdvd : B ∣ B₁ := hcop.symm.dvd_of_dvd_mul_left (heq ▸ dvd_mul_left B A₁)
  obtain ⟨Q, hQ⟩ := hdvd
  by_cases hQz : Q = 0
  · refine ⟨0, ?_, ?_⟩
    · have hz : A₁ = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_right hBn
        rw [heq, hQ, hQz, mul_zero, mul_zero]
      simpa using hz
    · simp [hQ, hQz]
  · have hdeg : Q.natDegree = 0 := by
      rw [hQ, Polynomial.natDegree_mul hBn hQz] at hB
      omega
    have hQc : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    refine ⟨Q.coeff 0, ?_, ?_⟩
    · apply mul_right_cancel₀ hBn
      conv_lhs => rw [heq, hQ, hQc]
      ring
    · calc B₁ = B * Q := hQ
           _ = B * C (Q.coeff 0) := congrArg (B * ·) hQc
           _ = C (Q.coeff 0) * B := mul_comm _ _

theorem interpolationRow_some_dot {R ι : Type*} [CommRing R] [DecidableEq R] {a b : ℕ}
    (s v : ι → R) (t : ι) (c : Fin (a + 1) ⊕ Fin (b + 1) → R) :
    interpolationRow s v (some t) ⬝ᵥ c =
      (Polynomial.ofFn (a + 1) (fun j => c (Sum.inl j))).eval (s t) -
      v t * (Polynomial.ofFn (b + 1) (fun j => c (Sum.inr j))).eval (s t) := by
  classical
  simp only [interpolationRow, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.mul_sum,
    neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)

theorem interpolationRow_none_dot {R ι : Type*} [CommRing R] {a b : ℕ}
    (s v : ι → R) (c : Fin (a + 1) ⊕ Fin (b + 1) → R) :
    interpolationRow s v none ⬝ᵥ c = c (Sum.inr ⟨b, Nat.lt_succ_self b⟩) := by
  rw [interpolationRow, single_dotProduct, one_mul]

theorem interpolationMatrix_det_ne_zero {F ι : Type*} [Field F] [Fintype ι]
    (A B : F[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → F) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i) = v i * B.eval (s i))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι) :
    (interpolationMatrix s v e).det ≠ 0 := by
  classical
  let M := interpolationMatrix s v e
  have hker : ∀ c, M *ᵥ c = 0 → c = 0 := by
    intro c hc
    let P := Polynomial.ofFn (A.natDegree + 1) (fun j => c (Sum.inl j))
    let Q := Polynomial.ofFn (B.natDegree + 1) (fun j => c (Sum.inr j))
    have hpdeg : P.natDegree ≤ A.natDegree := by
      have h := Polynomial.ofFn_natDegree_lt (R := F) (Nat.succ_pos A.natDegree)
        (fun j => c (Sum.inl j))
      exact Nat.le_of_lt_succ h
    have hqdeg : Q.natDegree ≤ B.natDegree := by
      have h := Polynomial.ofFn_natDegree_lt (R := F) (Nat.succ_pos B.natDegree)
        (fun j => c (Sum.inr j))
      exact Nat.le_of_lt_succ h
    have hpeval (i : ι) : P.eval (s i) = v i * Q.eval (s i) := by
      have hh := congrFun hc (e.symm (some i))
      change interpolationRow s v (e (e.symm (some i))) ⬝ᵥ c = 0 at hh
      rw [e.apply_symm_apply, interpolationRow_some_dot] at hh
      exact sub_eq_zero.mp hh
    have hcross : P * B = A * Q := by
      apply rational_function_interpolation_cross A B P Q (Finset.univ.image s) hpdeg hqdeg
      · simpa only [Finset.card_image_of_injective _ hs, Finset.card_univ] using hcard
      · intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        rw [hpeval, heval]
        ring
    obtain ⟨r, hP, hQ⟩ := rational_function_interpolation_unique A B P Q hcop hBn hqdeg hcross
    have hqzero : Q.coeff B.natDegree = 0 := by
      have hh := congrFun hc (e.symm none)
      change interpolationRow s v (e (e.symm none)) ⬝ᵥ c = 0 at hh
      rw [e.apply_symm_apply, interpolationRow_none_dot] at hh
      simpa only [Q, Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_self _)] using hh
    have hr : r = 0 := by
      rw [hQ, Polynomial.coeff_C_mul] at hqzero
      exact (mul_eq_zero.mp hqzero).resolve_right (Polynomial.leadingCoeff_ne_zero.mpr hBn)
    have hpzero : P = 0 := by simp [hP, hr]
    have hqzero' : Q = 0 := by simp [hQ, hr]
    funext j
    rcases j with j | j
    · have hh := congrArg (fun p : F[X] => p.coeff j.val) hpzero
      simpa only [P, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
        Pi.zero_apply] using hh
    · have hh := congrArg (fun p : F[X] => p.coeff j.val) hqzero'
      simpa only [Q, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
        Pi.zero_apply] using hh
  have hi : Function.Injective (Matrix.mulVecLin M) :=
    LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  exact (M.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

theorem interpolationMatrix_map {R S ι : Type*} [CommRing R] [CommRing S]
    {a b : ℕ} (f : R →+* S) (s v : ι → R)
    (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι) :
    (interpolationMatrix s v e).map f =
      interpolationMatrix (fun i => f (s i)) (fun i => f (v i)) e := by
  classical
  ext i j
  change f (interpolationRow s v (e i) j) = _
  change _ = interpolationRow (fun i => f (s i)) (fun i => f (v i)) (e i) j
  rcases h : e i with _ | t
  · simp only [interpolationRow]
    by_cases hj : j = Sum.inr ⟨b, Nat.lt_succ_self b⟩
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hj]
  · rcases j with j | j <;> simp [interpolationRow]

theorem rational_interpolation_integral_pair {ι : Type*} [Fintype ι]
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → ℤ) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i : ℂ) = (v i : ℂ) * B.eval (s i : ℂ))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι) :
    ∃ P Q : ℤ[X], ∃ r : ℂ, r ≠ 0 ∧
      P.map (Int.castRingHom ℂ) = C r * A ∧
      Q.map (Int.castRingHom ℂ) = C r * B ∧
      P.natDegree ≤ A.natDegree ∧ Q.natDegree ≤ B.natDegree ∧
      P = Polynomial.ofFn (A.natDegree + 1)
        (fun j => interpolationCramer s v e (Sum.inl j)) ∧
      Q = Polynomial.ofFn (B.natDegree + 1)
        (fun j => interpolationCramer s v e (Sum.inr j)) := by
  classical
  let M := interpolationMatrix s v e
  let u : Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1) → ℤ :=
    fun j => if e j = none then 1 else 0
  let c := M.cramer u
  let P := Polynomial.ofFn (A.natDegree + 1) (fun j => c (Sum.inl j))
  let Q := Polynomial.ofFn (B.natDegree + 1) (fun j => c (Sum.inr j))
  have hdet : M.det ≠ 0 := by
    have h := interpolationMatrix_det_ne_zero A B hcop hBn
      (fun i => (s i : ℂ)) (fun i => (v i : ℂ))
      (Int.cast_injective.comp hs) hcard heval e
    intro hz
    apply h
    have hm := interpolationMatrix_map (Int.castRingHom ℂ) s v e
    simp only [Int.coe_castRingHom] at hm
    rw [← hm, ← Int.cast_det,
      show (interpolationMatrix s v e).det = 0 from hz, Int.cast_zero]
  have hc : M *ᵥ c = M.det • u := M.mulVec_cramer u
  have hpdeg : P.natDegree ≤ A.natDegree := Nat.le_of_lt_succ
    (Polynomial.ofFn_natDegree_lt (R := ℤ) (Nat.succ_pos _) _)
  have hqdeg : Q.natDegree ≤ B.natDegree := Nat.le_of_lt_succ
    (Polynomial.ofFn_natDegree_lt (R := ℤ) (Nat.succ_pos _) _)
  let f := Int.castRingHom ℂ
  have heval' (i : ι) : (P.map f).eval (s i : ℂ) = (v i : ℂ) * (Q.map f).eval (s i : ℂ) := by
    have hh := congrFun hc (e.symm (some i))
    change interpolationRow s v (e (e.symm (some i))) ⬝ᵥ c = _ at hh
    rw [e.apply_symm_apply, interpolationRow_some_dot] at hh
    have hz : P.eval (s i) - v i * Q.eval (s i) = 0 := by
      simpa [P, Q, u] using hh
    have he := congrArg f (sub_eq_zero.mp hz)
    simpa only [Polynomial.eval_intCast_map, Int.cast_id, map_mul, f, Int.coe_castRingHom] using he
  have hcross : (P.map f) * B = A * (Q.map f) := by
    apply rational_function_interpolation_cross A B _ _
      (Finset.univ.image (fun i => (s i : ℂ)))
    · rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    · rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    · have hsQ : Function.Injective (fun i => (s i : ℂ)) := Int.cast_injective.comp hs
      rw [Finset.card_image_of_injective _ hsQ, Finset.card_univ]
      exact hcard
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [heval', heval]
      ring
  obtain ⟨r, hP, hQ⟩ := rational_function_interpolation_unique A B _ _ hcop hBn
    (by rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]) hcross
  have hr : r ≠ 0 := by
    intro hr
    have hzero : Q.map f = 0 := by simp [hQ, hr]
    have hcoef : Q.coeff B.natDegree = M.det := by
      have hh := congrFun hc (e.symm none)
      change interpolationRow s v (e (e.symm none)) ⬝ᵥ c = _ at hh
      rw [e.apply_symm_apply, interpolationRow_none_dot] at hh
      simpa [Q, u, Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_self _)] using hh
    have hz := congrArg (fun p : ℂ[X] => p.coeff B.natDegree) hzero
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, hcoef] at hz
    exact hdet (Int.cast_eq_zero.mp hz)
  exact ⟨P, Q, r, hr, hP, hQ, hpdeg, hqdeg, rfl, rfl⟩

theorem det_abs_le_row_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (B : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ B i) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
  calc
    |A.det| = |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i| := by
      rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [show |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| from
        AbsoluteValue.abs.map_units_int_smul _ _, Finset.abs_prod]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, B (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
    _ = (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
      simp_rw [Equiv.prod_comp]
      simp [Fintype.card_perm]

theorem det_abs_le_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (B : ℝ) (hA : ∀ i j, |(A i j : ℝ)| ≤ B) :
    |(A.det : ℝ)| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
  rw [Int.cast_det]
  simpa only [Finset.prod_const, Finset.card_univ] using
    det_abs_le_row_product (A.map fun x => (x : ℝ)) (fun _ => B) hA

theorem interpolationRow_abs_le {ι : Type*} {a b : ℕ} (s v : ι → ℤ)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (i : Option ι)
    (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |((interpolationRow s v i j : ℤ) : ℝ)| ≤ H ^ (max a b + 1) := by
  classical
  have h0 : 0 ≤ H := zero_le_one.trans hH
  cases i with
  | none =>
    by_cases hj : j = Sum.inr ⟨b, Nat.lt_succ_self b⟩
    · subst j
      simpa [interpolationRow] using one_le_pow₀ hH (n := max a b + 1)
    · simp [interpolationRow, Pi.single_eq_of_ne hj, pow_nonneg h0]
  | some i =>
    cases j with
    | inl j =>
      simp only [interpolationRow, Sum.elim_inl, Int.cast_pow, abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hs i) _).trans
        (pow_le_pow_right₀ hH (by have := j.isLt; omega))
    | inr j =>
      simp only [interpolationRow, Sum.elim_inr, Int.cast_neg, Int.cast_mul,
        Int.cast_pow, abs_neg, abs_mul, abs_pow]
      calc
        |(v i : ℝ)| * |(s i : ℝ)| ^ j.val ≤ H * H ^ j.val :=
          mul_le_mul (hv i) (pow_le_pow_left₀ (abs_nonneg _) (hs i) _)
            (by positivity) h0
        _ = H ^ (j.val + 1) := by rw [pow_succ]; ring
        _ ≤ H ^ (max a b + 1) := pow_le_pow_right₀ hH (by have := j.isLt; omega)

theorem interpolationCramer_abs_le {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |(interpolationCramer s v e j : ℝ)| ≤
      (Nat.factorial (a + b + 2) : ℝ) * H ^ ((max a b + 1) * (a + b + 2)) := by
  classical
  unfold interpolationCramer
  rw [Matrix.cramer_apply]
  have h := det_abs_le_uniform
    ((interpolationMatrix s v e).updateCol j (fun j => if e j = none then 1 else 0))
    (H ^ (max a b + 1)) (fun i j' => ?_)
  · simpa only [Fintype.card_sum, Fintype.card_fin, ← pow_mul,
      show a + 1 + (b + 1) = a + b + 2 by omega] using h
  · by_cases hj : j' = j
    · subst j'
      simp only [Matrix.updateCol_self]
      split_ifs
      · simpa using one_le_pow₀ hH (n := max a b + 1)
      · simp [pow_nonneg (zero_le_one.trans hH)]
    · rw [Matrix.updateCol_ne hj]
      exact interpolationRow_abs_le s v H hH hs hv (e i) j'

theorem interpolationHeight_one_le (D : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    1 ≤ interpolationHeight D H := by
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos (2 * D + 2))
    (one_le_pow₀ hH)

theorem interpolationCramer_abs_le_degree_bound {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι)
    (D : ℕ) (ha : a ≤ D) (hb : b ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |(interpolationCramer s v e j : ℝ)| ≤ interpolationHeight D H := by
  apply (interpolationCramer_abs_le s v e H hH hs hv j).trans
  apply mul_le_mul
  · exact_mod_cast Nat.factorial_le (show a + b + 2 ≤ 2 * D + 2 by omega)
  · exact pow_le_pow_right₀ hH (Nat.mul_le_mul (by omega) (by omega))
  · positivity
  · positivity

theorem resultant_abs_le_coeff_bound (P Q : ℤ[X]) (H : ℝ) (hH : 0 ≤ H)
    (hP : ∀ j, |(P.coeff j : ℝ)| ≤ H) (hQ : ∀ j, |(Q.coeff j : ℝ)| ≤ H) :
    |(P.resultant Q : ℝ)| ≤ (Nat.factorial (P.natDegree + Q.natDegree) : ℝ) *
      H ^ (P.natDegree + Q.natDegree) := by
  unfold Polynomial.resultant
  apply (det_abs_le_uniform _ H ?_).trans_eq
  · simp only [Fintype.card_fin]
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j'
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · simpa using hH
    · intro j'
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · simpa using hH

theorem resultant_ne_zero_of_scalar_maps (A B : ℂ[X]) (P Q : ℤ[X])
    (hcop : IsCoprime A B) (r : ℂ) (hr : r ≠ 0)
    (hP : P.map (Int.castRingHom ℂ) = C r * A)
    (hQ : Q.map (Int.castRingHom ℂ) = C r * B) : P.resultant Q ≠ 0 := by
  have hcop' : IsCoprime (P.map (Int.castRingHom ℂ)) (Q.map (Int.castRingHom ℂ)) := by
    rw [hP, hQ]
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨C r⁻¹ * u, C r⁻¹ * v, ?_⟩
    calc
      C r⁻¹ * u * (C r * A) + C r⁻¹ * v * (C r * B) =
          C r⁻¹ * C r * (u * A + v * B) := by ring
      _ = 1 := by rw [huv, ← Polynomial.C_mul]; simp [hr]
  have hh := Polynomial.resultant_ne_zero _ _ hcop'
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.resultant_map_map] at hh
  exact fun hz => hh (by simp only [hz, map_zero])

theorem rational_interpolation_height {ι : Type*} [Fintype ι]
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → ℤ) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i : ℂ) = (v i : ℂ) * B.eval (s i : ℂ))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι)
    (D : ℕ) (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hsH : ∀ i, |(s i : ℝ)| ≤ H)
    (hvH : ∀ i, |(v i : ℝ)| ≤ H) :
    ∃ P Q : ℤ[X], ∃ r : ℂ, r ≠ 0 ∧
      P.map (Int.castRingHom ℂ) = C r * A ∧
      Q.map (Int.castRingHom ℂ) = C r * B ∧
      P.natDegree ≤ D ∧ Q.natDegree = B.natDegree ∧
      P.resultant Q ≠ 0 ∧
      (∀ j, |(P.coeff j : ℝ)| ≤ interpolationHeight D H) ∧
      (∀ j, |(Q.coeff j : ℝ)| ≤ interpolationHeight D H) := by
  obtain ⟨P, Q, r, hr, hP, hQ, hpdeg, _, hPc, hQc⟩ :=
    rational_interpolation_integral_pair A B hcop hBn s v hs hcard heval e
  have hqdeg : Q.natDegree = B.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective (p := Q) (f := Int.castRingHom ℂ) Int.cast_injective,
      hQ, Polynomial.natDegree_C_mul hr]
  refine ⟨P, Q, r, hr, hP, hQ, hpdeg.trans hA, hqdeg,
    resultant_ne_zero_of_scalar_maps A B P Q hcop r hr hP hQ, ?_, ?_⟩
  · intro j
    rw [hPc]
    by_cases hj : j < A.natDegree + 1
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
      exact interpolationCramer_abs_le_degree_bound s v e D hA hB H hH hsH hvH _
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact_mod_cast (zero_le_one.trans (interpolationHeight_one_le D hH))
  · intro j
    rw [hQc]
    by_cases hj : j < B.natDegree + 1
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
      exact interpolationCramer_abs_le_degree_bound s v e D hA hB H hH hsH hvH _
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact_mod_cast (zero_le_one.trans (interpolationHeight_one_le D hH))

theorem eval_eq_mul_of_scalar_maps (A B : ℂ[X]) (P Q : ℤ[X]) (r : ℂ)
    (hP : P.map (Int.castRingHom ℂ) = C r * A)
    (hQ : Q.map (Int.castRingHom ℂ) = C r * B) (s v : ℤ)
    (hv : A.eval (s : ℂ) = (v : ℂ) * B.eval (s : ℂ)) :
    P.eval s = v * Q.eval s := by
  apply Int.cast_injective (α := ℂ)
  have hp := congrArg (Polynomial.eval (s : ℂ)) hP
  have hq := congrArg (Polynomial.eval (s : ℂ)) hQ
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_intCast_map, Int.coe_castRingHom, Int.cast_id] at hp hq
  push_cast
  rw [hp, hq, hv]
  ring

theorem rational_values_height_representative
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (S : Finset ℤ) (v : ℤ → ℤ)
    (heval : ∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ))
    (hcard : A.natDegree + B.natDegree < S.card)
    (D : ℕ) (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hsH : ∀ s ∈ S, |(s : ℝ)| ≤ H)
    (hvH : ∀ s ∈ S, |(v s : ℝ)| ≤ H) :
    ∃ P Q : ℤ[X], P.natDegree ≤ D ∧ Q.natDegree = B.natDegree ∧
      P.resultant Q ≠ 0 ∧
      (∀ j, |(P.coeff j : ℝ)| ≤ interpolationHeight D H) ∧
      (∀ j, |(Q.coeff j : ℝ)| ≤ interpolationHeight D H) ∧
      ∀ s ∈ S, P.eval s = v s * Q.eval s := by
  classical
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hcard)
  let e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option T :=
    Fintype.equivOfCardEq (by simp [hTc]; omega)
  obtain ⟨P, Q, r, _, hP, hQ, hpdeg, hqdeg, hres, hpH, hqH⟩ :=
    rational_interpolation_height A B hcop hBn
      (fun s : T => s.val) (fun s : T => v s.val) Subtype.val_injective
      (by simp [hTc])
      (fun s => heval s.val (hTS s.property)) e D hA hB H hH
      (fun s => hsH s.val (hTS s.property)) (fun s => hvH s.val (hTS s.property))
  refine ⟨P, Q, hpdeg, hqdeg, hres, hpH, hqH, ?_⟩
  intro s hs
  exact eval_eq_mul_of_scalar_maps A B P Q r hP hQ s (v s) (heval s hs)

theorem rationalResultantConstant_pos (D : ℕ) : 0 < rationalResultantConstant D := by
  unfold rationalResultantConstant
  positivity

theorem rationalResultantExponent_pos {D : ℕ} (hD : 0 < D) :
    0 < rationalResultantExponent D := by
  unfold rationalResultantExponent
  positivity

theorem resultant_abs_le_interpolation_height (P Q : ℤ[X]) (D : ℕ)
    (hPdeg : P.natDegree ≤ D) (hQdeg : Q.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H)
    (hP : ∀ j, |(P.coeff j : ℝ)| ≤ interpolationHeight D H)
    (hQ : ∀ j, |(Q.coeff j : ℝ)| ≤ interpolationHeight D H) :
    |(P.resultant Q : ℝ)| ≤ rationalResultantConstant D * H ^ rationalResultantExponent D := by
  have hi := interpolationHeight_one_le D hH
  apply (resultant_abs_le_coeff_bound P Q (interpolationHeight D H)
    (zero_le_one.trans hi) hP hQ).trans
  calc
    _ ≤ (Nat.factorial (2 * D) : ℝ) * interpolationHeight D H ^ (2 * D) := by
      apply mul_le_mul
      · exact_mod_cast Nat.factorial_le (show P.natDegree + Q.natDegree ≤ 2 * D by omega)
      · exact pow_le_pow_right₀ hi (by omega)
      · positivity
      · positivity
    _ = rationalResultantConstant D * H ^ rationalResultantExponent D := by
      simp only [interpolationHeight, rationalResultantConstant, rationalResultantExponent,
        mul_pow, ← pow_mul]
      rw [Nat.mul_comm ((D + 1) * (2 * D + 2)) (2 * D)]
      ring

open Filter

theorem succ_le_geometric (r : ℝ) (hr : 1 < r) (a : ℕ) :
    (a : ℝ) + 1 ≤ (1 + (r - 1)⁻¹) * r ^ a := by
  have h₁ := a.cast_le_pow_div_sub hr
  have h₂ : (1 : ℝ) ≤ r ^ a := one_le_pow₀ hr.le
  calc
    (a : ℝ) + 1 ≤ r ^ a / (r - 1) + r ^ a := add_le_add h₁ h₂
    _ = (1 + (r - 1)⁻¹) * r ^ a := by ring

theorem divisors_card_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (r - 1)⁻¹
  have hc : 1 ≤ c := by
    have hh : 0 ≤ (r - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hr.le)
    dsimp [c]
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have ht : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨c ^ N, pow_pos hc0 _, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hε.ne']
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall : p < N
    · rw [ite_eq_left hsmall]
      exact (succ_le_geometric r hr _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hε.le) _)
        hc0.le)
    · rw [ite_eq_right hsmall, one_mul]
      have hh : (n.factorization p : ℝ) + 1 ≤ (2 : ℝ) ^ n.factorization p := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n.factorization p))
      exact hh.trans (pow_le_pow_left₀ (by norm_num) (hN p (Nat.le_of_not_gt hsmall)) _)
  have hconstant : (∏ p ∈ n.primeFactors, if p < N then c else 1) ≤ c ^ N := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ hc
    exact (Finset.card_le_card (show n.primeFactors.filter (fun p => p < N) ⊆
      Finset.range N from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)).trans
        (by rw [Finset.card_range])
  have hpowers : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
      (n : ℝ) ^ ε := by
    simp_rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) ε,
      mul_comm ε, Real.rpow_natCast_mul (Nat.cast_nonneg _) _ ε]
    rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn]
      push_cast
      rfl
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p :=
      Finset.prod_le_prod (fun p _ => by positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, if p < N then c else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ c ^ N * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hconstant (by positivity)

theorem rational_values_card_le_rpow (D : ℕ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℂ[X]), IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      ∀ (S : Finset ℤ) (v : ℤ → ℤ) (H : ℝ), 1 ≤ H →
      (∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ)) →
      (∀ s ∈ S, |(s : ℝ)| ≤ H) → (∀ s ∈ S, |(v s : ℝ)| ≤ H) →
      (S.card : ℝ) ≤ C * H ^ ε := by
  let E := rationalResultantExponent D
  have hE : (0 : ℝ) < E := by exact_mod_cast rationalResultantExponent_pos hD
  let δ := ε / (E : ℝ)
  have hδ : 0 < δ := div_pos hε hE
  obtain ⟨c, hc, hdiv⟩ := divisors_card_le_rpow δ hδ
  let K := rationalResultantConstant D
  have hK : 0 < K := rationalResultantConstant_pos D
  let C : ℝ := (2 * D : ℕ) + (2 * D : ℕ) * c * K ^ δ
  have h2D : (0 : ℝ) < (2 * D : ℕ) := by exact_mod_cast (by omega : 0 < 2 * D)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A B hcop hBpos hAdeg hBdeg S v H hH heval hsH hvH
  have hHε : 1 ≤ H ^ ε := Real.one_le_rpow hH hε.le
  by_cases hcard : A.natDegree + B.natDegree < S.card
  · have hBn : B ≠ 0 := by
      intro hz
      simp only [hz, Polynomial.natDegree_zero, lt_self_iff_false] at hBpos
    obtain ⟨P, Q, hPdeg, hQdeg, hres, hP, hQ, hpq⟩ :=
      rational_values_height_representative A B hcop hBn S v heval hcard D hAdeg hBdeg
        H hH hsH hvH
    have hi : S.filter (fun s => Q.eval s ∣ P.eval s) = S := by
      apply Finset.filter_eq_self.mpr
      intro s hs
      rw [hpq s hs]
      exact dvd_mul_left _ _
    have hτ := rational_values_card_le_divisors P Q (by omega) hres S
    rw [hi] at hτ
    have hR : ((P.resultant Q).natAbs : ℝ) ≤ K * H ^ E := by
      have hab : ((P.resultant Q).natAbs : ℝ) = |(P.resultant Q : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hab]
      exact resultant_abs_le_interpolation_height P Q D hPdeg (hQdeg ▸ hBdeg) H hH hP hQ
    have hpowers : (K * H ^ E) ^ δ = K ^ δ * H ^ ε := by
      rw [Real.mul_rpow hK.le (pow_nonneg (zero_le_one.trans hH) _),
        ← Real.rpow_natCast_mul (zero_le_one.trans hH)]
      congr 1
      dsimp [δ]
      rw [mul_div_cancel₀ _ hE.ne']
    calc
      (S.card : ℝ) ≤ ((2 * Q.natDegree : ℕ) : ℝ) *
          ((P.resultant Q).natAbs.divisors.card : ℝ) := by exact_mod_cast hτ
      _ ≤ ((2 * D : ℕ) : ℝ) * (c * (((P.resultant Q).natAbs : ℝ) ^ δ)) := by
        apply mul_le_mul
        · exact_mod_cast Nat.mul_le_mul_left 2 (hQdeg ▸ hBdeg)
        · exact hdiv _
        · positivity
        · positivity
      _ ≤ ((2 * D : ℕ) : ℝ) * (c * ((K * H ^ E) ^ δ)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hR hδ.le) hc.le) h2D.le
      _ = (((2 * D : ℕ) : ℝ) * c * K ^ δ) * H ^ ε := by rw [hpowers]; ring
      _ ≤ C * H ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        linarith
  · have hsmall : (S.card : ℝ) ≤ (2 * D : ℕ) := by exact_mod_cast (by omega : S.card ≤ 2 * D)
    calc
      (S.card : ℝ) ≤ (2 * D : ℕ) := hsmall
      _ ≤ ((2 * D : ℕ) : ℝ) * H ^ ε := le_mul_of_one_le_right h2D.le hHε
      _ ≤ C * H ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        have hnonneg : 0 ≤ ((2 * D : ℕ) : ℝ) * c * K ^ δ := by positivity
        linarith

theorem rational_integer_values_uniform (D : ℕ) (hD : 0 < D)
    (a b C₀ : ℝ) (ha : 0 < a) (_hb : 0 < b) (_hC₀ : 0 < C₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℂ[X]), IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      ∀ (S : Finset ℤ) (v : ℤ → ℤ) (X : ℝ), 2 ≤ X →
      (∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ)) →
      (∀ s ∈ S, |(s : ℝ)| ≤ C₀ * X ^ a) →
      (∀ s ∈ S, |(v s : ℝ)| ≤ C₀ * X ^ b) →
      (S.card : ℝ) ≤ C * X ^ ε := by
  let M := max a b
  have hM : 0 < M := lt_of_lt_of_le ha (le_max_left _ _)
  let K := max 1 C₀
  have hK : 1 ≤ K := le_max_left _ _
  let δ := ε / M
  have hδ : 0 < δ := div_pos hε hM
  obtain ⟨c, hc, h⟩ := rational_values_card_le_rpow D hD δ hδ
  refine ⟨c * K ^ δ, by positivity, ?_⟩
  intro A B hcop hBpos hAdeg hBdeg S v X hX heval hsX hvX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hXM : 1 ≤ X ^ M := Real.one_le_rpow hX1 hM.le
  have hH : 1 ≤ K * X ^ M := one_le_mul_of_one_le_of_one_le hK hXM
  have hbound (c₁ : ℝ) (hc₁ : c₁ ≤ M) : C₀ * X ^ c₁ ≤ K * X ^ M := by
    exact mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le hX1 hc₁)
      (by positivity) (zero_le_one.trans hK)
  have hh := h A B hcop hBpos hAdeg hBdeg S v (K * X ^ M) hH heval
    (fun s hs => (hsX s hs).trans (hbound a (le_max_left _ _)))
    (fun s hs => (hvX s hs).trans (hbound b (le_max_right _ _)))
  have hp : (K * X ^ M) ^ δ = K ^ δ * X ^ ε := by
    rw [Real.mul_rpow (zero_le_one.trans hK) (Real.rpow_nonneg hX0 _),
      ← Real.rpow_mul hX0]
    congr 1
    dsimp [δ]
    rw [mul_div_cancel₀ _ hM.ne']
  simpa only [hp, mul_assoc] using hh

end QuarticPowerFree.ComplexValues

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_CurveAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open MvPolynomial
open scoped BigOperators Classical

theorem algebraic_coordinate_constant {K A : Type*} [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [Algebra K A] (x : A) (hx : IsAlgebraic K x) :
    ∃ c : K, algebraMap K A c = x := by
  have hi := hx.isIntegral
  have hd := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi)
  have he := minpoly.aeval K x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd,
    (minpoly.monic hi).leadingCoeff, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
    add_eq_zero_iff_eq_neg] at he
  exact ⟨-(minpoly K x).coeff 0, by rw [map_neg]; exact he.symm⟩

theorem curve_coordinate_relation {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hI : affineDimension I ≤ 1) (x y : Fin n)
    (hx : Transcendental K (Ideal.Quotient.mk I (X x))) :
    ∃ q : MvPolynomial (Fin 2) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (q.totalDegree:ℚ) ≤ affineDegree I ∧
      (∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) := by
  have hind : AlgebraicIndependent K
      (fun a : Fin 1 => Ideal.Quotient.mk I (X (![y,x] a.succ))) := by
    apply algebraicIndependent_unique_type_iff.mpr
    simpa using hx
  have hdim : affineDimension I = 1 := by
    have htr := hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)
    have hh := hind.lift_cardinalMk_le_trdeg
    rw [← htr] at hh
    have hl : 1 ≤ affineDimension I := by simpa [affineDimension] using hh
    omega
  obtain ⟨q,hq,hd,hb,hker⟩ := bounded_projection_relation I (coordinateHilbert I)
    hI (coordinateHilbert_eventually I) ![y,x] hind
  refine ⟨q,hq,hd,?_,hker⟩
  simpa only [affineDegree,hdim] using hb

theorem binaryPolynomialEquiv_eval {K A : Type*} [CommSemiring K] [CommSemiring A]
    (f : K →+* A) (x y : A) (q : MvPolynomial (Fin 2) K) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom f x) y (binaryPolynomialEquiv K q) =
      MvPolynomial.eval₂ f ![y,x] q := by
  let e : MvPolynomial (Fin 2) K →+* A :=
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom f x) y).comp
      (binaryPolynomialEquiv K).toRingHom
  have he : e = MvPolynomial.eval₂Hom f ![y,x] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e,binaryPolynomialEquiv,finSuccEquiv_apply,uniqueAlgEquiv]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e,binaryPolynomialEquiv,finSuccEquiv_apply,uniqueAlgEquiv]
      · simp [e,binaryPolynomialEquiv,finSuccEquiv_apply,uniqueAlgEquiv]
  exact congrArg (fun g : MvPolynomial (Fin 2) K →+* A => g q) he

theorem uniquePolynomial_natDegree_le {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 1) K) : (uniqueAlgEquiv K (Fin 1) q).natDegree ≤ q.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [coeff_uniqueAlgEquiv]
  apply coeff_eq_zero_of_totalDegree_lt
  change q.totalDegree < (Finsupp.single (default : Fin 1) m).sum (fun _ e => e)
  rw [Finsupp.sum_single_index (by simp)]
  exact hm

theorem binaryPolynomial_coeff_degree {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 2) K) (i : ℕ) :
    ((binaryPolynomialEquiv K q).coeff i).natDegree ≤ q.totalDegree := by
  simp only [binaryPolynomialEquiv,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,Polynomial.coeff_map]

  by_cases hz : (finSuccEquiv K 1 q).coeff i = 0
  · simp [hz]
  · exact (uniquePolynomial_natDegree_le _).trans
      (Nat.le_sub_of_add_le (totalDegree_coeff_finSuccEquiv_add_le q i hz) |>.trans (Nat.sub_le _ _))

theorem linear_projection_rational {K : Type*} [Field K]
    (q : MvPolynomial (Fin 2) K) (hq : Irreducible q) (hd : q.degreeOf 0 = 1) :
    ∃ A B : Polynomial K, IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree ≤ q.totalDegree ∧
      B.natDegree ≤ q.totalDegree ∧
      ∀ {S : Type*} [CommRing S] (f : K →+* S) (x y : S),
        MvPolynomial.eval₂ f ![y,x] q = 0 ↔
          A.eval₂ f x = y * B.eval₂ f x := by
  let p := binaryPolynomialEquiv K q
  have hp : Irreducible p := (MulEquiv.irreducible_iff (binaryPolynomialEquiv K)).mpr hq
  have hpd : p.natDegree = 1 := (binaryPolynomialEquiv_natDegree q).trans hd
  have he : p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := by
    simpa only [hpd] using Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq hpd))
  have hbn : p.coeff 1 ≠ 0 := by
    rw [← hpd]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp.ne_zero
  have prim := hp.isPrimitive (by rw [hpd]; decide)
  have hcop : IsCoprime (p.coeff 0) (p.coeff 1) := by
    apply IsRelPrime.isCoprime
    intro d hd0 hd1
    apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp prim
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi : i = 0
    · subst i; exact hd0
    by_cases hi1 : i = 1
    · subst i; exact hd1
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _
  refine ⟨-p.coeff 0,p.coeff 1,hcop.neg_left,hbn,?_,binaryPolynomial_coeff_degree q 1,?_⟩
  · simpa using binaryPolynomial_coeff_degree q 0
  · intro S _ f x y
    rw [← binaryPolynomialEquiv_eval,show binaryPolynomialEquiv K q = p from rfl]
    conv_lhs => rw [he]
    simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
      Polynomial.eval₂_X,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_neg]
    constructor <;> intro h <;> linear_combination -h

theorem binaryStripExponent_injective (M : ℕ) :
    Function.Injective (binaryStripExponent (M := M)) := by
  intro i j h
  have h0 := congrArg (fun a : Fin 2 →₀ ℕ => a 0) h
  have h1 := congrArg (fun a : Fin 2 →₀ ℕ => a 1) h
  simp only [binaryStripExponent,Finsupp.coe_add,Pi.add_apply,Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (0:Fin 2) ≠ 1 by decide),
    Finsupp.single_eq_of_ne (show (1:Fin 2) ≠ 0 by decide),add_zero,zero_add] at h0 h1
  exact Prod.ext (Fin.ext h0) (Fin.ext h1)

theorem projection_strip_independent {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (x y : Fin n)
    (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) (M : ℕ) :
    LinearIndependent K (fun i : Fin 2 × Fin (M+1) =>
      Ideal.Quotient.mk I (rename ![y,x] (monomial (binaryStripExponent i) (1:K)))) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  let p : MvPolynomial (Fin 2) K := ∑ j ∈ s, c j • monomial (binaryStripExponent j) 1
  have hpker : Ideal.Quotient.mk I (rename ![y,x] p) = 0 := by
    change (Ideal.Quotient.mkₐ K I) (rename ![y,x] p) = 0
    simpa only [p,map_sum,map_smul,Ideal.Quotient.mkₐ_eq_mk] using hc
  have hpdeg : p.degreeOf 0 ≤ 1 := by
    apply (degreeOf_sum_le 0 s _).trans
    apply Finset.sup_le
    intro j _
    rw [smul_monomial,smul_eq_mul,mul_one]
    by_cases hz : c j = 0
    · simp [hz]
    · rw [degreeOf_monomial_eq _ _ hz]
      simp only [binaryStripExponent,Finsupp.coe_add,Pi.add_apply,Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0:Fin 2) ≠ 1 by decide),add_zero]
      omega
  have hp : p = 0 := by
    by_contra hp
    obtain ⟨t,ht⟩ := (hker p).mp hpker
    have hmul : q*t ≠ 0 := ht ▸ hp
    have hd := degreeOf_mul_eq (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul) (n := 0)
    rw [← ht] at hd
    omega
  have hl := (basisMonomials (Fin 2) K).linearIndependent.comp
    (binaryStripExponent (M := M)) (binaryStripExponent_injective M)
  simp only [coe_basisMonomials,Function.comp_def] at hl
  exact linearIndependent_iff'.mp hl s c hp i hi

theorem coordinate_power_mem_weighted {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (a b : ℕ) (T : ℝ) (hb : ω y*a+ω x*b ≤ T) :
    Ideal.Quotient.mk I ((X y)^a*(X x)^b) ∈ weightedFunctions I ω T := by
  classical
  have hweight : monomialWeight ω (Finsupp.single y a + Finsupp.single x b) = ω y*a+ω x*b := by
    simp only [monomialWeight,Finsupp.coe_add,Pi.add_apply,Nat.cast_add,mul_add,Finset.sum_add_distrib]
    simp [Finsupp.single_apply]
  rw [X_pow_eq_monomial,X_pow_eq_monomial,monomial_mul_monomial,one_mul]
  apply Submodule.subset_span
  refine ⟨_,(mem_weightedMonomials ω hω T _).mpr (hweight ▸ hb),rfl⟩

theorem projection_equation_quotient {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (x y : Fin n)
    (q : MvPolynomial (Fin 2) K)
    (hq : Ideal.Quotient.mk I (rename ![y,x] q) = 0) :
    MvPolynomial.eval₂ (algebraMap K (MvPolynomial (Fin n) K ⧸ I))
      ![Ideal.Quotient.mk I (X y),Ideal.Quotient.mk I (X x)] q = 0 := by
  have he : MvPolynomial.aeval ![Ideal.Quotient.mk I (X y),Ideal.Quotient.mk I (X x)] =
      (Ideal.Quotient.mkₐ K I).comp (rename ![y,x]) := by
    ext i
    fin_cases i <;> simp
  change (MvPolynomial.aeval _) q = 0
  rw [he]
  exact hq

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_SelectedPrimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open Polynomial
open scoped BigOperators Classical

theorem primitive_map_zmod_ne_zero (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hz
  have hd : Polynomial.C (p:ℤ) ∣ f := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    have hh := congrArg (fun g : Polynomial (ZMod p) => g.coeff i) hz
    simpa using hh
  have hu := Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hf (p:ℤ) hd
  have he := Int.isUnit_iff_natAbs_eq.mp hu
  exact hp.ne_one (by simpa using he)

end
open MvPolynomial
open scoped BigOperators Classical

theorem coordinate_constant_at_point {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : PointOn I z) (j : Fin n)
    (c : K) (hc : algebraMap K (MvPolynomial (Fin n) K ⧸ I) c = Ideal.Quotient.mk I (X j)) :
    (z j:K) = c := by
  have he := congrArg (pointEvaluation I z hz) hc
  simpa only [AlgHom.commutes,Algebra.algebraMap_self, RingHom.id_apply,pointEvaluation_X] using he.symm

theorem rational_coordinate_at_point {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : PointOn I z) (x j : Fin n)
    (A B : Polynomial K)
    (he : Polynomial.aeval (Ideal.Quotient.mk I (X x)) A =
      Ideal.Quotient.mk I (X j)*Polynomial.aeval (Ideal.Quotient.mk I (X x)) B) :
    A.eval (z x:K) = (z j:K)*B.eval (z x:K) := by
  have hh := congrArg (pointEvaluation I z hz) he
  rw [map_mul,← Polynomial.aeval_algHom_apply,← Polynomial.aeval_algHom_apply] at hh
  simpa only [pointEvaluation_X,Polynomial.aeval_def,
    Algebra.algebraMap_self,Polynomial.eval₂_id] using hh

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_SurfaceCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open MvPolynomial
open scoped BigOperators Classical

theorem weightedSpace_map_le_weightedFunctions {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (w : Fin n → ℕ) (ω : Fin n → ℝ)
    (hω : ∀ i, 0 < ω i) (L : ℝ) (hL : 0 < L)
    (hw : ∀ i, (w i : ℝ) = L*ω i) (T : ℝ) (hT : 0 ≤ T) :
    (weightedSpace w ⌊L*T⌋₊).map (Ideal.Quotient.mkₐ K I).toLinearMap ≤
      weightedFunctions I ω T := by
  classical
  rintro y ⟨p,hp,rfl⟩
  have hs : ∀ a ∈ p.support, monomialWeight ω a ≤ T := by
    intro a ha
    have hh : Finsupp.weight w a ≤ ⌊L*T⌋₊ :=
      hp ha
    have he : (Finsupp.weight w a : ℝ) = L*monomialWeight ω a := by
      rw [Finsupp.weight_eq_sum]
      simp only [Nat.cast_sum,monomialWeight,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [nsmul_eq_mul,Nat.cast_mul,hw]
      norm_cast
      ring
    have hhN : (Finsupp.weight w a : ℝ) ≤ (⌊L*T⌋₊:ℕ) := by exact_mod_cast hh
    have hh' : (Finsupp.weight w a : ℝ) ≤ L*T :=
      hhN.trans (Nat.floor_le (mul_nonneg hL.le hT))
    rw [he] at hh'
    exact (mul_le_mul_iff_right₀ hL).mp hh'
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro a ha
  have hm : Ideal.Quotient.mk I (monomial a (1:K)) ∈ weightedFunctions I ω T :=
    Submodule.subset_span ⟨a,(mem_weightedMonomials ω hω T a).mpr (hs a ha),rfl⟩
  have he : monomial a (p.coeff a) = (p.coeff a) • monomial a (1:K) := by
    rw [smul_monomial,smul_eq_mul,mul_one]
  rw [he]
  simpa using (weightedFunctions I ω T).smul_mem (p.coeff a) hm

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_HighDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open scoped BigOperators

theorem polynomial_dyadic_eval_bound (f : Polynomial ℤ) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (n : ℤ), 0 ≤ n → (n:ℝ) ≤ 2*X →
      |((f.eval n:ℤ):ℝ)| ≤ C*X^(f.natDegree:ℝ) := by
  classical
  let A : ℝ := ∑ i ∈ f.support, |(f.coeff i:ℝ)|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let C := 2+A*2^f.natDegree
  have hC : 2 ≤ C := by dsimp [C]; nlinarith [pow_pos (show (0:ℝ)<2 by norm_num) f.natDegree]
  refine ⟨C,hC,fun X hX n hn hnX => ?_⟩
  have hXp : 0 ≤ X := by linarith
  have hn' : 0 ≤ (n:ℝ) := by exact_mod_cast hn
  have hh : |((f.eval n:ℤ):ℝ)| ≤ A*(2*X)^f.natDegree := by
    rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
    push_cast
    calc
      _ ≤ ∑ i ∈ f.support, |(f.coeff i:ℝ)*(n:ℝ)^i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ f.support, |(f.coeff i:ℝ)| *(2*X)^f.natDegree := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul,abs_pow,abs_of_nonneg hn']
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (pow_le_pow_left₀ hn' hnX i).trans (pow_le_pow_right₀ (by linarith)
          (Polynomial.le_natDegree_of_mem_supp i hi))
      _ = A*(2*X)^f.natDegree := by rw [Finset.sum_mul]
  rw [mul_pow] at hh
  rw [Real.rpow_natCast]
  have hc : A*2^f.natDegree ≤ C := by dsimp [C]; linarith
  exact hh.trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hc (pow_nonneg hXp _))

theorem rational_irreducible_eval_ne_zero (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 2 ≤ f.natDegree) (n : ℤ) :
    f.eval n ≠ 0 := by
  intro hz
  have hr : (f.map (Int.castRingHom ℚ)).IsRoot (n:ℚ) := by
    change (f.map (Int.castRingHom ℚ)).eval (n:ℚ) = 0
    rw [Polynomial.eval_intCast_map]
    change (Int.castRingHom ℚ) (f.eval n) = 0
    rw [hz,map_zero]
  have hdvd := Polynomial.dvd_iff_isRoot.mpr hr
  have hu : ¬ IsUnit (Polynomial.X-Polynomial.C (n:ℚ)) := by
    exact Polynomial.not_isUnit_of_natDegree_pos _ (by rw [Polynomial.natDegree_X_sub_C]; decide)
  have ha := (hf.dvd_iff.mp hdvd).resolve_left hu
  have he := Polynomial.natDegree_le_of_dvd ha.dvd (Polynomial.X_sub_C_ne_zero (n:ℚ))
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_X_sub_C] at he
  omega

open Filter
open scoped Topology Classical

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open MvPolynomial MonomialOrder
open scoped MonomialOrder

theorem pair_ideal_isPrime {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    (Ideal.span (Set.range (pairRelation k q))).IsPrime := by
  rw [pair_ideal_eq_ker k q hq]
  exact RingHom.ker_isPrime _

theorem pairNormalBasis_apply {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0)
    (m : {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}) :
    pairNormalBasis k q hq m = Ideal.Quotient.mk _ (monomial m.val 1) := by
  simp only [pairNormalBasis, Module.Basis.map_apply, pairNormalEquiv,
    LinearEquiv.ofBijective_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
  congr 1
  ext d
  change (((AddMonoidAlgebra.supportedEquivFinsupp _).symm
    (Finsupp.single m (1:R))) : MvPolynomial (Fin n ⊕ Fin n) R).coeff d = _
  simp only [AddMonoidAlgebra.supportedEquivFinsupp, LinearEquiv.symm_trans_apply]
  change (((Finsupp.supportedEquivFinsupp (R := R) {m | PairNormal k m}).symm
    (Finsupp.single m (1:R))) : (((Fin n ⊕ Fin n) →₀ ℕ) →₀ R)) d = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

theorem aevalTower_monomial_homogeneous {σ K R S : Type*} [Field K] [CommRing R]
    [CommRing S] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (L : R →ₐ[K] Polynomial S) (g : σ → S) (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) (e : ℕ) (hr : L r = Polynomial.monomial e (f r)) :
    MvPolynomial.aevalTower L (fun i => Polynomial.monomial (w i) (g i)) (monomial m r) =
      Polynomial.monomial (e + Finsupp.weight w m)
        (MvPolynomial.aevalTower f g (monomial m r)) := by
  classical
  change eval₂ L.toRingHom _ (monomial m r) = Polynomial.monomial _
    (eval₂ f.toRingHom g (monomial m r))
  rw [eval₂_monomial, eval₂_monomial]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [hr]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, Finsupp.prod, mul_pow,
    ← map_pow, Finset.prod_mul_distrib, ← map_prod]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
  have hw : (∑ i ∈ m.support, w i * m i) = Finsupp.weight w m := by
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]
  rw [hw, pow_add, map_mul]
  ring

theorem pairScale_monomial {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i))
    (m : (Fin n ⊕ Fin n) →₀ ℕ) (r : R) (e : ℕ)
    (hr : L r = Polynomial.monomial e r) :
    pairScale k A B q L hq (Ideal.Quotient.mk _ (monomial m r)) =
      Polynomial.monomial (e+Finsupp.weight (Sum.elim (fun _ => A) (fun _ => B)) m)
        (Ideal.Quotient.mk _ (monomial m r)) := by
  change pairScalePre k A B q L (monomial m r) = _
  have hs := aevalTower_monomial_homogeneous (pairCoeffs (K := K) k q)
    ((Polynomial.mapAlgHom (pairCoeffs (K := K) k q)).comp L)
    (fun i : Fin n ⊕ Fin n => Ideal.Quotient.mk _ (X i))
    (Sum.elim (fun _ => A) (fun _ => B)) m r e
    (by simp [hr])
  have he : MvPolynomial.aevalTower (pairCoeffs (K := K) k q)
      (fun i : Fin n ⊕ Fin n => Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mkₐ K _ := by
    apply MvPolynomial.algHom_ext'
    · ext r
      simp [pairCoeffs]
    · intro i
      simp
  simpa only [pairScalePre, he, Ideal.Quotient.mkₐ_eq_mk] using hs

theorem pairNormalBasis_smul {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0)
    (m : {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}) (r : R) :
    r • pairNormalBasis k q hq m = Ideal.Quotient.mk _ (monomial m.val r) := by
  rw [pairNormalBasis_apply]
  have hh := map_smul (Ideal.Quotient.mkₐ R (Ideal.span (Set.range (pairRelation k q)))) r
    (monomial m.val 1)
  simpa [MvPolynomial.smul_monomial, smul_eq_mul] using hh.symm

theorem pairBasis_homogeneous {n : ℕ} {ι K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (hnq : ∀ i, q i ≠ 0)
    (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i))
    (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (i : ι × {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}) :
    pairScale k A B q L hq ((b.smulTower (pairNormalBasis k q hnq)) i) =
      Polynomial.monomial (w i.1 +
        Finsupp.weight (Sum.elim (fun _ => A) (fun _ => B)) i.2.val)
        ((b.smulTower (pairNormalBasis k q hnq)) i) := by
  simp only [Module.Basis.smulTower_apply, pairNormalBasis_smul]
  exact pairScale_monomial k A B q L hq i.2.val (b i.1) (w i.1) (hb i.1)

theorem normPair_weightedLift_monomial {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) :
    normPair_weightedLift w (monomial m r) =
      Polynomial.C (monomial m r) * Polynomial.X ^ (Finsupp.weight w m) := by
  classical
  simp only [normPair_weightedLift, eval₂Hom_monomial, RingHom.comp_apply]
  simp only [Finsupp.prod, mul_pow, ← map_pow, Finset.prod_mul_distrib,
    ← map_prod]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  · rw [monomial_eq, Finsupp.prod]
  · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]

theorem weightedScale_monomial {σ K : Type*} [Field K] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : K) :
    weightedScale w (MvPolynomial.monomial m r) =
      Polynomial.monomial (Finsupp.weight w m) (MvPolynomial.monomial m r) := by
  exact (normPair_weightedLift_monomial w m r).trans Polynomial.C_mul_X_pow_eq_monomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

theorem mem_homogeneousSpace {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (T : ℕ) (x : R) :
    x ∈ homogeneousSpace L T ↔ L x = Polynomial.monomial T x := Iff.rfl

open scoped BigOperators

theorem homogeneous_coord {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (x : R) (t : ℕ) (i : ι) :
    b.repr ((L x).coeff t) i = if w i = t then b.repr x i else 0 := by
  classical
  let f := (b.coord i).comp (((Polynomial.lcoeff R t).restrictScalars K).comp L.toLinearMap)
  have hf : f = if w i = t then b.coord i else 0 := by
    apply b.ext
    intro j
    simp only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply, Polynomial.lcoeff_apply, hb, Polynomial.coeff_monomial]
    by_cases hij : i = j
    · subst j
      split_ifs <;> simp_all [Module.Basis.coord_apply]
    · have hji : j ≠ i := Ne.symm hij
      split_ifs <;> simp_all [Module.Basis.coord_apply]
  have hh := LinearMap.congr_fun hf x
  by_cases hi : w i = t
  · simpa [f, hi, Module.Basis.coord_apply] using hh
  · simpa [f, hi, Module.Basis.coord_apply] using hh

theorem homogeneousSpace_eq_basis_span {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i)) (T : ℕ) :
    homogeneousSpace L T = Submodule.span K (b '' {i | w i = T}) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [b.mem_span_image]
    intro i hi
    have hc := homogeneous_coord L b w hb x (w i) i
    rw [(mem_homogeneousSpace L T x).mp hx, Polynomial.coeff_monomial] at hc
    simp only [ite_true] at hc
    by_contra hn
    have hn' : w i ≠ T := hn
    rw [ite_eq_right (Ne.symm hn')] at hc
    simp only [map_zero, Finsupp.zero_apply] at hc
    exact (Finsupp.mem_support_iff.mp hi) hc.symm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact (hb i).trans (by rw [hi])

theorem homogeneousSpace_finrank {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i)) (T : ℕ)
    [Fintype {i // w i = T}] :
    Module.finrank K (homogeneousSpace L T) = Fintype.card {i // w i = T} := by
  rw [homogeneousSpace_eq_basis_span L b w hb T]
  have hs : b '' {i | w i = T} = Set.range (fun i : {i // w i = T} => b i.val) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  rw [hs]
  exact finrank_span_eq_card (b.linearIndependent.comp
    (fun i : {i // w i = T} => i.val) Subtype.val_injective)

open scoped BigOperators

private theorem normPair_card_antidiagonalTuple (h N : ℕ) :
    (Finset.Nat.antidiagonalTuple h N).card = h.multichoose N := by
  classical
  have hc := Finset.card_finsuppAntidiag_nat_eq_multichoose
    (s := (Finset.univ : Finset (Fin h))) N
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [← hc]
  apply Finset.card_bij (fun x _ => Finsupp.equivFunOnFinite.symm x)
  · intro x hx
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨by simpa [Finsupp.sum_fintype] using Finset.Nat.mem_antidiagonalTuple.mp hx,
      Finset.subset_univ _⟩
  · intro x _ y _ he
    exact Finsupp.equivFunOnFinite.symm.injective he
  · intro x hx
    refine ⟨Finsupp.equivFunOnFinite x, ?_, by simp⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [Finsupp.sum_fintype] using (Finset.mem_finsuppAntidiag'.mp hx).1

theorem normPair_card_simplexTuple (h N : ℕ) :
    (normPair_simplexTuple h N).card = (N+h).choose h := by
  classical
  rw [normPair_simplexTuple, Finset.card_biUnion]
  · simp_rw [normPair_card_antidiagonalTuple]
    exact Nat.sum_range_multichoose N h
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact hij ((Finset.Nat.mem_antidiagonalTuple.mp hi).symm.trans
      (Finset.Nat.mem_antidiagonalTuple.mp hj))

theorem mem_weightedTuple {h : ℕ} (w : Fin h → ℕ) (hw : ∀ i, 0 < w i)
    (T : ℕ) (x : Fin h → ℕ) :
    x ∈ weightedTuple w T ↔ ∑ i, w i*x i ≤ T := by
  classical
  simp only [weightedTuple, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hx
    refine ⟨fun i => ?_, hx⟩
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (w j*x j))
      (Finset.mem_univ i)
    have hixi : x i ≤ w i*x i := by nlinarith [hw i]
    omega

private theorem tuple_divmod_injective {h : ℕ} (m : Fin h → ℕ) :
    Function.Injective (fun x => (tupleQuot m x, tupleRem m x)) := by
  intro x y he
  have hq := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  funext i
  have hqi := congrFun hq i
  have hri := congrFun hr i
  dsimp [tupleQuot, tupleRem] at hqi hri
  have hx := Nat.mod_add_div (x i) (m i)
  have hy := Nat.mod_add_div (y i) (m i)
  rw [hqi, hri] at hx
  omega

theorem weightedTuple_upper {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i) (hL : 0 < L)
    (hprod : ∀ i, w i*m i = L) (T : ℕ) :
    (weightedTuple w T).card ≤ (normPair_simplexTuple h (T/L)).card * ∏ i, m i := by
  classical
  let R := Fintype.piFinset (fun i => Finset.range (m i))
  let f := fun x => (tupleQuot m x, tupleRem m x)
  have hin (x : Fin h → ℕ) (hx : x ∈ weightedTuple w T) :
      f x ∈ (normPair_simplexTuple h (T/L)) ×ˢ R := by
    apply Finset.mem_product.mpr
    refine ⟨(normPair_mem_simplexTuple _).mpr ?_, ?_⟩
    · apply (Nat.le_div_iff_mul_le hL).mpr
      calc
        (∑ i, tupleQuot m x i)*L = ∑ i, w i*(m i*(x i/m i)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          dsimp [tupleQuot]
          rw [← hprod i]
          ring
        _ ≤ ∑ i, w i*x i := Finset.sum_le_sum (fun i _ =>
          Nat.mul_le_mul_left (w i) (Nat.mul_div_le (x i) (m i)))
        _ ≤ T := (mem_weightedTuple w hw T x).mp hx
    · simp [R, f, tupleRem, Nat.mod_lt _ (hm _)]
  have hc := Finset.card_le_card_of_injOn f hin
    (fun _ _ _ _ he => tuple_divmod_injective m he)
  simpa [R, Finset.card_product, Fintype.card_piFinset] using hc

theorem weightedTuple_lower {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i)
    (hprod : ∀ i, w i*m i = L) (T : ℕ) (hT : h ≤ T/L) :
    (normPair_simplexTuple h (T/L-h)).card * ∏ i, m i ≤ (weightedTuple w T).card := by
  classical
  let R := Fintype.piFinset (fun i => Finset.range (m i))
  let f : (Fin h → ℕ) × (Fin h → ℕ) → (Fin h → ℕ) :=
    fun x i => m i*x.1 i+x.2 i
  have hh (x : (Fin h → ℕ) × (Fin h → ℕ))
      (hx : x ∈ (normPair_simplexTuple h (T/L-h)) ×ˢ R) :
      (∑ i, x.1 i ≤ T/L-h) ∧ ∀ i, x.2 i < m i := by
    rcases Finset.mem_product.mp hx with ⟨hq, hr⟩
    exact ⟨(normPair_mem_simplexTuple _).mp hq, by simpa [R] using hr⟩
  have hin (x : (Fin h → ℕ) × (Fin h → ℕ))
      (hx : x ∈ (normPair_simplexTuple h (T/L-h)) ×ˢ R) : f x ∈ weightedTuple w T := by
    apply (mem_weightedTuple w hw T _).mpr
    obtain ⟨hxq, hxr⟩ := hh x hx
    calc
      (∑ i, w i*(f x i)) = L*(∑ i, x.1 i) + ∑ i, w i*x.2 i := by
        simp only [f, mul_add, ← mul_assoc, hprod, Finset.sum_add_distrib,
          Finset.mul_sum]
      _ ≤ L*(T/L-h) + h*L := by
        apply Nat.add_le_add (Nat.mul_le_mul_left L hxq)
        calc
          ∑ i, w i*x.2 i ≤ ∑ _i : Fin h, L := Finset.sum_le_sum (fun i _ => by
            rw [← hprod i]; exact Nat.mul_le_mul_left _ (hxr i).le)
          _ = h*L := by simp
      _ = L*(T/L) := by rw [Nat.mul_sub_left_distrib, Nat.mul_comm h L,
        Nat.sub_add_cancel (Nat.mul_le_mul_left L hT)]
      _ ≤ T := Nat.mul_div_le T L
  have hi : Set.InjOn f ↑((normPair_simplexTuple h (T/L-h)) ×ˢ R) := by
    intro x hx y hy he
    obtain ⟨_, hxr⟩ := hh x hx
    obtain ⟨_, hyr⟩ := hh y hy
    have hq : x.1 = y.1 := by
      funext i
      have hd := congrArg (fun v => v i / m i) he
      simpa [f, Nat.mul_add_div (hm i), Nat.div_eq_of_lt (hxr i),
        Nat.div_eq_of_lt (hyr i)] using hd
    apply Prod.ext hq
    funext i
    have hd := congrFun he i
    dsimp [f] at hd
    rw [hq] at hd
    omega
  have hc := Finset.card_le_card_of_injOn f hin hi
  simpa [R, Finset.card_product, Fintype.card_piFinset] using hc

theorem simplexTuple_power_bounds (h N : ℕ) :
    N^h ≤ h.factorial*(normPair_simplexTuple h N).card ∧
    h.factorial*(normPair_simplexTuple h N).card ≤ (N+h)^h := by
  rw [normPair_card_simplexTuple, ← Nat.descFactorial_eq_factorial_mul_choose]
  refine ⟨?_, Nat.descFactorial_le_pow _ _⟩
  have he : N+h+1-h = N+1 := by omega
  exact (Nat.pow_le_pow_left (by omega : N ≤ N+1) h).trans
    (he ▸ Nat.pow_sub_le_descFactorial (N+h) h)

theorem prod_weight_comultiples {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hprod : ∀ i, w i*m i = L) :
    (∏ i, w i)*(∏ i, m i) = L^h := by
  rw [← Finset.prod_mul_distrib]
  simp_rw [hprod]
  simp

theorem weightedTuple_power_bounds {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i) (hL : 0 < L)
    (hprod : ∀ i, w i*m i = L) (T : ℕ) (hT : h ≤ T/L) :
    (L*(T/L-h))^h ≤ h.factorial*(∏ i, w i)*(weightedTuple w T).card ∧
    h.factorial*(∏ i, w i)*(weightedTuple w T).card ≤ (L*(T/L+h))^h := by
  have hu := weightedTuple_upper w m L hw hm hL hprod T
  have hl := weightedTuple_lower w m L hw hm hprod T hT
  have hpu := (simplexTuple_power_bounds h (T/L)).2
  have hpl := (simplexTuple_power_bounds h (T/L-h)).1
  have hp := prod_weight_comultiples w m L hprod
  constructor
  · calc
      (L*(T/L-h))^h = (∏ i, w i)*(∏ i, m i)*(T/L-h)^h := by rw [mul_pow, hp]
      _ ≤ (∏ i, w i)*(∏ i, m i)*(h.factorial*(normPair_simplexTuple h (T/L-h)).card) :=
        Nat.mul_le_mul_left _ hpl
      _ = (h.factorial*(∏ i, w i))*
          ((normPair_simplexTuple h (T/L-h)).card*(∏ i, m i)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hl
  · calc
      h.factorial*(∏ i, w i)*(weightedTuple w T).card ≤
          h.factorial*(∏ i, w i)*((normPair_simplexTuple h (T/L)).card*(∏ i, m i)) :=
        Nat.mul_le_mul_left _ hu
      _ = (∏ i, w i)*(∏ i, m i)*(h.factorial*(normPair_simplexTuple h (T/L)).card) := by ring
      _ ≤ (∏ i, w i)*(∏ i, m i)*(T/L+h)^h := Nat.mul_le_mul_left _ hpu
      _ = (L*(T/L+h))^h := by rw [mul_pow, hp]

private theorem nearby_power_error (h : ℕ) {x y c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c) (hd : |y-x| ≤ c) :
    |y^h-x^h| ≤ c*h*(c+1)^(h-1)*(x+1)^(h-1) := by
  have hmax : max |y| |x| ≤ (c+1)*(x+1) := by
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    apply max_le
    · have hi := (abs_le.mp hd).2
      nlinarith
    · nlinarith
  calc
    |y^h-x^h| ≤ |y-x| * h * max |y| |x| ^ (h-1) := abs_pow_sub_pow_le y x h
    _ ≤ c*h*((c+1)*(x+1))^(h-1) := by gcongr
    _ = c*h*(c+1)^(h-1)*(x+1)^(h-1) := by rw [mul_pow]; ring

theorem weightedTuple_volume_error_with_scale {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i) (hL : 0 < L)
    (hprod : ∀ i, w i*m i = L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, h*L ≤ T →
      |((weightedTuple w T).card : ℝ) -
        (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)| ≤ C*((T:ℝ)+1)^(h-1) := by
  let c : ℝ := (h+1:ℕ)*L
  let s : ℝ := (h.factorial*(∏ i, w i) : ℕ)
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos h) (Finset.prod_pos (fun i _ => hw i))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c*h*(c+1)^(h-1)/s, by positivity, fun T hT => ?_⟩
  have hq : h ≤ T/L := (Nat.le_div_iff_mul_le hL).mpr hT
  obtain ⟨hl, hu⟩ := weightedTuple_power_bounds w m L hw hm hL hprod T hq
  have hl' : ((L*(T/L-h):ℕ):ℝ)^h ≤ s*(weightedTuple w T).card := by dsimp [s]; exact_mod_cast hl
  have hu' : s*(weightedTuple w T).card ≤ ((L*(T/L+h):ℕ):ℝ)^h := by dsimp [s]; exact_mod_cast hu
  have hnl : L*(T/L-h) ≤ T := by
    calc L*(T/L-h) ≤ L*(T/L) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
         _ ≤ T := Nat.mul_div_le T L
  have hnr : T < L*(T/L-h)+(h+1)*L := by
    have he : L*(T/L-h)+h*L = L*(T/L) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_comm h L,
        Nat.sub_add_cancel (Nat.mul_le_mul_left L hq)]
    have hr := Nat.mod_lt T hL
    have ht := Nat.mod_add_div T L
    nlinarith
  have hup : L*(T/L+h) ≤ T+(h+1)*L := by
    have ht := Nat.mul_div_le T L
    nlinarith
  have hdown : T ≤ L*(T/L+h)+(h+1)*L := by
    have ht := Nat.mod_add_div T L
    have hr := Nat.mod_lt T hL
    nlinarith
  have hnl' : ((L*(T/L-h):ℕ):ℝ) ≤ (T:ℝ) := by exact_mod_cast hnl
  have hnr' : (T:ℝ) < ((L*(T/L-h):ℕ):ℝ)+c := by dsimp [c]; exact_mod_cast hnr
  have hup' : ((L*(T/L+h):ℕ):ℝ) ≤ (T:ℝ)+c := by dsimp [c]; exact_mod_cast hup
  have hdown' : (T:ℝ) ≤ ((L*(T/L+h):ℕ):ℝ)+c := by dsimp [c]; exact_mod_cast hdown
  have hdl : |((L*(T/L-h):ℕ):ℝ)-(T:ℝ)| ≤ c := by
    apply abs_le.mpr
    constructor <;> linarith
  have hdu : |((L*(T/L+h):ℕ):ℝ)-(T:ℝ)| ≤ c := by
    apply abs_le.mpr
    constructor <;> linarith
  have el := nearby_power_error h (Nat.cast_nonneg T) (Nat.cast_nonneg _) hc hdl
  have eu := nearby_power_error h (Nat.cast_nonneg T) (Nat.cast_nonneg _) hc hdu
  have he : |s*(weightedTuple w T).card-(T:ℝ)^h| ≤
      c*h*(c+1)^(h-1)*((T:ℝ)+1)^(h-1) := by
    apply abs_le.mpr
    have hel := (abs_le.mp el).1
    have heu := (abs_le.mp eu).2
    constructor <;> linarith
  change |(weightedTuple w T).card-(T:ℝ)^h/s| ≤ _
  calc
    |(weightedTuple w T).card-(T:ℝ)^h/s| =
        |s*(weightedTuple w T).card-(T:ℝ)^h|/s := by
      rw [← abs_of_pos hs, ← abs_div]
      congr 1
      rw [abs_of_pos hs]
      field_simp
    _ ≤ (c*h*(c+1)^(h-1)*((T:ℝ)+1)^(h-1))/s :=
      div_le_div_of_nonneg_right he hs.le
    _ = _ := by ring

theorem weightedTuple_volume_error {h : ℕ} (w : Fin h → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((weightedTuple w T).card : ℝ) -
        (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)| ≤ C*((T:ℝ)+1)^(h-1) := by
  classical
  let L := ∏ i, w i
  let m := fun i => ∏ j ∈ Finset.univ.erase i, w j
  have hL : 0 < L := Finset.prod_pos (fun i _ => hw i)
  have hm : ∀ i, 0 < m i := fun _ => Finset.prod_pos (fun i _ => hw i)
  have hprod : ∀ i, w i*m i = L := fun i =>
    Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  obtain ⟨C, hC, herror⟩ := weightedTuple_volume_error_with_scale w m L hw hm hL hprod
  let e := fun T : ℕ => |((weightedTuple w T).card : ℝ) -
    (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)|
  let S := ∑ T ∈ Finset.range (h*L), e T
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C+S, by linarith, fun T => ?_⟩
  by_cases ht : h*L ≤ T
  · exact (herror T ht).trans (mul_le_mul_of_nonneg_right (by linarith)
      (by positivity))
  · have he : e T ≤ S := Finset.single_le_sum (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
    have hfactor : 1 ≤ ((T:ℝ)+1)^(h-1) := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
    change e T ≤ _
    calc e T ≤ C+S := by linarith
         _ ≤ (C+S)*((T:ℝ)+1)^(h-1) := le_mul_of_one_le_right (by linarith) hfactor

theorem shiftedTuple_volume_error {h : ℕ} (w : Fin h → ℕ) (hw : ∀ i, 0 < w i)
    (e : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |(shiftedTupleCount w e T : ℝ) -
        (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)| ≤ C*((T:ℝ)+1)^(h-1) := by
  obtain ⟨C, hC, herror⟩ := weightedTuple_volume_error w hw
  let s : ℝ := (h.factorial*(∏ i, w i) : ℕ)
  let B : ℝ := (e:ℝ)*h*((e:ℝ)+1)^(h-1)/s
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos h) (Finset.prod_pos (fun i _ => hw i))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨C+B+(e:ℝ)^h/s, by positivity, fun T => ?_⟩
  have ht0 : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have hf : 1 ≤ ((T:ℝ)+1)^(h-1) := one_le_pow₀ (by linarith)
  by_cases heT : e ≤ T
  · rw [shiftedTupleCount, ite_eq_left heT]
    have hnat : ((T-e:ℕ):ℝ) ≤ (T:ℝ) := by exact_mod_cast Nat.sub_le T e
    have hdiff : |((T-e:ℕ):ℝ)-(T:ℝ)| ≤ (e:ℝ) := by
      rw [Nat.cast_sub heT]
      have : (T:ℝ)-(e:ℝ)-(T:ℝ) = -(e:ℝ) := by ring
      rw [this, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    have he := nearby_power_error h (Nat.cast_nonneg T) (Nat.cast_nonneg _)
      (Nat.cast_nonneg e) hdiff
    have he' : |((T-e:ℕ):ℝ)^h/s-(T:ℝ)^h/s| ≤ B*((T:ℝ)+1)^(h-1) := by
      rw [← sub_div, abs_div, abs_of_pos hs]
      calc
        |((T-e:ℕ):ℝ)^h-(T:ℝ)^h|/s ≤
            ((e:ℝ)*h*((e:ℝ)+1)^(h-1)*((T:ℝ)+1)^(h-1))/s :=
          div_le_div_of_nonneg_right he hs.le
        _ = _ := by dsimp [B]; ring
    have hbase : |((weightedTuple w (T-e)).card : ℝ)-((T-e:ℕ):ℝ)^h/s| ≤
        C*((T:ℝ)+1)^(h-1) := by
      exact (herror (T-e)).trans (by gcongr)
    change |((weightedTuple w (T-e)).card : ℝ)-(T:ℝ)^h/s| ≤ _
    calc
      _ ≤ |((weightedTuple w (T-e)).card : ℝ)-((T-e:ℕ):ℝ)^h/s| +
          |((T-e:ℕ):ℝ)^h/s-(T:ℝ)^h/s| := abs_sub_le _ _ _
      _ ≤ (C+B)*((T:ℝ)+1)^(h-1) := by nlinarith [hbase, he']
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · rw [shiftedTupleCount, ite_eq_right heT, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (by positivity)]
    change (T:ℝ)^h/s ≤ _
    have he : (T:ℝ) ≤ (e:ℝ) := by exact_mod_cast (by omega : T ≤ e)
    calc
      (T:ℝ)^h/s ≤ (e:ℝ)^h/s := by gcongr
      _ ≤ C+B+(e:ℝ)^h/s := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hf

theorem sectorPoint_normal {u v : ℕ} (c : PairSector u v) (x : ℕ) :
    (sectorPoint c x).1 < u ∨ (sectorPoint c x).2 < v := by
  cases c with
  | inl r => exact Or.inl r.isLt
  | inr r => exact Or.inr r.isLt

theorem sectorPoint_injective {u v : ℕ} :
    Function.Injective (fun p : PairSector u v × ℕ => sectorPoint p.1 p.2) := by
  rintro ⟨c,x⟩ ⟨d,y⟩ he
  cases c with
  | inl r =>
    cases d with
    | inl s =>
      simp only [sectorPoint, Prod.mk.injEq] at he
      exact Prod.ext (congrArg Sum.inl (Fin.ext he.1)) he.2
    | inr s =>
      have he' := congrArg Prod.fst he
      dsimp [sectorPoint] at he'
      have := r.isLt
      omega
  | inr r =>
    cases d with
    | inl s =>
      have he' := congrArg Prod.fst he
      dsimp [sectorPoint] at he'
      have := s.isLt
      omega
    | inr s =>
      simp only [sectorPoint, Prod.mk.injEq] at he
      exact Prod.ext (congrArg Sum.inr (Fin.ext he.2)) (Nat.add_left_cancel he.1)

theorem sectorPoint_surjective {u v : ℕ} (p : ℕ × ℕ)
    (hp : p.1 < u ∨ p.2 < v) :
    ∃ c : PairSector u v, ∃ x : ℕ, sectorPoint c x = p := by
  by_cases h : p.1 < u
  · exact ⟨Sum.inl ⟨p.1,h⟩, p.2, rfl⟩
  · have h' : p.2 < v := hp.resolve_left h
    refine ⟨Sum.inr ⟨p.2,h'⟩, p.1-u, ?_⟩
    exact Prod.ext (by dsimp [sectorPoint]; omega) rfl

theorem sector_weight_identity (A B : ℕ) {u v : ℕ} (c : PairSector u v) (x : ℕ) :
    A*(sectorPoint c x).1+B*(sectorPoint c x).2 =
      sectorShift A B c + sectorWeight A B c*x := by
  cases c with
  | inl r => rfl
  | inr r => simp only [sectorPoint, sectorShift, sectorWeight]; ring

theorem sectorWeight_pos {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    {u v : ℕ} (c : PairSector u v) : 0 < sectorWeight A B c := by
  cases c <;> assumption

theorem mem_normalPairTuples {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) (T : ℕ) (p : Fin h → ℕ × ℕ) :
    p ∈ normalPairTuples A B u v T ↔
      (∀ i, (p i).1 < u i ∨ (p i).2 < v i) ∧
        ∑ i, (A*(p i).1+B*(p i).2) ≤ T := by
  classical
  simp only [normalPairTuples, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hp
    refine ⟨fun i => ?_, hp⟩
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      Nat.zero_le (A*(p j).1+B*(p j).2)) (Finset.mem_univ i)
    have ha : (p i).1 ≤ A*(p i).1 := by nlinarith
    have hb : (p i).2 ≤ B*(p i).2 := by nlinarith
    constructor <;> omega

theorem mem_sectorTuples {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) (T : ℕ)
    (p : Σ _c : (i : Fin h) → PairSector (u i) (v i), Fin h → ℕ) :
    p ∈ sectorTuples A B u v T ↔
      (∑ i, sectorShift A B (p.1 i)) +
        (∑ i, sectorWeight A B (p.1 i)*p.2 i) ≤ T := by
  classical
  simp only [sectorTuples, Finset.mem_sigma, Finset.mem_univ, true_and]
  split_ifs with ht
  · rw [mem_weightedTuple _ (fun _ => sectorWeight_pos hA hB _)]; omega
  · simp only [Finset.notMem_empty, false_iff]; omega

theorem card_normalPairTuples {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) (T : ℕ) :
    (normalPairTuples A B u v T).card =
      ∑ c : (i : Fin h) → PairSector (u i) (v i),
        shiftedTupleCount (fun i => sectorWeight A B (c i))
          (∑ i, sectorShift A B (c i)) T := by
  classical
  have hc : (sectorTuples A B u v T).card = (normalPairTuples A B u v T).card := by
    apply Finset.card_bij (fun p _ => fun i => sectorPoint (p.1 i) (p.2 i))
    · intro p hp
      apply (mem_normalPairTuples hA hB u v T _).mpr
      refine ⟨fun i => sectorPoint_normal _ _, ?_⟩
      simp_rw [sector_weight_identity, Finset.sum_add_distrib]
      exact (mem_sectorTuples hA hB u v T p).mp hp
    · intro p _ q _ hpq
      have he (i : Fin h) : (p.1 i, p.2 i) = (q.1 i, q.2 i) :=
        sectorPoint_injective (congrFun hpq i)
      have hc : p.1 = q.1 := funext (fun i => congrArg Prod.fst (he i))
      have hx : p.2 = q.2 := funext (fun i => congrArg Prod.snd (he i))
      cases p; cases q; dsimp at hc hx; cases hc; cases hx; rfl
    · intro p hp
      obtain ⟨hn, ht⟩ := (mem_normalPairTuples hA hB u v T p).mp hp
      choose c x hx using (fun i => sectorPoint_surjective (p i) (hn i))
      refine ⟨⟨c,x⟩, (mem_sectorTuples hA hB u v T _).mpr ?_, funext hx⟩
      simpa only [← Finset.sum_add_distrib, ← sector_weight_identity, hx] using ht
  rw [← hc]
  simp only [sectorTuples, Finset.card_sigma, shiftedTupleCount]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

theorem normalPairTuples_volume_error {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((normalPairTuples A B u v T).card : ℝ) -
        (T:ℝ)^h * (∑ c : (i : Fin h) → PairSector (u i) (v i),
          1 / ((h.factorial * ∏ i, sectorWeight A B (c i) : ℕ):ℝ))| ≤
        C*((T:ℝ)+1)^(h-1) := by
  classical
  have he (c : (i : Fin h) → PairSector (u i) (v i)) :=
    shiftedTuple_volume_error (fun i => sectorWeight A B (c i))
      (fun _ => sectorWeight_pos hA hB _) (∑ i, sectorShift A B (c i))
  choose C hC herr using he
  refine ⟨∑ c, C c, Finset.sum_nonneg (fun c _ => hC c), fun T => ?_⟩
  rw [card_normalPairTuples hA hB, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, |(shiftedTupleCount (fun i => sectorWeight A B (c i))
        (∑ i, sectorShift A B (c i)) T : ℝ) -
        (T:ℝ)^h*(1 / ((h.factorial * ∏ i, sectorWeight A B (c i) : ℕ):ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, C c*((T:ℝ)+1)^(h-1) := Finset.sum_le_sum (fun c _ => by
      simpa only [mul_one_div] using herr c T)
    _ = _ := by rw [Finset.sum_mul]

private theorem sector_reciprocal_sum (A B u v : ℕ) :
    (∑ c : PairSector u v, 1/(sectorWeight A B c : ℝ)) = (u:ℝ)/B+(v:ℝ)/A := by
  change (∑ c : Fin u ⊕ Fin v, 1/(sectorWeight A B c : ℝ)) = _
  rw [Fintype.sum_sum_type]
  simp [sectorWeight, nsmul_eq_mul, div_eq_mul_inv]

private theorem sector_coefficient {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) :
    (∑ c : (i : Fin h) → PairSector (u i) (v i),
      1 / ((h.factorial * ∏ i, sectorWeight A B (c i) : ℕ):ℝ)) =
      (∏ i, ((u i:ℝ)*A+(v i:ℝ)*B)) /
        ((h.factorial:ℝ)*(A:ℝ)^h*(B:ℝ)^h) := by
  classical
  have ha : (A:ℝ) ≠ 0 := by positivity
  have hb : (B:ℝ) ≠ 0 := by positivity
  calc
    _ = (∑ c : (i : Fin h) → PairSector (u i) (v i),
        ∏ i, 1/(sectorWeight A B (c i) : ℝ))/(h.factorial:ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      simp [Nat.cast_mul, Nat.cast_prod, div_eq_mul_inv, Finset.prod_inv_distrib, mul_comm]
    _ = (∏ i, ∑ c : PairSector (u i) (v i),
        1/(sectorWeight A B c : ℝ))/(h.factorial:ℝ) := by
      rw [Fintype.prod_sum]
    _ = (∏ i, ((u i:ℝ)*A+(v i:ℝ)*B)/((A:ℝ)*B))/(h.factorial:ℝ) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [sector_reciprocal_sum]
      field_simp
    _ = _ := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
      rw [div_div]
      congr 1
      ring

theorem normalPairTuples_hilbert_error {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((normalPairTuples A B u v T).card : ℝ) -
        (∏ i, ((u i:ℝ)*A+(v i:ℝ)*B)) /
          ((h.factorial:ℝ)*(A:ℝ)^h*(B:ℝ)^h)*(T:ℝ)^h| ≤
        C*((T:ℝ)+1)^(h-1) := by
  obtain ⟨C,hC,herror⟩ := normalPairTuples_volume_error hA hB u v
  refine ⟨C,hC,fun T => ?_⟩
  simpa only [sector_coefficient hA hB, mul_comm] using herror T

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open scoped BigOperators

theorem pairConeBasis_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (i : PairBasisIndex n k) :
    pairConeScale k A B θ (pairConeBasis k A B hB θ i) =
      Polynomial.monomial (pairBasisWeight A B i) (pairConeBasis k A B hB θ i) := by
  apply pairBasis_homogeneous
  intro m
  exact weightedScale_monomial (triplePairWeights A B) m 1

theorem pairCone_finrank {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K) (T : ℕ) :
    Module.finrank K (homogeneousSpace (pairConeScale k A B θ) T) =
      (ambientPairTuples n A B k T).card := by
  classical
  let := Fintype.ofEquiv _ (pairBasisWeightEquiv (n := n) (k := k) hA hB T).symm
  rw [homogeneousSpace_finrank _ (pairConeBasis k A B hB θ) (pairBasisWeight A B)
    (pairConeBasis_homogeneous k A B hB θ) T]
  exact (Fintype.card_congr (pairBasisWeightEquiv hA hB T)).trans (Fintype.card_coe _)

open MvPolynomial

theorem pairMap_eq_zero_iff_dvd {n : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (k : ℕ) (q : Fin n → R) (f : R →+* S)
    (hq : ∀ i, q i ≠ 0) (hFq : ∀ i, f (q i) ≠ 0)
    (t : R) (ht : ∀ r, f r = 0 ↔ t ∣ r) (x : PairRing k q) :
    pairMap k q f x = 0 ↔ pairCoeffMap k q t ∣ x := by
  classical
  obtain ⟨p,hp⟩ := (pair_normal_quotient_bijective k q hq).2 x
  change Ideal.Quotient.mk _ p.val = x at hp
  subst x
  constructor
  · intro hx
    have hn : ∀ m ∈ (MvPolynomial.map f p.val).support, PairNormal k m :=
      fun m hm => p.property (MvPolynomial.support_map_subset _ _ hm)
    have hz : MvPolynomial.map f p.val = 0 := by
      apply pairLaurentMap_normal_injective k (fun i => f (q i)) hFq _ hn
      have hh : MvPolynomial.map f p.val ∈
          Ideal.span (Set.range (pairRelation k (fun i => f (q i)))) :=
        Ideal.Quotient.eq_zero_iff_mem.mp hx
      rwa [pair_ideal_eq_ker k _ hFq] at hh
    obtain ⟨r,hr⟩ := (MvPolynomial.C_dvd_iff_map_hom_eq_zero f t ht p.val).mpr hz
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    change Ideal.Quotient.mk _ p.val =
      Ideal.Quotient.mk _ (C t) * Ideal.Quotient.mk _ r
    rw [← map_mul, hr]
  · rintro ⟨r,hr⟩
    rw [hr, map_mul]
    have hft : f t = 0 := (ht t).mpr dvd_rfl
    suffices pairMap k q f (pairCoeffMap k q t) = 0 by rw [this, zero_mul]
    change Ideal.Quotient.mk _ (MvPolynomial.map f (C t)) = 0
    simp [hft]

theorem pairCoeff_span_isPrime {n : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (k : ℕ) (q : Fin n → R) (f : R →+* S)
    (hq : ∀ i, q i ≠ 0) (hFq : ∀ i, f (q i) ≠ 0)
    (t : R) (ht : ∀ r, f r = 0 ↔ t ∣ r) :
    (Ideal.span {pairCoeffMap k q t}).IsPrime := by
  let : (Ideal.span (Set.range (pairRelation k (fun i => f (q i))))).IsPrime :=
    pair_ideal_isPrime k _ hFq
  have he : Ideal.span {pairCoeffMap k q t} = RingHom.ker (pairMap k q f) := by
    ext x
    simp only [Ideal.mem_span_singleton, RingHom.mem_ker]
    exact (pairMap_eq_zero_iff_dvd k q f hq hFq t ht x).symm
  rw [he]
  exact RingHom.ker_isPrime _

theorem pairCoeffMap_injective {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Function.Injective (pairCoeffMap k q) := by
  intro r s h
  have hm : C (r-s) ∈ Ideal.span (Set.range (pairRelation k q)) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change pairCoeffMap k q (r-s) = 0
    rw [map_sub,h,sub_self]
  rw [pair_ideal_eq_ker k q hq] at hm
  have hh : pairLaurentMap k q (C (r-s)) = 0 := hm
  simpa [pairLaurentMap, AddMonoidAlgebra.single_eq_zero, sub_eq_zero] using hh

open Classical

theorem X_dvd_sub_eraseVariable {σ R : Type*} [CommRing R]
    (i : σ) (p : MvPolynomial σ R) : X i ∣ p - eraseVariable i p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hp hq
  | mul_X p j hp =>
    rw [map_mul, eraseVariable_X]
    by_cases hj : j = i
    · simp only [hj, ite_true, mul_zero, sub_zero]
      exact dvd_mul_left _ _
    · simpa only [ite_eq_right hj, ← sub_mul] using dvd_mul_of_dvd_left hp (X j)

theorem eraseVariable_eq_zero_iff {σ R : Type*} [CommRing R]
    (i : σ) (p : MvPolynomial σ R) : eraseVariable i p = 0 ↔ X i ∣ p := by
  classical
  constructor
  · intro h
    simpa [h] using X_dvd_sub_eraseVariable i p
  · rintro ⟨r,rfl⟩
    simp

theorem pairCone_t_prime {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) :
    Prime (pairCoeffMap k (pairConeQ k A B θ) (X 2)) := by
  have hq := pairConeQ_ne_zero k A B hB θ
  have hQ : k*A+B ≠ 0 := by omega
  have hf : ∀ i, eraseVariable (R := K) (2 : Fin 3) (pairConeQ k A B θ i) ≠ 0 := by
    intro i
    simp only [pairConeQ, map_add, map_mul, map_pow, eraseVariable_X,
      eraseVariable_C, show (0:Fin 3) ≠ 2 by decide, show (1:Fin 3) ≠ 2 by decide,
      ite_false, ite_true, zero_pow hQ, mul_zero, add_zero]
    exact mul_ne_zero (pow_ne_zero _ (X_ne_zero _)) (X_ne_zero _)
  have ht : pairCoeffMap k (pairConeQ k A B θ) (X 2) ≠ 0 := by
    intro hz
    exact X_ne_zero (R := K) (2 : Fin 3)
      ((pairCoeffMap_injective k _ hq) (hz.trans (map_zero _).symm))
  apply (Ideal.span_singleton_prime ht).mp
  exact pairCoeff_span_isPrime k _ (eraseVariable (R := K) (2:Fin 3)) hq hf (X 2)
    (eraseVariable_eq_zero_iff _)

theorem pairScale_coeff {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i)) (r : R) :
    pairScale k A B q L hq (pairCoeffMap k q r) =
      Polynomial.map (pairCoeffMap k q) (L r) := by
  change pairScalePre k A B q L (C r) = _
  simp only [pairScalePre, MvPolynomial.aevalTower_C, AlgHom.comp_apply]
  rfl

theorem pairCone_t_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) :
    pairConeScale k A B θ (pairCoeffMap k (pairConeQ k A B θ) (X 2)) =
      Polynomial.monomial 1 (pairCoeffMap k (pairConeQ k A B θ) (X 2)) := by
  simp only [pairConeScale, pairScale_coeff, weightedScale_X, triplePairWeights,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Polynomial.map_monomial]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_BoundedLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section

open scoped BigOperators

lemma monomial_eq_univ_prod {σ R : Type*} [Fintype σ] [CommSemiring R]
    (m : σ →₀ ℕ) (r : R) : MvPolynomial.monomial m r =
      MvPolynomial.C r * ∏ j, MvPolynomial.X j ^ m j := by
  rw [MvPolynomial.monomial_eq]
  congr 1
  exact Finsupp.prod_fintype _ _ (fun j => pow_zero _)

end

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_QuarticPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

lemma pairConeBasis_map {n : ℕ} {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (i : PairBasisIndex n k) :
    φ (pairConeBasis k A B hB θ i) =
      MvPolynomial.aeval (Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ))
        (MvPolynomial.monomial (pairABExponent i) (1 : K)) := by
  classical
  simp only [pairConeBasis,Module.Basis.smulTower_apply,pairNormalBasis_smul]
  change φ (Ideal.Quotient.mk _ (MvPolynomial.monomial i.2.val (MvPolynomial.monomial i.1 (1 : K)))) = _
  simp only [monomial_eq_univ_prod,map_mul,map_prod,map_pow,map_one,one_mul,
    MvPolynomial.aeval_X]
  have ht' : φ (Ideal.Quotient.mk _ (MvPolynomial.C (MvPolynomial.X 2))) = 1 := ht
  simp only [Fintype.prod_sum_type]
  simp [Fin.prod_univ_succ,ht',pairABExponent,pairConeA,pairConeB,pairIndexToTuple,pairCoeffMap]
  ring

lemma pairConePolynomial_eval {n : ℕ} {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (c : PairCone k A B θ) :
    MvPolynomial.aeval (Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ))
      (pairConePolynomial k A B hB θ c) = φ c := by
  classical
  let b := pairConeBasis k A B hB θ
  have he (i : PairBasisIndex n k) (r : K) :
      MvPolynomial.monomial (pairABExponent i) r =
        r • MvPolynomial.monomial (pairABExponent i) (1 : K) := by
    simp [MvPolynomial.smul_monomial]
  have heval (i : PairBasisIndex n k) (r : K) :
      MvPolynomial.aeval (Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ))
        (MvPolynomial.monomial (pairABExponent i) r) = r • φ (b i) := by
    rw [he,map_smul,← pairConeBasis_map k A B hB θ φ ht]
  simp only [pairConePolynomial,Finsupp.sum,map_sum,heval]
  simpa only [b,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul] using
    congrArg φ (b.linearCombination_repr c)

lemma pairConePolynomial_weight {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (c : PairCone k A B θ) (D : ℕ)
    (hc : pairConeScale k A B θ c = Polynomial.monomial D c) :
    ∀ m ∈ (pairConePolynomial k A B hB θ c).support,
      A * (∑ i, m (Sum.inl i)) + B * (∑ j, m (Sum.inr j)) ≤ D := by
  classical
  let b := pairConeBasis k A B hB θ
  have hcoord (i : PairBasisIndex n k) (hi : i ∈ (b.repr c).support) :
      pairBasisWeight A B i = D := by
    have h := homogeneous_coord (pairConeScale k A B θ) b (pairBasisWeight A B)
      (pairConeBasis_homogeneous k A B hB θ) c D i
    simp only [hc,Polynomial.coeff_monomial,ite_true] at h
    by_contra hn
    rw [ite_eq_right hn] at h
    exact (Finsupp.mem_support_iff.mp hi) h
  intro m hm
  have hmem := MvPolynomial.support_sum hm
  obtain ⟨i,hi,hm'⟩ := Finset.mem_biUnion.mp hmem
  have hmi : m = pairABExponent i := by
    exact Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')
  rw [hmi]
  have he := hcoord i hi
  rw [pairBasisWeight_eq] at he
  change A * (∑ j, (pairIndexToTuple i j).1) + B * (∑ j, (pairIndexToTuple i j).2) ≤ D
  have hsum : (∑ j, (A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2)) =
      A * (∑ j, (pairIndexToTuple i j).1) + B * (∑ j, (pairIndexToTuple i j).2) := by
    simp only [Finset.sum_add_distrib,Finset.mul_sum]
  rw [hsum] at he
  omega

open scoped BigOperators
open MvPolynomial

end

open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_LaurentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

theorem pairToLaurent_injective {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Function.Injective (pairToLaurent k q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [pair_ideal_eq_ker k q hq]
  exact hx

end

open MvPolynomial

open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PrincipalLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

theorem homogeneous_dehomogenization_zero {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {t x : R} {D : ℕ} (ht0 : t ≠ 0)
    (ht : L t = Polynomial.monomial 1 t)
    (hx : L x = Polynomial.monomial D x)
    (hzero : Ideal.Quotient.mk (Ideal.span {t-1}) x = 0) : x = 0 := by
  let S := Localization.Away t
  let a : R →+* S := algebraMap R S
  let z : S := IsLocalization.Away.invSelf t
  let ev : R →+* S := (Polynomial.eval₂RingHom a z).comp L.toRingHom
  have het : ev (t-1) = 0 := by
    rw [map_sub,map_one,sub_eq_zero]
    change Polynomial.eval₂ a z (L t) = 1
    rw [ht,Polynomial.eval₂_monomial,pow_one]
    exact IsLocalization.Away.mul_invSelf t
  have hker : Ideal.span {t-1} ≤ RingHom.ker ev :=
    Ideal.span_le.mpr (by rintro _ rfl; exact het)
  have he : a x * z^D = 0 := by
    have h := hker (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    change Polynomial.eval₂ a z (L x) = 0 at h
    rwa [hx,Polynomial.eval₂_monomial] at h
  have hz : z*a t = 1 := by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf t
  have hax : a x = 0 := by
    have h := congrArg (fun y : S => y*(a t)^D) he
    simpa only [mul_assoc,←mul_pow,hz,one_pow,mul_one,zero_mul] using h
  apply IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors ht0)
  simpa only [map_zero] using hax

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PositiveCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

theorem positiveLaurentMap_injective {n : ℕ} {R : Type*} [CommRing R] :
    Function.Injective (positiveLaurentMap : MvPolynomial (Fin n) R →+* _) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro e f h
  ext i
  have hi : (e i : ℤ) = (f i : ℤ) := congrFun h i
  exact_mod_cast hi

theorem positiveLaurentMap_prod_X {n : ℕ} {R : Type*} [CommRing R] (m : Fin n → ℕ) :
    positiveLaurentMap (∏ i, (X i : MvPolynomial (Fin n) R)^m i) =
      AddMonoidAlgebra.single (fun i => (m i : ℤ)) 1 := by
  classical
  simp only [map_prod,map_pow,positiveLaurentMap_X,AddMonoidAlgebra.single_pow,
    one_pow,AddMonoidAlgebra.prod_single,Finset.prod_const_one]
  congr 1
  ext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem positiveLaurent_fractions {n : ℕ} {R : Type*} [CommRing R]
    (z : AddMonoidAlgebra R (Fin n → ℤ)) :
    ∃ x y : MvPolynomial (Fin n) R, y ∈ Submonoid.closure (Set.range X) ∧
      z * positiveLaurentMap y = positiveLaurentMap x := by
  classical
  induction z using AddMonoidAlgebra.induction_on with
  | of e =>
    refine ⟨∏ i, X i ^ (e i).toNat, ∏ i, X i ^ (-e i).toNat,?_,?_⟩
    · exact Submonoid.prod_mem _ fun i _ => Submonoid.pow_mem _
        (Submonoid.subset_closure (show X i ∈ Set.range (X : Fin n → MvPolynomial (Fin n) R) from ⟨i,rfl⟩)) _
    · change AddMonoidAlgebra.single e 1 * _ = _
      rw [positiveLaurentMap_prod_X,positiveLaurentMap_prod_X,
        AddMonoidAlgebra.single_mul_single,one_mul]
      congr 1
      ext i
      simp only [Pi.add_apply]
      omega
  | add z w hz hw =>
    obtain ⟨x,a,ha,hx⟩ := hz
    obtain ⟨y,b,hb,hy⟩ := hw
    refine ⟨x*b+y*a,a*b,Submonoid.mul_mem _ ha hb,?_⟩
    rw [map_add,map_mul,map_mul,map_mul,←hx,←hy]
    ring
  | smul r z hz =>
    obtain ⟨x,a,ha,hx⟩ := hz
    refine ⟨C r*x,a,ha,?_⟩
    rw [map_mul,positiveLaurentMap_C,←hx,←mul_assoc]
    congr 1
    ext e
    simp

theorem positiveLaurent_isLocalization {n : ℕ} {R : Type*} [CommRing R] :
    let : Algebra (MvPolynomial (Fin n) R) (AddMonoidAlgebra R (Fin n → ℤ)) :=
      positiveLaurentMap.toAlgebra
    IsLocalization (Submonoid.closure (Set.range (X : Fin n → MvPolynomial (Fin n) R)))
      (AddMonoidAlgebra R (Fin n → ℤ)) := by
  let : Algebra (MvPolynomial (Fin n) R) (AddMonoidAlgebra R (Fin n → ℤ)) :=
    positiveLaurentMap.toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro y
    change IsUnit (positiveLaurentMap y.val)
    have hu : ∀ a ∈ Submonoid.closure (Set.range (X : Fin n → MvPolynomial (Fin n) R)),
        IsUnit (positiveLaurentMap a) := by
      intro a ha
      induction ha using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨i,rfl⟩ := ha
        rw [positiveLaurentMap_X]
        exact ⟨⟨AddMonoidAlgebra.single (Pi.single i 1) 1,
          AddMonoidAlgebra.single (-(Pi.single i 1)) 1,
          by simp [AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.one_def],
          by simp [AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.one_def]⟩,rfl⟩
      | one => simp
      | mul a b ha hb iha ihb => simpa only [map_mul] using iha.mul ihb
    exact hu y.val y.property
  · intro z
    obtain ⟨x,y,hy,hxy⟩ := positiveLaurent_fractions z
    exact ⟨(x,⟨y,hy⟩),hxy⟩
  · intro x y he
    exact ⟨1,by simpa only [OneMemClass.coe_one,one_mul] using positiveLaurentMap_injective he⟩

end
open MvPolynomial

theorem positiveToPair_toLaurent {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (p : MvPolynomial (Fin n) R) :
    pairToLaurent k q (positiveToPair k q p) = positiveLaurentMap p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [pairCoeffMap]
  | add p r hp hr => simp only [map_add,hp,hr]
  | mul_X p i hp => simp only [map_mul,hp,positiveToPair_X,pairToLaurent_coordinate,positiveLaurentMap_X]

theorem pair_laurent_evaluation {n : ℕ} {R L : Type*} [CommRing R] [Field L]
    (k : ℕ) (q : Fin n → R) (ψ : PairRing k q →+* L)
    (ℓ : AddMonoidAlgebra R (Fin n → ℤ) →+* L)
    (ha : ∀ i, ψ (pairCoordinate k q i) ≠ 0)
    (hcomp : ∀ p, ℓ (positiveLaurentMap p) = ψ (positiveToPair k q p)) :
    ℓ.comp (pairToLaurent k q) = ψ := by
  have hC (r : R) : ℓ (pairToLaurent k q (pairCoeffMap k q r)) = ψ (pairCoeffMap k q r) := by
    simpa only [←positiveToPair_toLaurent k q,positiveToPair_C] using hcomp (C r)
  have hA (i : Fin n) : ℓ (pairToLaurent k q (pairCoordinate k q i)) = ψ (pairCoordinate k q i) := by
    simpa only [←positiveToPair_toLaurent k q,positiveToPair_X] using hcomp (X i)
  have hB (i : Fin n) : ℓ (pairToLaurent k q (Ideal.Quotient.mk _ (X (Sum.inr i)))) =
      ψ (Ideal.Quotient.mk _ (X (Sum.inr i))) := by
    apply mul_left_cancel₀ (pow_ne_zero k (ha i))
    have he1 := congrArg (fun x => ℓ (pairToLaurent k q x)) (pairCoordinate_equation k q i)
    have he2 := congrArg ψ (pairCoordinate_equation k q i)
    simp only [map_mul,map_pow] at he1 he2
    change ℓ (pairToLaurent k q (pairCoordinate k q i)) ^ k * _ = _ at he1
    rw [hA,hC] at he1
    exact he1.trans he2.symm
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r => exact hC r
  | add p r hp hr => simpa only [map_add] using congrArg₂ (·+·) hp hr
  | mul_X p i hp =>
    simp only [RingHom.comp_apply,map_mul,hp]
    cases i with
    | inl j => rw [show Ideal.Quotient.mk _ (X (Sum.inl j)) = pairCoordinate k q j from rfl,hA]
    | inr j => rw [hB]

theorem positiveLaurent_kernel {n : ℕ} {R L : Type*} [CommRing R] [Field L]
    (φ : MvPolynomial (Fin n) R →+* L) (ha : ∀ i, φ (X i) ≠ 0) :
    ∃ ℓ : AddMonoidAlgebra R (Fin n → ℤ) →+* L,
      (∀ p, ℓ (positiveLaurentMap p) = φ p) ∧
      RingHom.ker ℓ = (RingHom.ker φ).map positiveLaurentMap := by
  let : Algebra (MvPolynomial (Fin n) R) (AddMonoidAlgebra R (Fin n → ℤ)) :=
    positiveLaurentMap.toAlgebra
  let M := Submonoid.closure (Set.range (X : Fin n → MvPolynomial (Fin n) R))
  let : IsLocalization M (AddMonoidAlgebra R (Fin n → ℤ)) := positiveLaurent_isLocalization
  have hu : ∀ y : M, IsUnit (φ y.val) := by
    intro y
    have hh : ∀ a ∈ M, IsUnit (φ a) := by
      intro a ha'
      induction ha' using Submonoid.closure_induction with
      | mem a ha' =>
        obtain ⟨i,rfl⟩ := ha'
        exact isUnit_iff_ne_zero.mpr (ha i)
      | one => simp
      | mul a b ha' hb' iha ihb => simpa only [map_mul] using iha.mul ihb
    exact hh y.val y.property
  let ℓ : AddMonoidAlgebra R (Fin n → ℤ) →+* L := IsLocalization.lift hu
  have hc : ∀ p, ℓ (positiveLaurentMap p) = φ p := IsLocalization.lift_eq hu
  refine ⟨ℓ,hc,?_⟩
  have hk : (RingHom.ker ℓ).under (MvPolynomial (Fin n) R) = RingHom.ker φ := by
    ext p
    change ℓ (positiveLaurentMap p) = 0 ↔ φ p = 0
    rw [hc]
  have hm := IsLocalization.map_under M (AddMonoidAlgebra R (Fin n → ℤ)) (RingHom.ker ℓ)
  rw [hk] at hm
  exact hm.symm

open MvPolynomial
open scoped BigOperators

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section

section
open MvPolynomial

theorem positiveToPairHom_apply {n : ℕ} {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] (k : ℕ) (q : Fin n → R) (p : MvPolynomial (Fin n) R) :
    positiveToPairHom (K := K) k q p = positiveToPair k q p := rfl

theorem positiveToPair_option {n : ℕ} {K : Type*} [Field K]
    (k : ℕ) (θ : Fin n → K) (p : MvPolynomial (Option (Fin n)) K) :
    positiveToPair k (rootPairQ θ) (optionEquivRight K (Fin n) p) =
      MvPolynomial.aeval (fun i => i.elim (pairCoeffMap k (rootPairQ θ) Polynomial.X)
        (pairLeft k (rootPairQ θ))) p := by
  have he : (positiveToPairHom (K := K) k (rootPairQ θ)).comp
      (optionEquivRight K (Fin n)).toAlgHom =
      MvPolynomial.aeval (fun i => i.elim (pairCoeffMap k (rootPairQ θ) Polynomial.X)
        (pairLeft k (rootPairQ θ))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none => simp [positiveToPairHom_apply]
    | some i => simp [positiveToPairHom_apply,pairLeft,pairCoordinate]
  exact AlgHom.congr_fun he p

theorem pairConeToRoot_kernel {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    RingHom.ker (pairConeToRoot k A B θ).toRingHom =
      Ideal.span {pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2)-1} := by
  ext x
  change pairConeToRoot k A B θ x = 0 ↔ _
  rw [←Ideal.Quotient.eq_zero_iff_mem]
  change pairConeToRoot k A B θ x = 0 ↔ pairAffineMk k A B (coneDifference θ) x = 0
  have h := AlgHom.congr_fun (rootPairToAffine_comp_cone k A B θ) x
  rw [←h]
  exact ((rootPairAffineEquiv k A B θ).map_eq_zero_iff).symm

end
open scoped BigOperators

theorem finrank_map_eq_of_kernel_eq {K R S T : Type*} [Field K]
    [AddCommGroup R] [AddCommGroup S] [AddCommGroup T]
    [Module K R] [Module K S] [Module K T]
    (f : R →ₗ[K] S) (g : R →ₗ[K] T) (hker : LinearMap.ker f = LinearMap.ker g)
    (V : Submodule K R) : Module.finrank K (V.map f) = Module.finrank K (V.map g) := by
  have he : LinearMap.ker (f.domRestrict V) = LinearMap.ker (g.domRestrict V) := by
    ext x
    change x.val ∈ LinearMap.ker f ↔ x.val ∈ LinearMap.ker g
    rw [hker]
  rw [←LinearMap.range_domRestrict,←LinearMap.range_domRestrict,
    ←(f.domRestrict V).quotKerEquivRange.finrank_eq,
    ←(g.domRestrict V).quotKerEquivRange.finrank_eq,he]

end

open MvPolynomial
open scoped BigOperators

theorem weightedSpace_mul_mem {σ K : Type*} [Field K]
    (w : σ → ℕ) {p q : MvPolynomial σ K} {A B : ℕ}
    (hp : p ∈ weightedSpace w A) (hq : q ∈ weightedSpace w B) :
    p*q ∈ weightedSpace w (A+B) := by
  rw [mem_weightedSpace] at hp hq ⊢
  by_cases hp0 : p = 0
  · simp [hp0,weightedTotalDegree_zero]
  by_cases hq0 : q = 0
  · simp [hq0,weightedTotalDegree_zero]
  rw [weightedTotalDegree_mul_exact w p q hp0 hq0]
  exact Nat.add_le_add hp hq

theorem weightedSpace_one {σ K : Type*} [Field K] (w : σ → ℕ) :
    (1 : MvPolynomial σ K) ∈ weightedSpace w 0 := by
  intro m hm
  have hm0 : m = 0 := Finset.mem_singleton.mp (support_one.subset hm)
  simp [hm0]

theorem weightedSpace_pow_mem {σ K : Type*} [Field K]
    (w : σ → ℕ) {p : MvPolynomial σ K} {A : ℕ}
    (hp : p ∈ weightedSpace w A) (e : ℕ) : p^e ∈ weightedSpace w (A*e) := by
  induction e with
  | zero => simpa using weightedSpace_one w
  | succ e ih => simpa only [pow_succ,Nat.mul_succ] using weightedSpace_mul_mem w ih hp

theorem weightedSpace_prod_mem {σ ι K : Type*} [Field K]
    (w : σ → ℕ) (s : Finset ι) (p : ι → MvPolynomial σ K) (A : ι → ℕ)
    (hp : ∀ i ∈ s, p i ∈ weightedSpace w (A i)) :
    ∏ i ∈ s, p i ∈ weightedSpace w (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weightedSpace_one w
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    exact weightedSpace_mul_mem w (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem weightedSpace_mono {σ K : Type*} [CommSemiring K]
    (w : σ → ℕ) {A B : ℕ} (h : A ≤ B) :
    weightedSpace (K := K) w A ≤ weightedSpace w B := by
  intro p hp m hm
  exact (hp hm).trans h

theorem weightedSpace_aeval {σ τ K : Type*} [Fintype σ] [Field K]
    (w : σ → ℕ) (v : τ → ℕ) (z : σ → MvPolynomial τ K)
    (hz : ∀ i, z i ∈ weightedSpace v (w i))
    (p : MvPolynomial σ K) (T : ℕ) (hp : p ∈ weightedSpace w T) :
    MvPolynomial.aeval z p ∈ weightedSpace v T := by
  classical
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro m hm
  rw [aeval_monomial,Finsupp.prod_fintype _ _ (by simp)]
  rw [←Algebra.smul_def]
  apply Submodule.smul_mem
  apply weightedSpace_mono v (hp hm)
  have hh := weightedSpace_prod_mem v Finset.univ (fun i => z i ^ m i)
    (fun i => w i * m i) (fun i _ => weightedSpace_pow_mem v (hz i) (m i))
  have he : Finsupp.weight w m = ∑ i, w i * m i := by
    rw [Finsupp.weight_eq_sum]
    simp only [nsmul_eq_mul,Nat.cast_id,mul_comm]
  rwa [he]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ProjectionDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

theorem left_coordinates_transcendence_selection {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (a : Fin d → A) (x : A) (hx : Transcendental K x)
    [Algebra.IsAlgebraic (Algebra.adjoin K (insert x (Set.range a))) A] :
    ∃ m : ℕ, ∃ j : Fin m → Fin d,
      AlgebraicIndependent K (Fin.cases x (a ∘ j)) ∧ Function.Injective j ∧
      Algebra.trdeg K A = (m+1 : ℕ) := by
  classical
  have hx' : AlgebraicIndepOn K id {x} := by
    change AlgebraicIndependent K (fun z : ({x} : Set A) => z.val)
    rw [algebraicIndependent_singleton_iff (⟨x,rfl⟩ : ({x} : Set A))]
    exact hx
  obtain ⟨t,hxt,htt,htb⟩ := exists_isTranscendenceBasis_between
    (R := K) (A := A) {x} (insert x (Set.range a)) (by simp) hx'
  have htfin : t.Finite := ((Set.finite_range a).insert x).subset htt
  let : Fintype t := htfin.fintype
  let xt : t := ⟨x,hxt (Set.mem_singleton x)⟩
  have hcard : 0 < Fintype.card t := Fintype.card_pos_iff.mpr ⟨xt⟩
  let m := Fintype.card t - 1
  have hm : m+1 = Fintype.card t := by omega
  let e₀ : Fin (m+1) ≃ t := (finCongr hm).trans (Fintype.equivFin t).symm
  let e : Fin (m+1) ≃ t := (Equiv.swap 0 (e₀.symm xt)).trans e₀
  have he0 : e 0 = xt := by simp [e]
  have heA (i : Fin m) : (e i.succ).val ∈ Set.range a := by
    have hh := htt (e i.succ).property
    rcases hh with hh | hh
    · have heq : e i.succ = xt := Subtype.ext hh
      have : i.succ = 0 := e.injective (heq.trans he0.symm)
      exact (Fin.succ_ne_zero i this).elim
    · exact hh
  choose j hj using heA
  have heval : (fun i : Fin (m+1) => (e i).val) = Fin.cases x (a ∘ j) := by
    funext i
    refine Fin.cases ?_ (fun l => ?_) i
    · exact congrArg Subtype.val he0
    · exact (hj l).symm
  have hi : AlgebraicIndependent K (Fin.cases x (a ∘ j)) := by
    simpa only [Function.comp_def,heval] using htb.1.comp e e.injective
  refine ⟨m,j,hi,?_,?_⟩
  · intro i l hil
    apply Fin.succ_injective
    apply hi.injective
    simp only [Fin.cases_succ,Function.comp_def,hil]
  · rw [←htb.cardinalMk_eq_trdeg,Cardinal.mk_fintype,←hm]

theorem pair_right_isAlgebraic {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (k : ℕ) (a b : Fin d → A) (x : A) (θ : Fin d → K)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, a i ^ k * b i = x - algebraMap K A (θ i))
    (i : Fin d) : IsAlgebraic (Algebra.adjoin K (insert x (Set.range a))) (b i) := by
  let S := Algebra.adjoin K (insert x (Set.range a))
  let ai : S := ⟨a i,Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i,rfl⟩)⟩
  let xi : S := ⟨x,Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let p : Polynomial S := Polynomial.C (ai^k) * Polynomial.X -
    Polynomial.C (xi - algebraMap K S (θ i))
  refine ⟨p,?_,?_⟩
  · intro hp
    have hh := congrArg (fun q : Polynomial S => q.coeff 1) hp
    have hh' : ai^k = 0 := by
      simpa only [p,Polynomial.coeff_sub,Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C,ite_eq_right (by decide : (1:ℕ) ≠ 0),
        ite_eq_left rfl,ite_true,sub_zero,Polynomial.coeff_zero] using hh
    have hai : ai ≠ 0 := fun h => ha i (congrArg Subtype.val h)
    exact pow_ne_zero k hai hh'
  · change Polynomial.aeval (b i) p = 0
    simp only [p,map_sub,map_mul,Polynomial.aeval_C,Polynomial.aeval_X]
    change a i ^ k * b i - (x - algebraMap K A (θ i)) = 0
    exact sub_eq_zero.mpr (hab i)

theorem pair_projection_isAlgebraic {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (k : ℕ) (a b : Fin d → A) (x : A) (θ : Fin d → K)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, a i ^ k * b i = x - algebraMap K A (θ i))
    (hgen : Algebra.adjoin K (Set.range a ∪ Set.range b) = ⊤) :
    Algebra.IsAlgebraic (Algebra.adjoin K (insert x (Set.range a))) A := by
  constructor
  intro z
  have hz : IsAlgebraic (Algebra.adjoin K (Set.range a ∪ Set.range b)) z := by
    rw [hgen]
    exact isAlgebraic_algebraMap (R := (⊤ : Subalgebra K A)) ⟨z,trivial⟩
  apply hz.adjoin_of_forall_isAlgebraic
  rintro y ⟨hy,hyn⟩
  rcases hy with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact (hyn (Set.mem_insert_of_mem _ ⟨i,rfl⟩)).elim
  · exact pair_right_isAlgebraic k a b x θ ha hab i

open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_RootPairHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial

theorem rootPairEvaluation_projection {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i))
    (p : MvPolynomial (Option (Fin d)) K) :
    rootPairEvaluation k θ a b x hab
      (positiveToPair k (rootPairQ θ) (optionEquivRight K (Fin d) p)) =
      MvPolynomial.aeval (fun o => o.elim x a) p := by
  rw [positiveToPair_option,MvPolynomial.comp_aeval_apply]
  congr 1
  congr 1
  funext o
  cases o with
  | none => exact rootPairEvaluation_number k θ a b x hab
  | some i => exact rootPairEvaluation_left k θ a b x hab i

end
section
open MvPolynomial
open scoped BigOperators

theorem pairCone_homogeneous_image_le {n : ℕ} {σ K S : Type*}
    [Fintype σ] [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S) (g : MvPolynomial σ K →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (X 2)) = 1)
    (a b : Fin (n+1) → MvPolynomial σ K) (w : σ → ℕ)
    (ha : ∀ i, a i ∈ weightedSpace w A) (hb : ∀ i, b i ∈ weightedSpace w B)
    (hφa : ∀ i, φ (pairConeA k A B θ i) = g (a i))
    (hφb : ∀ i, φ (pairConeB k A B θ i) = g (b i)) (T : ℕ) :
    (homogeneousSpace (pairConeScale k A B θ) T).map φ.toLinearMap ≤
      (weightedSpace w T).map g.toLinearMap := by
  classical
  rintro y ⟨c,hc,rfl⟩
  let p := pairConePolynomial k A B hB θ c
  let z := Sum.elim a b
  let v : Fin (n+1) ⊕ Fin (n+1) → ℕ := Sum.elim (fun _ => A) (fun _ => B)
  have hp : p ∈ weightedSpace v T := by
    intro m hm
    have hh := pairConePolynomial_weight k A B hB θ c T
      ((mem_homogeneousSpace _ _ _).mp hc) m hm
    have he : Finsupp.weight v m = A*(∑ i, m (Sum.inl i))+ B*(∑ i, m (Sum.inr i)) := by
      rw [Finsupp.weight_eq_sum,Fintype.sum_sum_type]
      simp only [v,Sum.elim_inl,Sum.elim_inr,nsmul_eq_mul,Nat.cast_id,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    change Finsupp.weight v m ≤ T
    rwa [he]
  have hz : ∀ i, z i ∈ weightedSpace w (v i) := by
    intro i
    cases i with
    | inl i => exact ha i
    | inr i => exact hb i
  refine ⟨MvPolynomial.aeval z p,weightedSpace_aeval v w z hz p T hp,?_⟩
  change g (MvPolynomial.aeval z p) = φ c
  rw [MvPolynomial.comp_aeval_apply]
  have hv : g ∘ z = Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ) := by
    funext i
    cases i with
    | inl i => exact (hφa i).symm
    | inr i => exact (hφb i).symm
  change MvPolynomial.aeval (g ∘ z) p = φ c
  rw [hv]
  exact pairConePolynomial_eval k A B hB θ φ ht c

theorem rootPair_actual_hilbert_le {n N : ℕ} {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial (Fin N) K))
    (e : (MvPolynomial (Fin N) K ⧸ I) →ₐ[K] L) (he : Function.Injective e)
    (k A B : ℕ) (hB : 0 < B) (θ : Fin (n+1) → K)
    (ψ : RootPair k θ →ₐ[K] L)
    (a b : Fin (n+1) → MvPolynomial (Fin N) K) (w : Fin N → ℕ)
    (hw : ∀ i, w i ≠ 0)
    (ha : ∀ i, a i ∈ weightedSpace w A) (hb : ∀ i, b i ∈ weightedSpace w B)
    (hψa : ∀ i, ψ (pairLeft k (rootPairQ θ) i) = e (Ideal.Quotient.mk I (a i)))
    (hψb : ∀ i, ψ (pairRight k (rootPairQ θ) i) = e (Ideal.Quotient.mk I (b i))) (T : ℕ) :
    Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference θ)) T).map
      (ψ.comp (pairConeToRoot k A B θ)).toLinearMap) ≤
    Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  let g := e.comp (Ideal.Quotient.mkₐ K I)
  have := weightedSpace_finite (K := K) w hw T
  have hh := pairCone_homogeneous_image_le k A B hB (coneDifference θ)
    (ψ.comp (pairConeToRoot k A B θ)) g (by simp) a b w ha hb
    (fun i => by simpa only [g,AlgHom.comp_apply,Ideal.Quotient.mkₐ_eq_mk,pairConeToRoot_left] using hψa i)
    (fun i => by simpa only [g,AlgHom.comp_apply,Ideal.Quotient.mkₐ_eq_mk,pairConeToRoot_right] using hψb i) T
  have hr : Module.finrank K ((weightedSpace w T).map g.toLinearMap) =
      Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
    apply finrank_map_eq_of_kernel_eq
    ext p
    change e (Ideal.Quotient.mk I p) = 0 ↔ Ideal.Quotient.mk I p = 0
    exact map_eq_zero_iff e he
  exact (Submodule.finrank_mono hh).trans_eq hr

end
open MvPolynomial

universe u

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_NormHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace QuarticPowerFree

section
open scoped BigOperators Classical

theorem pairSplitFirst_injective {h : ℕ} : Function.Injective (pairSplitFirst (h := h)) := by
  intro p q he
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h0 := congrArg (fun r => (r 0).1) he
    have h1 := congrArg (fun r => (r 1).2) he
    exact Prod.ext h0 h1
  · exact congrFun he j.succ.succ

theorem pairSplitFirst_weight {h : ℕ} (A B : ℕ) (p : Fin (h+1) → ℕ × ℕ) :
    ∑ i, (A*(pairSplitFirst p i).1+B*(pairSplitFirst p i).2) =
      ∑ i, (A*(p i).1+B*(p i).2) := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [pairSplitFirst,Fin.cons_zero,Fin.cons_succ,mul_zero,add_zero,zero_add]
  omega

theorem ambientPairTuples_card_full {h A B k T : ℕ} (hA : 0 < A) (hB : 0 < B) :
    (ambientPairTuples h A B k T).card =
      (normalPairTuples A B (Fin.cons 0 (Fin.cons 1 (fun _ : Fin h => k)))
        (Fin.cons 1 (Fin.cons 0 (fun _ : Fin h => 1))) T).card := by
  classical
  apply Finset.card_bij (fun p _ => pairSplitFirst p)
  · intro p hp
    obtain ⟨hn,hw⟩ := (mem_ambientPairTuples hA hB p).mp hp
    apply (mem_normalPairTuples hA hB _ _ _ _).mpr
    refine ⟨?_,(pairSplitFirst_weight A B p).symm ▸ hw⟩
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
    · simp [pairSplitFirst]
    · simp [pairSplitFirst]
    · simpa only [Fin.cons_succ,pairSplitFirst,Nat.lt_one_iff] using hn l
  · intro p _ q _ he
    exact pairSplitFirst_injective he
  · intro q hq
    obtain ⟨hn,hw⟩ := (mem_normalPairTuples hA hB _ _ _ _).mp hq
    have h0 : (q 0).2 = 0 := by
      have hh := hn 0
      simp only [Fin.cons_zero,Nat.not_lt_zero,false_or] at hh
      omega
    have h1 : (q 1).1 = 0 := by
      have hh := hn 1
      change (q 1).1 < 1 ∨ (q 1).2 < 0 at hh
      omega
    let p : Fin (h+1) → ℕ × ℕ := Fin.cons ((q 0).1,(q 1).2) (fun i => q i.succ.succ)
    have he : pairSplitFirst p = q := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
      · exact Prod.ext rfl h0.symm
      · exact Prod.ext h1.symm rfl
      · rfl
    refine ⟨p,(mem_ambientPairTuples hA hB p).mpr ⟨?_,?_⟩,he⟩
    · intro i
      simpa only [p,Fin.cons_succ,Nat.lt_one_iff] using hn i.succ.succ
    · rw [←pairSplitFirst_weight A B p,he]
      exact hw

theorem ambientPairTuples_hilbert_error {h A B k : ℕ} (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((ambientPairTuples h A B k T).card : ℝ) -
        ((k*A+B : ℕ):ℝ)^h / (((h+2).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*(T:ℝ)^(h+2)| ≤
        C*((T:ℝ)+1)^(h+1) := by
  obtain ⟨C,hC,hh⟩ := normalPairTuples_hilbert_error hA hB
    (Fin.cons 0 (Fin.cons 1 (fun _ : Fin h => k)))
    (Fin.cons 1 (Fin.cons 0 (fun _ : Fin h => 1)))
  refine ⟨C,hC,fun T => ?_⟩
  rw [ambientPairTuples_card_full hA hB]
  have hp : (∏ i : Fin (h+2),
      (((((Fin.cons (α := fun _ => ℕ) 0 (Fin.cons 1 (fun _ : Fin h => k))) i):ℕ):ℝ)*A+
        ((((Fin.cons (α := fun _ => ℕ) 1 (Fin.cons 0 (fun _ : Fin h => 1))) i):ℕ):ℝ)*B)) =
        (A:ℝ)*B*((k*A+B:ℕ):ℝ)^h := by
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,
      zero_add,add_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_mul]
    ring
  have ha : (A:ℝ) ≠ 0 := by positivity
  have hb : (B:ℝ) ≠ 0 := by positivity
  have hc : (A:ℝ)*B*((k*A+B:ℕ):ℝ)^h /
      (((h+2).factorial:ℝ)*(A:ℝ)^(h+2)*(B:ℝ)^(h+2)) =
      ((k*A+B:ℕ):ℝ)^h/(((h+2).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1)) := by
    rw [show h+2 = (h+1)+1 by omega,pow_succ,pow_succ]
    field_simp
    ring
  simpa only [hp,hc,show h+2-1 = h+1 by omega] using hh T

end
section
open MvPolynomial

theorem norm_full_projection_independent {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (k : ℕ) (a b : Fin d → A) (x : A) (θ : Fin d → K)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, a i^k*b i = x-algebraMap K A (θ i))
    (hgen : Algebra.adjoin K (Set.range a ∪ Set.range b) = ⊤)
    (hx : Transcendental K x) (htr : Algebra.trdeg K A = (d+1:ℕ)) :
    AlgebraicIndependent K (fun o : Option (Fin d) => o.elim x a) := by
  let := pair_projection_isAlgebraic k a b x θ ha hab hgen
  obtain ⟨m,j,hj,hji,hm⟩ := left_coordinates_transcendence_selection a x hx
  have hmd : m = d := by rw [htr] at hm; exact_mod_cast (Nat.add_right_cancel (by exact_mod_cast hm.symm))
  subst m
  let e : Fin d ≃ Fin d := Equiv.ofBijective j ⟨hji,Finite.surjective_of_injective hji⟩
  let g : Option (Fin d) → Fin (d+1) := fun o => o.elim 0 (fun i => (e.symm i).succ)
  have hg : Function.Injective g := by
    intro o p he
    cases o <;> cases p
    · rfl
    · exact (Fin.succ_ne_zero _ he.symm).elim
    · exact (Fin.succ_ne_zero _ he).elim
    · exact congrArg some (e.symm.injective (Fin.succ_injective _ he))
  have heq : Fin.cases x (a ∘ j) ∘ g = fun o : Option (Fin d) => o.elim x a := by
    funext o
    cases o with
    | none => rfl
    | some i =>
      change a (e (e.symm i)) = a i
      rw [e.apply_symm_apply]
  exact heq ▸ hj.comp g hg

theorem rootPair_evaluation_injective {d : ℕ} {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → L) (x : L)
    (hab : ∀ i, a i^k*b i = x-algebraMap K L (θ i))
    (hi : AlgebraicIndependent K (fun o : Option (Fin d) => o.elim x a)) :
    Function.Injective (rootPairEvaluation k θ a b x hab) := by
  let q := rootPairQ θ
  let ψ := rootPairEvaluation k θ a b x hab
  let φ := ψ.toRingHom.comp (positiveToPair k q)
  have hφ : Function.Injective φ := by
    have he (p) : φ ((optionEquivRight K (Fin d)) p) = aeval (fun o => o.elim x a) p :=
      rootPairEvaluation_projection k θ a b x hab p
    intro p r hpr
    let E := optionEquivRight K (Fin d)
    have hp := he (E.symm p)
    have hr := he (E.symm r)
    rw [E.apply_symm_apply] at hp hr
    have hinj := hi
    exact E.symm.injective (hinj (hp.symm.trans (hpr.trans hr)))
  have ha (i) : ψ.toRingHom (pairCoordinate k q i) ≠ 0 := by
    have hn : (X i : MvPolynomial (Fin d) (Polynomial K)) ≠ 0 := X_ne_zero i
    have hh : φ (X i) ≠ 0 := (map_ne_zero_iff φ hφ).mpr hn
    simpa only [φ,RingHom.comp_apply,positiveToPair_X] using hh
  have haφ (i) : φ (X i) ≠ 0 := by simpa only [φ,RingHom.comp_apply,positiveToPair_X] using ha i
  obtain ⟨ℓ,hℓ,hker⟩ := positiveLaurent_kernel φ haφ
  rw [(RingHom.ker_eq_bot_iff_eq_zero φ).mpr (fun p hp => hφ (hp.trans (map_zero φ).symm)),Ideal.map_bot] at hker
  have hℓinj : Function.Injective ℓ := (RingHom.injective_iff_ker_eq_bot ℓ).mpr hker
  have he := pair_laurent_evaluation k q ψ.toRingHom ℓ ha hℓ
  change Function.Injective ψ.toRingHom
  rw [←he]
  exact hℓinj.comp (pairToLaurent_injective k q (fun i => Polynomial.X_sub_C_ne_zero (θ i)))

theorem pairCone_full_finrank {n : ℕ} {K L : Type*} [Field K] [Field L] [Algebra K L]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin (n+1) → K)
    (ψ : RootPair k θ →ₐ[K] L) (hψ : Function.Injective ψ) (T : ℕ) :
    Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference θ)) T).map
      (ψ.comp (pairConeToRoot k A B θ)).toLinearMap) =
      (ambientPairTuples n A B k T).card := by
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B (coneDifference θ))))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB (coneDifference θ))
  let f := (ψ.comp (pairConeToRoot k A B θ)).toLinearMap.domRestrict
    (homogeneousSpace (pairConeScale k A B (coneDifference θ)) T)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    apply Subtype.ext
    have hz : pairConeToRoot k A B θ c.val = 0 := hψ (hc.trans (map_zero ψ).symm)
    have hmem : c.val ∈ Ideal.span {pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2)-1} := by
      rw [←pairConeToRoot_kernel k A B θ]
      exact hz
    exact homogeneous_dehomogenization_zero (pairConeScale k A B (coneDifference θ))
      (pairCone_t_prime k A B hB (coneDifference θ)).ne_zero
      (pairCone_t_homogeneous k A B (coneDifference θ)) c.property
      (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have he := LinearMap.finrank_range_of_inj hf
  rw [LinearMap.range_domRestrict] at he
  exact he.trans (pairCone_finrank k A B hA hB (coneDifference θ) T)

theorem norm_full_hilbert_uniform {N n : ℕ} {K : Type u} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) K)) [I.IsPrime]
        (a b : Fin (n+1) → MvPolynomial (Fin N) K) (x : MvPolynomial (Fin N) K)
        (θ : Fin (n+1) → K),
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin N) K ⧸ I) (θ i)) →
      Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
        Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ →
      Transcendental K (Ideal.Quotient.mk I x) → affineDimension I = n+2 →
      ∀ (w : Fin N → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w A) → (∀ i, b i ∈ weightedSpace w B) →
      ∀ T : ℕ,
        ((k*A+B : ℕ):ℝ)^n / (((n+2).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+2) -
          C*((T:ℝ)+1)^(n+1) ≤
          (Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℝ) := by
  obtain ⟨C,hC,hH⟩ := ambientPairTuples_hilbert_error (h := n) (k := k) hA hB
  refine ⟨C,hC,fun I _ a b x θ ha hab hgen hx hdim w hw haw hbw T => ?_⟩
  let S := MvPolynomial (Fin N) K ⧸ I
  let L := FractionRing S
  let e : S →ₐ[K] L := IsScalarTower.toAlgHom K S L
  have he : Function.Injective e := IsFractionRing.injective S L
  let aj : Fin (n+1) → S := fun i => Ideal.Quotient.mk I (a i)
  let bj : Fin (n+1) → S := fun i => Ideal.Quotient.mk I (b i)
  let xj : S := Ideal.Quotient.mk I x
  have htr : Algebra.trdeg K S = (n+2:ℕ) := by
    rw [←hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)]
    change (affineDimension I : Cardinal) = _
    rw [hdim]
  have hi := norm_full_projection_independent k aj bj xj θ ha hab hgen hx htr
  have hil : AlgebraicIndependent K (fun o : Option (Fin (n+1)) => o.elim (e xj) (e ∘ aj)) := by
    have hh := hi.map' he
    convert hh using 1
    funext o
    cases o <;> rfl
  have habL (i) : (e (aj i))^k*e (bj i) = e xj-algebraMap K L (θ i) := by
    have hh : aj i^k*bj i = xj-algebraMap K S (θ i) := hab i
    simpa only [map_mul,map_pow,map_sub,AlgHom.commutes] using congrArg e hh
  let ψ : RootPair k θ →ₐ[K] L := rootPairEvaluation k θ (e ∘ aj) (e ∘ bj) (e xj) habL
  have hinj : Function.Injective ψ := rootPair_evaluation_injective k θ (e ∘ aj) (e ∘ bj) (e xj) habL hil
  have hR := rootPair_actual_hilbert_le I e he k A B hB θ ψ a b w hw haw hbw
    (fun i => rootPairEvaluation_left k θ (e ∘ aj) (e ∘ bj) (e xj) habL i)
    (fun i => rootPairEvaluation_right k θ (e ∘ aj) (e ∘ bj) (e xj) habL i) T
  rw [pairCone_full_finrank k A B hA hB θ ψ hinj T] at hR
  have hR' : ((ambientPairTuples n A B k T).card:ℝ) ≤
      (Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap):ℝ) := by exact_mod_cast hR
  have hh := (abs_le.mp (hH T)).1
  linarith

end

theorem uniform_real_hilbert_floor (h M : ℕ) (L α C : ℝ)
    (hL : 0 < L) (hα : 0 ≤ α) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (H : ℕ → ℝ) (G : ℝ → ℝ),
      (∀ T, 0 ≤ G T) →
      (∀ T, 1 ≤ T → H ⌊L*T⌋₊ ≤ G T) →
      (∀ N, M ≤ N → α*(N:ℝ)^(h+1)-C*((N:ℝ)+1)^h ≤ H N) →
      ∀ T, 1 ≤ T → α*L^(h+1)*T^(h+1)-c*T^h ≤ G T := by
  let c := α*(h+1)*L^h + C*(L+1)^h + α*(M:ℝ)^(h+1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c,hc,fun H G hG hi hl T hT => ?_⟩
  let N := ⌊L*T⌋₊
  have hT0 : 0 ≤ T := by linarith
  have hLT : 0 ≤ L*T := mul_nonneg hL.le hT0
  have hN : (N:ℝ) ≤ L*T := Nat.floor_le hLT
  have hN1 : L*T < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hTh : 1 ≤ T^h := one_le_pow₀ hT
  have hpowtarget : α*L^(h+1)*T^(h+1) = α*(L*T)^(h+1) := by rw [mul_pow]; ring
  rw [hpowtarget]
  by_cases hMN : M ≤ N
  · have hh := (hl N hMN).trans (hi T hT)
    have hab : |L*T-(N:ℝ)| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hN)]; linarith
    have hdiff := abs_pow_sub_pow_le (a := L*T) (b := (N:ℝ)) (n := h+1)
    rw [abs_of_nonneg hLT,abs_of_nonneg hN0,max_eq_left hN,Nat.add_sub_cancel] at hdiff
    have hdiff' : (L*T)^(h+1)-(N:ℝ)^(h+1) ≤ (h+1:ℕ)*(L*T)^h := by
      refine (le_abs_self _).trans (hdiff.trans ?_)
      calc |L*T-(N:ℝ)| * (h+1:ℕ)*(L*T)^h ≤ 1*(h+1:ℕ)*(L*T)^h := by gcongr
           _ = (h+1:ℕ)*(L*T)^h := by ring
    have hd := mul_le_mul_of_nonneg_left hdiff' hα
    have hNp : (N:ℝ)+1 ≤ (L+1)*T := by nlinarith
    have he : C*((N:ℝ)+1)^h ≤ C*(L+1)^h*T^h := by
      rw [mul_assoc,←mul_pow]
      gcongr
    have hsmall : 0 ≤ α*(M:ℝ)^(h+1)*T^h := by positivity
    simp only [mul_pow] at hd ⊢
    push_cast at hd
    dsimp only [c]
    nlinarith only [hh,hd,he,hsmall]
  · have hNM : N+1 ≤ M := by omega
    have hNM' : (N:ℝ)+1 ≤ M := by exact_mod_cast hNM
    have hM : L*T ≤ M := by linarith
    have hp : (L*T)^(h+1) ≤ (M:ℝ)^(h+1) := pow_le_pow_left₀ hLT hM _
    have hpα := mul_le_mul_of_nonneg_left hp hα
    have hscale : α*(M:ℝ)^(h+1) ≤ α*(M:ℝ)^(h+1)*T^h :=
      le_mul_of_one_le_right (by positivity) hTh
    have hother : 0 ≤ (α*(h+1)*L^h+C*(L+1)^h)*T^h := by positivity
    dsimp only [c]
    linarith [hG T]

open MvPolynomial

theorem norm_full_real_hilbert_uniform {N n : ℕ} {K : Type u} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) K)) [I.IsPrime]
        (a b : Fin (n+1) → MvPolynomial (Fin N) K) (x : MvPolynomial (Fin N) K)
        (θ : Fin (n+1) → K),
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin N) K ⧸ I) (θ i)) →
      Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
        Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ →
      Transcendental K (Ideal.Quotient.mk I x) → affineDimension I = n+2 →
      ∀ (w : Fin N → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w A) → (∀ i, b i ∈ weightedSpace w B) →
      ∀ (ω : Fin N → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = L*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        ((k*A+B : ℕ):ℝ)^n*L^(n+2) / (((n+2).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*T^(n+2) -
          C*T^(n+1) ≤ weightedHilbert I ω T := by
  let α : ℝ := ((k*A+B : ℕ):ℝ)^n /
    (((n+2).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))
  have hα : 0 ≤ α := by dsimp [α]; positivity
  obtain ⟨C,hC,hh⟩ := norm_full_hilbert_uniform (N := N) (n := n) (K := K) k A B hA hB
  obtain ⟨c,hc,hr⟩ := uniform_real_hilbert_floor (n+1) 0 L α C hL hα hC
  refine ⟨c,hc,fun I _ a b x θ ha hab hgen hx hdim w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hr (fun N => (Module.finrank K ((weightedSpace w N).map
        (Ideal.Quotient.mkₐ K I).toLinearMap):ℝ))
    (fun t => (weightedHilbert I ω t:ℝ))
    (fun t => Nat.cast_nonneg _)
    (fun t ht => by
      exact_mod_cast Submodule.finrank_mono
        (weightedSpace_map_le_weightedFunctions I w ω hω L hL hscale t (by linarith)))
    (fun t _ => hh I a b x θ ha hab hgen hx hdim w hw haw hbw t) T hT
  dsimp only [α] at hb
  convert hb using 1
  ring

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_RationalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace QuarticPowerFree

section

open Polynomial

theorem curve_parameter_injective {F ι : Type*} [Field F]
    (N : F[X]) (θ τ : ι → F) (hθ : Function.Injective θ)
    {k : ℕ} (hk : 0 < k)
    (hdiv : ∀ i, (X - C (τ i)) ^ k ∣ N - C (θ i)) : Function.Injective τ := by
  have heval (i : ι) : N.eval (τ i) = θ i := by
    obtain ⟨q, hq⟩ := hdiv i
    have he := congrArg (Polynomial.eval (τ i)) hq
    have hz : N.eval (τ i) - θ i = 0 := by
      simpa [zero_pow (Nat.ne_zero_of_lt hk)] using he
    exact sub_eq_zero.mp hz
  intro i j hij
  apply hθ
  rw [← heval i, ← heval j, hij]

theorem curve_input_degree_lower_bound {F ι : Type*} [Field F] [CharZero F]
    [Fintype ι] (N : F[X]) (hN : 0 < N.natDegree)
    (θ τ : ι → F) (hθ : Function.Injective θ) {k : ℕ} (hk : 0 < k)
    (hdiv : ∀ i, (X - C (τ i)) ^ k ∣ N - C (θ i)) :
    1 + Fintype.card ι * (k - 1) ≤ N.natDegree := by
  classical
  have hτ := curve_parameter_injective N θ τ hθ hk hdiv
  have hder (i : ι) : (X - C (τ i)) ^ (k - 1) ∣ N.derivative := by
    have hh := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd (hdiv i)
    simpa only [derivative_sub, derivative_C, sub_zero] using hh
  have hprod : ∏ i, (X - C (τ i)) ^ (k - 1) ∣ N.derivative := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (Polynomial.pairwise_coprime_X_sub_C hτ hij).pow
    · intro i _
      exact hder i
  have hdeg := Polynomial.natDegree_le_of_dvd hprod
    (Polynomial.derivative_ne_zero.mpr (Nat.ne_zero_of_lt hN))
  rw [Polynomial.natDegree_prod] at hdeg
  · simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one,
      Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Polynomial.natDegree_derivative] at hdeg
    omega
  · intro i _
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)

theorem affine_factor_eq {F : Type*} [Field F] (r q : F) (hr : r ≠ 0) :
    C r * X + C q = C r * (X - C (-q / r)) := by
  rw [mul_sub, ← C_mul]
  congr 1
  rw [mul_div_cancel₀ _ hr, C_neg, neg_neg]

theorem curve_polynomial_degrees {F ι : Type*} [Field F] [CharZero F]
    [Fintype ι] [Nonempty ι] (N : F[X]) (hN : 0 < N.natDegree)
    (θ r q : ι → F) (b : ι → F[X]) (hθ : Function.Injective θ)
    (hr : ∀ i, r i ≠ 0) {k : ℕ} (hk : 0 < k)
    (hidentity : ∀ i, (C (r i) * X + C (q i)) ^ k * b i = N - C (θ i)) :
    1 + Fintype.card ι * (k - 1) ≤ N.natDegree ∧
      ∀ i, (b i).natDegree = N.natDegree - k ∧
        (Fintype.card ι - 1) * (k - 1) ≤ (b i).natDegree := by
  classical
  let τ : ι → F := fun i => -q i / r i
  have hdiv (i : ι) : (X - C (τ i)) ^ k ∣ N - C (θ i) := by
    rw [← hidentity i, affine_factor_eq _ _ (hr i), mul_pow]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hdeg := curve_input_degree_lower_bound N hN θ τ hθ hk hdiv
  refine ⟨hdeg, fun i => ?_⟩
  have hnz : N - C (θ i) ≠ 0 := by
    intro hh
    have hz := congrArg Polynomial.natDegree hh
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_zero] at hz
    omega
  have hab : (C (r i) * X + C (q i)) ^ k * b i ≠ 0 := by
    rw [hidentity i]
    exact hnz
  have heq := congrArg Polynomial.natDegree (hidentity i)
  rw [Polynomial.natDegree_mul (left_ne_zero_of_mul hab) (right_ne_zero_of_mul hab),
    Polynomial.natDegree_pow, Polynomial.natDegree_sub_C,
    affine_factor_eq _ _ (hr i), Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr (hr i)) (Polynomial.X_sub_C_ne_zero _),
    Polynomial.natDegree_C, Polynomial.natDegree_X_sub_C, zero_add, mul_one] at heq
  constructor
  · omega
  · have hcard : 0 < Fintype.card ι := Fintype.card_pos
    have hkm : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hcount : Fintype.card ι - 1 + 1 = Fintype.card ι := Nat.sub_add_cancel hcard
    nlinarith

theorem polynomial_linearIndependent_of_degrees {F ι : Type*} [Field F]
    (p : ι → F[X]) (hp : ∀ i, p i ≠ 0)
    (hdeg : Function.Injective (fun i => (p i).natDegree)) : LinearIndependent F p := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci
  let t := s.filter (fun j => c j ≠ 0)
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨j, hjt, hjmax⟩ := Finset.exists_max_image t (fun j => (p j).natDegree) ht
  have hj : j ∈ s := (Finset.mem_filter.mp hjt).1
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hjt).2
  have he := congrArg (fun f : F[X] => f.coeff (p j).natDegree) hsum
  simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_zero] at he
  rw [Finset.sum_eq_single j] at he
  · exact (mul_ne_zero hcj (Polynomial.leadingCoeff_ne_zero.mpr (hp j))) he
  · intro l hls hlj
    by_cases hcl : c l = 0
    · simp [hcl]
    · have hlt : l ∈ t := Finset.mem_filter.mpr ⟨hls, hcl⟩
      have hle := hjmax l hlt
      have hne : (p l).natDegree ≠ (p j).natDegree := fun hh => hlj (hdeg hh)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne hle hne)]
      exact mul_zero _
  · exact fun hnot => False.elim (hnot hj)

theorem curve_polynomial_families_independent {F : Type*} [Field F]
    (b : F[X]) {g : ℕ} (hg : 0 < g) (hbdeg : g ≤ b.natDegree) :
    LinearIndependent F (fun v : Fin g × ℕ => X ^ v.1.val * b ^ v.2) := by
  have hb : b ≠ 0 := by
    intro hh
    simp only [hh, Polynomial.natDegree_zero] at hbdeg
    omega
  have hp (v : Fin g × ℕ) : (X : F[X]) ^ v.1.val * b ^ v.2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hb)
  apply polynomial_linearIndependent_of_degrees _ hp
  intro v w h
  have hdegree (v : Fin g × ℕ) :
      ((X : F[X]) ^ v.1.val * b ^ v.2).natDegree = v.1.val + v.2 * b.natDegree := by
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hb),
      Polynomial.natDegree_X_pow, Polynomial.natDegree_pow]
  change (X ^ v.1.val * b ^ v.2).natDegree = (X ^ w.1.val * b ^ w.2).natDegree at h
  rw [hdegree, hdegree] at h
  have hv : v.1.val < b.natDegree := lt_of_lt_of_le v.1.isLt hbdeg
  have hw : w.1.val < b.natDegree := lt_of_lt_of_le w.1.isLt hbdeg
  have hm := congrArg (fun n => n % b.natDegree) h
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hw] at hm
  have hfst : v.1 = w.1 := Fin.ext hm
  have hmul : v.2 * b.natDegree = w.2 * b.natDegree := by omega
  have hpos : 0 < b.natDegree := lt_of_lt_of_le hg hbdeg
  exact Prod.ext hfst (Nat.eq_of_mul_eq_mul_right hpos hmul)

end
open MvPolynomial
open scoped Classical BigOperators

theorem projection_strip_hilbert_weighted {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p)
    (M : ℕ) (T : ℝ) (hT : ω x * M + ω y ≤ T) :
    2*(M+1) ≤ weightedHilbert I ω T := by
  classical
  let v := fun i : Fin 2 × Fin (M+1) =>
    Ideal.Quotient.mk I (rename ![y,x] (monomial (binaryStripExponent i) (1:K)))
  have hv (i : Fin 2 × Fin (M+1)) : v i ∈ weightedFunctions I ω T := by
    have he : rename ![y,x] (monomial (binaryStripExponent i) (1:K)) = (X y)^i.1.val*(X x)^i.2.val := by
      rw [binaryStripExponent,← one_mul (1:K),← monomial_mul_monomial,← X_pow_eq_monomial,← X_pow_eq_monomial]
      simp
    dsimp only [v]
    rw [he]
    apply coordinate_power_mem_weighted I ω hω x y _ _ T
    have h1 : (i.1.val:ℝ) ≤ 1 := by exact_mod_cast (show i.1.val ≤ 1 by omega)
    have h2 : (i.2.val:ℝ) ≤ M := by exact_mod_cast (show i.2.val ≤ M by omega)
    nlinarith [mul_le_mul_of_nonneg_left h1 (hω y).le,
      mul_le_mul_of_nonneg_left h2 (hω x).le]
  let u : (Fin 2 × Fin (M+1)) → weightedFunctions I ω T := fun i => ⟨v i,hv i⟩
  have hu : LinearIndependent K u := LinearIndependent.of_comp (weightedFunctions I ω T).subtype
    (projection_strip_independent I x y q hq hker M)
  simpa only [Fintype.card_prod,Fintype.card_fin,weightedHilbert] using hu.fintype_card_le_finrank

theorem projection_curve_hilbert_weighted {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) :
    ∀ T : ℝ, 0 ≤ T → 2*T/(ω x)-2*(ω y/(ω x)+1) ≤ weightedHilbert I ω T := by
  intro T _
  by_cases hT : ω y ≤ T
  · let M := ⌊(T-ω y)/(ω x)⌋₊
    have hf : (M:ℝ) ≤ (T-ω y)/(ω x) := Nat.floor_le (div_nonneg (sub_nonneg.mpr hT) (hω x).le)
    have hb := projection_strip_hilbert_weighted I ω hω x y q hq hker M T (by
      have := (le_div_iff₀ (hω x)).mp hf
      nlinarith)
    have hbr : 2*((M:ℝ)+1) ≤ weightedHilbert I ω T := by exact_mod_cast hb
    have hl : (T-ω y)/(ω x) < (M:ℝ)+1 := Nat.lt_floor_add_one _
    rw [sub_div] at hl
    rw [mul_div_assoc]
    linarith
  · have hh : (0:ℝ) ≤ weightedHilbert I ω T := Nat.cast_nonneg _
    have ht : T/(ω x) < (ω y)/(ω x) := (div_lt_div_iff_of_pos_right (hω x)).mpr (lt_of_not_ge hT)
    rw [mul_div_assoc]
    linarith

theorem curve_coordinate_rationalization {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hI : affineDimension I ≤ 1) (e : ℕ) (hdeg : affineDegree I ≤ e)
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (s : Fin n)
    (hs : Transcendental K (Ideal.Quotient.mk I (X s))) :
    (∃ j, ∀ T : ℝ, 0 ≤ T →
      2*T/(ω s)-2*(ω j/(ω s)+1) ≤ weightedHilbert I ω T) ∨
    (∃ A B : Fin n → Polynomial K, ∀ j, IsCoprime (A j) (B j) ∧ B j ≠ 0 ∧
      (A j).natDegree ≤ e ∧ (B j).natDegree ≤ e ∧
      Polynomial.aeval (Ideal.Quotient.mk I (X s)) (A j) =
        Ideal.Quotient.mk I (X j)*Polynomial.aeval (Ideal.Quotient.mk I (X s)) (B j)) := by
  classical
  choose q hq hd hb hker using fun j => curve_coordinate_relation I hI s j hs
  by_cases h2 : ∃ j, 2 ≤ (q j).degreeOf 0
  · obtain ⟨j,hj⟩ := h2
    exact Or.inl ⟨j,projection_curve_hilbert_weighted I ω hω s j (q j) hj (hker j)⟩
  push Not at h2
  have hone (j) : (q j).degreeOf 0 = 1 := by have := hd j; have := h2 j; omega
  choose A B hcop hB hAdeg hBdeg hrel using fun j => linear_projection_rational (q j) (hq j) (hone j)
  refine Or.inr ⟨A,B,fun j => ⟨hcop j,hB j,?_,?_,?_⟩⟩
  · exact (hAdeg j).trans (by exact_mod_cast (hb j).trans hdeg)
  · exact (hBdeg j).trans (by exact_mod_cast (hb j).trans hdeg)
  · exact (hrel j (algebraMap K _) (Ideal.Quotient.mk I (X s)) (Ideal.Quotient.mk I (X j))).mp
      (projection_equation_quotient I s j (q j) ((hker j (q j)).mpr (dvd_refl _)))

theorem rational_graph_denominator_ne_zero {K : Type*} [Field K]
    (A B : Polynomial K) (hcop : IsCoprime A B) (x y : K)
    (he : A.eval x = y*B.eval x) : B.eval x ≠ 0 := by
  intro hz
  obtain ⟨u,v,huv⟩ := hcop
  have hh := congrArg (Polynomial.eval x) huv
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,he,hz,mul_zero,
    add_zero] at hh
  exact zero_ne_one hh

theorem rational_coordinates_injOn {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (s : Fin n) (A B : Fin n → Polynomial ℂ)
    (hcop : ∀ j, IsCoprime (A j) (B j))
    (hrel : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (X s)) (A j) =
      Ideal.Quotient.mk I (X j)*Polynomial.aeval (Ideal.Quotient.mk I (X s)) (B j)) :
    Set.InjOn (fun z : Fin n → ℤ => z s) {z | PointOn I z} := by
  intro z hz v hv h
  funext j
  have hez := rational_coordinate_at_point I z hz s j (A j) (B j) (hrel j)
  have hev := rational_coordinate_at_point I v hv s j (A j) (B j) (hrel j)
  have hn := rational_graph_denominator_ne_zero (A j) (B j) (hcop j) (z s) (z j) hez
  change z s = v s at h
  rw [←h] at hev
  apply Int.cast_injective (α := ℂ)
  exact mul_right_cancel₀ hn (hez.symm.trans hev)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_WeightedFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped Classical BigOperators

theorem weightedFunctions_mono {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    {A B : ℝ} (h : A ≤ B) : weightedFunctions I ω A ≤ weightedFunctions I ω B :=
  Submodule.span_mono (Set.image_mono (weightedMonomials_mono ω hω h))

theorem weightedFunctions_one {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j) :
    (1 : MvPolynomial σ K ⧸ I) ∈ weightedFunctions I ω 0 := by
  apply Submodule.subset_span
  refine ⟨0,(mem_weightedMonomials ω hω 0 0).mpr (by simp [monomialWeight]),?_⟩
  simp

theorem weightedFunctions_mul {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    {A B : ℝ} {x y : MvPolynomial σ K ⧸ I}
    (hx : x ∈ weightedFunctions I ω A) (hy : y ∈ weightedFunctions I ω B) :
    x*y ∈ weightedFunctions I ω (A+B) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,ha,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b,hb,rfl⟩ := hy
      rw [←map_mul,monomial_mul_monomial,one_mul]
      apply Submodule.subset_span
      refine ⟨a+b,(mem_weightedMonomials ω hω (A+B) (a+b)).mpr ?_,rfl⟩
      have he : monomialWeight ω (a+b) = monomialWeight ω a+monomialWeight ω b := by
        simp only [monomialWeight,Finsupp.coe_add,Pi.add_apply,Nat.cast_add,mul_add,Finset.sum_add_distrib]
      rw [he]
      exact add_le_add ((mem_weightedMonomials ω hω A a).mp ha) ((mem_weightedMonomials ω hω B b).mp hb)
    | zero => simp
    | add y z _ _ hy hz => simpa only [mul_add] using (weightedFunctions I ω (A+B)).add_mem hy hz
    | smul c y _ hy => simpa only [mul_smul_comm] using (weightedFunctions I ω (A+B)).smul_mem c hy
  | zero => simp
  | add x z _ _ hx hz => simpa only [add_mul] using (weightedFunctions I ω (A+B)).add_mem hx hz
  | smul c x _ hx => simpa only [smul_mul_assoc] using (weightedFunctions I ω (A+B)).smul_mem c hx

theorem weightedFunctions_pow {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    {A : ℝ} {x : MvPolynomial σ K ⧸ I} (hx : x ∈ weightedFunctions I ω A) (e : ℕ) :
    x^e ∈ weightedFunctions I ω (A*e) := by
  induction e with
  | zero => simpa using weightedFunctions_one I ω hω
  | succ e ih =>
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,mul_add,mul_one] using weightedFunctions_mul I ω hω ih hx

theorem weightedFunctions_coordinate {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j) (j : σ) :
    Ideal.Quotient.mk I (X j) ∈ weightedFunctions I ω (ω j) := by
  classical
  apply Submodule.subset_span
  refine ⟨Finsupp.single j 1,(mem_weightedMonomials ω hω _ _).mpr ?_,rfl⟩
  simp [monomialWeight,Finsupp.single_apply]

theorem polynomial_curve_strip {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    (s b : MvPolynomial σ K ⧸ I) (hs : Transcendental K s)
    (P : Polynomial K) (hP : Polynomial.aeval s P = b) (g : ℕ) (hg : 0 < g)
    (hdeg : g ≤ P.natDegree) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hsw : s ∈ weightedFunctions I ω U) (hbw : b ∈ weightedFunctions I ω V)
    (M : ℕ) (T : ℝ) (hT : U*(g-1:ℕ)+V*M ≤ T) :
    g*(M+1) ≤ weightedHilbert I ω T := by
  classical
  let v : Fin g × Fin (M+1) → MvPolynomial σ K ⧸ I := fun i => s^i.1.val*b^i.2.val
  have hl := (curve_polynomial_families_independent P hg hdeg).comp
    (fun i : Fin g × Fin (M+1) => (i.1,(i.2.val:ℕ))) (by
      intro i j h
      change (i.1,i.2.val) = (j.1,j.2.val) at h
      exact Prod.ext (congrArg (fun z : Fin g × ℕ => z.1) h) (Fin.ext (congrArg (fun z : Fin g × ℕ => z.2) h)))
  have hi : LinearIndependent K v := by
    have hh := hl.map' (Polynomial.aeval s).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hs))
    simpa only [v,Function.comp_def,AlgHom.toLinearMap_apply,map_mul,map_pow,Polynomial.aeval_X,hP] using hh
  have hv (i : Fin g × Fin (M+1)) : v i ∈ weightedFunctions I ω T := by
    apply weightedFunctions_mono I ω hω _ (weightedFunctions_mul I ω hω
      (weightedFunctions_pow I ω hω hsw i.1.val) (weightedFunctions_pow I ω hω hbw i.2.val))
    have h1 : (i.1.val:ℝ) ≤ (g-1:ℕ) := by exact_mod_cast (show i.1.val ≤ g-1 by omega)
    have h2 : (i.2.val:ℝ) ≤ M := by exact_mod_cast (show i.2.val ≤ M by omega)
    nlinarith [mul_le_mul_of_nonneg_left h1 hU,mul_le_mul_of_nonneg_left h2 hV]
  let u : Fin g × Fin (M+1) → weightedFunctions I ω T := fun i => ⟨v i,hv i⟩
  have hu : LinearIndependent K u := LinearIndependent.of_comp (weightedFunctions I ω T).subtype hi
  simpa only [Fintype.card_prod,Fintype.card_fin,weightedHilbert] using hu.fintype_card_le_finrank

theorem polynomial_curve_hilbert_gain {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    (s b : MvPolynomial σ K ⧸ I) (hs : Transcendental K s)
    (P : Polynomial K) (hP : Polynomial.aeval s P = b) (g : ℕ) (hg : 0 < g)
    (hdeg : g ≤ P.natDegree) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 < V)
    (hsw : s ∈ weightedFunctions I ω U) (hbw : b ∈ weightedFunctions I ω V) :
    ∀ T : ℝ, 0 ≤ T → (g:ℝ)*T/V-(g:ℝ)*U*(g-1:ℕ)/V ≤ weightedHilbert I ω T := by
  intro T _
  let W : ℝ := U*(g-1:ℕ)
  by_cases hT : W ≤ T
  · let M := ⌊(T-W)/V⌋₊
    have hf : (M:ℝ) ≤ (T-W)/V := Nat.floor_le (div_nonneg (sub_nonneg.mpr hT) hV.le)
    have ht : U*(g-1:ℕ)+V*M ≤ T := by
      have := (le_div_iff₀ hV).mp hf
      dsimp [W] at this
      nlinarith
    have hb := polynomial_curve_strip I ω hω s b hs P hP g hg hdeg U V hU hV.le hsw hbw M T ht
    have hbr : (g:ℝ)*((M:ℝ)+1) ≤ weightedHilbert I ω T := by exact_mod_cast hb
    have hl : (T-W)/V < (M:ℝ)+1 := Nat.lt_floor_add_one _
    have hg0 : (0:ℝ) < g := by exact_mod_cast hg
    have hm := mul_lt_mul_of_pos_left hl hg0
    dsimp [W] at hm
    have he : (g:ℝ)*((T-U*(g-1:ℕ))/V) = (g:ℝ)*T/V-(g:ℝ)*U*(g-1:ℕ)/V := by ring
    rw [he] at hm
    linarith
  · have hs : T-W < 0 := by linarith
    have hh : (g:ℝ)*((T-W)/V) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (div_nonpos_of_nonpos_of_nonneg hs.le hV.le)
    have he : (g:ℝ)*((T-W)/V) = (g:ℝ)*T/V-(g:ℝ)*U*(g-1:ℕ)/V := by dsimp [W]; ring
    rw [he] at hh
    exact hh.trans (Nat.cast_nonneg _)

theorem rational_selected_count_general {n : ℕ} (D : ℕ) (hD : 0 < D)
    (W Cbox : ℝ) (hW : 0 < W) (hCbox : 0 < Cbox) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin n → ℤ)),
      ∀ (s j : Fin n), Set.InjOn (fun z : Fin n → ℤ => z s) (S:Set _) →
      (∀ z ∈ S, ∀ i, |(z i:ℝ)| ≤ Cbox*X^W) →
      ∀ (A B : Polynomial ℂ), IsCoprime A B → 0 < B.natDegree →
      A.natDegree ≤ D → B.natDegree ≤ D →
      (∀ z ∈ S, A.eval (z s:ℂ) = (z j:ℂ)*B.eval (z s:ℂ)) →
      (S.card:ℝ) ≤ C*X^ε := by
  classical
  obtain ⟨C,hC,hbound⟩ := ComplexValues.rational_integer_values_uniform D hD W W Cbox hW hW hCbox ε hε
  refine ⟨C,hC,?_⟩
  intro X hX S s j hinj hbox A B hcop hB hAD hBD he
  let v : ℤ → ℤ := fun a => if ha : ∃ z ∈ S, z s = a then ha.choose j else 0
  have hv (z) (hz : z ∈ S) : v (z s) = z j := by
    have ha : ∃ u ∈ S, u s = z s := ⟨z,hz,rfl⟩
    dsimp only [v]
    rw [dite_eq_left ha]
    exact congrArg (fun u => u j) (hinj ha.choose_spec.1 hz ha.choose_spec.2)
  have hcard : (S.image fun z => z s).card = S.card := Finset.card_image_of_injOn hinj
  rw [←hcard]
  apply hbound A B hcop hB hAD hBD _ v X hX
  · intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    rw [hv z hz]
    exact he z hz
  · intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    exact hbox z hz s
  · intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    rw [hv z hz]
    exact hbox z hz j

theorem bounded_polynomial_of_constant_denominator {K R : Type*} [Field K] [CommRing R]
    (φ : K →+* R) (x y : R) (A B : Polynomial K) (hB : B ≠ 0)
    (hdeg : B.natDegree = 0) (he : A.eval₂ φ x = y*B.eval₂ φ x) :
    ∃ P : Polynomial K, P.natDegree ≤ A.natDegree ∧ P.eval₂ φ x = y := by
  have hBc : B = Polynomial.C (B.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hb : B.coeff 0 ≠ 0 := by intro h; apply hB; rw [hBc,h,Polynomial.C_0]
  refine ⟨Polynomial.C (B.coeff 0)⁻¹ * A,?_,?_⟩
  · exact Polynomial.natDegree_C_mul_le _ _
  · have hev : B.eval₂ φ x = φ (B.coeff 0) := by
      conv_lhs => rw [hBc]
      rw [Polynomial.eval₂_C]
    rw [Polynomial.eval₂_mul,Polynomial.eval₂_C,he,hev,←mul_assoc,mul_comm (φ _),mul_assoc,
      ←map_mul,inv_mul_cancel₀ hb,map_one,mul_one]

theorem curve_polynomial_left_gain {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (s j : Fin n) (hweight : ω j = ω s)
    (hs : Transcendental ℂ (Ideal.Quotient.mk I (X s)))
    (P : Polynomial ℂ) (hP : Polynomial.aeval (Ideal.Quotient.mk I (X s)) P = Ideal.Quotient.mk I (X j))
    (hdeg : 2 ≤ P.natDegree) :
    ∀ T : ℝ, 0 ≤ T → 2*T/(ω s)-2 ≤ weightedHilbert I ω T := by
  have hh := polynomial_curve_hilbert_gain I ω hω _ _ hs P hP 2 (by decide) hdeg
    (ω s) (ω s) (hω s).le (hω s) (weightedFunctions_coordinate I ω hω s)
    (hweight ▸ weightedFunctions_coordinate I ω hω j)
  intro T hT
  have he : (2:ℝ)*(ω s)*(2-1:ℕ)/(ω s) = 2 := by
    norm_num
    exact mul_div_cancel_right₀ _ (hω s).ne'
  simpa only [Nat.cast_ofNat,he] using hh T hT

theorem norm_curve_polynomial_reduction {n d : ℕ}
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (x : Fin d → Fin n)
    (U W Cbox : ℝ) (hU : 0 < U) (hW : 0 < W) (hCbox : 0 < Cbox)
    (hxw : ∀ j, ω (x j) = U) (hωW : ∀ j, ω j ≤ W)
    (e : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin n → ℤ)),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime →
      affineDimension I ≤ 1 → affineDegree I ≤ e → (∀ z ∈ S, PointOn I z) →
      ∀ s : Fin d, Transcendental ℂ (Ideal.Quotient.mk I (MvPolynomial.X (x s))) →
      (S.card:ℝ) ≤ C*X^ε ∨
      (∀ T : ℝ, 0 ≤ T → 2*T/U-2*(W/U+1) ≤ weightedHilbert I ω T) ∨
      (∃ P : Fin n → Polynomial ℂ, (∀ j, (P j).natDegree ≤ e ∧
        Polynomial.aeval (Ideal.Quotient.mk I (MvPolynomial.X (x s))) (P j) =
          Ideal.Quotient.mk I (MvPolynomial.X j)) ∧ ∀ j, (P (x j)).natDegree ≤ 1) := by
  classical
  obtain ⟨C,hC,hcount⟩ := rational_selected_count_general (n := n) (e+1) (by omega) W Cbox hW hCbox ε hε
  refine ⟨C,hC,?_⟩
  intro X hX S hbox I hI hdim hdeg hon s hs
  let : I.IsPrime := hI
  rcases curve_coordinate_rationalization I hdim e hdeg ω hω (x s) hs with ⟨j,hj⟩ | ⟨A,B,hAB⟩
  · right; left
    intro T hT
    have hh := hj T hT
    rw [hxw] at hh
    have hw := (div_le_div_iff_of_pos_right hU).mpr (hωW j)
    linarith
  have hcop (j) := (hAB j).1
  have hrel (j) := (hAB j).2.2.2.2
  by_cases hb : ∃ j, 0 < (B j).natDegree
  · obtain ⟨j,hj⟩ := hb
    left
    apply hcount X hX S (x s) j
      ((rational_coordinates_injOn I (x s) A B hcop hrel).mono (fun z hz => hon z hz))
    · intro z hz i
      apply (hbox z hz i).trans
      gcongr
      · linarith
      · exact hωW i
    · exact hcop j
    · exact hj
    · exact (hAB j).2.2.1.trans (by omega)
    · exact (hAB j).2.2.2.1.trans (by omega)
    · intro z hz
      exact rational_coordinate_at_point I z (hon z hz) (x s) j (A j) (B j) (hrel j)
  push Not at hb
  choose P hPd hP using fun j => bounded_polynomial_of_constant_denominator
    (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I)) _ _ (A j) (B j) (hAB j).2.1 (by have := hb j; omega) (hrel j)
  by_cases hp : ∃ j, 2 ≤ (P (x j)).natDegree
  · obtain ⟨j,hj⟩ := hp
    right; left
    intro T hT
    have hh := curve_polynomial_left_gain I ω hω (x s) (x j) (by rw [hxw,hxw]) hs (P (x j)) (hP (x j)) hj T hT
    rw [hxw] at hh
    have hw : 0 ≤ W/U := div_nonneg hW.le hU.le
    linarith
  · right; right
    refine ⟨P,fun j => ⟨(hPd j).trans (hAB j).2.2.1,hP j⟩,?_⟩
    intro j
    have := not_exists.mp hp j
    omega

end
open scoped BigOperators Classical

theorem integer_conjugate_form_injective {d : ℕ} {K : Type*} [Field K] [CharZero K]
    (v : Fin d → K) (hv : LinearIndependent ℚ v) (σ : K →+* ℂ) :
    Function.Injective (fun z : Fin d → ℤ => ∑ j, σ (v j)*(z j:ℂ)) := by
  intro z w h
  have he : ∑ j, (z j:K)*v j = ∑ j, (w j:K)*v j := by
    apply σ.injective
    simpa only [map_sum,map_mul,map_intCast,mul_comm] using h
  have hz : ∑ j, ((z j:ℚ)-(w j:ℚ)) • v j = 0 := by
    simpa only [Algebra.smul_def,map_sub,map_intCast,sub_mul,Finset.sum_sub_distrib] using sub_eq_zero.mpr he
  funext j
  have hj := linearIndependent_iff'.mp hv Finset.univ _ hz j (Finset.mem_univ j)
  exact Int.cast_injective (α := ℚ) (sub_eq_zero.mp hj)

theorem conjugateLinePolynomial_degree {d : ℕ} {K : Type*} [Field K]
    (v : Fin d → K) (σ : K →+* ℂ) (P : Fin d → Polynomial ℂ)
    (hP : ∀ j, (P j).natDegree ≤ 1) : (conjugateLinePolynomial v σ P).natDegree ≤ 1 := by
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => (Polynomial.natDegree_C_mul_le _ _).trans (hP j))

theorem conjugateLinePolynomial_slope_ne_zero {d : ℕ} {K : Type*} [Field K] [CharZero K]
    (v : Fin d → K) (hv : LinearIndependent ℚ v) (σ : K →+* ℂ)
    (P : Fin d → Polynomial ℂ) (hP : ∀ j, (P j).natDegree ≤ 1)
    (s : Fin d) (z w : Fin d → ℤ) (hne : z s ≠ w s)
    (hz : ∀ j, (P j).eval (z s:ℂ) = (z j:ℂ))
    (hw : ∀ j, (P j).eval (w s:ℂ) = (w j:ℂ)) :
    (conjugateLinePolynomial v σ P).coeff 1 ≠ 0 := by
  intro hzero
  have hp := Polynomial.eq_X_add_C_of_natDegree_le_one (conjugateLinePolynomial_degree v σ P hP)
  rw [hzero,Polynomial.C_0,zero_mul,zero_add] at hp
  have he : (conjugateLinePolynomial v σ P).eval (z s:ℂ) =
      (conjugateLinePolynomial v σ P).eval (w s:ℂ) := by rw [hp]; simp
  simp only [conjugateLinePolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,hz,hw] at he
  exact hne (congrArg (fun a => a s) (integer_conjugate_form_injective v hv σ he))

theorem curve_polynomial_substitution {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (s : Fin n) (P : Fin n → Polynomial K)
    (hP : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (MvPolynomial.X s)) (P j) =
      Ideal.Quotient.mk I (MvPolynomial.X j))
    (q : MvPolynomial (Fin n) K) :
    Polynomial.aeval (Ideal.Quotient.mk I (MvPolynomial.X s)) (MvPolynomial.aeval P q) =
      Ideal.Quotient.mk I q := by
  rw [MvPolynomial.comp_aeval_apply]
  simp only [hP]
  have he : MvPolynomial.aeval (fun j => Ideal.Quotient.mk I (MvPolynomial.X j)) = Ideal.Quotient.mkₐ K I := by
    ext j; simp
  rw [he]
  rfl

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_CurveThresholds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped Classical BigOperators

theorem conjugateLinePolynomial_aeval {n d : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (s : Fin n) (x : Fin d → Fin n)
    (v : Fin d → K) (σ : K →+* ℂ) (P : Fin n → Polynomial ℂ)
    (hP : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (X s)) (P j) = Ideal.Quotient.mk I (X j)) :
    Polynomial.aeval (Ideal.Quotient.mk I (X s)) (conjugateLinePolynomial v σ (P ∘ x)) =
      Ideal.Quotient.mk I (coordinateLinearForm x (σ ∘ v)) := by
  simp only [conjugateLinePolynomial,coordinateLinearForm,map_sum,map_mul,Polynomial.aeval_C,
    Function.comp_apply,hP]
  congr 1

theorem norm_polynomial_line_degrees {n d : ℕ} {K : Type*} [Field K] [CharZero K]
    (hd : 0 < d) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (x : Fin d → Fin n) (s : Fin d)
    (v : Fin d → K) (hv : LinearIndependent ℚ v) (σ : Fin d → K →+* ℂ)
    (θ : Fin d → ℂ) (hθ : Function.Injective θ)
    (b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (k : ℕ) (hk : 0 < k)
    (hs : Transcendental ℂ (Ideal.Quotient.mk I (X (x s))))
    (hq : Transcendental ℂ (Ideal.Quotient.mk I q))
    (heq : ∀ i, Ideal.Quotient.mk I (coordinateLinearForm x (σ i ∘ v))^k * Ideal.Quotient.mk I (b i) =
      Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i))
    (P : Fin n → Polynomial ℂ)
    (hP : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (X (x s))) (P j) = Ideal.Quotient.mk I (X j))
    (hPx : ∀ j, (P (x j)).natDegree ≤ 1)
    (z w : Fin n → ℤ) (hz : PointOn I z) (hw : PointOn I w) (hne : z (x s) ≠ w (x s)) :
    1+d*(k-1) ≤ (MvPolynomial.aeval P q).natDegree ∧
      ∀ i, (d-1)*(k-1) ≤ (MvPolynomial.aeval P (b i)).natDegree := by
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  let N : Polynomial ℂ := MvPolynomial.aeval P q
  let B : Fin d → Polynomial ℂ := fun i => MvPolynomial.aeval P (b i)
  let A : Fin d → Polynomial ℂ := fun i => conjugateLinePolynomial v (σ i) (P ∘ x)
  have hN : 0 < N.natDegree := by
    by_contra h
    have hp := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h)
    have hev := curve_polynomial_substitution I (x s) P hP q
    change Polynomial.aeval _ N = _ at hev
    rw [hp,Polynomial.aeval_C] at hev
    exact hq (hev ▸ isAlgebraic_algebraMap (N.coeff 0))
  have hzP (j) : (P (x j)).eval (z (x s):ℂ) = (z (x j):ℂ) := by
    have hh := congrArg (pointEvaluation I z hz) (hP (x j))
    rw [←Polynomial.aeval_algHom_apply] at hh
    simpa only [pointEvaluation_X,Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] using hh
  have hwP (j) : (P (x j)).eval (w (x s):ℂ) = (w (x j):ℂ) := by
    have hh := congrArg (pointEvaluation I w hw) (hP (x j))
    rw [←Polynomial.aeval_algHom_apply] at hh
    simpa only [pointEvaluation_X,Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] using hh
  have hr (i) : (A i).coeff 1 ≠ 0 :=
    conjugateLinePolynomial_slope_ne_zero v hv (σ i) (P ∘ x) hPx s (z ∘ x) (w ∘ x) hne hzP hwP
  have hA (i) : A i = Polynomial.C ((A i).coeff 1)*Polynomial.X+Polynomial.C ((A i).coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one (conjugateLinePolynomial_degree v (σ i) (P ∘ x) hPx)
  have hid (i) : (Polynomial.C ((A i).coeff 1)*Polynomial.X+Polynomial.C ((A i).coeff 0))^k * B i =
      N-Polynomial.C (θ i) := by
    rw [←hA i]
    apply (transcendental_iff_injective.mp hs)
    simp only [map_mul,map_pow,map_sub,Polynomial.aeval_C]
    rw [conjugateLinePolynomial_aeval I (x s) x v (σ i) P hP,
      curve_polynomial_substitution I (x s) P hP (b i),curve_polynomial_substitution I (x s) P hP q]
    exact heq i
  have hh := curve_polynomial_degrees N hN θ (fun i => (A i).coeff 1) (fun i => (A i).coeff 0) B hθ hr hk hid
  simpa only [Fintype.card_fin,N,B] using And.intro hh.1 (fun i => (hh.2 i).2)

theorem norm_polynomial_line_hilbert {n d : ℕ} {K : Type*} [Field K] [CharZero K]
    (hd : 2 ≤ d) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x : Fin d → Fin n) (s : Fin d) (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hxw : ω (x s) = U)
    (v : Fin d → K) (hv : LinearIndependent ℚ v) (σ : Fin d → K →+* ℂ)
    (θ : Fin d → ℂ) (hθ : Function.Injective θ)
    (b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (hbw : ∀ i, Ideal.Quotient.mk I (b i) ∈ weightedFunctions I ω V)
    (k : ℕ) (hk : 2 ≤ k)
    (hs : Transcendental ℂ (Ideal.Quotient.mk I (X (x s))))
    (hq : Transcendental ℂ (Ideal.Quotient.mk I q))
    (heq : ∀ i, Ideal.Quotient.mk I (coordinateLinearForm x (σ i ∘ v))^k * Ideal.Quotient.mk I (b i) =
      Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i))
    (P : Fin n → Polynomial ℂ)
    (hP : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (X (x s))) (P j) = Ideal.Quotient.mk I (X j))
    (hPx : ∀ j, (P (x j)).natDegree ≤ 1)
    (z w : Fin n → ℤ) (hz : PointOn I z) (hw : PointOn I w) (hne : z (x s) ≠ w (x s)) :
    let g := (d-1)*(k-1)
    ∀ T : ℝ, 0 ≤ T → T/U ≤ weightedHilbert I ω T ∧
      (g:ℝ)*T/V-(g:ℝ)*U*(g-1:ℕ)/V ≤ weightedHilbert I ω T := by
  dsimp only
  let g := (d-1)*(k-1)
  have hg : 0 < g := Nat.mul_pos (by omega) (by omega)
  have hdeg := (norm_polynomial_line_degrees (by omega) I x s v hv σ θ hθ b q k (by omega) hs hq heq P hP hPx z w hz hw hne).2
  have hsw : Ideal.Quotient.mk I (X (x s)) ∈ weightedFunctions I ω U := hxw ▸ weightedFunctions_coordinate I ω hω (x s)
  intro T hT
  constructor
  · have hh := polynomial_curve_hilbert_gain I ω hω _ _ hs Polynomial.X (Polynomial.aeval_X _) 1 (by decide)
      (by simp) U U hU.le hU hsw hsw T hT
    simpa only [Nat.cast_one,one_mul,Nat.sub_self,Nat.cast_zero,mul_zero,zero_div,sub_zero] using hh
  · let i : Fin d := ⟨0,by omega⟩
    exact polynomial_curve_hilbert_gain I ω hω _ _ hs (MvPolynomial.aeval P (b i))
      (curve_polynomial_substitution I (x s) P hP (b i)) g hg (hdeg i) U V hU.le hV hsw (hbw i) T hT

theorem polynomial_coordinates_injOn {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (s : Fin n)
    (P : Fin n → Polynomial ℂ)
    (hP : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (X s)) (P j) = Ideal.Quotient.mk I (X j)) :
    Set.InjOn (fun z : Fin n → ℤ => z s) {z | PointOn I z} := by
  intro z hz w hw he
  funext j
  have hzP := congrArg (pointEvaluation I z hz) (hP j)
  have hwP := congrArg (pointEvaluation I w hw) (hP j)
  rw [←Polynomial.aeval_algHom_apply] at hzP hwP
  simp only [pointEvaluation_X,Polynomial.aeval_def,Algebra.algebraMap_self,Polynomial.eval₂_id] at hzP hwP
  change z s = w s at he
  rw [he] at hzP
  exact Int.cast_injective (α := ℂ) (hzP.symm.trans hwP)

theorem norm_curve_alternatives {n d : ℕ}
    (hd : 2 ≤ d) (k : ℕ) (hk : 2 ≤ k)
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (x : Fin d → Fin n)
    (U V W Cbox : ℝ) (hU : 0 < U) (hV : 0 < V) (hW : 0 < W) (hCbox : 0 < Cbox)
    (hxw : ∀ j, ω (x j) = U) (hωW : ∀ j, ω j ≤ W)
    (e : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C H : ℝ, 0 < C ∧ 0 ≤ H ∧
      ∀ (K : Type) [Field K] [CharZero K] (v : Fin d → K), LinearIndependent ℚ v →
      ∀ (σ : Fin d → K →+* ℂ) (θ : Fin d → ℂ), Function.Injective θ →
      ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin n → ℤ)),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime →
      affineDimension I ≤ 1 → affineDegree I ≤ e → (∀ z ∈ S, PointOn I z) →
      ∀ (b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ),
      (∀ i, Ideal.Quotient.mk I (b i) ∈ weightedFunctions I ω V) →
      Transcendental ℂ (Ideal.Quotient.mk I q) →
      (∀ i, Ideal.Quotient.mk I (coordinateLinearForm x (σ i ∘ v))^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i)) →
      ∀ s : Fin d, Transcendental ℂ (Ideal.Quotient.mk I (MvPolynomial.X (x s))) →
      (S.card:ℝ) ≤ C*X^ε ∨
      (∀ T : ℝ, 0 ≤ T →
        min (2/U) (max (1/U) (((d-1)*(k-1):ℕ)/V))*T-H ≤ weightedHilbert I ω T) := by
  classical
  obtain ⟨C,hC,hred⟩ := norm_curve_polynomial_reduction ω hω x U W Cbox hU hW hCbox hxw hωW e ε hε
  let g := (d-1)*(k-1)
  let H := 2*(W/U+1)+(g:ℝ)*U*(g-1:ℕ)/V
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨max C 1,H,lt_of_lt_of_le hC (le_max_left _ _),hH,?_⟩
  intro K _ _ v hv σ θ hθ X hX S hbox I hI hdim hdeg hon b q hbw hq heq s hs
  have hCge : C*X^ε ≤ max C 1*X^ε := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
  rcases hred X hX S hbox I hI hdim hdeg hon s hs with hc | hh | ⟨P,hP,hPx⟩
  · exact Or.inl (hc.trans hCge)
  · right
    intro T hT
    have hl : min (2/U) (max (1/U) ((g:ℝ)/V))*T ≤ (2/U)*T :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hT
    have her : 2*(W/U+1) ≤ H := by
      dsimp [H]
      exact le_add_of_nonneg_right (by positivity)
    have hb := hh T hT
    change min (2/U) (max (1/U) ((g:ℝ)/V))*T-H ≤ _
    calc
      _ ≤ (2/U)*T-2*(W/U+1) := sub_le_sub hl her
      _ = 2*T/U-2*(W/U+1) := by ring
      _ ≤ _ := hb
  have hinj := polynomial_coordinates_injOn I (x s) P (fun j => (hP j).2)
  by_cases hp : ∃ z ∈ S, ∃ w ∈ S, z (x s) ≠ w (x s)
  · obtain ⟨z,hz,w,hw,hne⟩ := hp
    have hh := norm_polynomial_line_hilbert hd I ω hω x s U V hU hV (hxw s) v hv σ θ hθ b q hbw k hk hs hq heq
      P (fun j => (hP j).2) hPx z w (hon z hz) (hon w hw) hne
    right
    intro T hT
    have h1 := (hh T hT).1
    have h2 := (hh T hT).2
    have her : (g:ℝ)*U*(g-1:ℕ)/V ≤ H := by
      dsimp [H]
      exact le_add_of_nonneg_left (by positivity)
    have hl : min (2/U) (max (1/U) ((g:ℝ)/V))*T ≤ max (1/U) ((g:ℝ)/V)*T :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hT
    change min (2/U) (max (1/U) ((g:ℝ)/V))*T-H ≤ _
    apply (sub_le_sub_right hl H).trans
    rcases le_total (1/U) ((g:ℝ)/V) with hl' | hl'
    · rw [max_eq_right hl']
      calc
        _ = (g:ℝ)*T/V-H := by ring
        _ ≤ (g:ℝ)*T/V-(g:ℝ)*U*(g-1:ℕ)/V := sub_le_sub_left her _
        _ ≤ _ := h2
    · rw [max_eq_left hl']
      calc
        _ = T/U-H := by ring
        _ ≤ T/U := sub_le_self _ hH
        _ ≤ _ := h1
  · left
    have hcard : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro z hz w hw
      apply hinj (hon z hz) (hon w hw)
      by_contra he
      exact hp ⟨z,hz,w,hw,he⟩
    have hx : 1 ≤ X^ε := Real.one_le_rpow (by linarith) hε.le
    have hc : 1 ≤ max C 1 := le_max_right _ _
    calc
      (S.card:ℝ) ≤ 1 := by exact_mod_cast hcard
      _ ≤ max C 1*X^ε := one_le_mul_of_one_le_of_one_le hc hx

end

open scoped BigOperators

theorem normBoxEnvelope_pos (d h : ℕ) : 0 < normBoxEnvelope d h := by
  unfold normBoxEnvelope
  split_ifs <;> norm_num

theorem normBox_increment_nonneg_5 (i : Fin (5+1)) : 0 ≤ normBoxIncrement 5 i := by
  fin_cases i <;> norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope]

theorem normBox_prefix_5 (i : Fin (5+1)) :
    normBoxStage 5 i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (5+1) => j.val ≤ i.val), normBoxIncrement 5 j := by
  fin_cases i <;> norm_num [normBoxStage,normBoxIncrement,normBoxEnvelope,Fin.sum_univ_succ,Finset.sum_filter]

theorem normBox_sum_5 :
    (∑ i : Fin (5+1), ((5+1-i.val:ℕ):ℝ)*normBoxIncrement 5 i)+1/1000 ≤ 997/1000 := by
  norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope,Fin.sum_univ_succ]

theorem normBox_increment_nonneg_6 (i : Fin (6+1)) : 0 ≤ normBoxIncrement 6 i := by
  fin_cases i <;> norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope]

theorem normBox_prefix_6 (i : Fin (6+1)) :
    normBoxStage 6 i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (6+1) => j.val ≤ i.val), normBoxIncrement 6 j := by
  fin_cases i <;> norm_num [normBoxStage,normBoxIncrement,normBoxEnvelope,Fin.sum_univ_succ,Finset.sum_filter]

theorem normBox_sum_6 :
    (∑ i : Fin (6+1), ((6+1-i.val:ℕ):ℝ)*normBoxIncrement 6 i)+1/1000 ≤ 997/1000 := by
  norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope,Fin.sum_univ_succ]

theorem normBox_increment_nonneg_7 (i : Fin (7+1)) : 0 ≤ normBoxIncrement 7 i := by
  fin_cases i <;> norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope]

theorem normBox_prefix_7 (i : Fin (7+1)) :
    normBoxStage 7 i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (7+1) => j.val ≤ i.val), normBoxIncrement 7 j := by
  fin_cases i <;> norm_num [normBoxStage,normBoxIncrement,normBoxEnvelope,Fin.sum_univ_succ,Finset.sum_filter]

theorem normBox_sum_7 :
    (∑ i : Fin (7+1), ((7+1-i.val:ℕ):ℝ)*normBoxIncrement 7 i)+1/1000 ≤ 997/1000 := by
  norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope,Fin.sum_univ_succ]

theorem normBox_increment_nonneg_8 (i : Fin (8+1)) : 0 ≤ normBoxIncrement 8 i := by
  fin_cases i <;> norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope]

theorem normBox_prefix_8 (i : Fin (8+1)) :
    normBoxStage 8 i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (8+1) => j.val ≤ i.val), normBoxIncrement 8 j := by
  fin_cases i <;> norm_num [normBoxStage,normBoxIncrement,normBoxEnvelope,Fin.sum_univ_succ,Finset.sum_filter]

theorem normBox_sum_8 :
    (∑ i : Fin (8+1), ((8+1-i.val:ℕ):ℝ)*normBoxIncrement 8 i)+1/1000 ≤ 997/1000 := by
  norm_num [normBoxIncrement,normBoxStage,normBoxEnvelope,Fin.sum_univ_succ]

theorem normBox_increment_nonneg (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8)
    (i : Fin (d+1)) : 0 ≤ normBoxIncrement d i := by
  interval_cases d
  · exact normBox_increment_nonneg_5 i
  · exact normBox_increment_nonneg_6 i
  · exact normBox_increment_nonneg_7 i
  · exact normBox_increment_nonneg_8 i

theorem normBox_prefix (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8)
    (i : Fin (d+1)) :
    normBoxStage d i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (d+1) => j.val ≤ i.val), normBoxIncrement d j := by
  interval_cases d
  · exact normBox_prefix_5 i
  · exact normBox_prefix_6 i
  · exact normBox_prefix_7 i
  · exact normBox_prefix_8 i

theorem normBox_sum (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8) :
    (∑ i : Fin (d+1), ((d+1-i.val:ℕ):ℝ)*normBoxIncrement d i)+1/1000 ≤ 997/1000 := by
  interval_cases d
  · exact normBox_sum_5
  · exact normBox_sum_6
  · exact normBox_sum_7
  · exact normBox_sum_8

theorem normBox_full_threshold (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8) :
    1/(((d+1).factorial:ℝ)*(normBoxEnvelope d (d+1))^(d+1)) ≤
      (((d-2)*5+6:ℕ):ℝ)^(d-1)*15^(d+1)/(((d+1).factorial:ℝ)*5^d*6^d) := by
  interval_cases d <;> norm_num [normBoxEnvelope]

theorem normBox_curve_threshold (d : ℕ) (hd : 5 ≤ d) (hd' : d ≤ 8) :
    1/normBoxEnvelope d 1 ≤ min (2/(1/3:ℝ)) (max (1/(1/3:ℝ)) (((d-1)*(d-2-1):ℕ)/(2/5:ℝ))) := by
  interval_cases d <;> norm_num [normBoxEnvelope]
end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_NormComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical

theorem quotient_pair_generates {n d : ℕ} (a b : Fin d → MvPolynomial (Fin n) ℂ)
    (hg : Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    Algebra.adjoin ℂ (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
      Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ := by
  let e := Ideal.Quotient.mkₐ ℂ I
  have hr : Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪ Set.range (fun i => Ideal.Quotient.mk I (b i)) =
      e '' (Set.range a ∪ Set.range b) := by
    simp only [Set.image_union,← Set.range_comp]
    rfl
  rw [hr,Algebra.adjoin_image,hg]
  apply top_unique
  intro z _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I z
  exact ⟨p,by trivial,_root_.rfl⟩

theorem norm_dimension_le {n d : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (k : ℕ) (a b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) (θ : Fin d → ℂ)
    (ha : ∀ i, Ideal.Quotient.mk I (a i) ≠ 0)
    (heq : ∀ i, Ideal.Quotient.mk I (a i)^k*Ideal.Quotient.mk I (b i) =
      Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i))
    (hg : Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤)
    (hq : Transcendental ℂ (Ideal.Quotient.mk I q)) : affineDimension I ≤ d+1 := by
  let := pair_projection_isAlgebraic k (fun i => Ideal.Quotient.mk I (a i))
    (fun i => Ideal.Quotient.mk I (b i)) (Ideal.Quotient.mk I q) θ ha heq (quotient_pair_generates a b hg I)
  obtain ⟨m,j,_,hj,ht⟩ := left_coordinates_transcendence_selection
    (fun i => Ideal.Quotient.mk I (a i)) (Ideal.Quotient.mk I q) hq
  have hm : m ≤ d := by simpa using Fintype.card_le_of_injective j hj
  have hdim := hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)
  rw [ht] at hdim
  have hh : affineDimension I = m+1 := by exact_mod_cast hdim
  omega

theorem polynomial_constant_at_point {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (q : MvPolynomial (Fin n) ℂ) (t : ℂ)
    (ht : algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) t = Ideal.Quotient.mk I q)
    (z : Fin n → ℤ) (hz : PointOn I z) : MvPolynomial.aeval (fun j => (z j:ℂ)) q = t := by
  have hh := congrArg (pointEvaluation I z hz) ht
  rw [AlgHom.commutes] at hh
  change t = MvPolynomial.aeval (fun j => (z j:ℂ)) q at hh
  exact hh.symm

theorem algebraic_polynomial_fibre_count {n : ℕ} (S : Finset (Fin n → ℤ)) (F : ℕ)
    (q : MvPolynomial (Fin n) ℂ)
    (hf : ∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) q = t)).card ≤ F)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hq : IsAlgebraic ℂ (Ideal.Quotient.mk I q)) : (S.filter (PointOn I)).card ≤ F := by
  obtain ⟨t,ht⟩ := algebraic_coordinate_constant (Ideal.Quotient.mk I q) hq
  apply (Finset.card_le_card ?_).trans (hf t)
  intro z hz
  have h := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨h.1,polynomial_constant_at_point I q t ht z h.2⟩

theorem algebraic_left_fibre_count {n d : ℕ} (S : Finset (Fin n → ℤ)) (F : ℕ)
    (x : Fin d → Fin n)
    (hf : ∀ c : Fin d → ℤ, (S.filter (fun z => ∀ i, z (x i) = c i)).card ≤ F)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hx : ∀ i, IsAlgebraic ℂ (Ideal.Quotient.mk I (MvPolynomial.X (x i)))) :
    (S.filter (PointOn I)).card ≤ F := by
  by_cases he : (S.filter (PointOn I)).Nonempty
  · obtain ⟨z,hz⟩ := he
    have hzI := (Finset.mem_filter.mp hz).2
    apply (Finset.card_le_card ?_).trans (hf (fun i => z (x i)))
    intro w hw
    obtain ⟨hwS,hwI⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_filter.mpr ⟨hwS,fun i => ?_⟩
    obtain ⟨t,ht⟩ := algebraic_coordinate_constant (Ideal.Quotient.mk I (MvPolynomial.X (x i))) (hx i)
    exact Int.cast_injective (α := ℂ) ((coordinate_constant_at_point I w hwI (x i) t ht).trans
      (coordinate_constant_at_point I z hzI (x i) t ht).symm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
    exact Nat.zero_le _

end
section
open MvPolynomial

theorem norm_full_threshold_uniform {n d : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
        (a b : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
        (θ : Fin d → ℂ),
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^(d-2)*Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i)) →
      Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤ →
      Transcendental ℂ (Ideal.Quotient.mk I q) → affineDimension I = d+1 →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w 5) → (∀ i, b i ∈ weightedSpace w 6) →
      ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = 15*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        T^(d+1)/(((d+1).factorial:ℝ)*(normBoxEnvelope d (d+1))^(d+1))-C*T^d ≤ weightedHilbert I ω T := by
  have hsucc : d-1+1 = d := by omega
  have hsucc' : d-1+2 = d+1 := by omega
  have hb := norm_full_real_hilbert_uniform (N := n) (n := d-1) (K := ℂ)
    (d-2) 5 6 (by norm_num) (by norm_num) 15 (by norm_num)
  rw [hsucc,hsucc'] at hb
  obtain ⟨C,hC,hbound⟩ := hb
  refine ⟨C,hC,fun I _ a b q θ ha heq hg hq hdim w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hbound I a b q θ ha heq (quotient_pair_generates a b hg I) hq
    hdim w hw haw hbw ω hω hscale T hT
  have hc := mul_le_mul_of_nonneg_right (normBox_full_threshold d hd hd')
    (pow_nonneg (by linarith : 0 ≤ T) (d+1))
  have hc' : T^(d+1)/(((d+1).factorial:ℝ)*(normBoxEnvelope d (d+1))^(d+1)) ≤
      (((d-2)*5+6:ℕ):ℝ)^(d-1)*15^(d+1)/(((d+1).factorial:ℝ)*5^d*6^d)*T^(d+1) := by
    simpa only [one_div_mul_eq_div] using hc
  norm_num only [Nat.cast_ofNat] at hb
  linarith only [hb,hc']

open MvPolynomial
open scoped BigOperators Classical

attribute [instance] NormBoxSystem.field NormBoxSystem.charZero

theorem NormBoxSystem.quotient_equations {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) (I : Ideal (MvPolynomial (Fin n) ℂ)) (hI : M.ideal ≤ I) :
    ∀ i, Ideal.Quotient.mk I (M.a i)^(d-2)*Ideal.Quotient.mk I (M.b i) =
      Ideal.Quotient.mk I M.q-algebraMap ℂ _ (M.θ i) := by
  intro i
  have hm : M.equation i ∈ I := hI (Ideal.subset_span ⟨i,rfl⟩)
  have he := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
  simp only [NormBoxSystem.equation,map_add,map_sub,map_mul,map_pow] at he
  change Ideal.Quotient.mk I (M.a i)^(d-2)*Ideal.Quotient.mk I (M.b i)-
    Ideal.Quotient.mk I M.q+algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) (M.θ i) = 0 at he
  linear_combination he

theorem NormBoxSystem.quotient_left_nonzero {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (z : Fin n → ℤ) (hz : PointOn I z)
    (ha : ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) :
    ∀ i, Ideal.Quotient.mk I (M.a i) ≠ 0 := by
  intro i hi
  have hh := congrArg (pointEvaluation I z hz) hi
  rw [map_zero] at hh
  change MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) = 0 at hh
  exact ha i hh

theorem NormBoxSystem.right_real_weight {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) (hω : ∀ i, 0 < ω i) (hscale : ∀ i, (w i:ℝ) = 15*ω i)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (i : Fin d) :
    Ideal.Quotient.mk I (M.b i) ∈ weightedFunctions I ω (2/5) := by
  have hh := weightedSpace_map_le_weightedFunctions I w ω hω 15 (by norm_num) hscale (2/5) (by norm_num)
  norm_num only [show (15:ℝ)*(2/5) = 6 by norm_num,Nat.floor_natCast] at hh
  exact hh ⟨M.b i,M.rightWeight i,rfl⟩

end
open MvPolynomial
open scoped BigOperators Classical

theorem norm_component_alternatives {n d h D : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8)
    (hh : 1 ≤ h) (hh' : h ≤ d+1) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 2/5)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 15*ω i)
    (M : NormBoxSystem n d D ω w) (Cbox : ℝ) (hCbox : 0 < Cbox)
    (F E : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K H : ℝ, 1 ≤ K ∧ 0 ≤ H ∧ ∀ X : ℝ, 2 ≤ X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin d → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
      affineDimension I = h → affineDegree I ≤ E →
      (∀ i, Ideal.Quotient.mk I (M.a i) ≠ 0) →
      ((S.filter (PointOn I)).card:ℝ) ≤ K*X^ε ∨
      ∀ T : ℝ, 1 ≤ T → T^h/((h.factorial:ℝ)*(normBoxEnvelope d h)^h)-H*T^(h-1) ≤ weightedHilbert I ω T := by
  classical
  have hsmall (X : ℝ) (hX : 2 ≤ X) (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) ℂ))
      (K : ℝ) (hKF : (F:ℝ) ≤ K) (hK : 0 ≤ K) (hcard : (S.filter (PointOn I)).card ≤ F) :
      ((S.filter (PointOn I)).card:ℝ) ≤ K*X^ε := by
    have hx : 1 ≤ X^ε := Real.one_le_rpow (by linarith) hε.le
    calc
      _ ≤ (F:ℝ) := by exact_mod_cast hcard
      _ ≤ K := hKF
      _ ≤ K*X^ε := by nlinarith
  by_cases h1 : h = 1
  · subst h
    obtain ⟨B,H,hB,hH,hcurve⟩ := norm_curve_alternatives (n := n) (d := d) (by omega)
      (d-2) (by omega) ω hω M.x (1/3) (2/5) (2/5) Cbox (by norm_num) (by norm_num)
      (by norm_num) hCbox M.xweight hωW E ε hε
    let K : ℝ := max 1 (max B F)
    have hK : 1 ≤ K := le_max_left _ _
    have hKF : (F:ℝ) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
    have hKB : B ≤ K := (le_max_left _ _).trans (le_max_right _ _)
    refine ⟨K,H,hK,hH,fun X hX S hbox hnF haF I hI hMI hdim hdeg ha => ?_⟩
    let : I.IsPrime := hI
    by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
    · exact Or.inl (hsmall X hX S I K hKF (by linarith) (algebraic_polynomial_fibre_count S F M.q hnF I hq))
    by_cases hxa : ∀ i, IsAlgebraic ℂ (Ideal.Quotient.mk I (MvPolynomial.X (M.x i)))
    · exact Or.inl (hsmall X hX S I K hKF (by linarith) (algebraic_left_fibre_count S F M.x haF I hxa))
    push Not at hxa
    obtain ⟨s,hs⟩ := hxa
    have hsS (z) (hz : z ∈ S.filter (PointOn I)) := (Finset.mem_filter.mp hz).1
    have hh := hcurve M.Carrier M.v M.independent M.σ M.θ M.distinct X hX
      (S.filter (PointOn I)) (fun z hz j => hbox z (hsS z hz) j) I hI hdim.le hdeg
      (fun z hz => (Finset.mem_filter.mp hz).2) M.b M.q
      (M.right_real_weight hω hscale I) hq (M.quotient_equations I hMI) s hs
    rcases hh with hc | hHilb
    · left
      exact hc.trans (mul_le_mul_of_nonneg_right hKB (Real.rpow_nonneg (by linarith) _))
    · right
      intro T hT
      have hb := hHilb T (by linarith)
      have hc := mul_le_mul_of_nonneg_right (normBox_curve_threshold d hd hd') (by linarith : 0 ≤ T)
      norm_num only [pow_one,Nat.factorial_one,Nat.cast_one,one_mul,Nat.sub_self,pow_zero,mul_one]
      have hc' : T/normBoxEnvelope d 1 ≤ min (2/(1/3:ℝ)) (max (1/(1/3:ℝ)) (((d-1)*(d-2-1):ℕ)/(2/5:ℝ)))*T := by
        simpa only [one_div_mul_eq_div] using hc
      linarith only [hb,hc']
  · have hh2 : 2 ≤ h := by omega
    by_cases hhd : h ≤ d
    · obtain ⟨H,hH,hHilb⟩ := norm_generic_threshold_uniform (n := n) hd hd' hh2 hhd E D hD
      let K : ℝ := max 1 F
      have hK : 1 ≤ K := le_max_left _ _
      have hKF : (F:ℝ) ≤ K := le_max_right _ _
      refine ⟨K,H,hK,hH,fun X hX S _ hnF _ I hI hMI hdim hdeg ha => ?_⟩
      let : I.IsPrime := hI
      by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
      · exact Or.inl (hsmall X hX S I K hKF (by linarith) (algebraic_polynomial_fibre_count S F M.q hnF I hq))
      · exact Or.inr (hHilb I M.a M.b M.q M.θ M.distinct ha (M.quotient_equations I hMI)
          M.generates hq hdim hdeg M.leftDegree M.qDegree w hw M.leftWeight M.rightWeight ω hω hscale)
    · have he : h = d+1 := by omega
      subst h
      obtain ⟨H,hH,hHilb⟩ := norm_full_threshold_uniform (n := n) hd hd'
      let K : ℝ := max 1 F
      have hK : 1 ≤ K := le_max_left _ _
      have hKF : (F:ℝ) ≤ K := le_max_right _ _
      refine ⟨K,H,hK,hH,fun X hX S _ hnF _ I hI hMI hdim _ ha => ?_⟩
      let : I.IsPrime := hI
      by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
      · exact Or.inl (hsmall X hX S I K hKF (by linarith) (algebraic_polynomial_fibre_count S F M.q hnF I hq))
      · right
        simpa only [Nat.add_sub_cancel] using hHilb I M.a M.b M.q M.θ ha (M.quotient_equations I hMI)
          M.generates hq hdim w hw M.leftWeight M.rightWeight ω hω hscale

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_NormBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical

theorem norm_box_prime_count {n d D : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 2/5)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 15*ω i)
    (M : NormBoxSystem n d D ω w) (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (F e₀ : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin d → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
        affineDimension I ≤ d+1 → affineDegree I ≤ e₀ → (∀ z ∈ S, PointOn I z) →
      (S.card:ℝ) ≤ C*X^(997/1000:ℝ) := by
  classical
  choose K H hK hH halt using fun (e : ℕ) (i : Fin (d+1)) =>
    norm_component_alternatives (h := d+1-i.val) hd hd' (by omega) (by omega) hD
      ω hω hωW w hw hscale M Cbox (by linarith) F e (1/4000) (by norm_num)
  let c := fun e => ∑ i : Fin (d+1), H e i
  let Ke := fun e => 1+∑ i : Fin (d+1), K e i
  have hc : ∀ e, 0 ≤ c e := fun e => Finset.sum_nonneg (fun i _ => hH e i)
  have hKe : ∀ e, 1 ≤ Ke e := by
    intro e
    dsimp [Ke]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hK e i)))
  have hci (e) (i : Fin (d+1)) : H e i ≤ c e := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => hH e j) (Finset.mem_univ i)
  have hKi (e) (i : Fin (d+1)) : K e i ≤ Ke e := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => zero_le_one.trans (hK e j)) (Finset.mem_univ i)
    dsimp [Ke]
    linarith
  let W : ℝ := 1+∑ j, ω j
  have hsum : 0 ≤ ∑ j, ω j := Finset.sum_nonneg (fun j _ => (hω j).le)
  have hW : 0 ≤ W := by dsimp [W]; linarith
  obtain ⟨C,Xcut,hC,hcount⟩ := physical_affine_count n (d+1) 0 e₀ (by omega)
    ω hω Cbox W hCbox hW (normBoxIncrement d) (normBoxStage d)
    (normBox_increment_nonneg d hd hd') (fun i => normBoxEnvelope_pos _ _)
    (normBox_prefix d hd hd') (1/1000) (by norm_num) c Ke hc hKe
  refine ⟨C,max (max 2 Cbox) Xcut,hC,fun X hX S hbox hnF haF hnonzero I hI hMI hdim hdeg hon => ?_⟩
  have hX2 : 2 < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hX
  have hCX : Cbox ≤ X := le_of_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hX)
  have hXcut : Xcut < X := lt_of_le_of_lt (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hmax (j : Fin n) : ω j ≤ ∑ l, ω l := Finset.single_le_sum
    (fun l _ => (hω l).le) (Finset.mem_univ j)
  have hbound (z) (hz : z ∈ S) (j) : |(z j:ℝ)| ≤ X^W := by
    calc
      _ ≤ Cbox*X^(ω j) := hbox z hz j
      _ ≤ X*X^(∑ l, ω l) := mul_le_mul hCX
        (Real.rpow_le_rpow_of_exponent_le hX1 (hmax j)) (Real.rpow_nonneg hXp.le _) hXp.le
      _ = X^W := by dsimp [W]; rw [Real.rpow_add hXp,Real.rpow_one]
  let G : KernelGeometry n := ⟨S,X^W,Real.one_le_rpow hX1 hW,hbound⟩
  have hb := hcount X hXcut G le_rfl hbox I hI hdim hdeg hon
  have hcS := hb (by
    intro i e J hJ hIJ _ hJe hJdim hp
    let : J.IsPrime := hJ
    obtain ⟨z,hz,hzJ⟩ := hp
    have ha := M.quotient_left_nonzero J z hzJ (hnonzero z hz)
    have hh := halt e i X hX2.le S hbox hnF haF J hJ (hMI.trans hIJ) hJdim hJe ha
    rcases hh with hs | hHilb
    · left
      have hm := mul_le_mul_of_nonneg_right (hKi e i) (Real.rpow_nonneg hXp.le (1/4000))
      norm_num only [show (1/1000:ℝ)/4=1/4000 by norm_num]
      exact hs.trans hm
    · right
      intro T hT
      have hh := hHilb T hT
      have hm := mul_le_mul_of_nonneg_right (hci e i) (pow_nonneg (by linarith : 0 ≤ T) (d+1-i.val-1))
      change T^(d+1-i.val)/(((d+1-i.val).factorial:ℝ)*(normBoxEnvelope d (d+1-i.val))^(d+1-i.val))-
        c e*T^(d+1-i.val-1) ≤ _
      linarith only [hh,hm])
  exact hcS.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX1 (normBox_sum d hd hd')) hC.le)

theorem norm_box_prime_count_unrestricted {n d D : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 2/5)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 15*ω i)
    (M : NormBoxSystem n d D ω w) (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (F e₀ : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin d → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
        affineDegree I ≤ e₀ → (∀ z ∈ S, PointOn I z) →
      (S.card:ℝ) ≤ C*X^(997/1000:ℝ) := by
  obtain ⟨C,X₀,hC,hb⟩ := norm_box_prime_count hd hd' hD ω hω hωW w hw hscale M Cbox hCbox F e₀
  refine ⟨C+F+1,max 2 X₀,by positivity,fun X hX S hbox hqF haF hn I hI hMI hdeg hon => ?_⟩
  let : I.IsPrime := hI
  have hX1 : 1 ≤ X := by have := (le_max_left 2 X₀).trans_lt hX; linarith
  have hp : 1 ≤ X^(997/1000:ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hfilter : S.filter (PointOn I) = S := Finset.filter_true_of_mem hon
  by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
  · have hcard := algebraic_polynomial_fibre_count S F M.q hqF I hq
    rw [hfilter] at hcard
    calc
      (S.card:ℝ) ≤ F := by exact_mod_cast hcard
      _ ≤ (C+F+1)*X^(997/1000:ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) F]
  · by_cases hs : S.Nonempty
    · obtain ⟨z,hz⟩ := hs
      have ha := M.quotient_left_nonzero I z (hon z hz) (hn z hz)
      have hdim := norm_dimension_le I (d-2) M.a M.b M.q M.θ ha (M.quotient_equations I hMI) M.generates hq
      have hh := hb X (lt_of_le_of_lt (le_max_right _ _) hX) S hbox hqF haF hn I hI hMI hdim hdeg hon
      exact hh.trans (mul_le_mul_of_nonneg_right (by have := Nat.cast_nonneg (α := ℝ) F; linarith : C ≤ C+F+1) (by positivity))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.card_empty,Nat.cast_zero]
      positivity

theorem norm_box_count {n d D : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 2/5)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 15*ω i)
    (M : NormBoxSystem n d D ω w) (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (F : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin d → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
      (∀ z ∈ S, PointOn M.ideal z) →
      (S.card:ℝ) ≤ C*X^(997/1000:ℝ) := by
  classical
  let Q := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) M.ideal).toFinset
  let E : ℕ := ∑ I ∈ Q, ⌈affineDegree I⌉₊
  have hQ (I) (hI : I ∈ Q) : I ∈ M.ideal.minimalPrimes := (Set.Finite.mem_toFinset _).mp hI
  have hE (I) (hI : I ∈ Q) : affineDegree I ≤ E := by
    have hsum : ⌈affineDegree I⌉₊ ≤ E := Finset.single_le_sum (f := fun J => ⌈affineDegree J⌉₊) (fun _ _ => Nat.zero_le _) hI
    exact (Nat.le_ceil _).trans (by exact_mod_cast hsum)
  obtain ⟨C,X₀,hC,hb⟩ := norm_box_prime_count_unrestricted hd hd' hD ω hω hωW w hw hscale M Cbox hCbox F E
  refine ⟨(Q.card+1)*C,max 2 X₀,by positivity,fun X hX S hbox hqF haF hn hon => ?_⟩
  have hXpos : 0 ≤ X := by have := (le_max_left 2 X₀).trans_lt hX; linarith
  have hX₀ : X₀ < X := (le_max_right _ _).trans_lt hX
  have cover : S ⊆ Q.biUnion (fun I => S.filter (PointOn I)) := by
    intro z hz
    obtain ⟨I,hI,hzI⟩ := point_on_minimal_component M.ideal (fun j => (z j:ℂ)) (hon z hz)
    exact Finset.mem_biUnion.mpr ⟨I,(Set.Finite.mem_toFinset _).mpr hI,Finset.mem_filter.mpr ⟨hz,hzI⟩⟩
  have hbound (I) (hI : I ∈ Q) : ((S.filter (PointOn I)).card:ℝ) ≤ C*X^(997/1000:ℝ) := by
    apply hb X hX₀ (S.filter (PointOn I))
    · intro z hz; exact hbox z (Finset.mem_filter.mp hz).1
    · intro t
      apply (Finset.card_le_card ?_).trans (hqF t)
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    · intro c
      apply (Finset.card_le_card ?_).trans (haF c)
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    · intro z hz; exact hn z (Finset.mem_filter.mp hz).1
    · exact (hQ I hI).isPrime
    · exact (hQ I hI).1.2
    · exact hE I hI
    · intro z hz; exact (Finset.mem_filter.mp hz).2
  calc
    (S.card:ℝ) ≤ (∑ I ∈ Q, (S.filter (PointOn I)).card : ℕ) := by
      exact_mod_cast (Finset.card_le_card cover).trans (Finset.card_biUnion_le)
    _ = ∑ I ∈ Q, ((S.filter (PointOn I)).card:ℝ) := by simp
    _ ≤ ∑ I ∈ Q, C*X^(997/1000:ℝ) := Finset.sum_le_sum hbound
    _ = Q.card*(C*X^(997/1000:ℝ)) := by simp
    _ ≤ ((Q.card+1)*C)*X^(997/1000:ℝ) := by nlinarith [Real.rpow_nonneg (x := X) hXpos (997/1000:ℝ)]

end

section
open Polynomial NumberField

theorem minpoly_integral_normalization {K : Type*} [Field K] [NumberField K]
    (f : Polynomial ℤ) (hf : Irreducible (f.map (Int.castRingHom ℚ)))
    (hd : 1 ≤ f.natDegree) (θ : K) (hθ : f.aeval θ = 0)
    (t : 𝓞 K) (ht : (t : K) = (f.leadingCoeff : K) * θ) :
    minpoly ℤ t = f.integralNormalization := by
  have hf0 : f ≠ 0 := fun h => hf.ne_zero (by simp [h])
  have he : (f.integralNormalization.map (Int.castRingHom ℚ)).aeval (t : K) = 0 := by
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap,
      aeval_def, ht]
    change f.integralNormalization.eval₂ (algebraMap ℤ K)
      ((algebraMap ℤ K) f.leadingCoeff * θ) = 0
    rw [integralNormalization_eval₂_leadingCoeff_mul hd]
    change (f.leadingCoeff : K) ^ (f.natDegree - 1) * f.aeval θ = 0
    rw [hθ, mul_zero]
  have hm := minpoly.eq_of_irreducible_of_monic (integralNormalization_irreducible f hf)
    he ((monic_integralNormalization hf0).map (Int.castRingHom ℚ))
  have htint : IsIntegral ℤ t := t.isIntegral
  have hm' := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K htint
  apply map_injective (Int.castRingHom ℚ) (Int.cast_injective)
  change (minpoly ℤ t).map (algebraMap ℤ ℚ) = _
  rw [← hm']
  change minpoly ℚ (t : K) = _
  exact hm.symm

open Polynomial NumberField
open scoped nonZeroDivisors

theorem exponent_ne_zero_of_powerBasis {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (pb : PowerBasis ℚ K) (hgen : pb.gen = (θ : K)) :
    RingOfIntegers.exponent θ ≠ 0 := by
  classical
  let b := RingOfIntegers.basis K
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  let A := Algebra.adjoin ℤ {θ}
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun ij : ι × Fin pb.dim => pb.basis.repr ((b ij.1 : 𝓞 K) : K) ij.2)
  choose a ha using hm
  have hmb (i : ι) : (m : ℤ) • b i ∈ A := by
    have he : (m : ℤ) • ((b i : 𝓞 K) : K) =
        ∑ j : Fin pb.dim, (a (i,j) : ℚ) • pb.basis j := by
      conv_lhs => rw [← pb.basis.sum_repr ((b i : 𝓞 K) : K)]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← smul_assoc, ← ha (i,j)]
      rfl
    have he' : (m : ℤ) • b i = ∑ j : Fin pb.dim, a (i,j) • θ ^ (j : ℕ) := by
      apply RingOfIntegers.ext
      simpa [pb.basis_eq_pow,hgen, Algebra.smul_def] using he
    rw [he']
    apply A.sum_mem
    intro j _
    exact A.smul_mem (A.pow_mem (Algebra.subset_adjoin (Set.mem_singleton θ)) _) _
  have hz (z : 𝓞 K) : (m : ℤ) • z ∈ A := by
    rw [← b.sum_repr z]
    rw [Finset.smul_sum]
    apply A.sum_mem
    intro i _
    rw [smul_comm]
    exact A.smul_mem (hmb i) _
  have hmc : (m : ℤ) ∈ Ideal.under ℤ (conductor ℤ θ) := by
    change ((m : ℤ) : 𝓞 K) ∈ conductor ℤ θ
    rw [mem_conductor_iff]
    intro z
    simpa [Algebra.smul_def] using hz z
  intro hzero
  have he := Int.ideal_span_absNorm_eq_self (Ideal.under ℤ (conductor ℤ θ))
  change Ideal.span {((RingOfIntegers.exponent θ : ℕ) : ℤ)} = _ at he
  rw [hzero, Nat.cast_zero, Ideal.span_singleton_zero] at he
  rw [← he, Ideal.mem_bot] at hmc
  exact nonZeroDivisors.coe_ne_zero m hmc

end

open Polynomial NumberField

theorem simple_root_ideal_power {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (f : Polynomial R)
    (a θ : R) (k : ℕ) (hθ : f.eval θ = 0) (haθ : a - θ ∈ P)
    (hd : f.derivative.eval a ∉ P) (hf : f.eval a ∈ P ^ k) : a - θ ∈ P ^ k := by
  let g := f /ₘ (X - C θ)
  have hfac : f.eval a = (a - θ) * g.eval a := by
    have h := congrArg (Polynomial.eval a)
      (Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic f θ)
    simpa only [eval_mul, eval_sub, eval_X, eval_C, modByMonic_X_sub_C_eq_C_eval,
      hθ, sub_zero] using h.symm
  have hdiag : g.eval θ = f.derivative.eval θ := by
    have h := congrArg (Polynomial.eval θ)
      (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f θ)
    simpa only [eval_add, eval_mul, eval_sub, eval_X, eval_C,
      sub_self, zero_mul, add_zero] using h
  have hsub (q : Polynomial R) : q.eval a - q.eval θ ∈ P := by
    obtain ⟨t, ht⟩ := Polynomial.sub_dvd_eval_sub a θ q
    rw [ht]
    exact P.mul_mem_right t haθ
  have hg : g.eval a ∉ P := by
    intro hga
    have hgθ := P.sub_mem hga (hsub g)
    have hh : f.derivative.eval θ ∈ P := by simpa [hdiag] using hgθ
    apply hd
    convert P.add_mem (hsub f.derivative) hh using 1
    ring
  cases k with
  | zero => simp
  | succ k =>
    by_contra hx
    apply hg
    exact Ideal.mem_prime_of_mul_mem_pow hP hx (by rwa [← hfac])

theorem root_prime_ideal {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (a : ℤ) (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (hc : ¬ p ∣ RingOfIntegers.exponent θ)
    (hd : ¬ (p : ℤ) ∣ (minpoly ℤ θ).derivative.eval a)
    (hf : (p : ℤ) ^ k ∣ (minpoly ℤ θ).eval a) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ P.absNorm = p ∧
      (a : 𝓞 K) - θ ∈ P ^ k := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let Q : Polynomial ℤ := X - C a
  have hf1 : (p : ℤ) ∣ (minpoly ℤ θ).eval a :=
    dvd_trans (dvd_pow_self (p : ℤ) hk.ne') hf
  have hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p := by
    change Q.map _ ∈ (UniqueFactorizationMonoid.normalizedFactors _).toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
      (Polynomial.map_monic_ne_zero (minpoly.monic θ.isIntegral))]
    simp only [Q, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, ?_⟩
    rw [Polynomial.dvd_iff_isRoot, IsRoot.def, eval_map, eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hf1
  let P' := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hc).symm ⟨_, hQ⟩
  let P : Ideal (𝓞 K) := P'
  let : P.IsPrime := P'.property.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := P'.property.2
  let : P.IsMaximal := Ideal.primesOver.isMaximal P'
  have hspan : P = Ideal.span {(p : 𝓞 K), θ - (a : 𝓞 K)} := by
    dsimp [P, P']
    rw [NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hc hQ]
    simp [Q]
  have hpP : (p : 𝓞 K) ∈ P := by rw [hspan]; exact Ideal.subset_span (Set.mem_insert _ _)
  have hP0 : P ≠ ⊥ := by
    intro h
    have : (p : 𝓞 K) = 0 := by simpa [h] using hpP
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) this
  have hab : (a : 𝓞 K) - θ ∈ P := by
    have h : θ - (a : 𝓞 K) ∈ P := by rw [hspan]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    simpa only [neg_sub] using P.neg_mem h
  have hn : P.absNorm = p := by
    have hdeg := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hc hQ
    have hdeg' : P.inertiaDeg ℤ = 1 := by
      simpa only [P, P', Q, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, natDegree_X_sub_C] using hdeg
    simpa only [hdeg', pow_one, Int.natAbs_natCast] using
      (Ideal.natAbs_pow_inertiaDeg (p : ℤ) P).symm
  refine ⟨P, inferInstance, hP0, hn, ?_⟩
  let f := (minpoly ℤ θ).map (Int.castRingHom (𝓞 K))
  apply simple_root_ideal_power P hP0 f (a : 𝓞 K) θ k
  · rw [show f = (minpoly ℤ θ).map (algebraMap ℤ (𝓞 K)) from rfl, eval_map]
    exact minpoly.aeval ℤ θ
  · exact hab
  · intro h
    have h' : (minpoly ℤ θ).derivative.eval a ∈ Ideal.span {(p : ℤ)} := by
      apply (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) _).mpr
      simpa [f, derivative_map, eval_map, eval₂_at_apply] using h
    exact hd (Ideal.mem_span_singleton.mp h')
  · obtain ⟨t, ht⟩ := hf
    have he : f.eval (a : 𝓞 K) = (p : 𝓞 K) ^ k * (t : 𝓞 K) := by
      dsimp [f]
      rw [eval_map]
      change (minpoly ℤ θ).eval₂ (Int.castRingHom (𝓞 K)) ((Int.castRingHom (𝓞 K)) a) = _
      rw [eval₂_at_apply]
      change (((minpoly ℤ θ).eval a : ℤ) : 𝓞 K) = _
      rw [ht, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [he]
    exact (P ^ k).mul_mem_right _ (Ideal.pow_mem_pow hpP k)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_UnitBalancing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace QuarticPowerFree

section
open Module

theorem lattice_covering_radius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] : ∃ R : ℝ, 0 < R ∧ ∀ x : E, ∃ z : L, ‖x - z‖ ≤ R := by
  classical
  have := ZLattice.module_free ℝ L
  let b := Module.Free.chooseBasis ℤ L
  let B := b.ofZLatticeBasis ℝ
  obtain ⟨R, hR⟩ := B.parallelepiped.isCompact.isBounded.exists_norm_le
  refine ⟨max R 0 + 1, by positivity, fun x => ?_⟩
  let z : L := b.repr.symm (Finsupp.equivFunOnFinite.symm fun i => ⌊B.repr x i⌋)
  refine ⟨z, le_trans (hR _ ?_) (by linarith [le_max_left R 0])⟩
  simp [parallelepiped_basis_eq, z, B]
  exact fun i => (Int.fract_lt_one _).le

open NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem

theorem logarithmic_units_cover (K : Type*) [Field K] [NumberField K] :
    ∃ R : ℝ, 0 < R ∧ ∀ x : logSpace K, ∃ u : (𝓞 K)ˣ,
      ‖x - logEmbedding K (Additive.ofMul u)‖ ≤ R := by
  obtain ⟨R, hR, h⟩ := lattice_covering_radius (unitLattice K)
  refine ⟨R, hR, fun x => ?_⟩
  obtain ⟨z, hz⟩ := h x
  obtain ⟨u, _, hu⟩ := z.2
  exact ⟨u.toMul, hu ▸ hz⟩

theorem unit_balancing_hyperplane (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ s : InfinitePlace K → ℝ,
      (∑ w, (mult w : ℝ) * s w) = 0 → ∃ u : (𝓞 K)ˣ,
      ∀ w, |Real.log (w (u : K)) + s w| ≤ C := by
  classical
  obtain ⟨R, hR, hcover⟩ := logarithmic_units_cover K
  refine ⟨(Fintype.card (InfinitePlace K) : ℝ) * R,
    mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hR, fun s hs => ?_⟩
  obtain ⟨u, hu⟩ := hcover (fun w => -(mult w.val : ℝ) * s w.val)
  have hsmall (w : {w : InfinitePlace K // w ≠ w₀}) :
      |(mult w.val : ℝ) * (Real.log (w.val (u : K)) + s w.val)| ≤ R := by
    have hh := (norm_le_pi_norm (fun w => -(mult w.val : ℝ) * s w.val -
      logEmbedding K (Additive.ofMul u) w) w).trans hu
    have he : (-(mult w.val : ℝ) * s w.val -
      logEmbedding K (Additive.ofMul u) w) =
      -((mult w.val : ℝ) * (Real.log (w.val (u : K)) + s w.val)) := by
      rw [logEmbedding_component]
      ring
    rw [he, norm_neg, Real.norm_eq_abs] at hh
    exact hh

  have hmult (w : InfinitePlace K) : (1 : ℝ) ≤ mult w := by
    rw [mult]; split_ifs <;> norm_num
  have habs (w : InfinitePlace K) : |Real.log (w (u : K)) + s w| ≤
      |(mult w : ℝ) * (Real.log (w (u : K)) + s w)| := by
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (hmult w)
  refine ⟨u, fun w => ?_⟩
  by_cases hw : w = w₀
  · have hsum : (mult w : ℝ) * (Real.log (w (u : K)) + s w) =
        -∑ v : {v : InfinitePlace K // v ≠ w₀},
          (mult v.val : ℝ) * (Real.log (v.val (u : K)) + s v.val) := by
      have ht : (∑ v : InfinitePlace K,
          (mult v : ℝ) * (Real.log (v (u : K)) + s v)) = 0 := by
        simp only [mul_add, Finset.sum_add_distrib, NumberField.Units.sum_mult_mul_log, hs,
          add_zero]
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at ht
      rw [hw]
      exact eq_neg_of_add_eq_zero_left ht
    refine (habs w).trans ?_
    rw [hsum, abs_neg]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun v _ => hsmall v)).trans
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Fintype.card_subtype_le _)) hR.le
  · exact (habs w).trans ((hsmall ⟨w,hw⟩).trans
      (le_mul_of_one_le_left hR.le (Nat.one_le_cast.mpr Fintype.card_pos)))

theorem unit_balancing_norm (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ x : K, x ≠ 0 → ∃ u : (𝓞 K)ˣ,
      ∀ w : InfinitePlace K,
        C⁻¹ * |(Algebra.norm ℚ x : ℝ)| ^ ((Module.finrank ℚ K : ℝ)⁻¹) ≤ w ((u : K) * x) ∧
        w ((u : K) * x) ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨R, hR, hbalance⟩ := unit_balancing_hyperplane K
  refine ⟨Real.exp R, Real.exp_pos _, fun x hx => ?_⟩
  let d : ℝ := Module.finrank ℚ K
  let a : ℝ := |(Algebra.norm ℚ x : ℝ)|
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (Nat.ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  have ha : 0 < a := by
    dsimp [a]
    apply abs_pos.mpr
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx)
  have hwpos (w : InfinitePlace K) : 0 < w x := InfinitePlace.pos_iff.mpr hx
  have hs : (∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w x)) = Real.log a := by
    have h := congrArg Real.log (prod_eq_abs_norm x)
    rw [Real.log_prod (fun w _ => pow_ne_zero _ (ne_of_gt (hwpos w)))] at h
    simpa [a, Real.log_pow] using h
  have hzero : (∑ w : InfinitePlace K,
      (mult w : ℝ) * (Real.log (w x) - Real.log a / d)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, hs, ← Finset.sum_mul]
    rw [← Nat.cast_sum, sum_mult_eq]
    change Real.log a - d * (Real.log a / d) = 0
    field_simp
    ring
  obtain ⟨u, hu⟩ := hbalance (fun w => Real.log (w x) - Real.log a / d) hzero
  refine ⟨u, fun w => ?_⟩
  have hb := abs_le.mp (hu w)
  have he : Real.exp (Real.log (w (u : K)) + Real.log (w x)) = w ((u : K) * x) := by
    rw [Real.exp_add, Real.exp_log (pos_at_place u w), Real.exp_log (hwpos w), map_mul]
  have hr : a ^ d⁻¹ = Real.exp (Real.log a / d) := by
    rw [Real.rpow_def_of_pos ha]
    congr 1
  change (Real.exp R)⁻¹ * a ^ d⁻¹ ≤ _ ∧ _ ≤ Real.exp R * a ^ d⁻¹
  rw [hr]
  constructor
  · rw [← Real.exp_neg, ← Real.exp_add, ← he]
    apply Real.exp_le_exp.mpr
    linarith [hb.1]
  · rw [← Real.exp_add, ← he]
    apply Real.exp_le_exp.mpr
    linarith [hb.2]

open NumberField
open scoped nonZeroDivisors

theorem finite_ideal_correction (K : Type*) [Field K] [NumberField K] (k : ℕ) :
    ∃ (μ : ℕ) (S : Finset (Ideal (𝓞 K))), 0 < μ ∧
      (∀ J ∈ S, J ≠ ⊥) ∧
      ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ → ∀ x ∈ I ^ k,
        ∃ J ∈ S, ∃ α : 𝓞 K, α ≠ 0 ∧ ∃ β : 𝓞 K,
          Ideal.span {α} = I * J ∧ α ^ k * β = (μ : 𝓞 K) * x := by
  classical
  let c : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰ := fun g =>
    (ClassGroup.mk0_surjective g⁻¹).choose
  have hc (g : ClassGroup (𝓞 K)) : ClassGroup.mk0 (c g) = g⁻¹ :=
    (ClassGroup.mk0_surjective g⁻¹).choose_spec
  let S : Finset (Ideal (𝓞 K)) := Finset.univ.image (fun g => (c g : Ideal (𝓞 K)))
  let M : ℕ := ∏ g : ClassGroup (𝓞 K), Ideal.absNorm (c g : Ideal (𝓞 K))
  have hMpos : 0 < M := Finset.prod_pos (fun g _ =>
    Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors (c g)))
  refine ⟨M ^ k, S, pow_pos hMpos _, ?_, ?_⟩
  · intro J hJ
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hJ
    exact mem_nonZeroDivisors_iff_ne_zero.mp (c g).property
  · intro I hI x hx
    let I' : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
    let g := ClassGroup.mk0 I'
    have he : ClassGroup.mk0 I' = (ClassGroup.mk0 (c g))⁻¹ := by rw [hc, inv_inv]
    obtain ⟨α, hα, hspan⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp he
    have hMmem : (M : 𝓞 K) ∈ (c g : Ideal (𝓞 K)) := by
      have hd : Ideal.absNorm (c g : Ideal (𝓞 K)) ∣ M :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ g)
      obtain ⟨a, ha⟩ := hd
      rw [ha, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    have hprod : ((M ^ k : ℕ) : 𝓞 K) * x ∈ Ideal.span {α ^ k} := by
      rw [← Ideal.span_singleton_pow, ← hspan, mul_pow]
      rw [Nat.cast_pow]
      simpa only [mul_comm] using (Ideal.mul_mem_mul hx (Ideal.pow_mem_pow hMmem k))
    obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton.mp hprod
    refine ⟨c g, Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩, α, hα, β, ?_, hβ.symm⟩
    exact hspan.symm

theorem balanced_ideal_factorization (K : Type*) [Field K] [NumberField K] (k : ℕ) :
    ∃ (μ : ℕ) (S : Finset (Ideal (𝓞 K))) (C : ℝ), 0 < μ ∧ 0 < C ∧
      (∀ J ∈ S, J ≠ ⊥) ∧
      ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ → ∀ x ∈ I ^ k,
        ∃ J ∈ S, ∃ α : 𝓞 K, α ≠ 0 ∧ ∃ β : 𝓞 K,
          Ideal.span {α} = I * J ∧ α ^ k * β = (μ : 𝓞 K) * x ∧
          ∀ w : InfinitePlace K,
            C⁻¹ * ((I.absNorm * J.absNorm : ℕ) : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) ≤ w (α : K) ∧
            w (α : K) ≤ C * ((I.absNorm * J.absNorm : ℕ) : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨μ, S, hμ, hS, hfactor⟩ := finite_ideal_correction K k
  obtain ⟨C, hC, hbalance⟩ := unit_balancing_norm K
  refine ⟨μ, S, C, hμ, hC, hS, fun I hI x hx => ?_⟩
  obtain ⟨J, hJ, α, hα, β, hspan, hβ⟩ := hfactor I hI x hx
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  obtain ⟨u, hu⟩ := hbalance α hαK
  have hn : |(Algebra.norm ℚ (α : K) : ℝ)| = ((I.absNorm * J.absNorm : ℕ) : ℝ) := by
    rw [← Algebra.coe_norm_int, Rat.cast_intCast]
    have h := congrArg Ideal.absNorm hspan
    rw [Ideal.absNorm_span_singleton, map_mul] at h
    rw [← h]
    norm_cast
    rw [Nat.cast_natAbs]
  refine ⟨J, hJ, (u : 𝓞 K) * α, mul_ne_zero (Units.ne_zero u) hα,
    ((↑u⁻¹ : 𝓞 K) ^ k) * β, ?_, ?_, ?_⟩
  · simpa only [Ideal.span_singleton_mul_left_unit u.isUnit] using hspan
  · calc
      ((u : 𝓞 K) * α) ^ k * ((↑u⁻¹ : 𝓞 K) ^ k * β) =
          (((u : 𝓞 K) * ↑u⁻¹) ^ k) * (α ^ k * β) := by ring
      _ = (μ : 𝓞 K) * x := by simp [hβ]
  · intro w
    change C⁻¹ * _ ≤ w ((algebraMap (𝓞 K) K) ((u : 𝓞 K) * α)) ∧
      w ((algebraMap (𝓞 K) K) ((u : 𝓞 K) * α)) ≤ C * _
    simpa only [map_mul, hn] using hu w

end

open Polynomial NumberField

theorem arithmetic_factorization_large_primes {K : Type*} [Field K] [NumberField K]
    (f : Polynomial ℤ) (hf : Irreducible (f.map (Int.castRingHom ℚ)))
    (hd : 1 ≤ f.natDegree) (hc : 0 < f.leadingCoeff)
    (θ : K) (hθ : f.aeval θ = 0) (t : 𝓞 K)
    (ht : (t : K) = (f.leadingCoeff : K) * θ)
    (pb : PowerBasis ℚ K) (hgen : pb.gen = (t : K))
    (k : ℕ) (hk : 0 < k) :
    ∃ (B μ : ℕ) (S : Finset (Ideal (𝓞 K))) (C : ℝ), 0 < μ ∧ 0 < C ∧
      (∀ J ∈ S, J ≠ ⊥) ∧
      ∀ (n : ℤ) (p : ℕ), p.Prime → B < p → (p : ℤ) ^ k ∣ f.eval n →
        ∃ J ∈ S, ∃ α : 𝓞 K, α ≠ 0 ∧ ∃ β : 𝓞 K,
          (α : K) ^ k * (β : K) = (μ : K) * ((n : K) - θ) ∧
          |(Algebra.norm ℚ (α : K) : ℝ)| = ((p * J.absNorm : ℕ) : ℝ) ∧
          ∀ w : InfinitePlace K,
            C⁻¹ * ((p * J.absNorm : ℕ) : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) ≤ w (α : K) ∧
            w (α : K) ≤ C * ((p * J.absNorm : ℕ) : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  let F := f.integralNormalization
  have hmin : minpoly ℤ t = F := minpoly_integral_normalization f hf hd θ hθ t ht
  have hFirr := integralNormalization_irreducible f hf
  have hR := resultant_derivative_ne_zero F hFirr
  have hE := exponent_ne_zero_of_powerBasis t pb hgen
  obtain ⟨q,S,C,hq,hC,hS,hfactor⟩ := balanced_ideal_factorization K k
  refine ⟨max (RingOfIntegers.exponent t) (F.resultant F.derivative).natAbs,
    q * f.leadingCoeff.natAbs, S,C, Nat.mul_pos hq (Int.natAbs_pos.mpr hc.ne'),
    hC,hS,?_⟩
  intro n p hp hBp hfp
  have hpE : ¬ p ∣ RingOfIntegers.exponent t := by
    intro h
    have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero hE) h
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_left _ _) hBp)) hh
  have hpR : ¬ (p : ℤ) ∣ F.resultant F.derivative := by
    intro h
    have hh : p ≤ (F.resultant F.derivative).natAbs := by
      apply Nat.le_of_dvd (Int.natAbs_pos.mpr hR)
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_right _ _) hBp)) hh
  have heval : F.eval (f.leadingCoeff * n) =
      f.leadingCoeff ^ (f.natDegree - 1) * f.eval n := by
    exact integralNormalization_eval₂_leadingCoeff_mul hd (RingHom.id ℤ) n
  have hfpF : (p : ℤ) ^ k ∣ F.eval (f.leadingCoeff * n) := by
    rw [heval]
    exact dvd_mul_of_dvd_right hfp _
  have hdF : F.natDegree ≠ 0 := by
    change f.integralNormalization.natDegree ≠ 0
    rw [natDegree_integralNormalization]
    omega
  have hderiv := derivative_not_dvd_of_good F hdF hpR
    (dvd_trans (dvd_pow_self (p : ℤ) hk.ne') hfpF)
  rw [← hmin] at hderiv hfpF
  obtain ⟨P,_,hP0,hNP,hmem⟩ := root_prime_ideal t (f.leadingCoeff*n) p k hp hk hpE hderiv hfpF
  obtain ⟨J,hJ,α,hα,β,hspan,hfac,hbal⟩ := hfactor P hP0 ((f.leadingCoeff*n : ℤ) - t) hmem
  refine ⟨J,hJ,α,hα,β,?_,?_,?_⟩
  · have hh := congrArg (algebraMap (𝓞 K) K) hfac
    have habs : (f.leadingCoeff.natAbs : K) = (f.leadingCoeff : K) := by
      have hz : (f.leadingCoeff.natAbs : ℤ) = f.leadingCoeff := by
        rw [Int.natCast_natAbs,abs_of_pos hc]
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : K)) hz
    simp only [map_mul,map_pow,map_sub,map_natCast,map_intCast,ht] at hh
    rw [Nat.cast_mul,habs]
    convert hh using 1
    push_cast
    ring
  · rw [← Algebra.coe_norm_int,Rat.cast_intCast]
    have hn := congrArg Ideal.absNorm hspan
    rw [Ideal.absNorm_span_singleton,map_mul,hNP] at hn
    rw [← hn]
    norm_cast
    rw [Nat.cast_natAbs]
  · simpa only [hNP] using hbal

attribute [instance] ArithmeticModel.field ArithmeticModel.numberField

theorem uniform_root_difference_bounds {K : Type*} [Field K] [NumberField K]
    (θ : K) : ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∀ n : ℤ, X < n → (n : ℝ) ≤ 2*X → ∀ w : InfinitePlace K,
        X/2 ≤ w ((n : K)-θ) ∧ w ((n : K)-θ) ≤ 3*X := by
  classical
  let R := ∑ w : InfinitePlace K, w θ
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  have hwR (w : InfinitePlace K) : w θ ≤ R := by
    change w θ ≤ ∑ v : InfinitePlace K, v θ
    exact Finset.single_le_sum (fun v _ => apply_nonneg v θ) (Finset.mem_univ w)
  refine ⟨2*R+1,by positivity,fun X hX n hn hn' w => ?_⟩
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity : 0 < 2*R+1) hX
  have hnpos : (0 : ℝ) < n := hXpos.trans hn
  have hwn : w (n : K) = (n : ℝ) := by
    rw [InfinitePlace.map_intCast,Int.norm_eq_abs,abs_of_pos hnpos]
  constructor
  · have hh := w.1.le_sub (n : K) θ
    change w (n : K) - w θ ≤ w ((n : K)-θ) at hh
    rw [hwn] at hh
    linarith [hwR w]
  · have hh := w.1.sub_le_add (n : K) θ
    change w ((n : K)-θ) ≤ w (n : K) + w θ at hh
    rw [hwn] at hh
    linarith [hwR w]

theorem absorb_finite_ideal_norms {K : Type*} [Field K] [NumberField K]
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ J ∈ S, J ≠ ⊥)
    (C : ℝ) (hC : 0 < C) (e : ℝ) (he : 0 ≤ e) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p : ℕ, 0 < p → ∀ J ∈ S, ∀ a : ℝ,
      C⁻¹ * ((p*J.absNorm : ℕ) : ℝ)^e ≤ a →
      a ≤ C * ((p*J.absNorm : ℕ) : ℝ)^e →
      D⁻¹ * (p : ℝ)^e ≤ a ∧ a ≤ D * (p : ℝ)^e := by
  classical
  let M := max 1 (S.sup Ideal.absNorm)
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast le_max_left 1 (S.sup Ideal.absNorm)
  let D := max 1 (C * (M : ℝ)^e)
  have hD1 : 1 ≤ D := le_max_left _ _
  have hCD : C ≤ D := by
    exact (le_mul_of_one_le_right hC.le (Real.one_le_rpow hM he)).trans (le_max_right _ _)
  refine ⟨D,hD1,fun p hp J hJ a hlo hhi => ?_⟩
  have hJpos : 0 < J.absNorm := Nat.pos_of_ne_zero fun hz => hS J hJ
    (Ideal.absNorm_eq_zero_iff.mp hz)
  have hJ1 : (1 : ℝ) ≤ J.absNorm := by exact_mod_cast hJpos
  have hJM : (J.absNorm : ℝ) ≤ M := by
    exact_mod_cast (Finset.le_sup hJ).trans (le_max_right 1 (S.sup Ideal.absNorm))
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [Nat.cast_mul,Real.mul_rpow hp0 (Nat.cast_nonneg _)] at hlo hhi
  constructor
  · calc
      D⁻¹ * (p : ℝ)^e ≤ C⁻¹ * (p : ℝ)^e :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hC hCD) (Real.rpow_nonneg hp0 _)
      _ ≤ C⁻¹ * ((p : ℝ)^e * (J.absNorm : ℝ)^e) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.rpow_nonneg hp0 _)
          (Real.one_le_rpow hJ1 he)) (inv_nonneg.mpr hC.le)
      _ ≤ a := hlo
  · calc
      a ≤ C * ((p : ℝ)^e * (J.absNorm : ℝ)^e) := hhi
      _ ≤ C * ((p : ℝ)^e * (M : ℝ)^e) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hJM he) (Real.rpow_nonneg hp0 _)) hC.le
      _ = (C*(M : ℝ)^e) * (p : ℝ)^e := by ring
      _ ≤ D * (p : ℝ)^e := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hp0 _)

theorem companion_archimedean_bounds {K : Type*} [Field K] [NumberField K] (w : InfinitePlace K)
    (α β θ : K) (n : ℤ) (μ k : ℕ) (hμ : 0 < μ)
    (hf : α^k*β = (μ : K)*((n : K)-θ))
    (P X C e : ℝ) (hP : 0 < P) (hX : 0 ≤ X) (hC : 0 < C)
    (ha : C⁻¹ * P^e ≤ w α) (ha' : w α ≤ C*P^e)
    (hb : X/2 ≤ w ((n : K)-θ)) (hb' : w ((n : K)-θ) ≤ 3*X) :
    (2*C^k)⁻¹ * (X/P^(e*k)) ≤ w (β / (μ : K)) ∧
    w (β / (μ : K)) ≤ (3*C^k) * (X/P^(e*k)) := by
  have hμK : (μ : K) ≠ 0 := by exact_mod_cast hμ.ne'
  have ha0 : 0 < w α := lt_of_lt_of_le (mul_pos (inv_pos.mpr hC) (Real.rpow_pos_of_pos hP e)) ha
  have hrel : w α ^ k * w (β / (μ : K)) = w ((n : K)-θ) := by
    have hh : α^k * (β / (μ : K)) = (n : K)-θ := by
      rw [← mul_div_assoc,hf,mul_div_cancel_left₀ _ hμK]
    simpa only [map_mul,map_pow] using congrArg w hh
  have hwβ : w (β / (μ : K)) = w ((n : K)-θ) / (w α)^k := by
    apply (eq_div_iff (pow_ne_zero _ ha0.ne')).mpr
    simpa only [mul_comm] using hrel
  rw [hwβ]
  have hpow := pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hC.le) (Real.rpow_nonneg hP.le _)) ha k
  have hpow' := pow_le_pow_left₀ ha0.le ha' k
  have heq : P^(e*k) = (P^e)^k := Real.rpow_mul_natCast hP.le e k
  rw [heq]
  constructor
  · have hh : (X/2) / (C*P^e)^k ≤ w ((n : K)-θ) / (w α)^k :=
      div_le_div₀ (apply_nonneg _ _) hb (pow_pos ha0 _) hpow'
    rw [mul_pow] at hh
    convert hh using 1
    ring
  · have hh : w ((n : K)-θ) / (w α)^k ≤ (3*X) / (C⁻¹*P^e)^k :=
      div_le_div₀ (by positivity) hb' (pow_pos (mul_pos (inv_pos.mpr hC)
        (Real.rpow_pos_of_pos hP e)) _) hpow
    rw [mul_pow,inv_pow] at hh
    convert hh using 1
    field_simp

theorem balanced_arithmetic (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 1 ≤ f.natDegree)
    (hc : 0 < f.leadingCoeff) (k : ℕ) (hk : 0 < k) :
    ∃ M : ArithmeticModel f, ∃ (μ : ℕ) (S : Finset (Ideal (𝓞 M.Carrier))) (C X₀ : ℝ),
      0 < μ ∧ 1 ≤ C ∧ 0 < X₀ ∧ (∀ J ∈ S, J ≠ ⊥) ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ (n : ℤ) (p : ℕ),
        X < n → (n : ℝ) ≤ 2*X → p.Prime → X < p → (p : ℤ)^k ∣ f.eval n →
        ¬ (p : ℤ) ∣ f.resultant f.derivative ∧
        ∃ J ∈ S, ∃ α : 𝓞 M.Carrier, α ≠ 0 ∧ ∃ β : 𝓞 M.Carrier,
          (α : M.Carrier)^k * (β : M.Carrier) = (μ : M.Carrier)*((n : M.Carrier)-M.root) ∧
          |(Algebra.norm ℚ (α : M.Carrier) : ℝ)| = ((p*J.absNorm : ℕ) : ℝ) ∧
          ∀ w : InfinitePlace M.Carrier,
            (C⁻¹ * (p : ℝ)^((f.natDegree : ℝ)⁻¹) ≤ w (α : M.Carrier) ∧
              w (α : M.Carrier) ≤ C*(p : ℝ)^((f.natDegree : ℝ)⁻¹)) ∧
            ((2*C^k)⁻¹ * (X/(p : ℝ)^((f.natDegree : ℝ)⁻¹*k)) ≤ w ((β : M.Carrier)/(μ : M.Carrier)) ∧
              w ((β : M.Carrier)/(μ : M.Carrier)) ≤ (3*C^k)*(X/(p : ℝ)^((f.natDegree : ℝ)⁻¹*k))) := by
  let M := arithmeticModel f hf hd
  obtain ⟨B,μ,S,C,hμ,hC,hS,hfac⟩ := arithmetic_factorization_large_primes f hf hd hc
    M.root M.root_eq M.integralRoot M.integralRoot_eq M.powerBasis M.powerBasis_gen k hk
  obtain ⟨D,hD,habsorb⟩ := absorb_finite_ideal_norms S hS C hC
    (f.natDegree : ℝ)⁻¹ (by positivity)
  obtain ⟨R,hR,hdiff⟩ := uniform_root_difference_bounds M.root
  let X₀ := max R (max (B : ℝ) (f.resultant f.derivative).natAbs)
  refine ⟨M,μ,S,D,X₀,hμ,hD,hR.trans_le (le_max_left _ _),hS,?_⟩
  intro X hX n p hn hn' hp hpX hfp
  have hBp : B < p := by
    have hh : (B : ℝ) < p := (le_max_left _ _).trans (le_max_right _ _) |>.trans hX |>.trans_lt hpX
    exact_mod_cast hh
  have hgood : ¬ (p : ℤ) ∣ f.resultant f.derivative := by
    intro h
    have hle : p ≤ (f.resultant f.derivative).natAbs := by
      apply Nat.le_of_dvd (Int.natAbs_pos.mpr (resultant_derivative_ne_zero f hf))
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h
    have hh : ((f.resultant f.derivative).natAbs : ℝ) < p :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hX |>.trans_lt hpX
    exact (not_le_of_gt hh) (by exact_mod_cast hle)
  obtain ⟨J,hJ,α,hα,β,hfactor,hnorm,hbalance⟩ := hfac n p hp hBp hfp
  refine ⟨hgood,J,hJ,α,hα,β,hfactor,hnorm,fun w => ?_⟩
  have hbal := hbalance w
  rw [M.degree_eq] at hbal
  have hαbounds := habsorb p hp.pos J hJ _ hbal.1 hbal.2
  have hXdiff : R ≤ X := (le_max_left _ _).trans hX
  have hβbounds := companion_archimedean_bounds w (α : M.Carrier) (β : M.Carrier)
    M.root n μ k hμ hfactor (p : ℝ) X D (f.natDegree : ℝ)⁻¹
    (by exact_mod_cast hp.pos) (hR.le.trans hXdiff) (lt_of_lt_of_le zero_lt_one hD)
    hαbounds.1 hαbounds.2 (hdiff X hXdiff n hn hn' w).1 (hdiff X hXdiff n hn hn' w).2
  exact ⟨hαbounds,hβbounds⟩

end QuarticPowerFree
end

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_EmbeddingCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

theorem IntegralEmbeddingChart.embedding {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α : 𝓞 K) :
    T.A.mulVec (fun j => (T.coord α j:ℂ)) = fun i => T.σ i (α:K) := by
  ext i
  have hh := congrArg (fun t : 𝓞 K => T.σ i (t:K)) (T.B.sum_repr α)
  simpa only [map_sum,map_zsmul,zsmul_eq_mul,map_mul,map_intCast,Matrix.mulVec,dotProduct,
    IntegralEmbeddingChart.A,IntegralEmbeddingChart.coord,T.compatible,mul_comm] using hh

theorem IntegralEmbeddingChart.inverse_coordinates {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α : 𝓞 K) :
    T.A⁻¹.mulVec (fun i => T.σ i (α:K)) = fun j => (T.coord α j:ℂ) := by
  rw [←T.embedding α,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul T.A (show IsUnit T.A.det from Ne.isUnit T.det_ne_zero),Matrix.one_mulVec]

theorem IntegralEmbeddingChart.coordinates_bound {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ (α : 𝓞 K) (R : ℝ), 0 ≤ R →
      (∀ i, ‖T.σ i (α:K)‖ ≤ R) → ∀ j, |(T.coord α j:ℝ)| ≤ E*R := by
  let E : ℝ := 1+∑ j, ∑ i, ‖T.A⁻¹ j i‖
  have hsum : 0 ≤ ∑ j, ∑ i, ‖T.A⁻¹ j i‖ := by positivity
  refine ⟨E,by dsimp [E]; linarith,fun α R hR hα j => ?_⟩
  have hej : ∑ i, ‖T.A⁻¹ j i‖ ≤ E := by
    have hh := Finset.single_le_sum (f := fun j => ∑ i, ‖T.A⁻¹ j i‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ j)
    dsimp [E]; linarith
  have hcoord := congrFun (T.inverse_coordinates α) j
  have hnorm : |(T.coord α j:ℝ)| = ‖(T.coord α j:ℂ)‖ := by simp
  rw [hnorm,←hcoord]
  calc
    ‖∑ i, T.A⁻¹ j i*T.σ i (α:K)‖ ≤ ∑ i, ‖T.A⁻¹ j i‖*‖T.σ i (α:K)‖ :=
      norm_sum_le_of_le _ (fun i _ => (norm_mul _ _).le)
    _ ≤ ∑ i, ‖T.A⁻¹ j i‖*R := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hα i) (norm_nonneg _))
    _ = (∑ i, ‖T.A⁻¹ j i‖)*R := (Finset.sum_mul ..).symm
    _ ≤ E*R := mul_le_mul_of_nonneg_right hej hR

end

section
open MvPolynomial
open scoped Classical BigOperators

theorem normBoxWeight_pos (d) (j) : 0 < normBoxWeight d j := by
  induction j using Fin.addCases <;> norm_num only [normBoxWeight,Fin.addCases_left,Fin.addCases_right]
theorem normBoxWeight_le (d) (j) : normBoxWeight d j ≤ 2/5 := by
  induction j using Fin.addCases <;> norm_num only [normBoxWeight,Fin.addCases_left,Fin.addCases_right]
theorem normBoxNatWeight_ne (d) (j) : normBoxNatWeight d j ≠ 0 := by
  induction j using Fin.addCases <;> norm_num only [normBoxNatWeight,Fin.addCases_left,Fin.addCases_right]
theorem normBoxWeight_scale (d) (j) : (normBoxNatWeight d j:ℝ) = 15*normBoxWeight d j := by
  induction j using Fin.addCases <;> norm_num only [normBoxWeight,normBoxNatWeight,Fin.addCases_left,Fin.addCases_right]

end

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

theorem arithmeticModel_distinct (f : Polynomial ℤ) (M : ArithmeticModel f)
    (e : Fin f.natDegree ≃ (M.Carrier →+* ℂ)) :
    Function.Injective (fun i => e i M.root) := by
  intro i j hij
  apply e.injective
  apply (RingHom.equivRatAlgHom M.Carrier ℂ).injective
  apply M.powerBasis.algHom_ext
  change e i M.powerBasis.gen = e j M.powerBasis.gen
  rw [M.powerBasis_gen,M.integralRoot_eq]
  simp only [map_mul,map_intCast,hij]

theorem normIntegralPoint_left {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α β : 𝓞 K) (i : Fin d) :
    MvPolynomial.aeval (fun j => (normIntegralPoint T α β j:ℂ))
      (coordinateLinearForm (Fin.castAdd d) (T.A i)) = T.σ i (α:K) := by
  simp only [coordinateLinearForm,map_sum,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X,
    normIntegralPoint,Fin.addCases_left]
  exact congrFun (T.embedding α) i

theorem normIntegralPoint_right {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α β : 𝓞 K) (μ : ℕ) (i : Fin d) :
    MvPolynomial.aeval (fun j => (normIntegralPoint T α β j:ℂ))
      (C (μ:ℂ)⁻¹*coordinateLinearForm (Fin.natAdd d) (T.A i)) = T.σ i (β:K)/(μ:ℂ) := by
  simp only [map_mul,MvPolynomial.aeval_C,coordinateLinearForm,map_sum,MvPolynomial.aeval_X,
    normIntegralPoint,Fin.addCases_right,Algebra.algebraMap_self,RingHom.id_apply]
  rw [show ∑ j, T.A i j*(T.coord β j:ℂ) = T.σ i (β:K) from congrFun (T.embedding β) i]
  rw [div_eq_mul_inv,mul_comm]

theorem normIntegralPoint_equation {K : Type} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (θ : K) (hθ : Function.Injective (fun i => T.σ i θ))
    (μ : ℕ) (hμ : 0 < μ) (hd : 0 < d) (α β : 𝓞 K) (n : ℤ)
    (he : (α:K)^(d-2)*(β:K) = (μ:K)*((n:K)-θ)) :
    let M := normBoxOfChart T θ hθ μ hμ hd
    let z := normIntegralPoint T α β
    MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = n ∧ PointOn M.ideal z := by
  let M := normBoxOfChart T θ hθ μ hμ hd
  let z := normIntegralPoint T α β
  have ha (i) : MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) = T.σ i (α:K) := normIntegralPoint_left T α β i
  have hb (i) : MvPolynomial.aeval (fun j => (z j:ℂ)) (M.b i) = T.σ i (β:K)/(μ:ℂ) := normIntegralPoint_right T α β μ i
  have hμc : (μ:ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hrel (i) : MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i)^(d-2)*
      MvPolynomial.aeval (fun j => (z j:ℂ)) (M.b i) = (n:ℂ)-T.σ i θ := by
    rw [ha,hb,←mul_div_assoc]
    have hh := congrArg (T.σ i) he
    simp only [map_mul,map_pow,map_natCast,map_sub,map_intCast] at hh
    rw [hh,mul_div_cancel_left₀ _ hμc]
  have hq : MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = (n:ℂ) := by
    change MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a ⟨0,hd⟩^(d-2)*M.b ⟨0,hd⟩+C (T.σ ⟨0,hd⟩ θ)) = _
    rw [map_add,map_mul,map_pow,MvPolynomial.aeval_C,hrel]
    simp only [Algebra.algebraMap_self,RingHom.id_apply]
    ring
  refine ⟨hq,?_⟩
  change M.ideal ≤ RingHom.ker (MvPolynomial.eval (fun j => (z j:ℂ)))
  apply Ideal.span_le.mpr
  rintro p ⟨i,rfl⟩
  change MvPolynomial.aeval (fun j => (z j:ℂ)) (M.equation i) = 0
  simp only [NormBoxSystem.equation,map_add,map_sub,map_mul,map_pow,MvPolynomial.aeval_C,hrel,hq]
  change (n:ℂ)-T.σ i θ-n+T.σ i θ = 0
  ring

end

open NumberField
open scoped Classical BigOperators

theorem selected_prime_count {ι : Type*} (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) (X : ℝ) (hXp : X < p) (S : Finset ι) (a : ι → ℤ)
    (hinj : Set.InjOn a (S:Set ι))
    (hrange : ∀ z ∈ S, X < (a z:ℝ) ∧ (a z:ℝ) ≤ 2*X)
    (hroot : ∀ z ∈ S, (p:ℤ) ∣ f.eval (a z)) : S.card ≤ f.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := primitive_map_zmod_ne_zero f hf p hp
  have hmap : Set.MapsTo (fun z => (a z : ZMod p)) (S:Set _) (F.roots.toFinset:Set _) := by
    intro z hz
    rw [Finset.mem_coe,Multiset.mem_toFinset,Polynomial.mem_roots hF]
    change F.eval (a z : ZMod p) = 0
    rw [show F = f.map (Int.castRingHom (ZMod p)) from rfl,Polynomial.eval_map]
    change f.eval₂ (Int.castRingHom (ZMod p)) ((Int.castRingHom (ZMod p)) (a z)) = 0
    rw [Polynomial.eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hroot z hz)
  have hmodinj : Set.InjOn (fun z => (a z : ZMod p)) (S:Set _) := by
    intro u hu v hv huv
    apply hinj hu hv
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (a u) (a v) p).mp huv
    obtain ⟨hu1,hu2⟩ := hrange u hu
    obtain ⟨hv1,hv2⟩ := hrange v hv
    have hh : |((a v-a u:ℤ):ℝ)| < (p:ℝ) := by
      push_cast
      rw [abs_lt]
      constructor <;> linarith
    have hh' : (a v-a u).natAbs < p := by
      exact_mod_cast (show ((a v-a u).natAbs:ℝ) < p by simpa only [Nat.cast_natAbs,Int.cast_abs] using hh)
    have he : a v-a u = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hh')
    exact (sub_eq_zero.mp he).symm
  calc
    S.card ≤ F.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmap hmodinj
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := Polynomial.card_roots' _
    _ ≤ f.natDegree := Polynomial.natDegree_map_le

theorem norm_left_fibre_count {ι K : Type*} [Field K] [NumberField K]
    (f : Polynomial ℤ) (hf : f.IsPrimitive) (S : Finset ι) (a : ι → ℤ)
    (hinj : Set.InjOn a (S:Set ι)) (X : ℝ)
    (hrange : ∀ i ∈ S, X < (a i:ℝ) ∧ (a i:ℝ) ≤ 2*X)
    (P : ι → ℕ) (J : ι → Ideal (𝓞 K)) (A : ι → 𝓞 K)
    (Q : Finset (Ideal (𝓞 K))) (hQ : ∀ I ∈ Q, I ≠ ⊥)
    (hq : ∀ i ∈ S, J i ∈ Q)
    (hp : ∀ i ∈ S, (P i).Prime ∧ X < P i ∧ (P i:ℤ) ∣ f.eval (a i))
    (hnorm : ∀ i ∈ S, |(Algebra.norm ℚ (A i:K):ℝ)| = ((P i*Ideal.absNorm (J i):ℕ):ℝ))
    (α : 𝓞 K) : (S.filter (fun i => A i = α)).card ≤ Q.card*f.natDegree := by
  classical
  let R := S.filter (fun i => A i=α)
  have hc (I) (hI : I ∈ Q) : (R.filter (fun i => J i=I)).card ≤ f.natDegree := by
    by_cases he : (R.filter (fun i => J i=I)).Nonempty
    · obtain ⟨i₀,hi₀⟩ := he
      obtain ⟨hiR,hiJ⟩ := Finset.mem_filter.mp hi₀
      obtain ⟨hiS,hiA⟩ := Finset.mem_filter.mp hiR
      have hN : 0 < I.absNorm := Nat.pos_of_ne_zero (fun hz => hQ I hI (Ideal.absNorm_eq_zero_iff.mp hz))
      have hP (i) (hi : i ∈ R.filter (fun i => J i=I)) : P i = P i₀ := by
        obtain ⟨hiR',hiJ'⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiS',hiA'⟩ := Finset.mem_filter.mp hiR'
        have h₁ := hnorm i hiS'
        have h₂ := hnorm i₀ hiS
        rw [hiA',hiJ'] at h₁
        rw [hiA,hiJ] at h₂
        have hmul : P i*I.absNorm = P i₀*I.absNorm := by exact_mod_cast h₁.symm.trans h₂
        exact Nat.eq_of_mul_eq_mul_right hN hmul
      apply selected_prime_count f hf (P i₀) (hp i₀ hiS).1 X (hp i₀ hiS).2.1 (R.filter (fun i => J i=I)) a
      · exact hinj.mono (fun i hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1)
      · intro i hi
        exact hrange i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
      · intro i hi
        rw [←hP i hi]
        exact (hp i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1).2.2
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
      exact Nat.zero_le _
  have hcover : R ⊆ Q.biUnion (fun I => R.filter (fun i => J i=I)) := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨J i,hq i (Finset.mem_filter.mp hi).1,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩
  calc
    R.card ≤ (Q.biUnion (fun I => R.filter (fun i => J i=I))).card := Finset.card_le_card hcover
    _ ≤ ∑ I ∈ Q, (R.filter (fun i => J i=I)).card := Finset.card_biUnion_le
    _ ≤ ∑ _I ∈ Q, f.natDegree := Finset.sum_le_sum hc
    _ = Q.card*f.natDegree := by simp

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_MediumDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

theorem norm_indexed_count (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hd : 5 ≤ f.natDegree) (hd' : f.natDegree ≤ 8)
    {K : Type} [Field K] [NumberField K]
    (T : IntegralEmbeddingChart K f.natDegree) (θ : K)
    (hθ : Function.Injective (fun i => T.σ i θ)) (μ : ℕ) (hμ : 0 < μ)
    (Q : Finset (Ideal (𝓞 K))) (hQ : ∀ I ∈ Q, I ≠ ⊥)
    (Cbox : ℝ) (hCbox : 1 ≤ Cbox) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ (ι : Type) [Fintype ι]
      (a : ι → ℤ) (P : ι → ℕ) (J : ι → Ideal (𝓞 K)) (A B : ι → 𝓞 K),
      Function.Injective a →
      (∀ i, X < (a i:ℝ) ∧ (a i:ℝ) ≤ 2*X) →
      (∀ i, J i ∈ Q) →
      (∀ i, (P i).Prime ∧ X < P i ∧ (P i:ℤ) ∣ f.eval (a i)) →
      (∀ i, A i ≠ 0) →
      (∀ i, (A i:K)^(f.natDegree-2)*(B i:K) = (μ:K)*((a i:K)-θ)) →
      (∀ i, |(Algebra.norm ℚ (A i:K):ℝ)| = ((P i*Ideal.absNorm (J i):ℕ):ℝ)) →
      (∀ i j, |(T.coord (A i) j:ℝ)| ≤ Cbox*X^(1/3:ℝ) ∧
        |(T.coord (B i) j:ℝ)| ≤ Cbox*X^(2/5:ℝ)) →
      (Fintype.card ι:ℝ) ≤ C*X^(997/1000:ℝ) := by
  classical
  let M := normBoxOfChart T θ hθ μ hμ (by omega : 0 < f.natDegree)
  let F := Q.card*f.natDegree+1
  obtain ⟨C,X₀,hC,hcount⟩ := norm_box_count hd hd' (by omega : 0 < f.natDegree+1)
    (normBoxWeight f.natDegree) (normBoxWeight_pos _) (normBoxWeight_le _)
    (normBoxNatWeight f.natDegree) (normBoxNatWeight_ne _) (normBoxWeight_scale _)
    M Cbox hCbox F
  refine ⟨C,X₀,hC,fun X hX ι _ a P J A B hainj hrange hJ hP hA he hnorm hbox => ?_⟩
  let z := fun i => normIntegralPoint T (A i) (B i)
  let S := Finset.univ.image z
  have heval (i) : MvPolynomial.aeval (fun j => (z i j:ℂ)) M.q = (a i:ℂ) ∧ PointOn M.ideal (z i) :=
    normIntegralPoint_equation T θ hθ μ hμ _ (A i) (B i) (a i) (he i)
  have hzinj : Function.Injective z := by
    intro i j hij
    apply hainj
    apply Int.cast_injective (α := ℂ)
    rw [←(heval i).1,←(heval j).1,hij]
  have hcard : S.card = Fintype.card ι := by simp only [S,Finset.card_image_of_injective _ hzinj,Finset.card_univ]
  have hb := hcount X hX S
  rw [←hcard]
  apply hb
  · intro v hv j
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    induction j using Fin.addCases with
    | left j => simpa only [z,normIntegralPoint,Fin.addCases_left,normBoxWeight] using (hbox i j).1
    | right j => simpa only [z,normIntegralPoint,Fin.addCases_right,normBoxWeight] using (hbox i j).2
  · intro t
    apply (Finset.card_le_one.mpr ?_).trans (by dsimp [F]; omega)
    intro v hv w hw
    obtain ⟨hvS,hvt⟩ := Finset.mem_filter.mp hv
    obtain ⟨hwS,hwt⟩ := Finset.mem_filter.mp hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hvS
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hwS
    have hij : a i = a j := Int.cast_injective (α := ℂ) ((heval i).1.symm.trans
      ((hvt.trans hwt.symm).trans (heval j).1))
    rw [hainj hij]
  · intro c
    let R := Finset.univ.filter (fun i => ∀ j, z i (Fin.castAdd f.natDegree j) = c j)
    have hsubset : S.filter (fun v => ∀ j, v (M.x j) = c j) ⊆ R.image z := by
      intro v hv
      obtain ⟨hvS,hvc⟩ := Finset.mem_filter.mp hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hvS
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hvc⟩,rfl⟩
    apply ((Finset.card_le_card hsubset).trans (Finset.card_image_le)).trans
    by_cases hR : R.Nonempty
    · obtain ⟨i₀,hi₀⟩ := hR
      have hRsub : R ⊆ Finset.univ.filter (fun i => A i=A i₀) := by
        intro i hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,T.B.repr.injective ?_⟩
        ext j
        have h₁ := (Finset.mem_filter.mp hi).2 j
        have h₂ := (Finset.mem_filter.mp hi₀).2 j
        simpa only [z,normIntegralPoint,Fin.addCases_left,IntegralEmbeddingChart.coord] using h₁.trans h₂.symm
      have hc := norm_left_fibre_count f hf Finset.univ a hainj.injOn X
        (fun i _ => hrange i) P J A Q hQ (fun i _ => hJ i) (fun i _ => hP i)
        (fun i _ => hnorm i) (A i₀)
      exact ((Finset.card_le_card hRsub).trans hc).trans (by dsimp [F]; omega)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hR,Finset.card_empty]
      exact Nat.zero_le _
  · intro v hv j
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    change MvPolynomial.aeval (fun l => (z i l:ℂ)) (coordinateLinearForm (Fin.castAdd f.natDegree) (T.A j)) ≠ 0
    rw [normIntegralPoint_left]
    apply (map_ne_zero (T.σ j)).mpr
    exact_mod_cast hA i
  · intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact (heval i).2

end

section

theorem norm_onebox_exponents {d p : ℕ} (hd : 5 ≤ d) {F X : ℝ}
    (hF : 1 ≤ F) (hX : 1 ≤ X) (hp : X < p)
    (hv : (p:ℝ)^(d-2) ≤ F*X^(d:ℝ)) :
    (p:ℝ)^((d:ℝ)⁻¹) ≤ F*X^(1/3:ℝ) ∧
      X/(p:ℝ)^((d:ℝ)⁻¹*(d-2:ℕ)) ≤ X^(2/5:ℝ) := by
  let k := d-2
  have hdR : (5:ℝ) ≤ d := by exact_mod_cast hd
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by dsimp [k]; omega)
  have hdk : (d:ℝ) = (k:ℝ)+2 := by exact_mod_cast (show d=k+2 by dsimp [k]; omega)
  have hd0 : (0:ℝ) < d := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hXp : 0 < X := by linarith
  have hpp : (0:ℝ) < p := by linarith
  have hFp : 0 < F := by linarith
  constructor
  · apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hpp.le _) (by positivity) (mul_pos hd0 hk0)).mp
    rw [←Real.rpow_mul hpp.le,show (d:ℝ)⁻¹*((d:ℝ)*k) = k by field_simp,
      Real.rpow_natCast,Real.mul_rpow hFp.le (Real.rpow_nonneg hXp.le _),←Real.rpow_mul hXp.le]
    have hFk : F ≤ F^((d:ℝ)*k) := by
      have hh : (1:ℝ) ≤ (d:ℝ)*k := by nlinarith
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hF hh
    have he : (d:ℝ) ≤ 1/3*((d:ℝ)*k) := by nlinarith
    exact hv.trans (mul_le_mul hFk (Real.rpow_le_rpow_of_exponent_le hX he)
      (Real.rpow_nonneg hXp.le _) (by positivity))
  · have hek : 0 ≤ (d:ℝ)⁻¹*(k:ℝ) := by positivity
    have hpw := Real.rpow_le_rpow hXp.le hp.le hek
    have he : 1-(d:ℝ)⁻¹*(k:ℝ) ≤ 2/5 := by
      rw [inv_mul_eq_div]
      have hh : (3/5:ℝ) ≤ (k:ℝ)/(d:ℝ) := (le_div_iff₀ hd0).mpr (by linarith)
      linarith
    calc
      X/(p:ℝ)^((d:ℝ)⁻¹*(d-2:ℕ)) ≤ X/X^((d:ℝ)⁻¹*k) :=
        div_le_div_of_nonneg_left hXp.le (Real.rpow_pos_of_pos hXp _) hpw
      _ = X^(1-(d:ℝ)⁻¹*k) := by rw [Real.rpow_sub hXp,Real.rpow_one]
      _ ≤ X^(2/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hX he

open NumberField Module
open scoped Classical BigOperators

theorem balanced_coordinates_onebox {K : Type} [Field K] [NumberField K] {d : ℕ}
    (hd : 5 ≤ d) (T : IntegralEmbeddingChart K d) (μ : ℕ) (hμ : 0 < μ)
    (C F : ℝ) (hC : 1 ≤ C) (hF : 1 ≤ F) :
    ∃ Cbox : ℝ, 1 ≤ Cbox ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (p : ℕ), X < p →
      (p:ℝ)^(d-2) ≤ F*X^(d:ℝ) → ∀ α β : 𝓞 K,
      (∀ w : InfinitePlace K, w (α:K) ≤ C*(p:ℝ)^((d:ℝ)⁻¹) ∧
        w ((β:K)/(μ:K)) ≤ (3*C^(d-2))*(X/(p:ℝ)^((d:ℝ)⁻¹*(d-2:ℕ)))) →
      ∀ j, |(T.coord α j:ℝ)| ≤ Cbox*X^(1/3:ℝ) ∧
        |(T.coord β j:ℝ)| ≤ Cbox*X^(2/5:ℝ) := by
  obtain ⟨E,hE,hbound⟩ := T.coordinates_bound
  let Ca := E*(C*F)
  let Cb := E*((μ:ℝ)*(3*C^(d-2)))
  let Cbox := 1+Ca+Cb
  have hCp : 0 ≤ C := by linarith
  have hFp : 0 ≤ F := by linarith
  have hEp : 0 ≤ E := by linarith
  have hCa : 0 ≤ Ca := mul_nonneg hEp (mul_nonneg hCp hFp)
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  have haC : Ca ≤ Cbox := by dsimp [Cbox]; linarith
  have hbC : Cb ≤ Cbox := by dsimp [Cbox]; linarith
  refine ⟨Cbox,by dsimp [Cbox]; linarith,fun X hX p hp hv α β harch j => ?_⟩
  have hXp : 0 < X := by linarith
  have hab := norm_onebox_exponents hd hF hX hp hv
  have hα (i) : ‖T.σ i (α:K)‖ ≤ (C*F)*X^(1/3:ℝ) := by
    have hh := (harch (InfinitePlace.mk (T.σ i))).1
    rw [InfinitePlace.apply] at hh
    exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hab.1 hCp)
  have hβ (i) : ‖T.σ i (β:K)‖ ≤ ((μ:ℝ)*(3*C^(d-2)))*X^(2/5:ℝ) := by
    have hh := (harch (InfinitePlace.mk (T.σ i))).2
    simp only [InfinitePlace.apply,map_div₀,map_natCast,Complex.norm_natCast] at hh
    have hμR : (0:ℝ) < μ := by exact_mod_cast hμ
    have ht : ‖T.σ i (β:K)‖/(μ:ℝ) ≤ (3*C^(d-2))*X^(2/5:ℝ) :=
      hh.trans (mul_le_mul_of_nonneg_left hab.2 (by positivity))
    have hh' := (div_le_iff₀ hμR).mp ht
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh'
  constructor
  · have hh := hbound α ((C*F)*X^(1/3:ℝ)) (by positivity) hα j
    exact hh.trans (by simpa only [Ca,mul_assoc] using mul_le_mul_of_nonneg_right haC (Real.rpow_nonneg hXp.le (1/3)))
  · have hh := hbound β (((μ:ℝ)*(3*C^(d-2)))*X^(2/5:ℝ)) (by positivity) hβ j
    exact hh.trans (by simpa only [Cb,mul_assoc] using mul_le_mul_of_nonneg_right hbC (Real.rpow_nonneg hXp.le (2/5)))

theorem large_prime_power_upper (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 2 ≤ f.natDegree)
    (D X : ℝ) (n : ℤ) (p k : ℕ)
    (hb : |((f.eval n:ℤ):ℝ)| ≤ D*X^(f.natDegree:ℝ))
    (hdiv : (p:ℤ)^k ∣ f.eval n) : (p:ℝ)^k ≤ D*X^(f.natDegree:ℝ) := by
  have hh := Int.natAbs_le_of_dvd_ne_zero hdiv (rational_irreducible_eval_ne_zero f hf hd n)
  have hh' : (p:ℝ)^k ≤ |((f.eval n:ℤ):ℝ)| := by
    have hn : (p:ℝ)^k ≤ ((f.eval n).natAbs:ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hn
  exact hh'.trans hb

end

section
open Filter NumberField
open scoped Topology Classical

theorem medium_degree_dyadic_tail_oai (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hc : 0 < f.leadingCoeff)
    (hd : 5 ≤ f.natDegree) (hd' : f.natDegree ≤ 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (dyadicTailCount f (f.natDegree-2) N:ℝ) ≤ C*(N:ℝ)^(1-3/1000:ℝ) := by
  classical
  obtain ⟨M,μ,Q,C,Xcut,hμ,hC,_hXcut,hQ,hfactor⟩ :=
    balanced_arithmetic f hirr (by omega) hc (f.natDegree-2) (by omega)
  obtain ⟨F,hF,heval⟩ := polynomial_dyadic_eval_bound f
  let T := integralEmbeddingChart M.Carrier f.natDegree M.degree_eq
  have hθ := arithmeticModel_distinct f M T.σ
  obtain ⟨Cbox,hCbox,hbox⟩ := balanced_coordinates_onebox hd T μ hμ C F hC (by linarith)
  obtain ⟨D,Xcount,hD,hcount⟩ := norm_indexed_count f hf hd hd' T M.root hθ μ hμ Q hQ Cbox hCbox
  refine ⟨D,hD,?_⟩
  have hlim : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_gt_atTop (max 1 (max Xcut Xcount)))] with N hN
  have hN1 : 1 ≤ (N:ℝ) := (le_max_left _ _).trans hN.le
  have hNcut : Xcut ≤ (N:ℝ) := (le_max_left _ _).trans (le_max_right _ _) |>.trans hN.le
  have hNcount : Xcount < (N:ℝ) := (le_max_right _ _).trans (le_max_right _ _) |>.trans_lt hN
  let S := (Finset.Ioc N (2*N)).filter fun n : ℕ =>
    ∃ p : ℕ, p.Prime ∧ N < p ∧ (p:ℤ)^(f.natDegree-2) ∣ f.eval (n:ℤ)
  have hS (n : S) : ∃ p : ℕ, p.Prime ∧ N < p ∧
      (p:ℤ)^(f.natDegree-2) ∣ f.eval (n.val:ℤ) := (Finset.mem_filter.mp n.property).2
  choose P hP hNP hdiv using hS
  have hrange (n : S) : (N:ℝ) < (n.val:ℝ) ∧ (n.val:ℝ) ≤ 2*(N:ℝ) := by
    have hn := Finset.mem_Ioc.mp (Finset.mem_filter.mp n.property).1
    constructor
    · exact_mod_cast hn.1
    · exact_mod_cast hn.2
  have hNP' (n : S) : (N:ℝ) < P n := by exact_mod_cast hNP n
  have hfac (n : S) := (hfactor N hNcut (n.val:ℤ) (P n)
    (by exact_mod_cast (hrange n).1) (by exact_mod_cast (hrange n).2)
    (hP n) (hNP' n) (hdiv n)).2
  choose J hJ A hA B hAB hnorm harch using hfac
  have hcoords (n : S) (j) : |(T.coord (A n) j:ℝ)| ≤ Cbox*(N:ℝ)^(1/3:ℝ) ∧
      |(T.coord (B n) j:ℝ)| ≤ Cbox*(N:ℝ)^(2/5:ℝ) := by
    apply hbox N hN1 (P n) (hNP' n) _ (A n) (B n) (fun w => ⟨(harch n w).1.2,(harch n w).2.2⟩) j
    apply large_prime_power_upper f hirr (by omega) F N (n.val:ℤ) (P n) (f.natDegree-2) _ (hdiv n)
    exact heval N hN1 (n.val:ℤ) (by positivity) (by exact_mod_cast (hrange n).2)
  have hprime (n : S) : (P n).Prime ∧ (N:ℝ) < P n ∧ (P n:ℤ) ∣ f.eval (n.val:ℤ) := by
    refine ⟨hP n,hNP' n,?_⟩
    exact dvd_trans (dvd_pow_self _ (by omega : f.natDegree-2 ≠ 0)) (hdiv n)
  have hninj : Function.Injective (fun n : S => (n.val:ℤ)) := by
    intro n m h
    apply Subtype.ext
    exact Int.natCast_inj.mp h
  have hh := hcount N hNcount S (fun n => (n.val:ℤ)) P J A B hninj
    (fun n => by simpa only [Int.cast_natCast] using hrange n) hJ hprime hA hAB hnorm hcoords
  norm_num only [show (1-3/1000:ℝ) = 997/1000 by norm_num]
  simpa only [Fintype.card_coe,dyadicTailCount,S] using hh

end

open MvPolynomial
open scoped Classical BigOperators

attribute [instance] QuarticBoxSystem.field QuarticBoxSystem.charZero

end QuarticPowerFree

end OAI
end

theorem solution : type_of% @OAI.QuarticPowerFree.medium_degree_dyadic_tail_oai := @OAI.QuarticPowerFree.medium_degree_dyadic_tail_oai
