-- Prove2me | solution 1 for OAI.TwoPointCorrelations.MRTShortExponentialInput.dilated_forward_windows
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:37:12.221497+00:00
-- url     : https://prove2.me/submissions/42ff81f3-b059-497e-acfe-03d127554834

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial




namespace Finset


/-- Backport (Mathlib d13f23b), additive form of `prod_le_prod_of_injOn`. -/
theorem sum_le_sum_of_injOn {ι α N : Type*} [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] [DecidableEq α]
    {f : ι → N} {g : α → N} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : image e s ⊆ t) (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ image e s → 0 ≤ g a) :
    ∑ i ∈ s, f i ≤ ∑ a ∈ t, g a := by
  refine le_trans ?_ <| sum_le_sum_of_subset_of_nonneg ht hg
  rw [sum_image he]
  exact sum_le_sum h

end Finset

section LogSubst
open _root_.Real _root_.Set _root_.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end LogSubst

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RescaledPrefixSums
namespace OAI

/-! Finite weighted assembly at the actual divisor scale `Y = X/u`.
The factor `1/u` is retained exactly, including floor cutoffs. -/

namespace TwoPointCorrelations

open _root_.Filter
open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma tendsto_nat_div_atTop (u : ℕ) (hu : 0 < u) :
    Tendsto (fun X : ℕ => X / u) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (N * u)] with X hX
  exact (Nat.le_div_iff_mul_le hu).mpr hX



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SmoothDivisorDecomposition
namespace OAI

/-! Exact decomposition along primes of a fixed dilation. The coefficient
of a smooth divisor is bounded by one; there is no signed local expansion
or factor exponential in the number of dilation primes. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical



lemma primeSmoothPart_mul_primeRoughPart (P : Finset ℕ) (n : ℕ) (hn : 0 < n) :
    primeSmoothPart P n * primeRoughPart P n = n := by
  have he := List.prod_map_filter_mul_prod_map_filter_not
    (fun p : ℕ => p ∈ P) (fun p : ℕ => p) n.primeFactorsList
  simpa [primeSmoothPart, primeRoughPart, Nat.prod_primeFactorsList hn.ne'] using he

lemma primeSmoothPart_pos (P : Finset ℕ) (n : ℕ) (hn : 0 < n) :
    0 < primeSmoothPart P n := by
  have he := primeSmoothPart_mul_primeRoughPart P n hn
  exact Nat.pos_of_ne_zero (fun hz => by rw [hz, zero_mul] at he; omega)

lemma primeRoughPart_pos (P : Finset ℕ) (n : ℕ) (hn : 0 < n) :
    0 < primeRoughPart P n := by
  have he := primeSmoothPart_mul_primeRoughPart P n hn
  exact Nat.pos_of_ne_zero (fun hz => by rw [hz, mul_zero] at he; omega)

lemma primeSmoothPart_support (P : Finset ℕ) (n : ℕ) :
    (primeSmoothPart P n).primeFactors ⊆ P := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨r, hr, hpr⟩ := hprime.prime.dvd_prod_iff.mp hd
  obtain ⟨hrn, hrP⟩ := List.mem_filter.mp hr
  have hrprime := Nat.prime_of_mem_primeFactorsList hrn
  have he : p = r := ((Nat.dvd_prime hrprime).mp hpr).resolve_left hprime.ne_one
  exact he.symm ▸ (of_decide_eq_true hrP)

lemma primeRoughPart_coprime (q n : ℕ) (hq : 0 < q) :
    q.Coprime (primeRoughPart q.primeFactors n) := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro p hp
  obtain ⟨hpn, hpq⟩ := List.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactorsList hpn
  apply Nat.Coprime.symm
  apply hprime.coprime_iff_not_dvd.mpr
  intro hd
  exact (of_decide_eq_true hpq) (Nat.mem_primeFactors.mpr ⟨hprime, hd, hq.ne'⟩)

lemma coprime_of_primeFactors_subset {a q n : ℕ}
    (ha : 0 < a) (hs : a.primeFactors ⊆ q.primeFactors)
    (hqn : q.Coprime n) : a.Coprime n := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpn
  have hpq := Nat.dvd_of_mem_primeFactors (hs (Nat.mem_primeFactors.mpr ⟨hp, hpa, ha.ne'⟩))
  have hcp : p.Coprime n := hqn.of_dvd_left hpq
  exact False.elim ((hp.coprime_iff_not_dvd.mp hcp) hpn)

lemma primeSmoothPart_unique (q n a : ℕ) (hq : 0 < q) (hn : 0 < n)
    (ha : a ∣ n) (hs : a.primeFactors ⊆ q.primeFactors) (hc : q.Coprime (n / a)) :
    a = primeSmoothPart q.primeFactors n := by
  have hap : 0 < a := Nat.pos_of_dvd_of_pos ha hn
  have hsp := primeSmoothPart_pos q.primeFactors n hn
  have he := primeSmoothPart_mul_primeRoughPart q.primeFactors n hn
  have har := coprime_of_primeFactors_subset hap hs (primeRoughPart_coprime q n hq)
  have has : a ∣ primeSmoothPart q.primeFactors n := by
    exact har.dvd_of_dvd_mul_right (he.symm ▸ ha)
  have hsc := coprime_of_primeFactors_subset hsp
    (primeSmoothPart_support q.primeFactors n) hc
  have hsa : primeSmoothPart q.primeFactors n ∣ a := by
    apply hsc.dvd_of_dvd_mul_right
    rw [Nat.mul_div_cancel' ha]
    exact ⟨primeRoughPart q.primeFactors n, he.symm⟩
  exact Nat.dvd_antisymm has hsa


lemma coprimeRestriction_oneBounded (q : ℕ) {f : ℕ → ℂ} (hf : OneBounded f) :
    OneBounded (coprimeRestriction q f) := by
  intro n hn
  unfold coprimeRestriction
  split_ifs
  · exact hf n hn
  · simp

lemma coprimeRestriction_multiplicative (q : ℕ) {f : ℕ → ℂ}
    (hf : Multiplicative f) : Multiplicative (coprimeRestriction q f) := by
  intro a b ha hb hab
  unfold coprimeRestriction
  by_cases hqa : q.Coprime a
  · by_cases hqb : q.Coprime b
    · rw [if_pos (Nat.coprime_mul_iff_right.mpr ⟨hqa, hqb⟩),
        if_pos hqa, if_pos hqb]
      exact hf a b ha hb hab
    · have hn : ¬q.Coprime (a * b) := fun hc => hqb (Nat.coprime_mul_iff_right.mp hc).2
      rw [if_neg hn, if_pos hqa, if_neg hqb, mul_zero]
  · have hn : ¬q.Coprime (a * b) := fun hc => hqa (Nat.coprime_mul_iff_right.mp hc).1
    rw [if_neg hn, if_neg hqa, zero_mul]

lemma coprimeRestriction_prime (q : ℕ) (hq : 0 < q) (f : ℕ → ℂ)
    {p : ℕ} (hp : p.Prime) (hpq : p ∉ q.primeFactors) :
    coprimeRestriction q f p = f p := by
  apply if_pos
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact hpq (Nat.mem_primeFactors.mpr ⟨hp, hd, hq.ne'⟩)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SmoothReciprocalMass
namespace OAI

/-! Finite-prime smooth reciprocal sums. The exact Euler factors make
averaging the dilation cost against the padding law possible. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical



lemma smoothReciprocalProduct_hasSum (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s) :
    HasSum (fun a : Nat.factoredNumbers P => (a.val : ℝ) ^ (-s))
      (smoothReciprocalProduct P s) := by
  have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := natNegativePower s) (fun {p} hp => by
      change ‖(p : ℝ) ^ (-s)‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)) P
  have he : P.filter Nat.Prime = P := filter_eq_self.mpr hP
  simpa [natNegativePower, smoothReciprocalProduct, he] using h.2

lemma smoothReciprocalProduct_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s) :
    0 ≤ smoothReciprocalProduct P s := by
  apply (smoothReciprocalProduct_hasSum P hP s hs).nonneg
  intro a
  exact Real.rpow_nonneg (Nat.cast_nonneg a.val) _

lemma smooth_reciprocal_sum_le (P A : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s)
    (hA : ∀ a ∈ A, a ∈ Nat.factoredNumbers P) :
    (∑ a ∈ A, (a : ℝ) ^ (-s)) ≤ smoothReciprocalProduct P s := by
  let e : A → Nat.factoredNumbers P := fun a => ⟨a.val, hA a.val a.property⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : Nat.factoredNumbers P => x.val) hab
  have hb := sum_le_hasSum (univ.image e)
    (fun a _ => Real.rpow_nonneg (Nat.cast_nonneg a.val) (-s))
    (smoothReciprocalProduct_hasSum P hP s hs)
  rw [sum_image (fun a _ b _ hab => he hab)] at hb
  rw [← sum_coe_sort A (fun a : ℕ => (a : ℝ) ^ (-s))]
  simpa only [e] using hb


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SmoothProductBounds
namespace OAI

/-! Elementary bounds for the Euler cost of adjoining retained tuple primes. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma one_le_smoothReciprocalProduct (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 0 < s) :
    1 ≤ smoothReciprocalProduct P s := by
  apply Finset.one_le_prod
  intro p hp
  have hr : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hP p hp).one_lt) (by linarith)
  exact (one_le_inv₀ (sub_pos.mpr hr)).mpr (by
    have hh := Real.rpow_nonneg (Nat.cast_nonneg p) (-s)
    linarith)






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.PretentiousDistance
namespace OAI

/-!
# The pretentious distance used in ordinary two-point correlations

These definitions use the prime cutoff and the twist-height cutoff at the same
integer scale.  The finite-prime perturbation estimate below is Lemma
`lem:finite-prime-stability` of *Ordinary two-point correlations of
multiplicative functions* (24 September 2026).  It is elementary and does not
assume any analytic input.
-/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter
open _root_.Finset hiding sum_le_sum_of_injOn





lemma characterTwist_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) : ‖characterTwist χ t n‖ ≤ 1 := by
  simpa only [characterTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
    χ.norm_le_one (n : ZMod q)





/-- Altering a fixed finite set of prime values changes the square of the
pretentious distance by at most twice their reciprocal sum. -/
lemma squaredDistance_finite_prime_change (f b g : ℕ → ℂ) (N : ℕ)
    (P : Finset ℕ) (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (hb : ∀ n, 0 < n → ‖b n‖ ≤ 1)
    (hg : ∀ n, 0 < n → ‖g n‖ ≤ 1)
    (heq : ∀ p, Nat.Prime p → p ∉ P → b p = f p) :
    |squaredDistance b g N - squaredDistance f g N| ≤
      2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
  let S := primesUpTo N
  have hterm (p : ℕ) (hp : 0 < p) :
      |(1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ)| ≤ 2 / (p : ℝ) := by
    have hdiff : ‖f p - b p‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by linarith [hf p hp, hb p hp])
    have hprod : ‖(f p - b p) * conj (g p)‖ ≤ 2 := by
      calc
        ‖(f p - b p) * conj (g p)‖ = ‖f p - b p‖ * ‖g p‖ := by simp
        _ ≤ 2 * 1 := mul_le_mul hdiff (hg p hp) (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have hre : |(f p * conj (g p)).re - (b p * conj (g p)).re| ≤ 2 := by
      calc
        |(f p * conj (g p)).re - (b p * conj (g p)).re| =
          |((f p - b p) * conj (g p)).re| := by rw [sub_mul, Complex.sub_re]
        _ ≤ ‖(f p - b p) * conj (g p)‖ := Complex.abs_re_le_norm _
        _ ≤ 2 := hprod
    rw [← sub_div, show (1 - (b p * conj (g p)).re) -
      (1 - (f p * conj (g p)).re) =
        (f p * conj (g p)).re - (b p * conj (g p)).re by ring,
      abs_div, show |(p : ℝ)| = (p : ℝ) from abs_of_nonneg (Nat.cast_nonneg p)]
    exact div_le_div_of_nonneg_right hre (Nat.cast_nonneg p)
  have htermP (p : ℕ) (hp : p ∈ S) :
      |(1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ)| ≤
      if p ∈ P then 2 / (p : ℝ) else 0 := by
    split_ifs with hP
    · exact hterm p ((Finset.mem_filter.mp hp).2.pos)
    · have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      rw [heq p hprime hP, sub_self, abs_zero]
  calc
    |squaredDistance b g N - squaredDistance f g N| =
      |∑ p ∈ S, ((1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ))| := by
          rw [Finset.sum_sub_distrib]
          rfl
    _ ≤ ∑ p ∈ S, |(1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, if p ∈ P then 2 / (p : ℝ) else 0 := Finset.sum_le_sum htermP
    _ = ∑ p ∈ S.filter (fun p => p ∈ P), 2 / (p : ℝ) := by rw [Finset.sum_filter]
    _ ≤ ∑ p ∈ P, 2 / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
      · intro p hp hnot
        positivity
    _ = 2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring


/-- One lower bound works for every member of a fixed finite character family,
and for every bounded sequence whose prime values are changed only in `P`.
This is the uniformity needed when taking the short-interval theorem at a fixed
auxiliary graph scale. -/
lemma UniformlyNonpretentious.finite_family {ι : Type*} [Finite ι]
    {f : ℕ → ℂ} (hfnp : UniformlyNonpretentious f) (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : Finset ℕ) (q : ι → ℕ) (hq : ∀ i, 0 < q i)
    (χ : ∀ i, DirichletCharacter ℂ (q i)) (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ i (b : ℕ → ℂ),
      (∀ n, 0 < n → ‖b n‖ ≤ 1) →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
      ∀ t : ℝ, |t| ≤ (N : ℝ) → K ≤ squaredDistance b (characterTwist (χ i) t) N := by
  have hfamily : ∀ᶠ N : ℕ in atTop, ∀ i,
      ∀ t : ℝ, |t| ≤ (N : ℝ) →
        K + 2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤
          squaredDistance f (characterTwist (χ i) t) N := by
    rw [Filter.eventually_all]
    intro i
    exact hfnp (q i) (hq i) (χ i) _
  filter_upwards [hfamily] with N hN
  intro i b hb heq t ht
  have hdist := squaredDistance_finite_prime_change f b (characterTwist (χ i) t) N
    P hf hb (fun n _ => characterTwist_norm_le_one (χ i) t n) heq
  have hlow := hN i t ht
  have := (abs_le.mp hdist).1
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.PublishedInputs
namespace OAI

/-!
# Short-interval estimates for multiplicative functions

The estimates specialize K. Matomäki, M. Radziwiłł and T. Tao,
*An averaged form of Chowla's conjecture*, Algebra & Number Theory 9 (2015),
2167–2196, corrected arXiv:1503.05121v3 (1 March 2022), Theorems 1.3 and 1.7;
DOI 10.2140/ant.2015.9.2167.

The frequency is fixed during the integral. A uniform lower bound on the
squared pretentious distances replaces the infimum in Theorem 1.7.
-/

namespace TwoPointCorrelations

open scoped _root_.BigOperators
open _root_.MeasureTheory









/-- At a fixed modulus cutoff, uniform nonpretentiousness gives one bound
simultaneously for every character and every permitted finite-prime change. -/
theorem UniformlyNonpretentious.bounded_moduli {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (P : Finset ℕ) (Q : ℕ) (K : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ q : ℕ, 0 < q → q ≤ Q →
      ∀ (χ : DirichletCharacter ℂ q) (b : ℕ → ℂ), OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
        ∀ t : ℝ, |t| ≤ (N : ℝ) → K ≤ squaredDistance b (characterTwist χ t) N := by
  classical
  let ι := (Σ q : Fin Q, DirichletCharacter ℂ (q.val + 1))
  have hfamily := hfnp.finite_family (ι := ι) hf P
    (fun i => i.1.val + 1) (fun _ => Nat.succ_pos _) (fun i => i.2) K
  filter_upwards [hfamily] with N hN
  intro q hq hqQ χ b hb heq t ht
  cases q with
  | zero => omega
  | succ q =>
      exact hN ⟨⟨q, Nat.lt_of_succ_le hqQ⟩, χ⟩ b hb heq t ht

/-- Fixing the short interval length leaves only finitely many moduli in the
published theorem. Thus the entire MRT distance hypothesis holds uniformly. -/
theorem UniformlyNonpretentious.eventually_mrt_lower_bound {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (P : Finset ℕ) (H : ℕ) (M : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ b : ℕ → ℂ, OneBounded b →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) → MRTDistanceLowerBound b N H M := by
  have hfinite := hfnp.bounded_moduli hf P (Nat.ceil ((Real.log (H : ℝ)) ^ (5 : ℕ))) M
  filter_upwards [hfinite] with N hN
  intro b hb heq q hq hqCutoff χ t ht
  have hqQ : q ≤ Nat.ceil ((Real.log (H : ℝ)) ^ (5 : ℕ)) := by
    exact_mod_cast hqCutoff.trans ((min_le_right _ _).trans (Nat.le_ceil _))
  exact hN q hq hqQ χ b hb heq t ht



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProgressionFourier
namespace OAI

/-!
# Additive Fourier resolution of every progression class

The coefficient mass is exactly one. There is no invertibility assumption
on the class, and no frequency supremum is put inside an integral.
-/

namespace TwoPointCorrelations

open scoped _root_.BigOperators

theorem additiveCharacter_add (α β : ℝ) (n : ℕ) :
    additiveCharacter (α + β) n = additiveCharacter α n * additiveCharacter β n := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stdAddChar_nat_mul (l : ℕ) [NeZero l] (a : ZMod l) (n : ℕ) :
    ZMod.stdAddChar (a * (n : ZMod l)) = additiveCharacter ((a.val : ℝ) / l) n := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a, ← Nat.cast_mul]
  rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

theorem zmod_indicator_fourier (l : ℕ) [NeZero l] (n b : ZMod l) :
    (if n = b then (1 : ℂ) else 0) =
      (l : ℂ)⁻¹ * ∑ a : ZMod l, ZMod.stdAddChar (a * (n - b)) := by
  classical
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar l), ZMod.card]
  have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne l
  by_cases h : n = b
  · simp [h, hlc]
  · simp [h, sub_ne_zero.mpr h]

theorem progression_fourier_identity (S : Finset ℕ) (v : ℕ → ℂ)
    (l : ℕ) [NeZero l] (b : ZMod l) (α : ℝ) :
    (∑ n ∈ S, if (n : ZMod l) = b then v n * additiveCharacter α n else 0) =
      (l : ℂ)⁻¹ * ∑ a : ZMod l, ZMod.stdAddChar (-(a * b)) *
        ∑ n ∈ S, v n * additiveCharacter (α + (a.val : ℝ) / l) n := by
  classical
  have hi (n : ℕ) :
      (if (n : ZMod l) = b then v n * additiveCharacter α n else 0) =
        (l : ℂ)⁻¹ * ∑ a : ZMod l,
          ZMod.stdAddChar (-(a * b)) * (v n * additiveCharacter (α + (a.val : ℝ) / l) n) := by
    have h := congrArg (fun z : ℂ => z * (v n * additiveCharacter α n))
      (zmod_indicator_fourier l (n : ZMod l) b)
    simp only [ite_mul, one_mul, zero_mul] at h
    rw [h, mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [additiveCharacter_add, ← stdAddChar_nat_mul l a n]
    have hm : a * ((n : ZMod l) - b) = -(a * b) + a * n := by ring
    rw [hm, AddChar.map_add_eq_mul]
    ring
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

/-- The progression mask averages `l` shifted frequencies with total
absolute coefficient mass one. -/
theorem norm_progression_fourier_le (S : Finset ℕ) (v : ℕ → ℂ)
    (l : ℕ) [NeZero l] (b : ZMod l) (α : ℝ) :
    ‖∑ n ∈ S, if (n : ZMod l) = b then v n * additiveCharacter α n else 0‖ ≤
      (l : ℝ)⁻¹ * ∑ a : ZMod l,
        ‖∑ n ∈ S, v n * additiveCharacter (α + (a.val : ℝ) / l) n‖ := by
  rw [progression_fourier_identity, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg l))
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul, le_refl]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open _root_.MeasureTheory
open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma shortExponentialSum_on_unit_cell (b : ℕ → ℂ) (D : ℕ) (α : ℝ)
    (v : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (v : ℝ) (v + 1)) :
    shortExponentialSum b D α y = shortExponentialSum b D α v := by
  have hy0 : 0 ≤ y := (Nat.cast_nonneg v).trans hy.1
  have hf := Nat.floor_eq_on_Ico v y hy
  unfold shortExponentialSum
  rw [Nat.floor_add_natCast hy0, hf, Nat.floor_natCast,
    Nat.floor_add_natCast (Nat.cast_nonneg v) D, Nat.floor_natCast]

lemma shortExponentialSum_unit_integrable (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) :
    IntervalIntegrable (fun y => ‖shortExponentialSum b D α y‖)
      volume (v : ℝ) (v + 1) := by
  apply (intervalIntegrable_const : IntervalIntegrable
    (fun _ : ℝ => ‖shortExponentialSum b D α v‖) volume (v : ℝ) (v + 1)).congr_uIoo
  intro y hy
  rw [Set.uIoo_of_le (by linarith : (v : ℝ) ≤ v + 1)] at hy
  exact congrArg norm (shortExponentialSum_on_unit_cell b D α v ⟨hy.1.le, hy.2⟩).symm

lemma integral_shortExponentialSum_unit (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) :
    (∫ y in (v : ℝ)..(v + 1), ‖shortExponentialSum b D α y‖) =
      ‖shortExponentialSum b D α v‖ := by
  calc
    _ = ∫ _y in (v : ℝ)..(v + 1), ‖shortExponentialSum b D α v‖ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
      intro y hy
      exact congrArg norm (shortExponentialSum_on_unit_cell b D α v ⟨hy.1.le, hy.2⟩)
    _ = _ := by simp

/-- Exact unit-cell decomposition, with no endpoint error. -/
theorem shortExponentialIntegral_eq_sum (b : ℕ → ℂ) (X D : ℕ) (α : ℝ) :
    shortExponentialIntegral b X D α =
      ∑ v ∈ range X, ‖shortExponentialSum b D α v‖ := by
  unfold shortExponentialIntegral
  symm
  calc
    _ = ∑ v ∈ range X, ∫ y in (v : ℝ)..((v + 1 : ℕ) : ℝ),
        ‖shortExponentialSum b D α y‖ := by
      apply sum_congr rfl
      intro v _
      simpa only [Nat.cast_add, Nat.cast_one] using
        (integral_shortExponentialSum_unit b D α v).symm
    _ = _ := by
      simpa only [Nat.cast_zero] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => (n : ℝ)) (n := X)
          (fun v _ => by simpa only [Nat.cast_add, Nat.cast_one] using
            shortExponentialSum_unit_integrable b D α v))

/-- The positive integer origins used in the manuscript occupy all but
the first unit cell of the published integral. -/
theorem sum_positive_shortExponentialSum_le (b : ℕ → ℂ) (Y D : ℕ) (α : ℝ) :
    (∑ v ∈ range Y, ‖shortExponentialSum b D α (v + 1 : ℕ)‖) ≤
      shortExponentialIntegral b (Y + 1) D α := by
  rw [shortExponentialIntegral_eq_sum, sum_range_succ']
  exact le_add_of_nonneg_right (norm_nonneg _)

lemma sum_Icc_shift (f : ℕ → ℂ) (v D : ℕ) :
    (∑ n ∈ Icc (v + 1) (v + D), f n) = ∑ m ∈ range D, f (v + m + 1) := by
  symm
  apply sum_bij (fun m _ => v + m + 1)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm n hn he
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - (v + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro m _
    rfl

lemma shortExponentialSum_at_nat (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortExponentialSum b D α v =
      ∑ n ∈ Icc (v + 1) (v + D), b n * additiveCharacter α n := by
  simp only [shortExponentialSum, Nat.floor_natCast,
    Nat.floor_add_natCast (Nat.cast_nonneg v) D]

lemma additiveCharacter_nat_add (α : ℝ) (m n : ℕ) :
    additiveCharacter α (m + n) = additiveCharacter α m * additiveCharacter α n := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_additiveCharacter (α : ℝ) (n : ℕ) : ‖additiveCharacter α n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _


lemma shortExponentialSum_eq_window (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortExponentialSum b D α v = additiveCharacter α v * shortWindowSum b D α v := by
  rw [shortExponentialSum_at_nat, sum_Icc_shift]
  unfold shortWindowSum
  rw [mul_sum]
  apply sum_congr rfl
  intro m _
  rw [show v + m + 1 = v + (m + 1) by omega, additiveCharacter_nat_add]
  ring

lemma norm_shortExponentialSum_eq_window (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    ‖shortExponentialSum b D α v‖ = ‖shortWindowSum b D α v‖ := by
  rw [shortExponentialSum_eq_window, norm_mul, norm_additiveCharacter, one_mul]

/-- A uniform fixed-frequency integral bound controls every progression
class of actual discrete windows, including nonunit classes. -/
theorem progression_short_sum_from_integral (b : ℕ → ℂ) (D Y l : ℕ)
    [NeZero l] (a : ZMod l) (α K : ℝ)
    (hK : ∀ β : ℝ, shortExponentialIntegral b (Y + 1) D β ≤ K) :
    (∑ v ∈ range Y, ‖∑ n ∈ Icc (v + 2) (v + 1 + D),
      if (n : ZMod l) = a then b n * additiveCharacter α n else 0‖) ≤ K := by
  calc
    _ ≤ ∑ v ∈ range Y, (l : ℝ)⁻¹ * ∑ j : ZMod l,
        ‖∑ n ∈ Icc (v + 2) (v + 1 + D),
          b n * additiveCharacter (α + (j.val : ℝ) / l) n‖ :=
      sum_le_sum (fun v _ => norm_progression_fourier_le _ b l a α)
    _ = (l : ℝ)⁻¹ * ∑ j : ZMod l, ∑ v ∈ range Y,
        ‖shortExponentialSum b D (α + (j.val : ℝ) / l) (v + 1 : ℕ)‖ := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro v _
      rw [shortExponentialSum_at_nat]
    _ ≤ (l : ℝ)⁻¹ * ∑ _j : ZMod l, K := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum (fun j _ =>
        (sum_positive_shortExponentialSum_le b Y D _).trans (hK _))
    _ = K := by
      simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      have hl : (l : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne l
      field_simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WindowPolynomialBounds
namespace OAI

/-! Concrete Parseval and short-sum bounds for the two window polynomials. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory
open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical _root_.ComplexConjugate









lemma fourier_nat_at_real (m : ℕ) (θ : ℝ) :
    fourier (m : ℤ) (θ : AddCircle (1 : ℝ)) = additiveCharacter θ m := by
  rw [fourier_coe_apply]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

lemma forwardWindowPolynomial_at_real (f : ℕ → ℂ) (D v : ℕ) (θ : ℝ) :
    forwardWindowPolynomial f D v (θ : AddCircle (1 : ℝ)) = shortWindowSum f D θ v := by
  unfold forwardWindowPolynomial fourierPolynomial
  simp_rw [fourier_nat_at_real]
  simpa only [Nat.zero_add, Nat.add_assoc, shortWindowSum] using
    (sum_Icc_shift (fun m => f (v + m) * additiveCharacter θ m) 0 D)



/-- Every circle frequency is represented by a real frequency, and the
unimodular origin phase disappears before applying MRT. -/
theorem progression_window_sum_from_integral (f : ℕ → ℂ) (D Y l : ℕ)
    [NeZero l] (a : ZMod l) (K : ℝ)
    (hK : ∀ α, shortExponentialIntegral f (Y + 1) D α ≤ K)
    (θ : AddCircle (1 : ℝ)) :
    (∑ v ∈ range Y,
      ‖forwardWindowPolynomial (progressionSequence f l a) D (v + 1) θ‖) ≤ K := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective θ
  calc
    _ = ∑ v ∈ range Y, ‖∑ n ∈ Icc (v + 2) (v + 1 + D),
        if (n : ZMod l) = a then f n * additiveCharacter α n else 0‖ := by
      apply sum_congr rfl
      intro v _
      rw [forwardWindowPolynomial_at_real, ← norm_shortExponentialSum_eq_window,
        shortExponentialSum_at_nat]
      simp only [progressionSequence, ite_mul, zero_mul]
    _ ≤ K := progression_short_sum_from_integral f D Y l a α K hK


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ModifiedShortSums
namespace OAI

/-! The precise MRT input on actual progression windows, uniformly over
all multiplicative finite-prime changes of the original nonpretentious factor. -/

namespace TwoPointCorrelations

open _root_.Filter
open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

theorem MRTShortExponentialInput.modified_windows
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (D : ℕ), 10 ≤ D → ∀ M : ℝ,
      ∀ᶠ Y : ℕ in atTop, ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
        ∀ (l : ℕ) [NeZero l] (a : ZMod l) (θ : AddCircle (1 : ℝ)),
        (∑ v ∈ range Y,
          ‖forwardWindowPolynomial (progressionSequence b l a) D (v + 1) θ‖) /
            ((D : ℝ) * (Y + 1 : ℕ)) ≤
          C * (Real.exp (-M / 20) + mrtShortError (Y + 1) D) := by
  obtain ⟨C, hC, hbound⟩ := hMRT
  refine ⟨C, hC, ?_⟩
  intro P D hD M
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hfnp.eventually_mrt_lower_bound hf P D M)
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop D] with Y hYN hYD
  intro b hb hbounded heq l _ a θ
  have hdist := hN₀ (Y + 1) (by omega) b hbounded heq
  have hDr : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hYr : (0 : ℝ) < (Y + 1 : ℕ) := by positivity
  apply (div_le_iff₀ (mul_pos hDr hYr)).mpr
  have hh := progression_window_sum_from_integral b D Y l a
    (C * (D : ℝ) * (Y + 1 : ℕ) *
      (Real.exp (-M / 20) + mrtShortError (Y + 1) D))
    (fun α => hbound (Y + 1) D hD (by omega) b hb hbounded M hdist α) θ
  convert (preTransparency := .instances) hh using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeShortSums
namespace OAI

/-! The published MRT theorem at fixed window length, uniformly over
all finite-prime modifications of the original nonpretentious factor. -/

namespace TwoPointCorrelations

open _root_.Filter
open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical _root_.Topology

lemma loglog_div_log_nonneg (D : ℕ) (hD : 10 ≤ D) :
    0 ≤ Real.log (Real.log (D : ℝ)) / Real.log D := by
  have hDr : (10 : ℝ) ≤ D := by exact_mod_cast hD
  have hdlog : 1 ≤ Real.log (D : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  exact div_nonneg (Real.log_nonneg hdlog) (by linarith)

/-- Fixed-length MRT, with an arbitrarily small residual error. The
supremum over frequencies remains outside the sum over window origins. -/
theorem MRTShortExponentialInput.modified_fixed_windows
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (D : ℕ), 10 ≤ D → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ Y : ℕ in atTop, ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
        ∀ (l : ℕ) [NeZero l] (a : ZMod l) (θ : AddCircle (1 : ℝ)),
        (∑ v ∈ range Y,
          ‖forwardWindowPolynomial (progressionSequence b l a) D (v + 1) θ‖) ≤
          C * D * Y * (Real.log (Real.log (D : ℝ)) / Real.log D + ε) := by
  obtain ⟨C, hC, hraw⟩ := hMRT.modified_windows hfnp hf
  refine ⟨2 * C, by positivity, ?_⟩
  intro P D hD ε hε
  have hehalf : 0 < ε / 2 := by positivity
  have ht : Tendsto (fun Y : ℕ => (Real.log (Y + 1 : ℕ)) ^ (-1 / (700 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (show 0 < (1 / (700 : ℝ)) by norm_num)).comp
      (Real.tendsto_log_atTop.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)))
  have hsmall := ht.eventually (gt_mem_nhds hehalf)
  filter_upwards [hraw P D hD (-20 * Real.log (ε / 2)), hsmall,
    eventually_ge_atTop 1] with Y hy hs hY
  intro b hb hbounded heq l _ a θ
  have hval := hy b hb hbounded heq l a θ
  have he : Real.exp (-(-20 * Real.log (ε / 2)) / 20) = ε / 2 := by
    convert (preTransparency := .instances) Real.exp_log hehalf using 1
    congr 1
    ring
  rw [he] at hval
  have hfirst := loglog_div_log_nonneg D hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hYpos : (0 : ℝ) < (Y + 1 : ℕ) := by positivity
  have hbound := (div_le_iff₀ (mul_pos hDpos hYpos)).mp hval
  have herror : ε / 2 + mrtShortError (Y + 1) D ≤
      Real.log (Real.log (D : ℝ)) / Real.log D + ε := by
    unfold mrtShortError
    linarith only [hs]
  have hYn : ((Y + 1 : ℕ) : ℝ) ≤ 2 * Y := by exact_mod_cast (show Y + 1 ≤ 2 * Y by omega)
  calc
    _ ≤ (C * (ε / 2 + mrtShortError (Y + 1) D)) * ((D : ℝ) * (Y + 1 : ℕ)) := hbound
    _ ≤ (C * (Real.log (Real.log (D : ℝ)) / Real.log D + ε)) *
        ((D : ℝ) * (Y + 1 : ℕ)) := by gcongr
    _ ≤ (C * (Real.log (Real.log (D : ℝ)) / Real.log D + ε)) *
        ((D : ℝ) * (2 * Y)) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TruncatedDilation
namespace OAI

/-! A fixed dilation is approximated by finitely many smooth-divisor
components. The discarded values lie in a literal smooth-divisor tail. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical


lemma smoothDilationTerm_eq_zero (q n a : ℕ) (f : ℕ → ℂ)
    (hq : 0 < q) (hn : 0 < n) (ha : a ≠ primeSmoothPart q.primeFactors n) :
    smoothDilationTerm q f a n = 0 := by
  unfold smoothDilationTerm coprimeRestriction
  split_ifs with has hc
  · exact False.elim (ha (primeSmoothPart_unique q n a hq hn has.2 has.1 hc))
  · exact mul_zero _
  · rfl

lemma smoothDilationTerm_at_part {f : ℕ → ℂ} (hf : Multiplicative f)
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) :
    smoothDilationTerm q f (primeSmoothPart q.primeFactors n) n = f (q * n) := by
  let a := primeSmoothPart q.primeFactors n
  let r := primeRoughPart q.primeFactors n
  have ha : 0 < a := primeSmoothPart_pos _ _ hn
  have hr : 0 < r := primeRoughPart_pos _ _ hn
  have he : a * r = n := primeSmoothPart_mul_primeRoughPart _ _ hn
  have hc : q.Coprime r := primeRoughPart_coprime q n hq
  have hac := coprime_of_primeFactors_subset ha (primeSmoothPart_support _ _) hc
  have hd : a ∣ n := ⟨r, he.symm⟩
  have hquot : n / a = r := by rw [← he, Nat.mul_div_cancel_left _ ha]
  change smoothDilationTerm q f a n = _
  rw [smoothDilationTerm, if_pos ⟨primeSmoothPart_support _ _, hd⟩,
    hquot, coprimeRestriction, if_pos hc,
    ← hf (q * a) r (Nat.mul_pos hq ha) hr (hc.mul_left hac)]
  congr 1
  rw [mul_assoc, he]


lemma truncatedDilation_eq_sum {f : ℕ → ℂ} (hf : Multiplicative f)
    (q n K : ℕ) (hq : 0 < q) (hn : 0 < n) :
    truncatedDilation q f K n = ∑ a ∈ Icc 1 K, smoothDilationTerm q f a n := by
  let a := primeSmoothPart q.primeFactors n
  have ha : 0 < a := primeSmoothPart_pos _ _ hn
  have hsum : (∑ b ∈ Icc 1 K, smoothDilationTerm q f b n) =
      if a ∈ Icc 1 K then smoothDilationTerm q f a n else 0 := by
    by_cases hak : a ∈ Icc 1 K
    · rw [if_pos hak]
      apply sum_eq_single a
      · intro b _ hba
        exact smoothDilationTerm_eq_zero q n b f hq hn hba
      · exact fun h => False.elim (h hak)
    · rw [if_neg hak]
      apply sum_eq_zero
      intro b hb
      apply smoothDilationTerm_eq_zero q n b f hq hn
      intro hba
      change b = a at hba
      exact hak (hba ▸ hb)
  rw [hsum, smoothDilationTerm_at_part hf q n hq hn]
  have ha1 : 1 ≤ a := ha
  change (if a ≤ K then f (q * n) else 0) = _
  simp only [mem_Icc, ha1, true_and]

lemma norm_truncatedDilation_error {f : ℕ → ℂ} (hf : OneBounded f)
    (q n K : ℕ) (hq : 0 < q) (hn : 0 < n) :
    ‖f (q * n) - truncatedDilation q f K n‖ ≤
      if K < primeSmoothPart q.primeFactors n then (1 : ℝ) else 0 := by
  unfold truncatedDilation
  by_cases hs : primeSmoothPart q.primeFactors n ≤ K
  · simp only [hs, ite_true, sub_self, norm_zero, Nat.not_lt.mpr hs, ite_false, le_refl]
  · simp only [hs, ite_false, sub_zero, Nat.lt_of_not_ge hs, ite_true]
    exact hf _ (Nat.mul_pos hq hn)

lemma smoothPart_tail_indicator (q n K : ℕ) (hn : 0 < n) :
    (if K < primeSmoothPart q.primeFactors n then (1 : ℝ) else 0) ≤
      ∑ a ∈ (Icc (K + 1) n).filter (fun a => a.primeFactors ⊆ q.primeFactors),
        if a ∣ n then (1 : ℝ) else 0 := by
  split_ifs with htail
  · let a := primeSmoothPart q.primeFactors n
    have hd : a ∣ n := ⟨primeRoughPart q.primeFactors n,
      (primeSmoothPart_mul_primeRoughPart _ _ hn).symm⟩
    have hm : a ∈ (Icc (K + 1) n).filter (fun a => a.primeFactors ⊆ q.primeFactors) := by
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨htail, Nat.le_of_dvd hn hd⟩,
        primeSmoothPart_support _ _⟩
    have h := single_le_sum (f := fun b : ℕ => if b ∣ n then (1 : ℝ) else 0)
      (fun b _ => by split_ifs <;> positivity) hm
    simpa only [if_pos hd] using h
  · exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedWindows
namespace OAI

/-! Exact short-window reindexing for a sequence supported on multiples
of a fixed integer. Only one endpoint term is lost to a fixed window length. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma additiveCharacter_nat_mul (α : ℝ) (a m : ℕ) :
    additiveCharacter α (a * m) = additiveCharacter (a * α) m := by
  unfold additiveCharacter
  congr 1
  push_cast
  ring

lemma shortExponentialSum_dilation (f : ℕ → ℂ) (a D v : ℕ)
    (ha : 0 < a) (α : ℝ) :
    shortExponentialSum (dilationSequence a f) D α v =
      shortExponentialSum f ((v + D) / a - v / a) (a * α) ((v / a : ℕ) : ℝ) := by
  have hle : v / a ≤ (v + D) / a := Nat.div_le_div_right (Nat.le_add_right _ _)
  rw [shortExponentialSum_at_nat, shortExponentialSum_at_nat,
    Nat.add_sub_of_le hle]
  have hleft : (∑ n ∈ Icc (v + 1) (v + D),
      dilationSequence a f n * additiveCharacter α n) =
      ∑ n ∈ (Icc (v + 1) (v + D)).filter (fun n => a ∣ n),
        f (n / a) * additiveCharacter α n := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    unfold dilationSequence
    split_ifs <;> simp
  rw [hleft]
  symm
  apply sum_bij (fun m _ => a * m)
  · intro m hm
    obtain ⟨hm0, hm1⟩ := mem_Icc.mp hm
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right a m⟩
    · have ht : v < a * m := by
        have hh := (Nat.div_lt_iff_lt_mul ha).mp (show v / a < m by omega)
        simpa only [Nat.mul_comm] using hh
      omega
    · have hh := (Nat.le_div_iff_mul_le ha).mp hm1
      simpa only [Nat.mul_comm] using hh
  · intro m _ n _ he
    exact Nat.eq_of_mul_eq_mul_left ha he
  · intro n hn
    obtain ⟨hnI, hd⟩ := mem_filter.mp hn
    obtain ⟨hn0, hn1⟩ := mem_Icc.mp hnI
    refine ⟨n / a, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hn1⟩,
      Nat.mul_div_cancel' hd⟩
    have he : v < a * (n / a) := by rw [Nat.mul_div_cancel' hd]; omega
    have hh : v / a < n / a := (Nat.div_lt_iff_lt_mul ha).mpr (by
      simpa only [Nat.mul_comm] using he)
    omega
  · intro m _
    rw [Nat.mul_div_cancel_left _ ha, additiveCharacter_nat_mul]

lemma quotient_window_length (a D v : ℕ) (_ha : 0 < a) :
    (v + D) / a - v / a = D / a ∨ (v + D) / a - v / a = D / a + 1 := by
  have hlo : v / a + D / a ≤ (v + D) / a := Nat.div_add_div_le_add_div
  have hhi := Nat.add_div_le_div_add_div_add_one v D a
  generalize (v + D) / a = t at *
  generalize v / a = u at *
  generalize D / a = w at *
  omega

lemma norm_shortWindowSum_le_succ (f : ℕ → ℂ) (hf : OneBounded f)
    (D v : ℕ) (α : ℝ) :
    ‖shortWindowSum f D α v‖ ≤ ‖shortWindowSum f (D + 1) α v‖ + 1 := by
  have he : shortWindowSum f (D + 1) α v = shortWindowSum f D α v +
      f (v + D + 1) * additiveCharacter α (D + 1) := by
    simp only [shortWindowSum, sum_range_succ]
  have hn : ‖f (v + D + 1) * additiveCharacter α (D + 1)‖ ≤ 1 := by
    rw [norm_mul, norm_additiveCharacter, mul_one]
    exact hf _ (by omega)
  have ht := norm_sub_le (shortWindowSum f (D + 1) α v)
    (f (v + D + 1) * additiveCharacter α (D + 1))
  have ht' : ‖shortWindowSum f D α v‖ ≤
      ‖shortWindowSum f (D + 1) α v‖ +
        ‖f (v + D + 1) * additiveCharacter α (D + 1)‖ := by
    simpa only [he, add_sub_cancel_right] using ht
  linarith

lemma norm_shortExponentialSum_dilation_le (f : ℕ → ℂ) (hf : OneBounded f)
    (a D v : ℕ) (ha : 0 < a) (α : ℝ) :
    ‖shortExponentialSum (dilationSequence a f) D α v‖ ≤
      ‖shortWindowSum f (D / a + 1) (a * α) (v / a)‖ + 1 := by
  rw [shortExponentialSum_dilation f a D v ha α,
    norm_shortExponentialSum_eq_window]
  rcases quotient_window_length a D v ha with he | he
  · rw [he]
    exact norm_shortWindowSum_le_succ f hf _ _ _
  · rw [he]
    exact le_add_of_nonneg_right zero_le_one

lemma quotient_sample_sum_le (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (a Y : ℕ) (ha : 0 < a) :
    (∑ v ∈ range Y, F (v / a)) ≤
      (a : ℝ) * ∑ m ∈ range (Y / a + 1), F m := by
  have hb : (∑ v ∈ range Y, F (v / a)) ≤
      ∑ x ∈ range (Y / a + 1) ×ˢ range a, F x.1 := by
    apply sum_le_sum_of_injOn (fun v => (v / a, v % a))
    · intro v _ w _ he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      nlinarith [Nat.div_add_mod v a, Nat.div_add_mod w a]
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact mem_product.mpr ⟨mem_range.mpr (by
        have hh : v / a ≤ Y / a := Nat.div_le_div_right (Nat.le_of_lt (mem_range.mp hv))
        exact Nat.lt_succ_of_le hh),
        mem_range.mpr (Nat.mod_lt _ ha)⟩
    · intro v _
      exact le_rfl
    · intro x _ _
      exact hF x.1
  apply hb.trans_eq
  rw [sum_product]
  simp only [sum_const, card_range, nsmul_eq_mul, ← mul_sum]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SmoothTailDensity
namespace OAI

/-! The density discarded by truncating the smooth part of an integer.
The bound retains the exact half-power Euler cost of the dilation. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma reciprocal_smooth_tail (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (K : ℝ) (hK : 0 < K) (hA : ∀ a ∈ A, a ∈ Nat.factoredNumbers P)
    (hlarge : ∀ a ∈ A, K ≤ (a : ℝ)) :
    (∑ a ∈ A, 1 / (a : ℝ)) ≤
      K ^ (-(1 / 2) : ℝ) * smoothReciprocalProduct P (1 / 2 : ℝ) := by
  calc
    _ ≤ ∑ a ∈ A, K ^ (-(1 / 2) : ℝ) * (a : ℝ) ^ (-(1 / 2) : ℝ) := by
      apply sum_le_sum
      intro a ha
      have hap : (0 : ℝ) < a := hK.trans_le (hlarge a ha)
      have he : 1 / (a : ℝ) = (a : ℝ) ^ (-(1 / 2) : ℝ) *
          (a : ℝ) ^ (-(1 / 2) : ℝ) := by
        rw [← Real.rpow_add hap]
        norm_num [Real.rpow_neg_one]
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hK (hlarge a ha) (by norm_num)) (by positivity)
    _ = K ^ (-(1 / 2) : ℝ) * ∑ a ∈ A, (a : ℝ) ^ (-(1 / 2) : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (smooth_reciprocal_sum_le P A hP (1 / 2) (by norm_num) hA) (by positivity)

lemma smooth_part_tail_density (q K N : ℕ) (hK : 0 < K) :
    (∑ v ∈ range N, if K < primeSmoothPart q.primeFactors (v + 1)
      then (1 : ℝ) else 0) ≤
      (N : ℝ) * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  let A := (Icc (K + 1) N).filter (fun a => a.primeFactors ⊆ q.primeFactors)
  have hA (a : ℕ) (ha : a ∈ A) : 0 < a := by
    have hh := (mem_Icc.mp (mem_filter.mp ha).1).1
    omega
  have hsum : (∑ v ∈ range N, if K < primeSmoothPart q.primeFactors (v + 1)
      then (1 : ℝ) else 0) ≤ ∑ a ∈ A, ((N / a : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ v ∈ range N, ∑ a ∈ A, if a ∣ v + 1 then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro v hv
        apply (smoothPart_tail_indicator q (v + 1) K (by omega)).trans
        apply sum_le_sum_of_subset_of_nonneg
        · intro a ha
          obtain ⟨ha, hs⟩ := mem_filter.mp ha
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha).1,
            (mem_Icc.mp ha).2.trans (by have hv' := mem_range.mp hv; omega)⟩, hs⟩
        · intro a _ _
          split_ifs <;> positivity
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a _
        have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.card_multiples N a)
        simpa only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero] using hh
  have hmass := reciprocal_smooth_tail q.primeFactors A
    (fun p hp => Nat.prime_of_mem_primeFactors hp) (K : ℝ)
    (by exact_mod_cast hK)
    (fun a ha => Nat.mem_factoredNumbers_of_primeFactors_subset (hA a ha).ne'
      (mem_filter.mp ha).2)
    (fun a ha => by exact_mod_cast (show K ≤ a by
      have hh := (mem_Icc.mp (mem_filter.mp ha).1).1; omega))
  calc
    _ ≤ ∑ a ∈ A, ((N / a : ℕ) : ℝ) := hsum
    _ ≤ ∑ a ∈ A, (N : ℝ) / a := sum_le_sum (fun _ _ => Nat.cast_div_le)
    _ = (N : ℝ) * ∑ a ∈ A, 1 / (a : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg N)).trans_eq (by ring)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SmoothWindowSum
namespace OAI

/-! The exact smooth-divisor decomposition inside a short Fourier window,
with the discarded tail bounded before any cancellation is used. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma shortWindowSum_sub (f g : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortWindowSum (fun n => f n - g n) D α v =
      shortWindowSum f D α v - shortWindowSum g D α v := by
  simp only [shortWindowSum, sub_mul, sum_sub_distrib]

lemma norm_shortWindowSum_le (f : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    ‖shortWindowSum f D α v‖ ≤ ∑ m ∈ range D, ‖f (v + m + 1)‖ := by
  apply (norm_sum_le _ _).trans
  simp only [norm_mul, norm_additiveCharacter, mul_one, le_refl]

lemma window_error_from_density (f g : ℕ → ℂ) (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hfg : ∀ n, 0 < n → ‖f n - g n‖ ≤ e n)
    (D Y : ℕ) (α : ℝ) :
    (∑ v ∈ range Y, ‖shortWindowSum f D α v - shortWindowSum g D α v‖) ≤
      (D : ℝ) * ∑ n ∈ range (Y + D), e (n + 1) := by
  calc
    _ ≤ ∑ v ∈ range Y, ∑ m ∈ range D, e (v + m + 1) := by
      apply sum_le_sum
      intro v _
      rw [← shortWindowSum_sub]
      exact (norm_shortWindowSum_le _ _ _ _).trans
        (sum_le_sum (fun m _ => hfg _ (by omega)))
    _ = ∑ m ∈ range D, ∑ v ∈ range Y, e (v + m + 1) := sum_comm
    _ ≤ ∑ _m ∈ range D, ∑ n ∈ range (Y + D), e (n + 1) := by
      apply sum_le_sum
      intro m hm
      apply sum_le_sum_of_injOn (fun v => v + m)
      · intro v _ w _ h
        change v + m = w + m at h
        omega
      · intro x hx
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
        simp only [mem_range] at hm hv ⊢
        omega
      · intro v _
        exact le_rfl
      · intro n _ _
        exact he _
    _ = _ := by simp

lemma truncated_window_error {f : ℕ → ℂ} (hf : OneBounded f)
    (q K D Y : ℕ) (hq : 0 < q) (hK : 0 < K) (α : ℝ) :
    (∑ v ∈ range Y, ‖shortWindowSum (fun n => f (q * n)) D α v -
      shortWindowSum (truncatedDilation q f K) D α v‖) ≤
      (D : ℝ) * (Y + D) * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  apply (window_error_from_density _ _
    (fun n => if K < primeSmoothPart q.primeFactors n then 1 else 0)
    (fun _ => by split_ifs <;> positivity)
    (fun n hn => norm_truncatedDilation_error hf q n K hq hn) D Y α).trans
  have hb := smooth_part_tail_density q K (Y + D) hK
  calc
    _ ≤ (D : ℝ) * ((Y + D : ℕ) * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg D)
    _ = _ := by push_cast; ring

lemma smoothDilationTerm_as_dilation (q a : ℕ) (f : ℕ → ℂ)
    (ha : a.primeFactors ⊆ q.primeFactors) :
    smoothDilationTerm q f a = fun n =>
      f (q * a) * dilationSequence a (coprimeRestriction q f) n := by
  funext n
  unfold smoothDilationTerm dilationSequence
  by_cases hd : a ∣ n
  · rw [if_pos ⟨ha, hd⟩, if_pos hd]
  · rw [if_neg (fun h => hd h.2), if_neg hd, mul_zero]

lemma truncated_shortWindowSum {f : ℕ → ℂ} (hf : Multiplicative f)
    (q K D v : ℕ) (hq : 0 < q) (α : ℝ) :
    shortWindowSum (truncatedDilation q f K) D α v =
      ∑ a ∈ (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors),
        f (q * a) * shortWindowSum (dilationSequence a (coprimeRestriction q f)) D α v := by
  unfold shortWindowSum
  have hexpand : (∑ m ∈ range D,
      truncatedDilation q f K (v + m + 1) * additiveCharacter α (m + 1)) =
      ∑ m ∈ range D, (∑ a ∈ Icc 1 K,
        smoothDilationTerm q f a (v + m + 1)) * additiveCharacter α (m + 1) := by
    apply sum_congr rfl
    intro m _
    rw [truncatedDilation_eq_sum hf q (v + m + 1) K hq (by omega)]
  rw [hexpand]
  simp_rw [sum_mul]
  rw [sum_comm]
  symm
  rw [sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : a.primeFactors ⊆ q.primeFactors
  · rw [if_pos ha]
    simp only [mul_sum, ← mul_assoc, smoothDilationTerm_as_dilation q a f ha]
  · rw [if_neg ha]
    symm
    apply sum_eq_zero
    intro m _
    rw [smoothDilationTerm, if_neg (fun h => ha h.1), zero_mul]

/-- Finite short-window majorant: one genuine shorter window for each
smooth divisor, and one density term for all discarded smooth divisors. -/
theorem smooth_dilation_window_sum {f : ℕ → ℂ} (hf : Multiplicative f)
    (hfb : OneBounded f) (q K D Y : ℕ) (hq : 0 < q) (hK : 0 < K) (α : ℝ) :
    (∑ v ∈ range Y, ‖shortWindowSum (fun n => f (q * n)) D α v‖) ≤
      (∑ a ∈ (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors),
        ((a : ℝ) * (∑ m ∈ range (Y / a + 1),
          ‖shortWindowSum (coprimeRestriction q f) (D / a + 1) (a * α) m‖) + Y)) +
      (D : ℝ) * (Y + D) * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  let A := (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors)
  have hs : (∑ v ∈ range Y, ‖shortWindowSum (truncatedDilation q f K) D α v‖) ≤
      ∑ a ∈ A, ((a : ℝ) * (∑ m ∈ range (Y / a + 1),
        ‖shortWindowSum (coprimeRestriction q f) (D / a + 1) (a * α) m‖) + Y) := by
    calc
      _ ≤ ∑ v ∈ range Y, ∑ a ∈ A,
          ‖shortWindowSum (dilationSequence a (coprimeRestriction q f)) D α v‖ := by
        apply sum_le_sum
        intro v _
        rw [truncated_shortWindowSum hf q K D v hq α]
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro a ha
        have hap : 0 < a := (mem_Icc.mp (mem_filter.mp ha).1).1
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hfb _ (Nat.mul_pos hq hap))
      _ = ∑ a ∈ A, ∑ v ∈ range Y,
          ‖shortWindowSum (dilationSequence a (coprimeRestriction q f)) D α v‖ := sum_comm
      _ ≤ _ := by
        apply sum_le_sum
        intro a ha
        have hap : 0 < a := (mem_Icc.mp (mem_filter.mp ha).1).1
        calc
          _ ≤ ∑ v ∈ range Y,
              (‖shortWindowSum (coprimeRestriction q f) (D / a + 1) (a * α) (v / a)‖ + 1) := by
            apply sum_le_sum
            intro v _
            rw [← norm_shortExponentialSum_eq_window]
            exact norm_shortExponentialSum_dilation_le _
              (coprimeRestriction_oneBounded q hfb) a D v hap α
          _ = (∑ v ∈ range Y,
              ‖shortWindowSum (coprimeRestriction q f) (D / a + 1) (a * α) (v / a)‖) + Y := by
            simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
          _ ≤ _ := add_le_add
            (quotient_sample_sum_le _ (fun _ => norm_nonneg _) a Y hap) le_rfl
  calc
    _ ≤ (∑ v ∈ range Y, ‖shortWindowSum (truncatedDilation q f K) D α v‖) +
        ∑ v ∈ range Y, ‖shortWindowSum (fun n => f (q * n)) D α v -
          shortWindowSum (truncatedDilation q f K) D α v‖ := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro v _
      have he : shortWindowSum (fun n => f (q * n)) D α v =
          shortWindowSum (truncatedDilation q f K) D α v +
          (shortWindowSum (fun n => f (q * n)) D α v -
            shortWindowSum (truncatedDilation q f K) D α v) := by abel
      calc
        _ = ‖shortWindowSum (truncatedDilation q f K) D α v +
            (shortWindowSum (fun n => f (q * n)) D α v -
              shortWindowSum (truncatedDilation q f K) D α v)‖ := congrArg norm he
        _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hs (truncated_window_error hfb q K D Y hq hK α)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilationMRT
namespace OAI

/-! MRT at the exact quotient-window lengths needed by a fixed dilation.
The published input is unchanged; only finite reindexing is performed. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma zero_origin_sum_le (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (Y : ℕ) :
    (∑ v ∈ range Y, F v) ≤ F 0 + ∑ v ∈ range Y, F (v + 1) := by
  have h1 := sum_range_succ F Y
  have h2 := sum_range_succ' F Y
  linarith [hF Y]

lemma shortWindowSum_norm_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (D v : ℕ) (α : ℝ) : ‖shortWindowSum f D α v‖ ≤ D := by
  apply (norm_shortWindowSum_le f D v α).trans
  calc
    _ ≤ ∑ _m ∈ range D, (1 : ℝ) := sum_le_sum (fun m _ => hf _ (by omega))
    _ = _ := by simp

theorem MRTShortExponentialInput.modified_zero_windows
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (D : ℕ), 10 ≤ D →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
        ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) → ∀ α : ℝ,
        (∑ v ∈ range Y, ‖shortWindowSum b D α v‖) ≤
          C * D * Y * (Real.log (Real.log (D : ℝ)) / Real.log D + ε) := by
  obtain ⟨C, hC, hbase⟩ := hMRT.modified_fixed_windows hfnp hf
  refine ⟨C + 1, by positivity, ?_⟩
  intro P D hD ε hε
  filter_upwards [hbase P D hD ε hε,
    eventually_ge_atTop (Nat.ceil (1 / ε))] with Y hY hYlarge
  intro b hb hbb heq α
  have hprog : progressionSequence b 1 (0 : ZMod 1) = b := by
    funext n
    simp only [progressionSequence, Subsingleton.elim (n : ZMod 1) 0, ite_true]
  have hw := hY b hb hbb heq 1 (0 : ZMod 1) (α : AddCircle (1 : ℝ))
  simp only [hprog, forwardWindowPolynomial_at_real] at hw
  have hYs : 1 / ε ≤ (Y : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hYlarge)
  have hYe : 1 ≤ (Y : ℝ) * ε := (div_le_iff₀ hε).mp hYs
  have hE : 0 ≤ Real.log (Real.log (D : ℝ)) / Real.log D :=
    loglog_div_log_nonneg D hD
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hpiece : (D : ℝ) ≤ (D : ℝ) * Y *
      (Real.log (Real.log (D : ℝ)) / Real.log D + ε) := by
    have hy : 1 ≤ (Y : ℝ) * (Real.log (Real.log (D : ℝ)) / Real.log D + ε) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg Y) hE]
    nlinarith
  calc
    _ ≤ ‖shortWindowSum b D α 0‖ + ∑ v ∈ range Y, ‖shortWindowSum b D α (v + 1)‖ :=
      zero_origin_sum_le _ (fun _ => norm_nonneg _) Y
    _ ≤ D + C * D * Y * (Real.log (Real.log (D : ℝ)) / Real.log D + ε) :=
      add_le_add (shortWindowSum_norm_bound b hbb D 0 α) hw
    _ ≤ _ := by nlinarith only [hpiece]

/-- Each quotient length is fixed before taking the long average. Thus
all shorter MRT estimates hold on a common tail, uniformly in the modified
function and in frequency. -/
theorem MRTShortExponentialInput.modified_quotient_windows
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (q D K : ℕ), 0 < q →
      (∀ a ∈ Icc 1 K, 10 ≤ D / a + 1) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
        ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
        ∀ a ∈ Icc 1 K, ∀ α : ℝ,
        (∑ m ∈ range (Y / a + 1),
          ‖shortWindowSum (coprimeRestriction q b) (D / a + 1) α m‖) ≤
          C * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) *
            (Real.log (Real.log (D / a + 1 : ℕ)) / Real.log (D / a + 1 : ℕ) + ε) := by
  obtain ⟨C, hC, hw⟩ := hMRT.modified_zero_windows hfnp hf
  refine ⟨C, hC, ?_⟩
  intro P q D K hq hlength ε hε
  have hall : ∀ᶠ Y : ℕ in atTop, ∀ a ∈ Icc 1 K,
      ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) → ∀ α : ℝ,
      (∑ m ∈ range (Y / a + 1),
        ‖shortWindowSum (coprimeRestriction q b) (D / a + 1) α m‖) ≤
        C * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) *
          (Real.log (Real.log (D / a + 1 : ℕ)) / Real.log (D / a + 1 : ℕ) + ε) := by
    apply (eventually_all_finset (Icc 1 K)).mpr
    intro a ha
    have hap : 0 < a := (mem_Icc.mp ha).1
    have ht : Tendsto (fun Y : ℕ => Y / a + 1) atTop atTop :=
      (tendsto_add_atTop_nat 1).comp (tendsto_nat_div_atTop a hap)
    filter_upwards [ht.eventually (hw (P ∪ q.primeFactors) (D / a + 1)
      (hlength a ha) ε hε)] with Y hY
    intro b hb hbb heq α
    refine hY (coprimeRestriction q b) (coprimeRestriction_multiplicative q hb)
      (coprimeRestriction_oneBounded q hbb) ?_ α
    intro p hp hnot
    rw [coprimeRestriction_prime q hq b hp (fun h => hnot (mem_union_right _ h))]
    exact heq p hp (fun h => hnot (mem_union_left _ h))
  filter_upwards [hall] with Y hY
  intro b hb hbb heq a ha α
  exact hY a ha b hb hbb heq α

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SmoothWindowBound
namespace OAI

/-! Summing the shorter-window estimates costs a reciprocal smooth sum,
not the number of smooth divisors. The elementary endpoint error is explicit. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma smooth_harmonic_sum_le (q K : ℕ) :
    (∑ a ∈ (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors),
      1 / (a : ℝ)) ≤ smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  let A := (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors)
  have hA (a : ℕ) (ha : a ∈ A) : 0 < a := (mem_Icc.mp (mem_filter.mp ha).1).1
  calc
    _ ≤ ∑ a ∈ A, (a : ℝ) ^ (-(1 / 2) : ℝ) := by
      apply sum_le_sum
      intro a ha
      rw [one_div, ← Real.rpow_neg_one]
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast hA a ha
      · norm_num
    _ ≤ _ := smooth_reciprocal_sum_le q.primeFactors A
      (fun p hp => Nat.prime_of_mem_primeFactors hp) (1 / 2) (by norm_num)
      (fun a ha => Nat.mem_factoredNumbers_of_primeFactors_subset (hA a ha).ne'
        (mem_filter.mp ha).2)

lemma dilation_window_count_bound (a D Y : ℕ)
    (ha : 0 < a) (haD : a ≤ D) (haY : a ≤ Y) :
    (a : ℝ) * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) ≤
      4 * (D : ℝ) * Y / a := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hd : (1 : ℝ) ≤ (D : ℝ) / a := (le_div_iff₀ hap).mpr (by simpa only [one_mul] using (show (a : ℝ) ≤ D by exact_mod_cast haD))
  have hy : (1 : ℝ) ≤ (Y : ℝ) / a := (le_div_iff₀ hap).mpr (by simpa only [one_mul] using (show (a : ℝ) ≤ Y by exact_mod_cast haY))
  have hD : ((D / a + 1 : ℕ) : ℝ) ≤ 2 * (D : ℝ) / a := by
    have hh : ((D / a : ℕ) : ℝ) ≤ (D : ℝ) / a := Nat.cast_div_le
    push_cast
    calc
      (D / a : ℕ) + (1 : ℝ) ≤ (D : ℝ) / a + 1 := add_le_add hh le_rfl
      _ ≤ 2 * ((D : ℝ) / a) := by linarith only [hd]
      _ = _ := by ring
  have hY : ((Y / a + 1 : ℕ) : ℝ) ≤ 2 * (Y : ℝ) / a := by
    have hh : ((Y / a : ℕ) : ℝ) ≤ (Y : ℝ) / a := Nat.cast_div_le
    push_cast
    calc
      (Y / a : ℕ) + (1 : ℝ) ≤ (Y : ℝ) / a + 1 := add_le_add hh le_rfl
      _ ≤ 2 * ((Y : ℝ) / a) := by linarith only [hy]
      _ = _ := by ring
  calc
    _ ≤ (a : ℝ) * (2 * D / a) * (2 * Y / a) := by gcongr
    _ = _ := by field_simp; ring

/-- The finite analytic assembly used for a dilated nonpretentious factor.
`hbase` is subsequently supplied by the published MRT theorem, uniformly in
the original function's finite-prime changes. -/
theorem smooth_dilation_window_bound {f : ℕ → ℂ}
    (hf : Multiplicative f) (hfb : OneBounded f)
    (q K D Y : ℕ) (hq : 0 < q) (hK : 0 < K)
    (hKD : K ≤ D) (hDY : D ≤ Y) (C E : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hbase : ∀ a ∈ Icc 1 K, ∀ β : ℝ,
      (∑ m ∈ range (Y / a + 1),
        ‖shortWindowSum (coprimeRestriction q f) (D / a + 1) β m‖) ≤
        C * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) * E)
    (α : ℝ) :
    (∑ v ∈ range Y, ‖shortWindowSum (fun n => f (q * n)) D α v‖) ≤
      4 * C * D * Y * E * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) +
        (K : ℝ) * Y + 2 * D * Y * (K : ℝ) ^ (-(1 / 2) : ℝ) *
          smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  let A := (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors)
  have hcoeff : 0 ≤ 4 * C * D * Y * E := by positivity
  have hs : (∑ a ∈ A, ((a : ℝ) * (∑ m ∈ range (Y / a + 1),
      ‖shortWindowSum (coprimeRestriction q f) (D / a + 1) (a * α) m‖) + Y)) ≤
      4 * C * D * Y * E * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) +
        (K : ℝ) * Y := by
    calc
      _ ≤ ∑ a ∈ A, (4 * C * D * Y * E * (1 / (a : ℝ)) + Y) := by
        apply sum_le_sum
        intro a ha
        have haI := (mem_filter.mp ha).1
        have hap : 0 < a := (mem_Icc.mp haI).1
        have haD := (mem_Icc.mp haI).2.trans hKD
        have haY := haD.trans hDY
        apply add_le_add ?_ le_rfl
        calc
          _ ≤ (a : ℝ) * (C * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) * E) :=
            mul_le_mul_of_nonneg_left (hbase a haI _) (Nat.cast_nonneg a)
          _ = (C * E) * ((a : ℝ) * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ)) := by ring
          _ ≤ (C * E) * (4 * (D : ℝ) * Y / a) :=
            mul_le_mul_of_nonneg_left (dilation_window_count_bound a D Y hap haD haY)
              (mul_nonneg hC hE)
          _ = _ := by ring
      _ = 4 * C * D * Y * E * (∑ a ∈ A, 1 / (a : ℝ)) + (A.card : ℝ) * Y := by
        rw [sum_add_distrib, ← mul_sum]
        simp only [sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (smooth_harmonic_sum_le q K) hcoeff
        · apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg Y)
          have hsub : A ⊆ Icc 1 K := filter_subset _ _
          have hcard : A.card ≤ K := by simpa using card_le_card hsub
          exact_mod_cast hcard
  have htail : (D : ℝ) * (Y + D) * (K : ℝ) ^ (-(1 / 2) : ℝ) *
      smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) ≤
      2 * D * Y * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
    have hDYr : (D : ℝ) ≤ Y := by exact_mod_cast hDY
    have hM := smoothReciprocalProduct_nonneg q.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp) (1 / 2) (by norm_num)
    have hh : (D : ℝ) * (Y + D) ≤ 2 * D * Y := by nlinarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (Nat.cast_nonneg K) _)) hM
  exact (smooth_dilation_window_sum hf hfb q K D Y hq hK α).trans
    ((add_le_add hs htail).trans_eq (by ring))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedShortSums
namespace OAI

/-! The published MRT input applied to the actual sequence f(qn), using
only the exact smooth-divisor expansion. All dilation dependence is exposed
through one Euler product and an elementary finite truncation error. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem MRTShortExponentialInput.dilated_short_sums
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (q D K : ℕ),
      0 < q → 0 < K → K ≤ D →
      (∀ a ∈ Icc 1 K, 10 ≤ D / a + 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ a ∈ Icc 1 K,
        Real.log (Real.log (D / a + 1 : ℕ)) / Real.log (D / a + 1 : ℕ) ≤ E) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
        ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) → ∀ α : ℝ,
        (∑ v ∈ range Y, ‖shortWindowSum (fun n => b (q * n)) D α v‖) ≤
          (D : ℝ) * Y *
            ((4 * C * (E + ε) + 2 * (K : ℝ) ^ (-(1 / 2) : ℝ)) *
              smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)) + K * Y := by
  obtain ⟨C, hC, hquotient⟩ := hMRT.modified_quotient_windows hfnp hf
  refine ⟨C, hC, ?_⟩
  intro P q D K hq hK hKD hlength E hE hlog ε hε
  filter_upwards [hquotient P q D K hq hlength ε hε,
    eventually_ge_atTop D] with Y hY hDY
  intro b hb hbb heq α
  have hbase : ∀ a ∈ Icc 1 K, ∀ β : ℝ,
      (∑ m ∈ range (Y / a + 1),
        ‖shortWindowSum (coprimeRestriction q b) (D / a + 1) β m‖) ≤
        C * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) * (E + ε) := by
    intro a ha β
    exact (hY b hb hbb heq a ha β).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hlog a ha) le_rfl) (by positivity))
  exact (smooth_dilation_window_bound hb hbb q K D Y hq hK hKD hDY C (E + ε)
    hC.le (by positivity) hbase α).trans_eq (by ring)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedWindowScale
namespace OAI

/-! The smooth-divisor truncation is far below the original window length.
All surviving quotient windows retain a fixed positive fraction of its
logarithmic length. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma quotient_log_error_bound (B C₀ : ℝ) (M : ℕ)
    (hB : Real.exp 1 ≤ B) (hC : 1 ≤ C₀)
    (hlo : B ^ (9999 / 10000 : ℝ) / 2 ≤ Real.log (M : ℝ))
    (hhi : Real.log (M : ℝ) ≤ (C₀ + 1) * B ^ (2 : ℕ)) :
    Real.log (Real.log (M : ℝ)) / Real.log M ≤
      (2 * (Real.log (C₀ + 1) + 2)) *
        (Real.log B / B ^ (9999 / 10000 : ℝ)) := by
  have hB1 : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hlogB : 1 ≤ Real.log B := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hB
  have hCpos : 0 < C₀ + 1 := by linarith
  have hClog : 0 ≤ Real.log (C₀ + 1) := Real.log_nonneg (by linarith)
  have hA : 0 < B ^ (9999 / 10000 : ℝ) := Real.rpow_pos_of_pos hBp _
  have hM : 0 < Real.log (M : ℝ) := lt_of_lt_of_le (by positivity) hlo
  have hnum : Real.log (Real.log (M : ℝ)) ≤
      (Real.log (C₀ + 1) + 2) * Real.log B := by
    have hh := Real.log_le_log hM hhi
    rw [Real.log_mul hCpos.ne' (pow_ne_zero 2 hBp.ne'), Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith [mul_nonneg hClog (sub_nonneg.mpr hlogB)]
  calc
    _ ≤ ((Real.log (C₀ + 1) + 2) * Real.log B) / Real.log M :=
      div_le_div_of_nonneg_right hnum hM.le
    _ ≤ ((Real.log (C₀ + 1) + 2) * Real.log B) /
        (B ^ (9999 / 10000 : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlo
    _ = _ := by ring

lemma dilationCutoff_bounds (B : ℝ)
    (_hB : 0 < B) (hlarge : 4 * Real.log 2 ≤ B ^ (9999 / 10000 : ℝ)) :
    0 < dilationCutoff B ∧
      Real.exp (B ^ (9999 / 10000 : ℝ) / 4) / 2 ≤ dilationCutoff B ∧
      (dilationCutoff B : ℝ) ≤ Real.exp (B ^ (9999 / 10000 : ℝ) / 4) := by
  have he : 2 ≤ Real.exp (B ^ (9999 / 10000 : ℝ) / 4) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlo := Nat.lt_floor_add_one (Real.exp (B ^ (9999 / 10000 : ℝ) / 4))
  have hhi := Nat.floor_le (le_of_lt (Real.exp_pos (B ^ (9999 / 10000 : ℝ) / 4)))
  change Real.exp (B ^ (9999 / 10000 : ℝ) / 4) < (dilationCutoff B : ℝ) + 1 at hlo
  change (dilationCutoff B : ℝ) ≤ _ at hhi
  refine ⟨?_, by linarith, hhi⟩
  have hh : (0 : ℝ) < dilationCutoff B := by linarith
  exact_mod_cast hh

lemma dilation_quotient_log_lower (B : ℝ) (D a : ℕ)
    (hB : 0 < B) (hlarge : 4 * Real.log 2 ≤ B ^ (9999 / 10000 : ℝ))
    (hD : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D)
    (ha : 0 < a) (haK : a ≤ dilationCutoff B) :
    B ^ (9999 / 10000 : ℝ) / 2 ≤ Real.log (D / a + 1 : ℕ) := by
  let t := B ^ (9999 / 10000 : ℝ)
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have haKr : (a : ℝ) ≤ dilationCutoff B := by exact_mod_cast haK
  have haexp : (a : ℝ) ≤ Real.exp (t / 4) :=
    haKr.trans (dilationCutoff_bounds B hB hlarge).2.2
  have hr : (1 / 2 : ℝ) * Real.exp (3 * t / 4) ≤ (D : ℝ) / a := by
    calc
      _ = ((1 / 2 : ℝ) * Real.exp t) / Real.exp (t / 4) := by
        calc
          _ = (1 / 2 : ℝ) * Real.exp (t - t / 4) := by congr 2; ring
          _ = (1 / 2 : ℝ) * (Real.exp t / Real.exp (t / 4)) := by rw [Real.exp_sub]
          _ = _ := by ring
      _ ≤ (D : ℝ) / a := div_le_div₀ (by positivity) hD hap haexp
  have hfloor : (D : ℝ) / a < (D / a + 1 : ℕ) := by
    have hh := Nat.lt_floor_add_one ((D : ℝ) / a)
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast, Nat.cast_add, Nat.cast_one] using hh
  have hM : (0 : ℝ) < (D / a + 1 : ℕ) := by positivity
  have hh := Real.log_le_log (by positivity : (0 : ℝ) <
    (1 / 2 : ℝ) * Real.exp (3 * t / 4)) (hr.trans hfloor.le)
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp, one_div, Real.log_inv] at hh
  change t / 2 ≤ _
  change 4 * Real.log 2 ≤ t at hlarge
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedWindowParameters
namespace OAI

/-! Uniform parameter bounds for the exact smooth-divisor MRT reduction. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma dilation_quotient_log_upper (B C₀ : ℝ) (D a : ℕ)
    (hB : 1 ≤ B) (hDpos : 0 < D)
    (hD : (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ))) :
    Real.log (D / a + 1 : ℕ) ≤ (C₀ + 1) * B ^ (2 : ℕ) := by
  have hM : (0 : ℝ) < (D / a + 1 : ℕ) := by positivity
  have hMbound : (D / a + 1 : ℕ) ≤ 2 * (D : ℝ) := by
    have hd : D / a + 1 ≤ 2 * D := by have hh := Nat.div_le_self D a; omega
    exact_mod_cast hd
  have hBsq : 1 ≤ B ^ (2 : ℕ) := one_le_pow₀ hB
  have hexp : 2 ≤ Real.exp (B ^ (2 : ℕ)) := by
    have hh := Real.add_one_le_exp (B ^ (2 : ℕ)); linarith
  have hlast : (2 : ℝ) * Real.exp (C₀ * B ^ (2 : ℕ)) ≤
      Real.exp ((C₀ + 1) * B ^ (2 : ℕ)) := by
    calc
      _ ≤ Real.exp (B ^ (2 : ℕ)) * Real.exp (C₀ * B ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact (Real.log_le_log hM
    (hMbound.trans ((mul_le_mul_of_nonneg_left hD (by norm_num)).trans hlast))).trans_eq
      (Real.log_exp _)

lemma dilation_cutoff_error_bounds (B : ℝ) (D : ℕ)
    (hB : 0 < B) (hlarge : 4 * Real.log 2 ≤ B ^ (9999 / 10000 : ℝ))
    (hD : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D) :
    (dilationCutoff B : ℝ) / D ≤ 2 * Real.exp (-B ^ (9999 / 10000 : ℝ) / 8) ∧
      (dilationCutoff B : ℝ) ^ (-(1 / 2) : ℝ) ≤
        2 * Real.exp (-B ^ (9999 / 10000 : ℝ) / 8) := by
  let t := B ^ (9999 / 10000 : ℝ)
  have ht : 0 < t := Real.rpow_pos_of_pos hB _
  have hk := dilationCutoff_bounds B hB hlarge
  have hkp : (0 : ℝ) < dilationCutoff B := by exact_mod_cast hk.1
  have hratio : (dilationCutoff B : ℝ) / D ≤ 2 * Real.exp (-3 * t / 4) := by
    calc
      _ ≤ Real.exp (t / 4) / ((1 / 2 : ℝ) * Real.exp t) :=
        div_le_div₀ (Real.exp_pos _).le hk.2.2 (by positivity) hD
      _ = _ := by
        rw [show -3 * t / 4 = t / 4 - t by ring, Real.exp_sub]
        field_simp
  have hexp : Real.exp (-3 * t / 4) ≤ Real.exp (-t / 8) :=
    Real.exp_le_exp.mpr (by linarith)
  refine ⟨hratio.trans (mul_le_mul_of_nonneg_left hexp (by norm_num)), ?_⟩
  have hlog : t / 4 - Real.log 2 ≤ Real.log (dilationCutoff B : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < Real.exp (t / 4) / 2) hk.2.1
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hh
    exact hh
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  rw [Real.rpow_def_of_pos hkp]
  calc
    _ ≤ Real.exp (-t / 8 + Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring


theorem eventually_dilationWindowParameters (C₀ : ℝ) (hC : 1 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ D : ℕ,
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      DilationWindowParameters B C₀ D := by
  have htend := tendsto_rpow_atTop (show 0 < (9999 / 10000 : ℝ) by norm_num)
  have hsmall := htend.eventually
    ((isLittleO_exp_neg_mul_rpow_atTop (show 0 < (1 / 8 : ℝ) by norm_num) (-1)).bound
      (show 0 < (1 : ℝ) by norm_num))
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    htend.eventually (eventually_ge_atTop (4 * Real.log 2)),
    htend.eventually (eventually_ge_atTop (2 * Real.log 10)), hsmall] with
    B hB hlarge hten hsmallB
  intro D hD hDupper
  have hB1 : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have ht : 0 < B ^ (9999 / 10000 : ℝ) := Real.rpow_pos_of_pos hBp _
  have hlogB : 1 ≤ Real.log B := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hB
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hK := dilationCutoff_bounds B hBp hlarge
  have hDpos : 0 < D := by
    have hh : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
    exact_mod_cast hh
  have hKD : dilationCutoff B ≤ D := by
    have he : Real.exp (B ^ (9999 / 10000 : ℝ) / 4) ≤
        (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) := by
      apply (Real.log_le_log_iff (Real.exp_pos _) (by positivity)).mp
      rw [Real.log_exp, Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
        (Real.exp_ne_zero _), one_div, Real.log_inv, Real.log_exp]
      linarith
    exact_mod_cast hK.2.2.trans (he.trans hD)
  have hsmall' : Real.exp (-B ^ (9999 / 10000 : ℝ) / 8) ≤
      Real.log B / B ^ (9999 / 10000 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht _), one_mul, Real.rpow_neg_one] at hsmallB
    calc
      _ = Real.exp (-(1 / 8 : ℝ) * B ^ (9999 / 10000 : ℝ)) := by congr 1; ring
      _ ≤ (B ^ (9999 / 10000 : ℝ))⁻¹ := hsmallB
      _ ≤ _ := by rw [div_eq_mul_inv]; exact le_mul_of_one_le_left (by positivity) hlogB
  have herr := dilation_cutoff_error_bounds B D hBp hlarge hD
  refine ⟨hK.1, hKD, ?_, ?_,
    herr.1.trans (mul_le_mul_of_nonneg_left hsmall' (by norm_num)),
    herr.2.trans (mul_le_mul_of_nonneg_left hsmall' (by norm_num))⟩
  · intro a ha
    have hm := dilation_quotient_log_lower B D a hBp hlarge hD
      (mem_Icc.mp ha).1 (mem_Icc.mp ha).2
    have hex : (10 : ℝ) ≤ (D / a + 1 : ℕ) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 10)]
      apply (Real.exp_le_exp.mpr (show Real.log 10 ≤ Real.log (D / a + 1 : ℕ) by linarith)).trans_eq
      exact Real.exp_log (by positivity)
    exact_mod_cast hex
  · intro a ha
    exact quotient_log_error_bound B C₀ (D / a + 1) hB hC
      (dilation_quotient_log_lower B D a hBp hlarge hD (mem_Icc.mp ha).1 (mem_Icc.mp ha).2)
      (dilation_quotient_log_upper B C₀ D a hB1 hDpos hDupper)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedMRTScale
namespace OAI

/-! The fixed-scale short-sum input for actual dilated factors. Its constant
is independent of the dilation and of the finite set of changed primes. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem MRTShortExponentialInput.dilated_window_scale
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ),
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) → ∀ α : ℝ,
      (∑ v ∈ range Y, ‖shortWindowSum (fun n => b (q * n)) D α v‖) ≤
        C * D * Y * (Real.log B / B ^ (9999 / 10000 : ℝ)) *
          smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hwindow⟩ := hMRT.dilated_short_sums hfnp hf
  let cE := 2 * (Real.log (C₀ + 1) + 2)
  have hcE : 0 < cE := by
    have hh : 0 ≤ Real.log (C₀ + 1) := Real.log_nonneg (by linarith)
    dsimp [cE]
    linarith
  let C' := 4 * C * (cE + 1) + 6
  refine ⟨C', by dsimp [C']; positivity, ?_⟩
  filter_upwards [eventually_dilationWindowParameters C₀ hC₀,
    eventually_ge_atTop (Real.exp 1)] with B hparams hB
  intro P D hDlo hDhi q hq
  have hp := hparams D hDlo hDhi
  have hBp : 0 < B := (Real.exp_pos 1).trans_le hB
  have hlog : 0 < Real.log B := by
    have hh : 1 ≤ Real.log B := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hB
    linarith
  let e := Real.log B / B ^ (9999 / 10000 : ℝ)
  have he : 0 < e := by dsimp [e]; positivity
  have hDpos : 0 < D := hp.cutoff_pos.trans_le hp.cutoff_le
  have hDr : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hM : 1 ≤ smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) :=
    one_le_smoothReciprocalProduct _ (fun _ hx => Nat.prime_of_mem_primeFactors hx) _ (by norm_num)
  filter_upwards [hwindow P q D (dilationCutoff B) hq hp.cutoff_pos hp.cutoff_le
    hp.quotient_ten (cE * e) (by positivity) hp.quotient_error e he] with Y hY
  intro b hb hbb heq α
  have hraw := hY b hb hbb heq α
  have hcoefficient : 4 * C * (cE * e + e) +
      2 * (dilationCutoff B : ℝ) ^ (-(1 / 2) : ℝ) ≤
      (4 * C * (cE + 1) + 4) * e := by
    have ht : (dilationCutoff B : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 * e := hp.cutoff_tail
    nlinarith
  have hK : (dilationCutoff B : ℝ) ≤ 2 * e * D :=
    (div_le_iff₀ hDr).mp hp.cutoff_relative
  have hboundary : (dilationCutoff B : ℝ) * Y ≤
      2 * D * Y * e * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
    calc
      _ ≤ (2 * e * D) * Y := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg Y)
      _ = 2 * D * Y * e := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hM
  apply hraw.trans
  calc
    _ ≤ (D : ℝ) * Y * ((4 * C * (cE + 1) + 4) * e *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)) +
        2 * D * Y * e * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
      apply add_le_add _ hboundary
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hcoefficient (by linarith)
    _ = _ := by dsimp [C', e]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedForwardWindows
namespace OAI

/-! Positive-origin Fourier windows for the exact dilated sequence. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


theorem MRTShortExponentialInput.dilated_forward_windows_oai
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ) (D : ℕ),
      (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D →
      (D : ℝ) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ q : ℕ, 0 < q → ∀ᶠ Y : ℕ in atTop,
      ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
      ∀ θ : AddCircle (1 : ℝ),
      (∑ v ∈ range Y, ‖forwardWindowPolynomial (fun n => b (q * n)) D (v + 1) θ‖) ≤
        C * D * Y * (Real.log B / B ^ (9999 / 10000 : ℝ)) *
          smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hwindow⟩ := hMRT.dilated_window_scale hfnp hf C₀ hC₀
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hwindow, eventually_ge_atTop 1] with B hB hB1
  intro P D hDlo hDhi q hq
  have ht : Tendsto (fun Y : ℕ => Y + 1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [ht.eventually (hB P D hDlo hDhi q hq),
    eventually_ge_atTop 1] with Y hY hY1
  intro b hb hbb heq θ
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective θ
  simp only [forwardWindowPolynomial_at_real]
  have hs : (∑ v ∈ range Y, ‖shortWindowSum (fun n => b (q * n)) D α (v + 1)‖) ≤
      ∑ v ∈ range (Y + 1), ‖shortWindowSum (fun n => b (q * n)) D α v‖ := by
    rw [sum_range_succ']
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hYr : ((Y + 1 : ℕ) : ℝ) ≤ 2 * Y := by exact_mod_cast (show Y + 1 ≤ 2 * Y by omega)
  have hM := smoothReciprocalProduct_nonneg q.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp) (1 / 2) (by norm_num)
  have hE : 0 ≤ Real.log B / B ^ (9999 / 10000 : ℝ) :=
    div_nonneg (Real.log_nonneg hB1) (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ _ := hs
    _ ≤ C * D * (Y + 1 : ℕ) * (Real.log B / B ^ (9999 / 10000 : ℝ)) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := hY b hb hbb heq α
    _ ≤ C * D * (2 * Y) * (Real.log B / B ^ (9999 / 10000 : ℝ)) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.MRTShortExponentialInput.dilated_forward_windows_oai := @OAI.TwoPointCorrelations.MRTShortExponentialInput.dilated_forward_windows_oai
