-- Prove2me | solution 1 for OAI.TwoPointCorrelations.sieve_goldbach_pairs_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:42:56.116967+00:00
-- url     : https://prove2.me/submissions/9a51cfe2-9edf-4443-a6c7-ceeaf07ae11b

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_Problem337_GoldbachSelberg_primePairs_le_primorial

section
-- module Solutions.OAIChowla.OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds
namespace OAI
noncomputable section

open scoped _root_.BigOperators

namespace Problem337


instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩







end Problem337

end

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.EgyptianFractions.SelbergOptimal
namespace OAI
noncomputable section

open scoped _root_.BigOperators _root_.ArithmeticFunction.Moebius
open _root_.Finset _root_.ArithmeticFunction

namespace Problem337.SelbergOptimal






theorem normalizer_pos (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    0 < normalizer s z := by
  apply Finset.sum_pos'
  · intro d hd
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)).le
    · exact le_rfl
  · refine ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, s.prodPrimes_ne_zero⟩, ?_⟩
    rw [if_pos hz]
    exact s.selbergTerms_pos (one_dvd _)
















end Problem337.SelbergOptimal

end

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.EgyptianFractions.GoldbachSelbergBound
namespace OAI
noncomputable section
open scoped _root_.BigOperators
open _root_.Finset

namespace Problem337.GoldbachSelberg



theorem normalizer_eq_denominator (N P z : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) :
    SelbergOptimal.normalizer (sieve N P hN hP) z = denominator N P z := by
  unfold SelbergOptimal.normalizer denominator
  apply sum_congr rfl
  intro d hd
  rw [BoundingSieve.selbergTerms_apply]
  rfl

theorem denominator_pos (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    {z : ℕ} (hz : 1 ≤ z) : 0 < denominator N P z := by
  rw [← normalizer_eq_denominator N P z hN hP]
  exact SelbergOptimal.normalizer_pos _ hz




/-- With the primorial cutoff, the denominator is a sum over every squarefree
integer up to the cutoff, not an unspecified subset of them. -/
theorem denominator_primorial (N z : ℕ) :
    denominator N (primorial z) z =
      ∑ d ∈ Icc 1 z, if Squarefree d then
        goldbachSieveDensity N d *
          ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹ else 0 := by
  classical
  unfold denominator
  rw [← sum_filter]
  have hsets : (primorial z).divisors.filter (fun d => d ≤ z) =
      (Icc 1 z).filter Squarefree := by
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, hdz⟩
      exact ⟨⟨Nat.pos_of_mem_divisors hd, hdz⟩,
        (squarefree_primorial z).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)⟩
    · rintro ⟨⟨hdpos, hdz⟩, hsq⟩
      exact ⟨Nat.mem_divisors.mpr
        ⟨hsq.dvd_primorial.trans (primorial_dvd_primorial hdz),
          primorial_ne_zero z⟩, hdz⟩
  rw [hsets, sum_filter]


end Problem337.GoldbachSelberg

end

end OAI

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveEulerTruncation
namespace OAI

/-! A finite Euler product retains at least half its mass below a cutoff
whenever its logarithmic moment is at most half that cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma sieve_euler_log_moment {ι : Type*} (S : Finset ι) (g ℓ : ι → ℝ)
    (hg : ∀ p ∈ S, 0 ≤ g p) :
    (∑ T ∈ S.powerset, (∏ p ∈ T, g p) * (∑ p ∈ T, ℓ p)) =
      (∏ p ∈ S, (1 + g p)) * (∑ p ∈ S, g p / (1 + g p) * ℓ p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hga : 0 ≤ g a := hg a (mem_insert_self _ _)
    have hgS : ∀ p ∈ S, 0 ≤ g p := fun p hp => hg p (mem_insert_of_mem hp)
    have hne : 1 + g a ≠ 0 := by positivity
    have hn (T : Finset ι) (hT : T ∈ S.powerset) : a ∉ T :=
      fun h => ha ((mem_powerset.mp hT) h)
    have hins :
        (∑ T ∈ S.powerset, (∏ p ∈ insert a T, g p) * (∑ p ∈ insert a T, ℓ p)) =
          g a * ℓ a * (∏ p ∈ S, (1 + g p)) +
            g a * ((∏ p ∈ S, (1 + g p)) * (∑ p ∈ S, g p / (1 + g p) * ℓ p)) := by
      calc
        _ = ∑ T ∈ S.powerset,
            (g a * ℓ a * (∏ p ∈ T, g p) + g a * ((∏ p ∈ T, g p) * (∑ p ∈ T, ℓ p))) := by
          apply sum_congr rfl
          intro T hT
          rw [prod_insert (hn T hT), sum_insert (hn T hT)]
          ring
        _ = _ := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← prod_one_add, ih hgS]
    rw [sum_powerset_insert ha, hins, ih hgS, prod_insert ha, sum_insert ha]
    field_simp
    ring

lemma sieve_euler_truncation {ι : Type*} (S : Finset ι) (g ℓ : ι → ℝ)
    (hg : ∀ p ∈ S, 0 ≤ g p) (hℓ : ∀ p ∈ S, 0 ≤ ℓ p)
    {L : ℝ} (hL : 0 < L)
    (hmean : (∑ p ∈ S, g p / (1 + g p) * ℓ p) ≤ L / 2) :
    (∏ p ∈ S, (1 + g p)) / 2 ≤
      ∑ T ∈ S.powerset with (∑ p ∈ T, ℓ p) ≤ L, ∏ p ∈ T, g p := by
  classical
  let Z := ∏ p ∈ S, (1 + g p)
  have hZ : 0 ≤ Z := prod_nonneg (fun p hp => by linarith [hg p hp])
  have hweight (T : Finset ι) (hT : T ∈ S.powerset) : 0 ≤ ∏ p ∈ T, g p :=
    prod_nonneg (fun p hp => hg p (mem_powerset.mp hT hp))
  have hcost (T : Finset ι) (hT : T ∈ S.powerset) : 0 ≤ ∑ p ∈ T, ℓ p :=
    sum_nonneg (fun p hp => hℓ p (mem_powerset.mp hT hp))
  have htail :
      L * (∑ T ∈ S.powerset with ¬ (∑ p ∈ T, ℓ p) ≤ L, ∏ p ∈ T, g p) ≤
        ∑ T ∈ S.powerset, (∏ p ∈ T, g p) * (∑ p ∈ T, ℓ p) := by
    rw [sum_filter, mul_sum]
    apply sum_le_sum
    intro T hT
    split_ifs with h
    · simpa using mul_nonneg (hweight T hT) (hcost T hT)
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (hweight T hT)
  rw [sieve_euler_log_moment S g ℓ hg] at htail
  have hm := mul_le_mul_of_nonneg_left hmean hZ
  have htotal := sum_filter_add_sum_filter_not S.powerset
    (fun T => (∑ p ∈ T, ℓ p) ≤ L) (fun T => ∏ p ∈ T, g p)
  rw [← prod_one_add] at htotal
  dsimp [Z] at hZ hm
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveGoldbachLocal
namespace OAI

/-! The positive Euler factors of the actual binary Goldbach sieve. -/

namespace TwoPointCorrelations

open _root_.Finset
open _root_.OAI.Problem337 hiding goldbachSieveRootFintype goldbachSieveRootLCMEmbedding goldbachSieveRootNonempty
open scoped _root_.Classical


lemma sieve_goldbach_density_lt_one {N p : ℕ} (hN : 2 ∣ N) (hp : p.Prime) :
    goldbachSieveDensity N p < 1 :=
  goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN)

lemma sieve_goldbach_weight_pos {N p : ℕ} (hN : 2 ∣ N) (hp : p.Prime) :
    0 < sieveGoldbachWeight N p :=
  div_pos (goldbachSieveDensity_prime_pos N p hp)
    (sub_pos.mpr (sieve_goldbach_density_lt_one hN hp))

lemma sieve_goldbach_one_add {N p : ℕ} (hN : 2 ∣ N) (hp : p.Prime) :
    1 + sieveGoldbachWeight N p = (1 - goldbachSieveDensity N p)⁻¹ := by
  have h := ne_of_gt (sub_pos.mpr (sieve_goldbach_density_lt_one hN hp))
  unfold sieveGoldbachWeight
  field_simp
  ring

lemma sieve_goldbach_normalized {N p : ℕ} (hN : 2 ∣ N) (hp : p.Prime) :
    sieveGoldbachWeight N p / (1 + sieveGoldbachWeight N p) =
      goldbachSieveDensity N p := by
  have h := ne_of_gt (sub_pos.mpr (sieve_goldbach_density_lt_one hN hp))
  rw [sieve_goldbach_one_add hN hp]
  unfold sieveGoldbachWeight
  field_simp

lemma sieve_goldbach_mean_le {N : ℕ} (hN : 2 ∣ N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, sieveGoldbachWeight N p / (1 + sieveGoldbachWeight N p) * Real.log p) ≤
      2 * (∑ p ∈ P, Real.log (p : ℝ) / p) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  rw [sieve_goldbach_normalized hN (hP p hp), goldbachSieveDensity_prime N p (hP p hp)]
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)
  split_ifs <;> simp only [div_eq_mul_inv] <;>
    nlinarith [mul_nonneg (inv_nonneg.mpr hpR.le) hlog]

lemma sieve_goldbach_factor_ge {N p : ℕ} (hN : 2 ∣ N) (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ ^ 2 * (if p ∣ N then 1 - 1 / (p : ℝ) else 1) ≤
      1 + sieveGoldbachWeight N p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [sieve_goldbach_one_add hN hp, goldbachSieveDensity_prime N p hp]
  by_cases hdiv : p ∣ N
  · simp only [hdiv, ite_true]
    field_simp
    nlinarith
  · have hp2 : (2 : ℝ) < p := by
      have h : 2 < p := by
        have := hp.two_le
        by_contra hc
        have he : p = 2 := by omega
        exact hdiv (he ▸ hN)
      exact_mod_cast h
    have hp2ne : (p : ℝ) - 2 ≠ 0 := by linarith
    simp only [hdiv, ite_false, mul_one]
    have he : (1 - 1 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
      field_simp
    have hd : (1 - 2 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 2) := by
      field_simp
    rw [he, hd, div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : (0 : ℝ) < p - 1))
      (by linarith : (0 : ℝ) < p - 2)).mpr
    nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SievePrimeSubsets
namespace OAI

/-! Products of prime subsets realize distinct terms of the finite sieve denominator. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.OAI.Problem337
open scoped _root_.Classical

lemma sieve_prime_subset_squarefree (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Squarefree (∏ p ∈ P, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  · exact fun p hp => (hP p hp).squarefree

lemma sieve_prime_subset_injective (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (↑P.powerset : Set (Finset ℕ)) := by
  intro S hS T hT hprod
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => hP p (mem_powerset.mp hS hp)
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_powerset.mp hT hp)
  calc
    S = (∏ p ∈ S, p).primeFactors := (Nat.primeFactors_prod hSp).symm
    _ = (∏ p ∈ T, p).primeFactors := congrArg Nat.primeFactors hprod
    _ = T := Nat.primeFactors_prod hTp

lemma sieve_prime_subset_weight (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    goldbachSieveDensity N (∏ p ∈ P, p) *
      (∏ p ∈ (∏ p ∈ P, p).primeFactors, (1 - goldbachSieveDensity N p)⁻¹) =
      ∏ p ∈ P, sieveGoldbachWeight N p := by
  rw [(goldbachSieveDensity_isMultiplicative N).map_prod_of_prime P hP,
    Nat.primeFactors_prod hP, ← prod_mul_distrib]
  rfl

lemma sieve_prime_subset_log (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.log (∏ p ∈ P, (p : ℝ)) = ∑ p ∈ P, Real.log p := by
  apply Real.log_prod
  intro p hp
  exact_mod_cast (hP p hp).ne_zero

/-- A truncated prime-subset Euler product is a genuine subsum of the actual
Goldbach denominator. -/
theorem sieve_prime_subset_denominator (N z : ℕ) (hN : 2 ∣ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ T ∈ P.powerset with (∏ p ∈ T, p) ≤ z, ∏ p ∈ T, sieveGoldbachWeight N p) ≤
      GoldbachSelberg.denominator N (primorial z) z := by
  let A := P.powerset.filter (fun T => (∏ p ∈ T, p) ≤ z)
  let w := fun d : ℕ => goldbachSieveDensity N d *
    ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹
  have hinj := (sieve_prime_subset_injective P hP).mono (show (↑A : Set (Finset ℕ)) ⊆ ↑P.powerset by
    intro T hT
    exact (mem_filter.mp hT).1)
  have himg : A.image (fun T => ∏ p ∈ T, p) ⊆ (Icc 1 z).filter Squarefree := by
    intro d hd
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hd
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_powerset.mp (mem_filter.mp hT).1 hp)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.succ_le_of_lt
      (prod_pos (fun p hp => (hTp p hp).pos)), (mem_filter.mp hT).2⟩,
      sieve_prime_subset_squarefree T hTp⟩
  have hnonneg (d : ℕ) (_hd : d ∈ (Icc 1 z).filter Squarefree) : 0 ≤ w d := by
    have hroot : 0 ≤ goldbachSieveDensity N d := by
      rw [goldbachSieveDensity_apply]
      positivity
    apply mul_nonneg hroot
    apply prod_nonneg
    intro p hp
    exact inv_nonneg.mpr (sub_nonneg.mpr (sieve_goldbach_density_lt_one hN
      (Nat.mem_primeFactors.mp hp).1).le)
  calc
    _ = ∑ T ∈ A, w (∏ p ∈ T, p) := by
      apply sum_congr rfl
      intro T hT
      exact (sieve_prime_subset_weight N T
        (fun p hp => hP p (mem_powerset.mp (mem_filter.mp hT).1 hp))).symm
    _ = ∑ d ∈ A.image (fun T => ∏ p ∈ T, p), w d := (sum_image hinj).symm
    _ ≤ ∑ d ∈ (Icc 1 z).filter Squarefree, w d :=
      sum_le_sum_of_subset_of_nonneg himg (fun d hd _ => hnonneg d hd)
    _ = _ := by rw [GoldbachSelberg.denominator_primorial, sum_filter]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MertensScale
namespace OAI

/-! The exact classical reciprocal-prime input and its sole required scale.

Published source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for
some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94,
Theorem 5, (3.17)–(3.18), bounded-error consequence of Mertens' second
theorem. DOI: https://doi.org/10.1215/ijm/1255631807.
The formal proof uses the bounded-error statement
`RS_prime.mertens_second_theorem'`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma sievePrimesUpTo_prime (y : ℝ) (p : ℕ) (hp : p ∈ sievePrimesUpTo y) :
    Nat.Prime p := (mem_filter.mp hp).2




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]



theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring







theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]


lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply Real.log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩





lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! (preTransparency := .instances) this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top


private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)


private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! (preTransparency := .instances) MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! (preTransparency := .instances) HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp





section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end











theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply Real.log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind



theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply Real.log_pos; norm_num
        linarith [E₁.nonneg]




























end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem
namespace OAI

/-! Mertens' second theorem in bounded-error form.

The formal proof uses `Erdos970.Mertens.sum_prime_div_eq_log_log`.
Only the convention for the finite prime set differs from
`PrimeReciprocalInput`; zero contributes no prime to either convention.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma sievePrimesUpTo_eq_Ioc (x : ℝ) :
    sievePrimesUpTo x = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [sievePrimesUpTo, mem_filter, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨hp, hprime⟩
    exact ⟨⟨hprime.pos, hp⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨hp, hprime⟩

/-- Mertens' second theorem implies the reciprocal-prime estimate. -/
theorem primeReciprocalInput : PrimeReciprocalInput := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun x hx => ?_⟩
  rw [sievePrimesUpTo_eq_Ioc]
  exact hC x hx

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveEulerLower
namespace OAI

/-! The required logarithmic Euler-product lower bound and singular factor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma sieve_euler_base_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [sub_pos, div_lt_one (by positivity)]
  exact hpR

lemma sieve_euler_factor_pos {p : ℕ} (hp : p.Prime) : 0 < sieveEulerFactor p :=
  inv_pos.mpr (sieve_euler_base_pos hp)


lemma sieve_euler_factor_exp {p : ℕ} (hp : p.Prime) :
    Real.exp (1 / (p : ℝ)) ≤ sieveEulerFactor p := by
  apply (Real.le_log_iff_exp_le (sieve_euler_factor_pos hp)).mp
  rw [sieveEulerFactor, Real.log_inv]
  linarith [Real.log_le_sub_one_of_pos (sieve_euler_base_pos hp)]

lemma sieve_euler_product_exp (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.exp (∑ p ∈ P, 1 / (p : ℝ)) ≤ ∏ p ∈ P, sieveEulerFactor p := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
    (fun p hp => sieve_euler_factor_exp (hP p hp))

lemma sieve_euler_product_log_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ℝ, 2 ≤ y →
      c * Real.log y ≤ ∏ p ∈ sievePrimesUpTo y, sieveEulerFactor p := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  refine ⟨Real.exp (-C), Real.exp_pos _, ?_⟩
  intro y hy
  have hy1 : 1 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy1
  have hsum : Real.log (Real.log y) - C ≤ ∑ p ∈ sievePrimesUpTo y, 1 / (p : ℝ) := by
    linarith [(abs_le.mp (hC y hy)).1]
  calc
    Real.exp (-C) * Real.log y = Real.exp (Real.log (Real.log y) - C) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hlog]
      ring
    _ ≤ Real.exp (∑ p ∈ sievePrimesUpTo y, 1 / (p : ℝ)) := Real.exp_le_exp.mpr hsum
    _ ≤ _ := sieve_euler_product_exp _ (sievePrimesUpTo_prime y)

lemma sieve_singular_factor_pos (N : ℕ) : 0 < sieveSingularFactor N := by
  apply prod_pos
  intro p hp
  exact sieve_euler_factor_pos (Nat.mem_primeFactors.mp hp).1


lemma sieve_singular_correction_le {N : ℕ} (hN : N ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (sieveSingularFactor N)⁻¹ ≤ ∏ p ∈ P, (if p ∣ N then 1 - 1 / (p : ℝ) else 1) := by
  have hsub : P.filter (fun p => p ∣ N) ⊆ N.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hP p (mem_filter.mp hp).1, (mem_filter.mp hp).2, hN⟩
  have he := Finset.prod_le_prod_of_subset_of_le_one (f := fun p : ℕ => 1 - 1 / (p : ℝ)) hsub
    (fun p hp => (sieve_euler_base_pos (Nat.mem_primeFactors.mp hp).1).le)
    (fun p _ _ => by
      have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith)
  simpa only [sieveSingularFactor, sieveEulerFactor, ← prod_inv_distrib, inv_inv, prod_filter] using he

lemma sieve_goldbach_product_lower {N : ℕ} (hN : 2 ∣ N) (hN0 : N ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, sieveEulerFactor p) ^ 2 / sieveSingularFactor N ≤
      ∏ p ∈ P, (1 + sieveGoldbachWeight N p) := by
  have hnonneg : 0 ≤ (∏ p ∈ P, sieveEulerFactor p) ^ 2 := sq_nonneg _
  calc
    _ ≤ (∏ p ∈ P, sieveEulerFactor p) ^ 2 *
        (∏ p ∈ P, (if p ∣ N then 1 - 1 / (p : ℝ) else 1)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (sieve_singular_correction_le hN0 P hP) hnonneg
    _ = ∏ p ∈ P, (sieveEulerFactor p ^ 2 * (if p ∣ N then 1 - 1 / (p : ℝ) else 1)) := by
      rw [prod_mul_distrib, prod_pow]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro p hp
        apply mul_nonneg (sq_nonneg _)
        split_ifs
        · exact (sieve_euler_base_pos (hP p hp)).le
        · norm_num
      · exact fun p hp => sieve_goldbach_factor_ge hN (hP p hp)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass
namespace OAI

/-! Mertens' first theorem, in the prime-band convention needed for the
small- and large-prime truncations in the Halasz convolution. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halaszMertensConstant_nonneg : 0 ≤ halaszMertensConstant := by
  unfold halaszMertensConstant
  positivity

lemma halasz_prime_prefix_mass {x : ℝ} (hx : 1 ≤ x) :
    |(∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) - Real.log x| ≤
      halaszMertensConstant := by
  rw [sievePrimesUpTo_eq_Ioc]
  exact Erdos970.Mertens.sum_log_prime_div_eq_log hx



lemma halasz_prime_prefix_mass_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) ≤
      Real.log x + halaszMertensConstant := by
  linarith [(abs_le.mp (halasz_prime_prefix_mass hx)).2]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveGoldbachTruncation
namespace OAI

/-! The logarithmic-moment criterion applied to the actual Goldbach sieve. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.OAI.Problem337
open scoped _root_.Classical

lemma sieve_prime_subset_log_cutoff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {z : ℕ} (hz : 0 < z) :
    (∑ p ∈ P, Real.log p) ≤ Real.log z ↔ (∏ p ∈ P, p) ≤ z := by
  have hp : 0 < ∏ p ∈ P, (p : ℝ) :=
    prod_pos (fun p hp => by exact_mod_cast (hP p hp).pos)
  rw [← sieve_prime_subset_log P hP, Real.log_le_log_iff hp (by exact_mod_cast hz)]
  rw [← Nat.cast_prod]
  exact Nat.cast_le

theorem sieve_goldbach_denominator_half_product (N z : ℕ) (hN : 2 ∣ N) (hz : 2 ≤ z)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hmean : 2 * (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ Real.log z / 2) :
    (∏ p ∈ P, (1 + sieveGoldbachWeight N p)) / 2 ≤
      GoldbachSelberg.denominator N (primorial z) z := by
  have hz0 : (0 : ℝ) < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have he := sieve_euler_truncation P (sieveGoldbachWeight N) (fun p => Real.log p)
    (fun p hp => (sieve_goldbach_weight_pos hN (hP p hp)).le)
    (fun p hp => Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) hz0
    ((sieve_goldbach_mean_le hN P hP).trans hmean)
  have hsets : P.powerset.filter (fun T : Finset ℕ => (∑ p ∈ T, Real.log (p : ℝ)) ≤ Real.log z) =
      P.powerset.filter (fun T => (∏ p ∈ T, p) ≤ z) := by
    ext T
    simp only [mem_filter]
    constructor
    · rintro ⟨hT, h⟩
      exact ⟨hT, (sieve_prime_subset_log_cutoff T
        (fun p hp => hP p (mem_powerset.mp hT hp)) (by omega)).mp h⟩
    · rintro ⟨hT, h⟩
      exact ⟨hT, (sieve_prime_subset_log_cutoff T
        (fun p hp => hP p (mem_powerset.mp hT hp)) (by omega)).mpr h⟩
  rw [hsets] at he
  exact he.trans (sieve_prime_subset_denominator N z hN P hP)

/-- The small-prime cutoff is chosen using a logarithmic inequality, avoiding
any rounding assumption on its real value. -/
theorem sieve_goldbach_denominator_small_primes (N z : ℕ) (hN : 2 ∣ N) (hz : 2 ≤ z)
    {y : ℝ} (hy : 1 ≤ y)
    (hscale : 4 * (Real.log y + halaszMertensConstant) ≤ Real.log z) :
    (∏ p ∈ sievePrimesUpTo y, (1 + sieveGoldbachWeight N p)) / 2 ≤
      GoldbachSelberg.denominator N (primorial z) z := by
  apply sieve_goldbach_denominator_half_product N z hN hz (sievePrimesUpTo y)
    (sievePrimesUpTo_prime y)
  linarith [halasz_prime_prefix_mass_le hy]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveGoldbachDenominator
namespace OAI

/-! The dimension-two denominator bound for the finite Goldbach sieve. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.OAI.Problem337
open scoped _root_.Classical

lemma sieve_goldbach_denominator_two_scale :
    ∃ c : ℝ, 0 < c ∧ ∀ N z : ℕ, 2 ∣ N → N ≠ 0 → 2 ≤ z →
      ∀ y : ℝ, 2 ≤ y →
      4 * (Real.log y + halaszMertensConstant) ≤ Real.log z →
      c * Real.log y ^ 2 / sieveSingularFactor N ≤
        GoldbachSelberg.denominator N (primorial z) z := by
  obtain ⟨c, hc, hEuler⟩ := sieve_euler_product_log_lower
  refine ⟨c ^ 2 / 2, by positivity, ?_⟩
  intro N z hN hN0 hz y hy hscale
  have hylog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have he := pow_le_pow_left₀ (mul_nonneg hc.le hylog) (hEuler y hy) 2
  have hprod := sieve_goldbach_product_lower hN hN0 (sievePrimesUpTo y) (sievePrimesUpTo_prime y)
  have hden := sieve_goldbach_denominator_small_primes N z hN hz (by linarith) hscale
  have hS := sieve_singular_factor_pos N
  have hdiv := div_le_div_of_nonneg_right he hS.le
  calc
    _ = (c * Real.log y) ^ 2 / sieveSingularFactor N / 2 := by ring
    _ ≤ (∏ p ∈ sievePrimesUpTo y, sieveEulerFactor p) ^ 2 / sieveSingularFactor N / 2 := by
      linarith
    _ ≤ (∏ p ∈ sievePrimesUpTo y, (1 + sieveGoldbachWeight N p)) / 2 := by linarith
    _ ≤ _ := hden

/-- A single explicit logarithmic lower threshold gives the usual
`log(z)^2 / singularFactor(N)` denominator. -/
theorem sieve_goldbach_denominator_log_square :
    ∃ c : ℝ, 0 < c ∧ ∀ N z : ℕ, 2 ∣ N → N ≠ 0 → 2 ≤ z →
      8 * (halaszMertensConstant + Real.log 2) ≤ Real.log z →
      c * Real.log z ^ 2 / sieveSingularFactor N ≤
        GoldbachSelberg.denominator N (primorial z) z := by
  obtain ⟨c, hc, hden⟩ := sieve_goldbach_denominator_two_scale
  refine ⟨c / 64, by positivity, ?_⟩
  intro N z hN hN0 hz hscale
  let y := Real.exp (Real.log z / 8)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hy : 2 ≤ y := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    linarith [halaszMertensConstant_nonneg]
  have hylog : Real.log y = Real.log z / 8 := Real.log_exp _
  have ht : 4 * (Real.log y + halaszMertensConstant) ≤ Real.log z := by
    rw [hylog]
    linarith
  have he := hden N z hN hN0 hz y hy ht
  rw [hylog] at he
  convert (preTransparency := .instances) he using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveGoldbachPairs
namespace OAI

/-! The finite Goldbach upper bound with its denominator evaluated. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.OAI.Problem337
open scoped _root_.Classical

lemma sieve_primesLE_card (z : ℕ) : (Nat.primesLE z).card ≤ z := by
  have hs : Nat.primesLE z ⊆ Icc 1 z := by
    intro p hp
    exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).pos, Nat.le_of_mem_primesLE hp⟩
  simpa using card_le_card hs

theorem sieve_goldbach_pairs_finite_oai :
    ∃ C : ℝ, 0 < C ∧ ∀ N z : ℕ, 2 ∣ N → N ≠ 0 → 2 ≤ z →
      8 * (halaszMertensConstant + Real.log 2) ≤ Real.log z →
      ((PrimePairSieve.primePairs N).card : ℝ) ≤
        C * N * sieveSingularFactor N / Real.log z ^ 2 +
          (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * z := by
  obtain ⟨c, hc, hden⟩ := sieve_goldbach_denominator_log_square
  refine ⟨1 / c, by positivity, ?_⟩
  intro N z hN hN0 hz hscale
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hS := sieve_singular_factor_pos N
  have hd := hden N z hN hN0 hz hscale
  have hmain : ((N - 1 : ℕ) : ℝ) / GoldbachSelberg.denominator N (primorial z) z ≤
      (1 / c) * N * sieveSingularFactor N / Real.log z ^ 2 := by
    calc
      _ ≤ (N : ℝ) / GoldbachSelberg.denominator N (primorial z) z := by
        apply div_le_div_of_nonneg_right _ (GoldbachSelberg.denominator_pos N (primorial z)
          hN (squarefree_primorial z) (by omega)).le
        exact_mod_cast Nat.sub_le N 1
      _ ≤ (N : ℝ) / (c * Real.log z ^ 2 / sieveSingularFactor N) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) hd
      _ = _ := by field_simp
  have hp := GoldbachSelberg.primePairs_le_primorial N hN (z := z) (by omega)
  have hcard : ((Nat.primesLE z).card : ℝ) ≤ z := by exact_mod_cast sieve_primesLE_card z
  linarith

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.sieve_goldbach_pairs_finite_oai := @OAI.TwoPointCorrelations.sieve_goldbach_pairs_finite_oai
