-- Prove2me | solution 1 for OAI.Erdos3.selectedResidueDensityPMF_stride_quantitative_badPrimeProduct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T07:02:03.638073+00:00
-- url     : https://prove2.me/submissions/b5b37d8e-3025-482f-bb7d-324d692de4f2

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B049

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eventProbability_false {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) (hE : ∀ x, ¬ E x) : p.eventProbability E = 0 := by
  classical
  simp only [eventProbability, hE, ite_false]
  exact p.mean_const 0

theorem eventProbability_mono {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E F : Ω → Prop) (hEF : ∀ x, E x → F x) : p.eventProbability E ≤ p.eventProbability F := by
  classical
  apply p.mean_mono
  intro x
  by_cases hE : E x
  · simp [hE, hEF x hE]
  · simp only [hE, ite_false]
    split_ifs <;> norm_num

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteEventUnion
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

theorem eventProbability_or_le {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (E F : Ω → Prop) :
    p.eventProbability (fun x => E x ∨ F x) ≤ p.eventProbability E + p.eventProbability F := by
  classical
  unfold eventProbability
  calc
    _ ≤ p.mean (fun x => (if E x then 1 else 0) + (if F x then 1 else 0)) := by
      apply p.mean_mono
      intro x
      by_cases hE : E x <;> by_cases hF : F x <;> simp [hE, hF]
    _ = _ := p.mean_add _ _

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductWitness
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_bounded_subproduct {I : Type*} (S : Finset I) (f : I → ℕ) {R : ℕ}
    (hR : 1 ≤ R) (hf : ∀ i ∈ S, f i ≤ R) (hprod : R < ∏ i ∈ S, f i) :
    ∃ T ⊆ S, R < ∏ i ∈ T, f i ∧ (∏ i ∈ T, f i) ≤ R ^ 2 := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, not_lt_of_ge hR] at hprod
  | @insert i S hi ih =>
    by_cases htail : R < ∏ j ∈ S, f j
    · obtain ⟨T, hT, hlo, hhi⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) htail
      exact ⟨T, hT.trans (Finset.subset_insert _ _), hlo, hhi⟩
    · refine ⟨insert i S, Finset.Subset.refl _, hprod, ?_⟩
      rw [Finset.prod_insert hi, pow_two]
      exact Nat.mul_le_mul (hf i (Finset.mem_insert_self _ _)) (Nat.le_of_not_gt htail)

theorem finite_product_witness {I : Type*} (S : Finset I) (f : I → ℕ) {R : ℕ}
    (hR : 1 ≤ R) (hprod : R < ∏ i ∈ S, f i) :
    (∃ i ∈ S, R < f i) ∨
      ∃ T ⊆ S, R < ∏ i ∈ T, f i ∧ (∏ i ∈ T, f i) ≤ R ^ 2 := by
  by_cases hlarge : ∃ i ∈ S, R < f i
  · exact Or.inl hlarge
  · right
    apply exists_bounded_subproduct S f hR _ hprod
    intro i hi
    exact Nat.le_of_not_gt (fun h => hlarge ⟨i, hi, h⟩)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem reciprocal_tenth_le_difference {n : ℕ} (hn : 0 < n) :
    1 / ((n : ℝ) + 1) ^ 10 ≤ 1 / (9 * (n : ℝ) ^ 9) - 1 / (9 * ((n : ℝ) + 1) ^ 9) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  apply (le_sub_iff_add_le).mpr
  have heq : 1 / ((n : ℝ) + 1) ^ 10 + 1 / (9 * ((n : ℝ) + 1) ^ 9) =
      ((n : ℝ) + 10) / (9 * ((n : ℝ) + 1) ^ 10) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hpoly : 0 ≤ ((n : ℝ) + 1) ^ 10 - ((n : ℝ) + 10) * (n : ℝ) ^ 9 := by
    ring_nf
    positivity
  nlinarith only [hpoly]

theorem finite_reciprocal_tenth_tail (S : Finset ℕ) {R : ℕ} (hR : 0 < R)
    (hS : ∀ d ∈ S, R < d) :
    (∑ d ∈ S, 1 / (d : ℝ) ^ 10) ≤ 1 / (9 * (R : ℝ) ^ 9) := by
  let shifted := S.image (fun d => d - 1)
  let B := max R (shifted.sup id + 1)
  have hRB : R ≤ B := Nat.le_max_left _ _
  have hshift : (∑ n ∈ shifted, 1 / ((n : ℝ) + 1) ^ 10) =
      ∑ d ∈ S, 1 / (d : ℝ) ^ 10 := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro d hd
      have heq : d - 1 + 1 = d := by have := hS d hd; omega
      have hreal : ((d - 1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast heq
      rw [hreal]
    · intro d hd e he hde
      change d - 1 = e - 1 at hde
      have := hS d hd
      have := hS e he
      omega
  have hsub : shifted ⊆ Finset.Ico R B := by
    intro n hn
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hn
    have hlo : R ≤ n := by have := hS d hd; omega
    exact Finset.mem_Ico.mpr ⟨hlo,
      (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)).trans_le (Nat.le_max_right _ _)⟩
  have htel : (∑ n ∈ Finset.Ico R B,
      (1 / (9 * (n : ℝ) ^ 9) - 1 / (9 * ((n : ℝ) + 1) ^ 9))) =
      1 / (9 * (R : ℝ) ^ 9) - 1 / (9 * (B : ℝ) ^ 9) := by
    convert Finset.sum_Ico_sub (fun n : ℕ => -(1 / (9 * (n : ℝ) ^ 9))) hRB using 1
    · apply Finset.sum_congr rfl
      intro n _
      push_cast
      ring
    · ring
  rw [← hshift]
  calc
    _ ≤ ∑ n ∈ Finset.Ico R B, 1 / ((n : ℝ) + 1) ^ 10 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ n ∈ Finset.Ico R B,
        (1 / (9 * (n : ℝ) ^ 9) - 1 / (9 * ((n : ℝ) + 1) ^ 9)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact reciprocal_tenth_le_difference (hR.trans_le (Finset.mem_Ico.mp hn).1)
    _ = _ := htel
    _ ≤ _ := sub_le_self _ (by positivity)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LargestBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selected_primePower_factorization (T : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ T, Nat.Prime p) (p : ℕ) :
    (∏ q ∈ T, q ^ a q).factorization p = if p ∈ T then a p else 0 := by
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (hprime q hq).ne_zero)]
  calc
    ∑ q ∈ T, (q ^ a q).factorization p =
        ∑ q ∈ T, if p = q then a q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(hprime q hq).factorization_pow]
      simp only [Finsupp.single_apply, eq_comm]
    _ = _ := by simp

theorem selected_primePower_primeFactors (T : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ T, Nat.Prime p) (ha : ∀ p ∈ T, 0 < a p) :
    (∏ p ∈ T, p ^ a p).primeFactors = T := by
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff,
    selected_primePower_factorization T a hprime]
  by_cases hp : p ∈ T
  · simp only [hp, ↓reduceIte, iff_true]
    exact (ha p hp).ne'
  · simp only [hp, ↓reduceIte, ne_eq, not_true_eq_false]

theorem selected_primePower_factorization_of_mem (T : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ T, Nat.Prime p) {p : ℕ} (hp : p ∈ T) :
    (∏ q ∈ T, q ^ a q).factorization p = a p := by
  rw [selected_primePower_factorization T a hprime, if_pos hp]

theorem selected_primePower_badPrimeModulusEvent {Ω : Type*}
    (S T : Finset ℕ) (A a : ℕ → ℕ) (Qs : ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (x : Ω) (hprime : ∀ p ∈ T, Nat.Prime p) (hTS : T ⊆ S)
    (ha : ∀ p ∈ T, 0 < a p) (hA : ∀ p ∈ T, a p ≤ A p)
    (hQs : ∀ p ∈ T, Qs ≤ p ^ a p) (hbad : ∀ p ∈ T, bad p (a p) x) :
    badPrimeModulusEvent S A Qs bad (∏ p ∈ T, p ^ a p) x := by
  constructor
  · intro p hp
    have hpT : p ∈ T := by rwa [selected_primePower_primeFactors T a hprime ha] at hp
    rw [selected_primePower_factorization_of_mem T a hprime hpT]
    exact ⟨hTS hpT, ha p hpT, hA p hpT, hQs p hpT⟩
  · intro p hp
    have hpT : p ∈ T := by rwa [selected_primePower_primeFactors T a hprime ha] at hp
    rw [selected_primePower_factorization_of_mem T a hprime hpT]
    exact hbad p hpT

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem largestTestedBadDepth_le {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) :
    largestTestedBadDepth A bad p x ≤ A p := by
  exact Finset.sup_le (fun _ ha => (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2)

theorem largestTestedBadDepth_bad {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω)
    (hpos : 0 < largestTestedBadDepth A bad p x) :
    bad p (largestTestedBadDepth A bad p x) x := by
  obtain ⟨a, ha, hle⟩ := (Finset.le_sup_iff hpos).mp
    (le_refl (largestTestedBadDepth A bad p x))
  have hge : a ≤ largestTestedBadDepth A bad p x := Finset.le_sup (f := id) ha
  have heq : a = largestTestedBadDepth A bad p x := le_antisymm hge hle
  exact heq ▸ (Finset.mem_filter.mp ha).2

theorem prime_power_small_correction (S : Finset ℕ) (b : ℕ → ℕ) {Qs : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs) :
    (∏ p ∈ S, p ^ b p) ≤ smallPrimePowerCorrection Qs *
      ∏ p ∈ S, (if Qs ≤ p ^ b p then p ^ b p else 1) := by
  let small := (Finset.range Qs).filter Nat.Prime
  let g := fun p => p ^ Nat.log p (Qs - 1)
  have hg (p) (hp : p.Prime) : 1 ≤ g p := one_le_pow₀ hp.one_le
  have hlocal (p) (hp : p ∈ S) : p ^ b p ≤ g p * (if Qs ≤ p ^ b p then p ^ b p else 1) := by
    by_cases hlarge : Qs ≤ p ^ b p
    · simp only [hlarge, ite_true]
      simpa only [one_mul] using Nat.mul_le_mul_right (p ^ b p) (hg p (hprime p hp))
    · simp only [hlarge, ite_false, mul_one]
      exact Nat.pow_le_pow_right (hprime p hp).pos
        (Nat.le_log_of_pow_le (hprime p hp).one_lt (by omega))
  have hout (p) (hp : p ∈ S ∪ small) (hnot : p ∉ small) : g p = 1 := by
    have hpp : p.Prime := by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hprime p hp
      · exact (Finset.mem_filter.mp hp).2
    have hcut : Qs ≤ p := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩)
    dsimp only [g]
    rw [Nat.log_eq_zero_iff.mpr (Or.inl (by omega)), pow_zero]
  have hbase : (∏ p ∈ S, g p) ≤ smallPrimePowerCorrection Qs := by
    calc
      _ ≤ ∏ p ∈ S ∪ small, g p :=
        Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left (fun p hp _ => by
          apply hg
          rcases Finset.mem_union.mp hp with hp | hp
          · exact hprime p hp
          · exact (Finset.mem_filter.mp hp).2)
      _ = ∏ p ∈ small, g p := (Finset.prod_subset Finset.subset_union_right hout).symm
      _ = _ := rfl
  calc
    _ ≤ ∏ p ∈ S, g p * (if Qs ≤ p ^ b p then p ^ b p else 1) :=
      Finset.prod_le_prod' hlocal
    _ = (∏ p ∈ S, g p) * ∏ p ∈ S, (if Qs ≤ p ^ b p then p ^ b p else 1) :=
      Finset.prod_mul_distrib
    _ ≤ _ := Nat.mul_le_mul_right _ hbase

theorem largestBadPrime_large_valid {Ω : Type*} (S : Finset ℕ) (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (x : Ω) {Qs p : ℕ} (hQs : 2 ≤ Qs)
    (_hp : p ∈ S) (hlarge : Qs ≤ p ^ largestTestedBadDepth A bad p x) :
    0 < largestTestedBadDepth A bad p x ∧
      largestTestedBadDepth A bad p x ≤ A p ∧
      bad p (largestTestedBadDepth A bad p x) x := by
  have hb : 0 < largestTestedBadDepth A bad p x := by
    by_contra hn
    have heq : largestTestedBadDepth A bad p x = 0 := by omega
    simp only [heq, pow_zero] at hlarge
    omega
  exact ⟨hb, largestTestedBadDepth_le A bad p x, largestTestedBadDepth_bad A bad p x hb⟩

theorem largestBadPrime_subproduct_modulus_event {Ω : Type*}
    (S T : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (x : Ω) {Qs : ℕ} (hQs : 2 ≤ Qs) (hprime : ∀ p ∈ S, p.Prime) (hTS : T ⊆ S) :
    badPrimeModulusEvent S A Qs bad
      (∏ p ∈ T, if Qs ≤ p ^ largestTestedBadDepth A bad p x then
        p ^ largestTestedBadDepth A bad p x else 1) x := by
  let U := T.filter (fun p => Qs ≤ p ^ largestTestedBadDepth A bad p x)
  have hUS : U ⊆ S := (Finset.filter_subset _ _).trans hTS
  have hvalid (p) (hp : p ∈ U) := largestBadPrime_large_valid S A bad x hQs
    (hUS hp) (Finset.mem_filter.mp hp).2
  have heq : (∏ p ∈ T, if Qs ≤ p ^ largestTestedBadDepth A bad p x then
      p ^ largestTestedBadDepth A bad p x else 1) =
      ∏ p ∈ U, p ^ largestTestedBadDepth A bad p x := (Finset.prod_filter _ _).symm
  rw [heq]
  exact selected_primePower_badPrimeModulusEvent S U A
    (fun p => largestTestedBadDepth A bad p x) Qs bad x
    (fun p hp => hprime p (hUS hp)) hUS (fun p hp => (hvalid p hp).1)
    (fun p hp => (hvalid p hp).2.1) (fun _ hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => (hvalid p hp).2.2)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProductWitnessProbability
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem finite_witness_probability_tenth_tail {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (E : ℕ → Ω → Prop) {R B : ℕ} (hR : 0 < R)
    {η : ℝ} (hη : 0 ≤ η)
    (hE : ∀ d ∈ Finset.Ioc R B, w.eventProbability (E d) ≤ 1 / (d : ℝ) ^ 10 + η) :
    w.eventProbability (fun x => ∃ d ∈ Finset.Ioc R B, E d x) ≤
      1 / (9 * (R : ℝ) ^ 9) + (B : ℝ) * η := by
  have hunion := w.eventProbability_union_bound
    (fun x => ∃ d ∈ Finset.Ioc R B, E d x)
    (fun (d : Finset.Ioc R B) x => E d.val x)
    (by intro x hx; obtain ⟨d, hd, hdx⟩ := hx; exact ⟨⟨d, hd⟩, hdx⟩)
  have htail := finite_reciprocal_tenth_tail (Finset.Ioc R B) hR
    (fun d hd => (Finset.mem_Ioc.mp hd).1)
  have hcard : ((Finset.Ioc R B).card : ℝ) ≤ B := by
    exact_mod_cast (show (Finset.Ioc R B).card ≤ B by simp)
  calc
    _ ≤ ∑ d : Finset.Ioc R B, (1 / (d.val : ℝ) ^ 10 + η) :=
      hunion.trans (Finset.sum_le_sum (fun d _ => hE d.val d.property))
    _ = (∑ d ∈ Finset.Ioc R B, 1 / (d : ℝ) ^ 10) + ((Finset.Ioc R B).card : ℝ) * η := by
      calc
        _ = ∑ d ∈ Finset.Ioc R B, (1 / (d : ℝ) ^ 10 + η) :=
          Finset.sum_coe_sort (Finset.Ioc R B) (fun d : ℕ => 1 / (d : ℝ) ^ 10 + η)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := add_le_add htail (mul_le_mul_of_nonneg_right hcard hη)

theorem finite_product_witness_probability {Ω I : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (S : Finset I) (f : Ω → I → ℕ)
    (single composite : ℕ → Ω → Prop) {R Q : ℕ} (hR : 0 < R)
    (hQ : ∀ x i, i ∈ S → f x i ≤ Q)
    (hsingle : ∀ x i, i ∈ S → R < f x i → single (f x i) x)
    (hcomposite : ∀ x T, T ⊆ S → R < ∏ i ∈ T, f x i →
      (∏ i ∈ T, f x i) ≤ R ^ 2 → composite (∏ i ∈ T, f x i) x)
    {η : ℝ} (hη : 0 ≤ η)
    (hsingleProb : ∀ d ∈ Finset.Ioc R Q,
      w.eventProbability (single d) ≤ 1 / (d : ℝ) ^ 10 + η)
    (hcompositeProb : ∀ d ∈ Finset.Ioc R (R ^ 2),
      w.eventProbability (composite d) ≤ 1 / (d : ℝ) ^ 10 + η) :
    w.eventProbability (fun x => R < ∏ i ∈ S, f x i) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  let Esingle := fun x => ∃ d ∈ Finset.Ioc R Q, single d x
  let Ecomposite := fun x => ∃ d ∈ Finset.Ioc R (R ^ 2), composite d x
  have hcover (x) (hx : R < ∏ i ∈ S, f x i) : Esingle x ∨ Ecomposite x := by
    obtain h | ⟨T, hT, hlo, hhi⟩ := finite_product_witness S (f x) hR hx
    · obtain ⟨i, hi, hlarge⟩ := h
      exact Or.inl ⟨f x i, Finset.mem_Ioc.mpr ⟨hlarge, hQ x i hi⟩, hsingle x i hi hlarge⟩
    · exact Or.inr ⟨∏ i ∈ T, f x i, Finset.mem_Ioc.mpr ⟨hlo, hhi⟩,
        hcomposite x T hT hlo hhi⟩
  have hsingleTail := finite_witness_probability_tenth_tail w single hR hη hsingleProb
  have hcompositeTail := finite_witness_probability_tenth_tail w composite hR hη hcompositeProb
  calc
    _ ≤ w.eventProbability (fun x => Esingle x ∨ Ecomposite x) :=
      w.eventProbability_mono _ _ hcover
    _ ≤ w.eventProbability Esingle + w.eventProbability Ecomposite :=
      w.eventProbability_or_le Esingle Ecomposite
    _ ≤ (1 / (9 * (R : ℝ) ^ 9) + (Q : ℝ) * η) +
        (1 / (9 * (R : ℝ) ^ 9) + ((R ^ 2 : ℕ) : ℝ) * η) :=
      add_le_add hsingleTail hcompositeTail
    _ = _ := by push_cast; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem badPrimeModulusEvent_probability_bounded {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (S : Finset ℕ) (A : ℕ → ℕ) (Qs B : ℕ)
    (bad : ℕ → ℕ → Ω → Prop) {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
      (∏ p ∈ T, p ^ a p) ≤ B →
      w.eventProbability (fun x => ∀ p ∈ T, bad p (a p) x) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η)
    {d : ℕ} (hd : 0 < d) (hdB : d ≤ B) :
    w.eventProbability (badPrimeModulusEvent S A Qs bad d) ≤ 1 / (d : ℝ) ^ 10 + η := by
  by_cases hvalid : ∀ p ∈ d.primeFactors, p ∈ S ∧ 0 < d.factorization p ∧
      d.factorization p ≤ A p ∧ Qs ≤ p ^ d.factorization p
  · have hprod := Nat.prod_primeFactors_pow_factorization hd.ne'
    have h := hjoint d.primeFactors (fun p hp => (hvalid p hp).1) d.factorization
      (fun p hp => (hvalid p hp).2) (hprod ▸ hdB)
    rw [← hprod] at h
    exact (w.eventProbability_mono _ _ (fun _ hx => hx.2)).trans h
  · rw [w.eventProbability_false _ (fun _ hx => hvalid hx.1)]
    positivity

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem largestBadPrimeProduct_probability_bounded {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (S : Finset ℕ) (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) {Qs Q R : ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs) (hQ : 1 ≤ Q) (hR : 0 < R)
    (hdepth : ∀ p ∈ S, p ^ A p ≤ Q) {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
      (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
      w.eventProbability (fun x => ∀ p ∈ T, bad p (a p) x) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    w.eventProbability (fun x => smallPrimePowerCorrection Qs * R <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  let f := fun x p => if Qs ≤ p ^ largestTestedBadDepth A bad p x then
    p ^ largestTestedBadDepth A bad p x else 1
  let E := badPrimeModulusEvent S A Qs bad
  have hfactor (x p) (hp : p ∈ S) : f x p ≤ Q := by
    dsimp only [f]
    split_ifs
    · exact (Nat.pow_le_pow_right (hprime p hp).pos (largestTestedBadDepth_le A bad p x)).trans
        (hdepth p hp)
    · exact hQ
  have hsingle (x p) (hp : p ∈ S) (_hlarge : R < f x p) : E (f x p) x := by
    simpa only [Finset.prod_singleton] using
      largestBadPrime_subproduct_modulus_event S {p} A bad x hQs hprime
        (Finset.singleton_subset_iff.mpr hp)
  have hcomposite (x T) (hTS : T ⊆ S) (_hlo : R < ∏ p ∈ T, f x p)
      (_hhi : (∏ p ∈ T, f x p) ≤ R ^ 2) : E (∏ p ∈ T, f x p) x :=
    largestBadPrime_subproduct_modulus_event S T A bad x hQs hprime hTS
  have hprob (d : ℕ) (hd : R < d) (hdB : d ≤ max Q (R ^ 2)) : w.eventProbability (E d) ≤ 1 / (d : ℝ) ^ 10 + η :=
    badPrimeModulusEvent_probability_bounded w S A Qs (max Q (R ^ 2)) bad hη hjoint (hR.trans hd) hdB
  have hwitness := finite_product_witness_probability w S f E E hR hfactor hsingle hcomposite hη
    (fun _ hd => hprob _ (Finset.mem_Ioc.mp hd).1
      ((Finset.mem_Ioc.mp hd).2.trans (le_max_left _ _)))
    (fun _ hd => hprob _ (Finset.mem_Ioc.mp hd).1
      ((Finset.mem_Ioc.mp hd).2.trans (le_max_right _ _)))
  apply (w.eventProbability_mono _ _ ?_).trans hwitness
  intro x hx
  have hcorrection := prime_power_small_correction S (fun p => largestTestedBadDepth A bad p x) hprime hQs
  change R < ∏ p ∈ S, f x p
  by_contra h
  have hle : (∏ p ∈ S, f x p) ≤ R := Nat.le_of_not_gt h
  have hupper := hcorrection.trans (Nat.mul_le_mul_left (smallPrimePowerCorrection Qs) hle)
  exact (Nat.not_lt_of_ge hupper) hx

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

theorem quantitativeBadPrimeRadius_error {E : ℝ} (hE : 0 ≤ E) (Q : ℕ) (hQ : 1 ≤ Q) :
    let R := quantitativeBadPrimeRadius E
    0 < Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) ∧
    2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) ≤ Real.exp (-E) := by
  dsimp only
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hden : 0 < (Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  have heq : ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2))) =
      Real.exp (-E) / 2 := by field_simp
  rw [heq]
  linarith [(quantitativeBadPrimeRadius_bounds hE).2.2]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)

theorem selectedResidueTiltedFiniteLaw_event (E : (K × I → ℤ) → Prop) :
    (selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD).eventProbability
      (fun x => E x.val) =
      ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if E x then 1 else 0) := by
  exact selectedResidueTiltedFiniteLaw_mean modulus G V hV hZ D hD0 hD
    (fun x => if E x then 1 else 0)

theorem selectedResidueDensityPMF_badPrimeProduct_probability
    (S : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → (K × I → ℤ) → Prop)
    {Qs Q R : ℕ} (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs)
    (hQ : 1 ≤ Q) (hR : 0 < R) (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p) →
      (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if ∀ p ∈ T, bad p (a p) x then 1 else 0)) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if smallPrimePowerCorrection Qs * R <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then 1 else 0)) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  have h := largestBadPrimeProduct_probability_bounded
    (selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD) S A
    (fun p a x => bad p a x.val) hprime hQs hQ hR hdepth hη
    (fun T hT a ha hbound => by
      rw [selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
        (fun x => ∀ p ∈ T, bad p (a p) x)]
      convert hjoint T hT a ha hbound using 1
      apply tsum_congr
      intro x
      by_cases hx : ∀ p ∈ T, bad p (a p) x <;> simp [hx])
  change (selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD).eventProbability
    (fun x => smallPrimePowerCorrection Qs * R <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x.val) ≤ _ at h
  rw [selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
    (fun x => smallPrimePowerCorrection Qs * R <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x)] at h
  convert h using 1
  apply tsum_congr
  intro x
  by_cases hx : smallPrimePowerCorrection Qs * R <
    ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x <;> simp [hx]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem largestTestedBadDepth_le_prescribed_max {Ω : Type*}
    (A b : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) :
    largestTestedBadDepth A bad p x ≤
      max (b p) (largestTestedBadDepth A (prescribedDeepBad b bad) p x) := by
  apply Finset.sup_le
  intro a ha
  obtain ⟨ha, hbad⟩ := Finset.mem_filter.mp ha
  by_cases h : b p < a
  · exact (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨ha, h, hbad⟩)).trans
      (le_max_right _ _)
  · exact (Nat.le_of_not_gt h).trans (le_max_left _ _)

theorem largestBadPrimeProduct_le_prescribed {Ω : Type*}
    (S : Finset ℕ) (A b : ℕ → ℕ) (bad : ℕ → ℕ → Ω → Prop)
    (hprime : ∀ p ∈ S, p.Prime) (x : Ω) :
    (∏ p ∈ S, p ^ largestTestedBadDepth A bad p x) ≤
      (∏ p ∈ S, p ^ b p) *
        ∏ p ∈ S, p ^ largestTestedBadDepth A (prescribedDeepBad b bad) p x := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p hp
  rw [← pow_add]
  exact Nat.pow_le_pow_right (hprime p hp).pos
    ((largestTestedBadDepth_le_prescribed_max A b bad p x).trans (by omega))

theorem selectedResidueDensityPMF_prescribed_badPrimeProduct
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (S : Finset ℕ) (A b : ℕ → ℕ) (bad : ℕ → ℕ → (K × I → ℤ) → Prop)
    {Qs Q R : ℕ} (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs)
    (hQ : 1 ≤ Q) (hR : 0 < R) (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p ∧ b p < a p) →
      (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if ∀ p ∈ T, bad p (a p) x then 1 else 0)) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if (∏ p ∈ S, p ^ b p) * (smallPrimePowerCorrection Qs * R) <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then 1 else 0)) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  let w := selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD
  have ht := selectedResidueDensityPMF_badPrimeProduct_probability modulus G V hV hZ D hD0 hD
    S A (prescribedDeepBad b bad) hprime hQs hQ hR hdepth hη
    (fun T hT a ha hbound => by
      by_cases hb : ∀ p ∈ T, b p < a p
      · have hh := hjoint T hT a (fun p hp => ⟨(ha p hp).1, (ha p hp).2.1,
          (ha p hp).2.2, hb p hp⟩) hbound
        convert hh using 1
        apply tsum_congr
        intro x
        have he : (∀ p ∈ T, prescribedDeepBad b bad p (a p) x) ↔
            ∀ p ∈ T, bad p (a p) x := by
          simp only [prescribedDeepBad]
          exact ⟨fun h p hp => (h p hp).2, fun h p hp => ⟨hb p hp, h p hp⟩⟩
        simp only [he]
      · have he (x : K × I → ℤ) : ¬ ∀ p ∈ T, prescribedDeepBad b bad p (a p) x :=
          fun h => hb (fun p hp => (h p hp).1)
        simp only [he, ite_false, mul_zero, tsum_zero]
        positivity)
  have hmono := w.eventProbability_mono
    (fun x => (∏ p ∈ S, p ^ b p) * (smallPrimePowerCorrection Qs * R) <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x.val)
    (fun x => smallPrimePowerCorrection Qs * R <
      ∏ p ∈ S, p ^ largestTestedBadDepth A (prescribedDeepBad b bad) p x.val)
    (fun x hx => by
      by_contra h
      have hh := Nat.mul_le_mul_left (∏ p ∈ S, p ^ b p) (Nat.le_of_not_gt h)
      exact (not_lt_of_ge ((largestBadPrimeProduct_le_prescribed S A b bad hprime x.val).trans hh)) hx)
  dsimp only [w] at hmono
  rw [selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
    (fun x => (∏ p ∈ S, p ^ b p) * (smallPrimePowerCorrection Qs * R) <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x),
    selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
    (fun x => smallPrimePowerCorrection Qs * R <
      ∏ p ∈ S, p ^ largestTestedBadDepth A (prescribedDeepBad b bad) p x)] at hmono
  refine le_trans ?_ ht
  convert hmono using 1 <;> first | rfl | (apply tsum_congr; intro x; split_ifs <;> rfl)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem selected_double_factorization_product_dvd (S : Finset ℕ) (n : ℕ) :
    (∏ p ∈ S, p ^ (2 * n.factorization p)) ∣ n ^ 2 := by
  simp_rw [Nat.mul_comm 2, pow_mul]
  rw [Finset.prod_pow]
  exact pow_dvd_pow_of_dvd (selected_factorization_product_dvd S n) 2

theorem selected_double_factorization_product_le (S : Finset ℕ) {n : ℕ}
    (hn : 0 < n) :
    (∏ p ∈ S, p ^ (2 * n.factorization p)) ≤ n ^ 2 :=
  Nat.le_of_dvd (pow_pos hn 2) (selected_double_factorization_product_dvd S n)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueDensityPMF_stride_badPrimeProduct
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (S : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → (K × I → ℤ) → Prop)
    {stride Qs Q R : ℕ} (hstride : 0 < stride)
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs)
    (hQ : 1 ≤ Q) (hR : 0 < R) (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    {η : ℝ} (hη : 0 ≤ η)
    (hjoint : ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
      (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p ∧
        2 * stride.factorization p < a p) →
      (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if ∀ p ∈ T, bad p (a p) x then 1 else 0)) ≤
        1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
      (if stride ^ 2 * (smallPrimePowerCorrection Qs * R) <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then 1 else 0)) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  have hprescribed := selectedResidueDensityPMF_prescribed_badPrimeProduct
    modulus G V hV hZ D hD0 hD S A (fun p => 2 * stride.factorization p) bad
    hprime hQs hQ hR hdepth hη hjoint
  let w := selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD
  have hmono := w.eventProbability_mono
    (fun x => stride ^ 2 * (smallPrimePowerCorrection Qs * R) <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x.val)
    (fun x => (∏ p ∈ S, p ^ (2 * stride.factorization p)) *
      (smallPrimePowerCorrection Qs * R) <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x.val)
    (fun _ hx => (Nat.mul_le_mul_right _
      (selected_double_factorization_product_le S hstride)).trans_lt hx)
  dsimp only [w] at hmono
  rw [selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
    (fun x => stride ^ 2 * (smallPrimePowerCorrection Qs * R) <
      ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x),
    selectedResidueTiltedFiniteLaw_event modulus G V hV hZ D hD0 hD
    (fun x => (∏ p ∈ S, p ^ (2 * stride.factorization p)) *
      (smallPrimePowerCorrection Qs * R) <
        ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x)] at hmono
  refine le_trans ?_ hprescribed
  convert hmono using 1 <;> first | rfl | (apply tsum_congr; intro x; split_ifs <;> rfl)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCertifiedPhysicalBadProduct
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueDensityPMF_stride_quantitative_badPrimeProduct
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (S : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → (K × I → ℤ) → Prop)
    {stride Qs Q : ℕ} (hstride : 0 < stride)
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs)
    (hQ : 1 ≤ Q) (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    {E Vlog : ℝ} (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hjoint :
      let R := quantitativeBadPrimeRadius E
      let η := Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))
      ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
        (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p ∧
          2 * stride.factorization p < a p) →
        (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
        (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
          (if ∀ p ∈ T, bad p (a p) x then 1 else 0)) ≤
          1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    let R := quantitativeBadPrimeRadius E
    let η := Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))
    0 < R ∧ (R : ℝ) ≤ Real.exp (E + 3) ∧ 0 < η ∧
      ((max Q (R ^ 2) : ℕ) : ℝ) ≤ Real.exp (Vlog + 2 * E + 6) ∧
      η⁻¹ ≤ Real.exp (Vlog + 3 * E + 8) ∧
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if stride ^ 2 * (smallPrimePowerCorrection Qs * R) <
          ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then 1 else 0)) ≤ Real.exp (-E) := by
  obtain ⟨hR, hRexp, _⟩ := quantitativeBadPrimeRadius_bounds hE
  obtain ⟨hη, herror⟩ := quantitativeBadPrimeRadius_error hE Q hQ
  obtain ⟨hwitness, haccuracy⟩ := quantitativeBadPrimeRadius_witness_budget hE hVlog Q hQexp
  refine ⟨hR, hRexp, hη, hwitness, ?_, ?_⟩
  · simpa only [one_div] using haccuracy
  · exact (selectedResidueDensityPMF_stride_badPrimeProduct
      modulus G V hV hZ D hD0 hD S A bad hstride hprime hQs hQ hR hdepth hη.le hjoint).trans herror

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

variable (Elog Vlog : ℝ) (Q : ℕ)
local notation "κ" => physicalBadProductAccuracy Elog Vlog
local notation "Rbad" => quantitativeBadPrimeRadius Elog
local notation "cap" => (max Q (Rbad ^ 2) : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

variable (Elog Vlog : ℝ) (Q : ℕ)
local notation "κ" => physicalBadProductAccuracy Elog Vlog
local notation "Rbad" => quantitativeBadPrimeRadius Elog
local notation "cap" => (max Q (Rbad ^ 2) : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
variable {R σ : Fin m → ℝ}

variable (C V : Fin m → ℝ≥0)

variable (Elog Vlog : ℝ) (Q : ℕ)

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.selectedResidueDensityPMF_stride_quantitative_badPrimeProduct.{u_1, u_2} := @OAI.Erdos3.selectedResidueDensityPMF_stride_quantitative_badPrimeProduct.{u_1, u_2}
