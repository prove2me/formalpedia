-- Prove2me | solution 1 for OAI.Problem344.large_gaps_and_ratio_density
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T05:02:02.86879+00:00
-- url     : https://prove2.me/submissions/a7a9e26c-03fd-4987-9937-06c801705d25

import Mathlib
import Definitions.Def_PrimeGaps
import Definitions.Def_OAIW2PG000
import Theorems.Thm_OAI_LargePrimeGaps_bombieriVinogradov
import Theorems.Thm_OAI_LargePrimeGaps_unorderedWeight_detector_bound
import Theorems.Thm_OAI_LargePrimeGaps_unorderedWeight_external_marked_limit
import Theorems.Thm_OAI_LargePrimeGaps_unorderedWeight_fourth_bound
import Theorems.Thm_OAI_LargePrimeGaps_unorderedWeight_internal_marked_limit

section
-- module Solutions.OAIW2_P344.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Indices
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

theorem prime_isPrime (n : ℕ) : Nat.Prime (prime n) :=
  Nat.prime_nth_prime _

theorem prime_primeIndex {p : ℕ} (hp : Nat.Prime p) : prime (primeIndex p) = p := by
  simpa [prime, primeIndex, Nat.primeCounting'] using Nat.nth_count hp

theorem primeIndex_pos (p : ℕ) : 0 < primeIndex p := by
  simp [primeIndex]

theorem primeIndex_prime {n : ℕ} (hn : 0 < n) : primeIndex (prime n) = n := by
  simp [primeIndex, prime, Nat.primeCounting'_nth_eq, Nat.sub_add_cancel hn]

theorem prime_lt_prime {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    prime m < prime n := by
  apply Nat.nth_strictMono Nat.infinite_setOfPred_prime
  omega

theorem lt_successor {p : ℕ} (hp : Nat.Prime p) : p < successor p := by
  calc
    p = prime (primeIndex p) := (prime_primeIndex hp).symm
    _ < successor p := prime_lt_prime (primeIndex_pos _) (Nat.lt_succ_self _)

theorem successor_isPrime (p : ℕ) : Nat.Prime (successor p) := prime_isPrime _

theorem exists_gapPrime_of_goodStart {X h m : ℕ} (hm : m ∈ goodStarts X h) :
    ∃ p ∈ gapPrimes X h, m ∈ Finset.Ico (p - h) p := by
  classical
  obtain ⟨hmrange, ⟨hex, hempty⟩⟩ := Finset.mem_filter.mp hm
  obtain ⟨hp, hpprime, hmp, hpend⟩ := hex
  let S := (Finset.Ioc m (m + h)).filter Nat.Prime
  have hSne : S.Nonempty := ⟨hp, by simp [S, hpprime, hmp, hpend]⟩
  let p := S.max' hSne
  have hpS : p ∈ S := Finset.max'_mem S hSne
  obtain ⟨hprange, hpprime⟩ := Finset.mem_filter.mp hpS
  obtain ⟨hmp, hpend⟩ := Finset.mem_Ioc.mp hprange
  have hn : m + 2 * h < successor p := by
    by_contra! hend
    have hnext := successor_isPrime p
    have hlt := lt_successor hpprime
    by_cases hsmall : successor p ≤ m + h
    · have hnS : successor p ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨lt_trans hmp hlt, hsmall⟩, hnext⟩
      have := Finset.le_max' S (successor p) hnS
      exact (not_le_of_gt hlt) this
    · exact hempty (successor p) (by omega) hend hnext
  refine ⟨p, ?_, ?_⟩
  · simp only [gapPrimes, Finset.mem_filter, Finset.mem_Ioc]
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Ioc.mp hmrange
    exact ⟨⟨by omega, by omega⟩, hpprime, by omega⟩
  · simp only [Finset.mem_Ico]
    omega

theorem goodStarts_card_le (X h : ℕ) :
    (goodStarts X h).card ≤ (gapPrimes X h).card * h := by
  classical
  calc
    (goodStarts X h).card ≤
        ((gapPrimes X h).biUnion fun p => Finset.Ico (p - h) p).card := by
      apply Finset.card_le_card
      intro m hm
      obtain ⟨p, hp, hmp⟩ := exists_gapPrime_of_goodStart hm
      exact Finset.mem_biUnion.mpr ⟨p, hp, hmp⟩
    _ ≤ ∑ p ∈ gapPrimes X h, (Finset.Ico (p - h) p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ gapPrimes X h, h := by
      apply Finset.sum_le_sum
      intro p _
      rw [Nat.card_Ico]
      omega
    _ = (gapPrimes X h).card * h := by simp

theorem primeIndex_injOn : Set.InjOn primeIndex {p | Nat.Prime p} := by
  intro p hp q hq h
  simpa [prime_primeIndex hp, prime_primeIndex hq] using congrArg prime h

theorem gapPrimes_card_le_largeGapIndices (C : ℝ) (X h N : ℕ) (hN : 0 < N)
    (hrange : 2 * X + h ≤ prime N)
    (hthreshold : ∀ p ∈ gapPrimes X h, C * Real.log (p : ℝ) ≤ (h : ℝ)) :
    (gapPrimes X h).card ≤ (largeGapIndices C N).card := by
  classical
  apply Finset.card_le_card_of_injOn primeIndex
  · intro p hp
    obtain ⟨hprange, hpprime, hgap⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hpupper⟩ := Finset.mem_Ioc.mp hprange
    have hipos := primeIndex_pos p
    have hiN : primeIndex p ≤ N := by
      by_contra! hi
      have := prime_lt_prime hN hi
      rw [prime_primeIndex hpprime] at this
      omega
    have hgapR : (p : ℝ) + (h : ℝ) < (successor p : ℝ) := by exact_mod_cast hgap
    change primeIndex p ∈ largeGapIndices C N
    simp only [largeGapIndices, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hipos, hiN⟩, ?_⟩
    rw [prime_primeIndex hpprime]
    have hth := hthreshold p hp
    change C * Real.log (p : ℝ) < (successor p : ℝ) - (p : ℝ)
    linarith
  · intro p hp q hq h
    exact primeIndex_injOn (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hq).2.1 h

theorem detector_cauchy {ι : Type*} (s : Finset ι) (w u : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, 0 ≤ u i) :
    (∑ i ∈ s, w i * u i) ^ 2 ≤
      (∑ i ∈ s with 0 < u i, w i) * (∑ i ∈ s, w i * u i ^ 2) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    split_ifs
    · exact hw i hi
    · exact le_rfl
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    by_cases hui : 0 < u i
    · simp only [ite_eq_left hui]
      nlinarith [sq_nonneg (w i * u i)]
    · have huzero : u i = 0 := le_antisymm (le_of_not_gt hui) (hu i hi)
      simp [huzero]

theorem mass_after_suppression {ι : Type*} (s : Finset ι) (w u v : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (hvone : ∀ i ∈ s, 0 < v i → 1 ≤ v i) :
    (∑ i ∈ s with 0 < u i, w i) ≤
      (∑ i ∈ s with 0 < u i ∧ v i = 0, w i) + ∑ i ∈ s, w i * v i := by
  classical
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hui : 0 < u i
  · by_cases hvi : v i = 0
    · simp [hui, hvi]
    · simp only [hui, hvi, and_false, ite_false, ite_true, zero_add]
      exact le_mul_of_one_le_right (hw i hi) (hvone i hi (lt_of_le_of_ne (hv i hi) (Ne.symm hvi)))
  · simp only [hui, false_and, ite_false, zero_add]
    exact mul_nonneg (hw i hi) (hv i hi)

theorem mass_cauchy {ι : Type*} [DecidableEq ι] (s t : Finset ι) (w : ι → ℝ)
    (ht : t ⊆ s) :
    (∑ i ∈ t, w i) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ s, w i ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) w
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  refine hc.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg ht (fun _ _ _ => sq_nonneg _)

theorem finite_moment_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w u v : ι → ℝ) (X a K b M : ℝ)
    (hX : 0 < X) (ha : 0 < a) (hK : 0 < K) (hM : 0 < M)
    (hb : b < a ^ 2 / K)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hvone : ∀ i ∈ s, 0 < v i → 1 ≤ v i)
    (hfirst : a * X ≤ ∑ i ∈ s, w i * u i)
    (hdetect : (∑ i ∈ s, w i * u i ^ 2) ≤ K * X)
    (hsuppress : (∑ i ∈ s, w i * v i) ≤ b * X)
    (hsecond : (∑ i ∈ s, w i ^ 2) ≤ M * X) :
    (a ^ 2 / K - b) ^ 2 / M * X ≤
      ((s.filter fun i => 0 < u i ∧ v i = 0).card : ℝ) := by
  classical
  let A := s.filter fun i => 0 < u i
  let T := s.filter fun i => 0 < u i ∧ v i = 0
  have hAnonneg : 0 ≤ ∑ i ∈ A, w i :=
    Finset.sum_nonneg fun i hi => hw i (Finset.mem_filter.mp hi).1
  have hAsq := detector_cauchy s w u hw hu
  have hfirstsq := mul_self_le_mul_self (le_of_lt (mul_pos ha hX)) hfirst
  have hAsq' : (a ^ 2 * X) * X ≤ ((∑ i ∈ A, w i) * K) * X := by
    calc
      _ = (a * X) * (a * X) := by ring
      _ ≤ (∑ i ∈ s, w i * u i) * (∑ i ∈ s, w i * u i) := hfirstsq
      _ = (∑ i ∈ s, w i * u i) ^ 2 := by ring
      _ ≤ (∑ i ∈ A, w i) * (∑ i ∈ s, w i * u i ^ 2) := hAsq
      _ ≤ (∑ i ∈ A, w i) * (K * X) := mul_le_mul_of_nonneg_left hdetect hAnonneg
      _ = _ := by ring
  have hAlower : a ^ 2 / K * X ≤ ∑ i ∈ A, w i := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    exact (mul_le_mul_iff_left₀ hX).mp (by nlinarith only [hAsq'])
  have hremoved := mass_after_suppression s w u v hw hv hvone
  have hTlower : (a ^ 2 / K - b) * X ≤ ∑ i ∈ T, w i := by
    dsimp [A] at hAlower
    dsimp [T]
    linarith
  have hTnonneg : 0 ≤ (a ^ 2 / K - b) * X := mul_nonneg (sub_nonneg.mpr hb.le) hX.le
  have hTfirstsq := mul_self_le_mul_self hTnonneg hTlower
  have hTsq := mass_cauchy s T w (Finset.filter_subset _ s)
  have hTcardnonneg : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hTbound : (a ^ 2 / K - b) ^ 2 * X * X ≤ (T.card : ℝ) * M * X := by
    calc
      _ = ((a ^ 2 / K - b) * X) * ((a ^ 2 / K - b) * X) := by ring
      _ ≤ (∑ i ∈ T, w i) * (∑ i ∈ T, w i) := hTfirstsq
      _ = (∑ i ∈ T, w i) ^ 2 := by ring
      _ ≤ (T.card : ℝ) * (∑ i ∈ s, w i ^ 2) := hTsq
      _ ≤ (T.card : ℝ) * (M * X) := mul_le_mul_of_nonneg_left hsecond hTcardnonneg
      _ = _ := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  exact (mul_le_mul_iff_left₀ hX).mp hTbound

theorem log_pos_of_two_le {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log (X : ℝ) :=
  Real.log_pos (by exact_mod_cast (show 1 < X by omega))

theorem theta_nonneg (n : ℕ) : 0 ≤ theta n := by
  by_cases hn : Nat.Prime n
  · simp only [theta, ite_eq_left hn]
    exact (log_pos_of_two_le hn.two_le).le
  · simp [theta, hn]

theorem theta_pos_iff (n : ℕ) : 0 < theta n ↔ Nat.Prime n := by
  by_cases hn : Nat.Prime n
  · simp only [theta, hn, iff_true]
    exact log_pos_of_two_le hn.two_le
  · simp [theta, hn]

theorem detector_nonneg {X : ℕ} (hX : 2 ≤ X) (B : Finset ℕ) (m : ℕ) :
    0 ≤ detector X B m :=
  div_nonneg (Finset.sum_nonneg fun _ _ => theta_nonneg _) (log_pos_of_two_le hX).le

theorem detector_pos_iff {X : ℕ} (hX : 2 ≤ X) (B : Finset ℕ) (m : ℕ) :
    0 < detector X B m ↔ ∃ b ∈ B, Nat.Prime (m + b) := by
  rw [detector, div_pos_iff_of_pos_right (log_pos_of_two_le hX),
    Finset.sum_pos_iff_of_nonneg (fun _ _ => theta_nonneg _)]
  simp only [theta_pos_iff]

theorem one_le_detector {X m : ℕ} (hX : 2 ≤ X) (hm : X < m)
    (B : Finset ℕ) (hv : 0 < detector X B m) : 1 ≤ detector X B m := by
  obtain ⟨b, hb, hp⟩ := (detector_pos_iff hX B m).mp hv
  have hlog : Real.log (X : ℝ) ≤ theta (m + b) := by
    rw [theta, ite_eq_left hp]
    apply Real.log_le_log (by exact_mod_cast (show 0 < X by omega))
    exact_mod_cast (show X ≤ m + b by omega)
  have hsum := Finset.single_le_sum (fun q (_ : q ∈ B) => theta_nonneg (m + q)) hb
  rw [detector, le_div_iff₀ (log_pos_of_two_le hX), one_mul]
  exact hlog.trans hsum

theorem first_detector_pos_iff {X : ℕ} (hX : 2 ≤ X) (h m : ℕ) :
    0 < detector X (Finset.Ioc 0 h) m ↔
      ∃ p, Nat.Prime p ∧ m < p ∧ p ≤ m + h := by
  rw [detector_pos_iff hX]
  constructor
  · rintro ⟨b, hb, hp⟩
    obtain ⟨hb0, hbh⟩ := Finset.mem_Ioc.mp hb
    exact ⟨m + b, hp, by omega, by omega⟩
  · rintro ⟨p, hp, hmp, hph⟩
    refine ⟨p - m, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · simpa [Nat.add_sub_of_le hmp.le] using hp

theorem second_detector_zero_iff {X : ℕ} (hX : 2 ≤ X) (h m : ℕ) :
    detector X (Finset.Ioc h (2 * h)) m = 0 ↔
      ∀ q, m + h < q → q ≤ m + 2 * h → ¬ Nat.Prime q := by
  have hnonneg := detector_nonneg hX (Finset.Ioc h (2 * h)) m
  have heq : detector X (Finset.Ioc h (2 * h)) m = 0 ↔
      ¬ 0 < detector X (Finset.Ioc h (2 * h)) m := by
    constructor <;> intro nh <;> linarith
  rw [heq, detector_pos_iff hX]
  constructor
  · intro hnone q hqlo hqhi hp
    apply hnone
    refine ⟨q - m, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · simpa [Nat.add_sub_of_le (show m ≤ q by omega)] using hp
  · intro hnone
    rintro ⟨b, hb, hp⟩
    obtain ⟨hblo, hbhi⟩ := Finset.mem_Ioc.mp hb
    exact hnone (m + b) (by omega) (by omega) hp

theorem goodStarts_eq_detector_filter {X : ℕ} (hX : 2 ≤ X) (h : ℕ) :
    goodStarts X h = (Finset.Ioc X (2 * X)).filter fun m =>
      0 < detector X (Finset.Ioc 0 h) m ∧ detector X (Finset.Ioc h (2 * h)) m = 0 := by
  classical
  ext m
  simp only [goodStarts, Finset.mem_filter, first_detector_pos_iff hX,
    second_detector_zero_iff hX]

theorem goodStarts_bound_of_moments {X h : ℕ} (hX : 2 ≤ X) (w : ℕ → ℝ)
    (a K b M : ℝ) (ha : 0 < a) (hK : 0 < K) (hM : 0 < M) (hb : b < a ^ 2 / K)
    (hw : ∀ m ∈ Finset.Ioc X (2 * X), 0 ≤ w m)
    (hfirst : a ≤ average X (fun m => w m * detector X (Finset.Ioc 0 h) m))
    (hdetect : average X (fun m => w m * detector X (Finset.Ioc 0 h) m ^ 2) ≤ K)
    (hsuppress : average X (fun m => w m * detector X (Finset.Ioc h (2 * h)) m) ≤ b)
    (hsecond : average X (fun m => w m ^ 2) ≤ M) :
    (a ^ 2 / K - b) ^ 2 / M * (X : ℝ) ≤ ((goodStarts X h).card : ℝ) := by
  classical
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  rw [goodStarts_eq_detector_filter hX]
  apply finite_moment_bound _ w _ _ (X : ℝ) a K b M hXpos ha hK hM hb hw
  · intro m _
    exact detector_nonneg hX _ m
  · intro m _
    exact detector_nonneg hX _ m
  · intro m hm hv
    exact one_le_detector hX (Finset.mem_Ioc.mp hm).1 _ hv
  · exact (le_div_iff₀ hXpos).mp hfirst
  · exact (div_le_iff₀ hXpos).mp hdetect
  · exact (div_le_iff₀ hXpos).mp hsuppress
  · exact (div_le_iff₀ hXpos).mp hsecond

open Filter

theorem le_prime (n : ℕ) : n ≤ prime n := by
  have := Nat.add_two_le_nth_prime (n - 1)
  change n ≤ Nat.nth Nat.Prime (n - 1)
  omega

theorem tendsto_prime : Tendsto prime atTop atTop :=
  tendsto_atTop_mono le_prime tendsto_id

theorem primeCounting_prime {n : ℕ} (hn : 0 < n) : Nat.primeCounting (prime n) = n := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  change Nat.count Nat.Prime (prime n + 1) = n
  rw [Nat.count_succ, ite_eq_left (prime_isPrime n)]
  have := primeIndex_prime hn
  exact this

theorem eventually_index_log_prime_le :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.log (prime n : ℝ) ≤ (Real.log 4 + 1) * (prime n : ℝ) := by
  have hcheb := (tendsto_natCast_atTop_atTop.comp tendsto_prime).eventually
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hcheb, eventually_ge_atTop 1] with n hn hnpos
  simp only [Function.comp_apply, Nat.floor_natCast, primeCounting_prime (by omega : 0 < n)] at hn
  exact (le_div_iff₀ (log_pos_of_two_le (prime_isPrime n).two_le)).mp hn

theorem tendsto_indexScale : Tendsto indexScale atTop atTop :=
  (Nat.tendsto_div_const_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_prime

theorem eventually_scale_comparison :
    ∀ᶠ N : ℕ in atTop, 2 ≤ indexScale N ∧
      (N : ℝ) * Real.log (indexScale N : ℝ) ≤
        (6 * (Real.log 4 + 1)) * (indexScale N : ℝ) := by
  filter_upwards [eventually_index_log_prime_le,
    tendsto_indexScale.eventually (eventually_ge_atTop 2)] with N hcheb hX
  refine ⟨hX, ?_⟩
  have hprime : indexScale N ≤ prime N := Nat.div_le_self _ _
  have hlog : Real.log (indexScale N : ℝ) ≤ Real.log (prime N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < indexScale N by omega))
      (by exact_mod_cast hprime)
  have hsizeN : prime N ≤ 6 * indexScale N := by
    have hmod := Nat.mod_lt (prime N) (by norm_num : 0 < 3)
    have hdiv := Nat.div_add_mod (prime N) 3
    change 2 ≤ prime N / 3 at hX
    change prime N ≤ 6 * (prime N / 3)
    omega
  have hsize : (prime N : ℝ) ≤ 6 * (indexScale N : ℝ) := by exact_mod_cast hsizeN
  have hA : 0 ≤ Real.log 4 + 1 := by positivity
  calc
    (N : ℝ) * Real.log (indexScale N : ℝ) ≤
        (N : ℝ) * Real.log (prime N : ℝ) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ ≤ (Real.log 4 + 1) * (prime N : ℝ) := hcheb
    _ ≤ (6 * (Real.log 4 + 1)) * (indexScale N : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hsize hA]

theorem blockLength_le_mul_log {lam : ℝ} (hlam : 0 ≤ lam) {X : ℕ} (hX : 2 ≤ X) :
    (blockLength lam X : ℝ) ≤ lam * Real.log (X : ℝ) :=
  Nat.floor_le (mul_nonneg hlam (log_pos_of_two_le hX).le)

theorem eventually_blockLength_le (lam : ℝ) (hlam : 0 < lam) :
    ∀ᶠ X : ℕ in atTop, blockLength lam X ≤ X := by
  have he := tendsto_natCast_atTop_atTop.eventually (Real.isLittleO_log_id_atTop.bound
    (by positivity : 0 < 1 / lam))
  filter_upwards [he, eventually_ge_atTop 2] with X hbound hX
  have hlog := log_pos_of_two_le hX
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hlog.le,
    abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X)] at hbound
  have hmul : lam * Real.log (X : ℝ) ≤ (X : ℝ) := by
    calc
      lam * Real.log (X : ℝ) ≤ lam * ((1 / lam) * (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound hlam.le
      _ = (X : ℝ) := by field_simp
  exact_mod_cast (blockLength_le_mul_log hlam.le hX).trans hmul

theorem eventually_blockLength_threshold (C : ℝ) (hC : 0 < C) :
    ∀ᶠ X : ℕ in atTop, ∀ p : ℕ, 0 < p → p ≤ 3 * X →
      C * Real.log (p : ℝ) ≤ (blockLength (C + 1) X : ℝ) := by
  have hlim : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop (C * Real.log 3 + 1)),
    eventually_ge_atTop 2] with X hlog hX
  intro p hp hpX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hupper : Real.log (p : ℝ) ≤ Real.log (3 * (X : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hpX)
  rw [Real.log_mul (by norm_num) hXpos.ne'] at hupper
  have hfloor := Nat.lt_floor_add_one ((C + 1) * Real.log (X : ℝ))
  change (C + 1) * Real.log (X : ℝ) < (blockLength (C + 1) X : ℝ) + 1 at hfloor
  nlinarith [mul_le_mul_of_nonneg_left hupper hC.le]

theorem index_bound_of_goodStarts {C delta lam A : ℝ} {X N : ℕ}
    (hdelta : 0 < delta) (hlam : 0 < lam) (hA : 0 < A)
    (hX : 2 ≤ X) (hN : 0 < N)
    (hrange : 2 * X + blockLength lam X ≤ prime N)
    (hthreshold : ∀ p ∈ gapPrimes X (blockLength lam X),
      C * Real.log (p : ℝ) ≤ (blockLength lam X : ℝ))
    (hcompare : (N : ℝ) * Real.log (X : ℝ) ≤ A * (X : ℝ))
    (hstarts : delta * (X : ℝ) ≤ ((goodStarts X (blockLength lam X)).card : ℝ)) :
    delta / (A * lam) * (N : ℝ) ≤ ((largeGapIndices C N).card : ℝ) := by
  have hcount := goodStarts_card_le X (blockLength lam X)
  have hindices := gapPrimes_card_le_largeGapIndices C X (blockLength lam X) N hN
    hrange hthreshold
  have hmul : delta * (X : ℝ) ≤
      ((largeGapIndices C N).card : ℝ) * (lam * Real.log (X : ℝ)) := by
    calc
      delta * (X : ℝ) ≤ ((goodStarts X (blockLength lam X)).card : ℝ) := hstarts
      _ ≤ ((gapPrimes X (blockLength lam X)).card : ℝ) * (blockLength lam X : ℝ) :=
        by exact_mod_cast hcount
      _ ≤ ((largeGapIndices C N).card : ℝ) * (blockLength lam X : ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hindices) (Nat.cast_nonneg _)
      _ ≤ ((largeGapIndices C N).card : ℝ) * (lam * Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_left (blockLength_le_mul_log hlam.le hX) (Nat.cast_nonneg _)
  have hcomp := mul_le_mul_of_nonneg_left hcompare hdelta.le
  have hmulA := mul_le_mul_of_nonneg_left hmul hA.le
  have hpos := log_pos_of_two_le hX
  apply (mul_le_mul_iff_left₀ hpos).mp
  apply (mul_le_mul_iff_right₀ (mul_pos hA hlam)).mp
  calc
    (A * lam) * (delta / (A * lam) * (N : ℝ) * Real.log (X : ℝ)) =
        delta * ((N : ℝ) * Real.log (X : ℝ)) := by field_simp [hA.ne', hlam.ne']
    _ ≤ A * (delta * (X : ℝ)) := by nlinarith
    _ ≤ (A * lam) * (((largeGapIndices C N).card : ℝ) * Real.log (X : ℝ)) := by
      nlinarith

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Profiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem reciprocalBump_eq_zero_left {R : ℝ} (hR : 2 ≤ R) {u : ℝ}
    (hu : u ≤ 1 / 2) : reciprocalBump R hR u = 0 := by
  apply ContDiffBump.zero_of_le_dist
  change R / 2 ≤ dist u ((R + 1) / 2)
  rw [Real.dist_eq, abs_of_nonpos (by linarith : u - (R + 1) / 2 ≤ 0)]
  linarith

theorem reciprocalBump_eq_zero_right {R : ℝ} (hR : 2 ≤ R) {u : ℝ}
    (hu : 2 * R ≤ u) : reciprocalBump R hR u = 0 := by
  apply ContDiffBump.zero_of_le_dist
  change R / 2 ≤ dist u ((R + 1) / 2)
  rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ u - (R + 1) / 2)]
  linarith

theorem reciprocalProfile_zero_left {R : ℝ} (hR : 2 ≤ R) {u : ℝ}
    (hu : u ≤ 1 / 2) : reciprocalProfile R hR u = 0 := by
  simp [reciprocalProfile, reciprocalBump_eq_zero_left hR hu]

theorem reciprocalProfile_zero_right {R : ℝ} (hR : 2 ≤ R) {u : ℝ}
    (hu : 2 * R ≤ u) : reciprocalProfile R hR u = 0 := by
  simp [reciprocalProfile, reciprocalBump_eq_zero_right hR hu]

theorem reciprocalProfile_eq_inv {R : ℝ} (hR : 2 ≤ R) {u : ℝ}
    (hu : u ∈ Icc 1 R) : reciprocalProfile R hR u = u⁻¹ := by
  have hb : reciprocalBump R hR u = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    change dist u ((R + 1) / 2) ≤ (R - 1) / 2
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hu.1, hu.2]
  simp [reciprocalProfile, hb]

theorem reciprocalProfile_nonneg {R : ℝ} (hR : 2 ≤ R) (u : ℝ) :
    0 ≤ reciprocalProfile R hR u := by
  by_cases hu : u ≤ 1 / 2
  · rw [reciprocalProfile_zero_left hR hu]
  · exact div_nonneg (ContDiffBump.nonneg _) (by linarith)

theorem reciprocalProfile_smooth {R : ℝ} (hR : 2 ≤ R) :
    ContDiff ℝ ∞ (reciprocalProfile R hR) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · subst u
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    exact reciprocalProfile_zero_left hR hx.le
  · exact (ContDiffBump.contDiffAt _).div contDiffAt_id hu

theorem reciprocalProfile_compact {R : ℝ} (hR : 2 ≤ R) :
    HasCompactSupport (reciprocalProfile R hR) := by
  unfold reciprocalProfile
  simp only [div_eq_mul_inv]
  exact ((reciprocalBump R hR).hasCompactSupport.mul_right (f' := fun u : ℝ => u⁻¹))

theorem reciprocalProfile_integrable {R : ℝ} (hR : 2 ≤ R) :
    Integrable (reciprocalProfile R hR) :=
  (reciprocalProfile_smooth hR).continuous.integrable_of_hasCompactSupport
    (reciprocalProfile_compact hR)

theorem reciprocalProfile_sq_integrable {R : ℝ} (hR : 2 ≤ R) :
    Integrable (fun u => reciprocalProfile R hR u ^ 2) := by
  apply ((reciprocalProfile_smooth hR).continuous.pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two] using (reciprocalProfile_compact hR).mul_right

theorem reciprocalProfile_moment_integrable {R : ℝ} (hR : 2 ≤ R) :
    Integrable (fun u => u * reciprocalProfile R hR u ^ 2) := by
  apply (continuous_id.mul ((reciprocalProfile_smooth hR).continuous.pow 2)).integrable_of_hasCompactSupport
  apply HasCompactSupport.mul_left
  simpa only [pow_two] using (reciprocalProfile_compact hR).mul_right

theorem reciprocalProfile_mass_lower {R : ℝ} (hR : 2 ≤ R) :
    Real.log R ≤ ∫ u, reciprocalProfile R hR u := by
  have h1 : (1 : ℝ) ≤ R := by linarith
  have heq : (∫ u in (1 : ℝ)..R, reciprocalProfile R hR u) = Real.log R := by
    rw [intervalIntegral.integral_congr (g := fun u : ℝ => u⁻¹) (by
      intro u hu
      rw [uIcc_of_le h1] at hu
      exact reciprocalProfile_eq_inv hR hu)]
    simpa using integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < R)
  rw [← heq, intervalIntegral.integral_of_le h1]
  exact setIntegral_le_integral (reciprocalProfile_integrable hR)
    (Filter.Eventually.of_forall (reciprocalProfile_nonneg hR))

theorem reciprocalProfile_sq_mass_pos {R : ℝ} (hR : 2 ≤ R) :
    0 < ∫ u, reciprocalProfile R hR u ^ 2 := by
  apply integral_pos_of_integrable_nonneg_nonzero
    ((reciprocalProfile_smooth hR).continuous.pow 2) (reciprocalProfile_sq_integrable hR)
      (fun u => sq_nonneg _) (x := 1)
  have h := reciprocalProfile_eq_inv hR (show (1 : ℝ) ∈ Icc 1 R by constructor <;> linarith)
  simp [h]

theorem reciprocalProfile_moment_upper {R : ℝ} (hR : 2 ≤ R) :
    (∫ u, u * reciprocalProfile R hR u ^ 2) ≤ Real.log (4 * R) := by
  have heq : (∫ u in (1/2 : ℝ)..(2*R), u * reciprocalProfile R hR u ^ 2) =
      ∫ u, u * reciprocalProfile R hR u ^ 2 := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro u hu
    constructor
    · by_contra hx
      have hz := reciprocalProfile_zero_left hR (le_of_not_gt hx)
      exact hu (by simp [hz])
    · by_contra hx
      have hz := reciprocalProfile_zero_right hR (le_of_not_ge hx)
      exact hu (by simp [hz])
  rw [← heq]
  calc
    _ ≤ ∫ u in (1/2 : ℝ)..(2*R), u⁻¹ := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (reciprocalProfile_moment_integrable hR).intervalIntegrable
      · apply intervalIntegral.intervalIntegrable_inv (f := fun u : ℝ => u)
        · intro u hu
          rw [uIcc_of_le (by linarith : (1/2 : ℝ) ≤ 2*R)] at hu
          linarith [hu.1]
        · exact continuous_id.continuousOn
      · intro u hu
        have hup : 0 < u := by linarith [hu.1]
        have hb0 : 0 ≤ reciprocalBump R hR u := ContDiffBump.nonneg _
        have hb1 : reciprocalBump R hR u ≤ 1 := ContDiffBump.le_one _
        calc
          u * reciprocalProfile R hR u ^ 2 = reciprocalBump R hR u ^ 2 / u := by
            dsimp [reciprocalProfile]
            field_simp
          _ ≤ 1 / u := div_le_div_of_nonneg_right (by nlinarith) hup.le
          _ = _ := one_div u
    _ = _ := by
      rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 1/2) (by linarith : 0 < 2*R)]
      congr 1
      ring

theorem exists_normalized_reciprocal_profile {lambda R : ℝ}
    (hlambda : 0 < lambda) (hR : 2 ≤ R) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ioi 0 ∧ (∀ u, 0 ≤ g u) ∧
      (∫ u, g u ^ 2) = 1 ∧ (∫ u, g u) = Real.sqrt lambda ∧
      (∫ u, u * g u ^ 2) = lambda * (∫ u, u * reciprocalProfile R hR u ^ 2) /
        (∫ u, reciprocalProfile R hR u) ^ 2 := by
  let A : ℝ := ∫ u, reciprocalProfile R hR u
  let Q : ℝ := ∫ u, reciprocalProfile R hR u ^ 2
  let B : ℝ := ∫ u, u * reciprocalProfile R hR u ^ 2
  have hA : 0 < A := lt_of_lt_of_le (Real.log_pos (by linarith : 1 < R))
    (reciprocalProfile_mass_lower hR)
  have hQ : 0 < Q := reciprocalProfile_sq_mass_pos hR
  have hroot : 0 < Real.sqrt lambda := Real.sqrt_pos.2 hlambda
  have hroot2 := Real.sq_sqrt hlambda.le
  let a : ℝ := A / (Real.sqrt lambda * Q)
  let b : ℝ := A ^ 2 / (lambda * Q)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  let g : ℝ → ℝ := fun u => a * reciprocalProfile R hR (b * u)
  have hsmooth : ContDiff ℝ ∞ g :=
    contDiff_const.mul ((reciprocalProfile_smooth hR).comp (contDiff_const.mul contDiff_id))
  have hcompact : HasCompactSupport g := by
    exact ((reciprocalProfile_compact hR).comp_smul hb.ne').mul_left
  have hsupp : tsupport g ⊆ Ioi 0 := by
    have hs : tsupport g ⊆ Ici ((1/2) / b) := by
      apply closure_minimal _ isClosed_Ici
      intro u hu
      by_contra hn
      have hub : b * u ≤ 1/2 := by
        have := (lt_div_iff₀ hb).mp (lt_of_not_ge hn)
        nlinarith
      exact hu (by dsimp [g]; rw [reciprocalProfile_zero_left hR hub, mul_zero])
    intro u hu
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (1/2)/b) (hs hu)
  have hmass1 : (∫ u, g u) = a * b⁻¹ * A := by
    dsimp only [g]
    rw [integral_const_mul, Measure.integral_comp_mul_left]
    rw [abs_of_pos (inv_pos.mpr hb)]
    simp only [smul_eq_mul, A]
    ring
  have hmass2 : (∫ u, g u ^ 2) = a ^ 2 * b⁻¹ * Q := by
    simp only [g, mul_pow]
    rw [integral_const_mul]
    change a ^ 2 * (∫ u, (fun x => reciprocalProfile R hR x ^ 2) (b * u)) = _
    rw [Measure.integral_comp_mul_left (fun x => reciprocalProfile R hR x ^ 2) b,
      abs_of_pos (inv_pos.mpr hb)]
    simp only [smul_eq_mul, Q]
    ring
  have hmom : (∫ u, u * g u ^ 2) = (a ^ 2 / b) * b⁻¹ * B := by
    calc
      _ = ∫ u, (a ^ 2 / b) * ((b * u) * reciprocalProfile R hR (b * u) ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with u
        dsimp only [g]
        field_simp
      _ = _ := by
        rw [integral_const_mul]
        change (a ^ 2 / b) * (∫ u, (fun x => x * reciprocalProfile R hR x ^ 2) (b * u)) = _
        rw [Measure.integral_comp_mul_left (fun x => x * reciprocalProfile R hR x ^ 2) b,
          abs_of_pos (inv_pos.mpr hb)]
        simp only [smul_eq_mul, B]
        ring
  refine ⟨g, hsmooth, hcompact, hsupp, (fun u => mul_nonneg ha.le (reciprocalProfile_nonneg hR _)), ?_, ?_, ?_⟩
  · rw [hmass2]
    dsimp only [a, b]
    field_simp
    nlinarith [hroot2]
  · rw [hmass1]
    dsimp only [a, b]
    field_simp
    nlinarith [hroot2]
  · rw [hmom]
    change (a ^ 2 / b) * b⁻¹ * B = lambda * B / A ^ 2
    dsimp only [a, b]
    field_simp
    rw [hroot2]

theorem exists_small_first_moment_profile {lambda beta : ℝ}
    (hlambda : 0 < lambda) (hbeta : 0 < beta) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ioi 0 ∧ (∀ u, 0 ≤ g u) ∧
      (∫ u, g u ^ 2) = 1 ∧ (∫ u, g u) = Real.sqrt lambda ∧
      (∫ u, u * g u ^ 2) < beta := by
  let t : ℝ := max (Real.log 4) (2 * lambda / beta) + 1
  have htlog : Real.log 4 < t := by dsimp [t]; linarith [le_max_left (Real.log 4) (2*lambda/beta)]
  have htlarge : 2 * lambda / beta < t := by dsimp [t]; linarith [le_max_right (Real.log 4) (2*lambda/beta)]
  have htpos : 0 < t := lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 4)) htlog
  let R : ℝ := Real.exp t
  have hR : 2 ≤ R := by
    have : 4 < R := by
      dsimp [R]
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      exact Real.exp_lt_exp.mpr htlog
    linarith
  obtain ⟨g, hgs, hgc, hgp, hgn, hg2, hg1, hgB⟩ :=
    exists_normalized_reciprocal_profile hlambda hR
  refine ⟨g, hgs, hgc, hgp, hgn, hg2, hg1, ?_⟩
  rw [hgB]
  have hA : t ≤ ∫ u, reciprocalProfile R hR u := by
    simpa only [R, Real.log_exp] using reciprocalProfile_mass_lower hR
  have hB : (∫ u, u * reciprocalProfile R hR u ^ 2) ≤ Real.log 4 + t := by
    convert reciprocalProfile_moment_upper hR using 1
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by exact (Real.exp_pos t).ne' : R ≠ 0)]
    simp only [R, Real.log_exp]
  apply (div_lt_iff₀ (sq_pos_of_pos (htpos.trans_le hA))).mpr
  have hva : 2 * lambda < t * beta := (div_lt_iff₀ hbeta).mp htlarge
  have hsq : t ^ 2 ≤ (∫ u, reciprocalProfile R hR u) ^ 2 := by nlinarith
  have hBt : (∫ u, u * reciprocalProfile R hR u ^ 2) < 2 * t := by linarith
  nlinarith

theorem productProfile_sq (g : ℝ → ℝ) {k : ℝ} (hk : 0 ≤ k)
    (j : ℕ) (t : Fin j → ℝ) :
    productProfile g k j t ^ 2 = productDensity (scaledProfileDensity g k) j t := by
  simp only [productProfile, productDensity, ← Finset.prod_pow, mul_pow,
    Real.sq_sqrt hk, scaledProfileDensity]

theorem scaledProfileDensity_integral {g : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hg : (∫ u, g u ^ 2) = 1) : (∫ u, scaledProfileDensity g k u) = 1 := by
  unfold scaledProfileDensity
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun u => g u ^ 2) k,
    abs_of_pos (inv_pos.mpr hk), smul_eq_mul, hg]
  field_simp

theorem scaledProfileDensity_moment (g : ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    (∫ u, u * scaledProfileDensity g k u) = (∫ u, u * g u ^ 2) / k := by
  calc
    _ = ∫ u, (k * u) * g (k * u) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [scaledProfileDensity]
      ring
    _ = _ := by
      rw [Measure.integral_comp_mul_left (fun u => u * g u ^ 2) k,
        abs_of_pos (inv_pos.mpr hk), smul_eq_mul]
      ring

theorem productDensity_integral {p : ℝ → ℝ} (hp : (∫ u, p u) = 1) (j : ℕ) :
    (∫ t : Fin j → ℝ, productDensity p j t) = 1 := by
  simp only [productDensity, integral_fintype_prod_volume_eq_pow, hp, one_pow]

theorem productDensity_nonneg {p : ℝ → ℝ} (hp : ∀ u, 0 ≤ p u)
    (j : ℕ) (t : Fin j → ℝ) : 0 ≤ productDensity p j t :=
  Finset.prod_nonneg fun i _ => hp (t i)

theorem productDensity_compact {p : ℝ → ℝ} (hp : HasCompactSupport p) (j : ℕ) :
    HasCompactSupport (productDensity p j) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_univ_pi fun _ => hp)
  intro t ht i _
  exact subset_closure (show t i ∈ Function.support p from
    (Finset.prod_ne_zero_iff.mp ht) i (Finset.mem_univ i))

theorem productDensity_continuous {p : ℝ → ℝ} (hp : Continuous p) (j : ℕ) :
    Continuous (productDensity p j) := by
  unfold productDensity
  fun_prop

theorem productDensity_integrable {p : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (j : ℕ) : Integrable (productDensity p j) :=
  (productDensity_continuous hp j).integrable_of_hasCompactSupport (productDensity_compact hpc j)

theorem poly_productDensity_integrable {p : ℝ → ℝ} {j : ℕ} (hp : Continuous p)
    (hpc : HasCompactSupport p) {P : (Fin j → ℝ) → ℝ} (hP : Continuous P) :
    Integrable (fun t => P t * productDensity p j t) :=
  (hP.mul (productDensity_continuous hp j)).integrable_of_hasCompactSupport
    ((productDensity_compact hpc j).mul_left)

theorem one_coordinate_productDensity {p f : ℝ → ℝ} {j : ℕ}
    (i : Fin j) (t : Fin j → ℝ) :
    f (t i) * productDensity p j t =
      ∏ l, (if l = i then f (t l) else 1) * p (t l) := by
  rw [Finset.prod_mul_distrib]
  simp [productDensity]

theorem two_coordinate_productDensity {p f : ℝ → ℝ} {j : ℕ}
    (i l : Fin j) (hil : i ≠ l) (t : Fin j → ℝ) :
    (f (t i) * f (t l)) * productDensity p j t =
      ∏ a, (if a = i then f (t a) else if a = l then f (t a) else 1) * p (t a) := by
  have hf : (fun a : Fin j => if a = i then f (t a) else if a = l then f (t a) else 1) =
      fun a => (if a = i then f (t a) else 1) * (if a = l then f (t a) else 1) := by
    funext a
    by_cases hai : a = i
    · subst a
      simp [hil]
    · simp [hai]
  rw [Finset.prod_mul_distrib, hf, Finset.prod_mul_distrib]
  simp [productDensity]

theorem one_coordinate_productDensity_integral {p f : ℝ → ℝ} {j : ℕ}
    (hp : (∫ u, p u) = 1) (i : Fin j) :
    (∫ t : Fin j → ℝ, f (t i) * productDensity p j t) = ∫ u, f u * p u := by
  simp only [one_coordinate_productDensity]
  rw [integral_fintype_prod_volume_eq_prod
    (fun l u => (if l = i then f u else 1) * p u)]
  have hf : (fun l : Fin j => ∫ u : ℝ, (if l = i then f u else 1) * p u) =
      fun l => if l = i then ∫ u, f u * p u else 1 := by
    funext l
    split_ifs with hl
    · rfl
    · simpa only [one_mul] using hp
  rw [hf]
  simp

theorem two_coordinate_productDensity_integral {p f : ℝ → ℝ} {j : ℕ}
    (hp : (∫ u, p u) = 1) (i l : Fin j) (hil : i ≠ l) :
    (∫ t : Fin j → ℝ, (f (t i) * f (t l)) * productDensity p j t) =
      (∫ u, f u * p u)^2 := by
  simp only [two_coordinate_productDensity i l hil]
  rw [integral_fintype_prod_volume_eq_prod
    (fun a u => (if a = i then f u else if a = l then f u else 1) * p u)]
  have hf : (fun a : Fin j => ∫ u : ℝ,
      (if a = i then f u else if a = l then f u else 1) * p u) =
      fun a => (if a = i then ∫ u, f u * p u else 1) *
        (if a = l then ∫ u, f u * p u else 1) := by
    funext a
    by_cases hai : a = i
    · subst a
      simp [hil]
    · by_cases hal : a = l
      · subst a
        simp [hil.symm]
      · simp [hai, hal, hp]
  rw [hf, Finset.prod_mul_distrib]
  simp [pow_two]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_ProfileVariance
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem centered_profile_integral {p : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hpi : (∫ u, p u) = 1) :
    (∫ u, (u - ∫ v, v * p v) * p u) = 0 := by
  simp only [sub_mul]
  have hp0 : Integrable p := hp.integrable_of_hasCompactSupport hpc
  have hp1 : Integrable (fun u => u * p u) :=
    (continuous_id.mul hp).integrable_of_hasCompactSupport hpc.mul_left
  rw [integral_sub hp1 (hp0.const_mul _), integral_const_mul, hpi]
  ring

theorem coordinateSum_variance {p : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hpi : (∫ u, p u) = 1) (j : ℕ) :
    (∫ t : Fin j → ℝ, (coordinateSum t - (j : ℝ) * ∫ u, u * p u)^2 *
      productDensity p j t) = (j : ℝ) * ∫ u, (u - ∫ v, v * p v)^2 * p u := by
  let m : ℝ := ∫ u, u * p u
  have hexpand (t : Fin j → ℝ) :
      (coordinateSum t - (j : ℝ) * m)^2 * productDensity p j t =
      ∑ i, ∑ l, ((t i - m) * (t l - m)) * productDensity p j t := by
    have hs : coordinateSum t - (j : ℝ) * m = ∑ i : Fin j, (t i - m) := by
      simp [coordinateSum, Finset.sum_sub_distrib]
    rw [hs, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
  change (∫ t : Fin j → ℝ, (coordinateSum t - (j : ℝ) * m)^2 *
    productDensity p j t) = (j : ℝ) * ∫ u, (u - m)^2 * p u
  simp only [hexpand]
  have hint (i l : Fin j) : Integrable (fun t : Fin j → ℝ =>
      ((t i - m) * (t l - m)) * productDensity p j t) :=
    poly_productDensity_integrable hp hpc (by fun_prop)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun l _ => hint i l))]
  simp only [integral_finsetSum _ (fun l _ => hint _ l)]
  have hterm (i l : Fin j) :
      (∫ t : Fin j → ℝ, ((t i - m) * (t l - m)) * productDensity p j t) =
      if l = i then ∫ u, (u - m)^2 * p u else 0 := by
    split_ifs with hli
    · subst l
      simpa only [← pow_two] using
        (one_coordinate_productDensity_integral (f := fun u => (u-m)^2) hpi i)
    · rw [two_coordinate_productDensity_integral (f := fun u => u-m) hpi i l (Ne.symm hli),
        centered_profile_integral hp hpc hpi]
      norm_num
  simp only [hterm]
  simp [m]

theorem scaledProfileDensity_continuous {g : ℝ → ℝ} (hg : Continuous g) (k : ℝ) :
    Continuous (scaledProfileDensity g k) := by
  unfold scaledProfileDensity
  fun_prop

theorem scaledProfileDensity_compact {g : ℝ → ℝ} (hg : HasCompactSupport g)
    {k : ℝ} (hk : k ≠ 0) : HasCompactSupport (scaledProfileDensity g k) := by
  have hh : HasCompactSupport (fun u => g (k*u)^2) := by
    have hh := (hg.comp_smul hk).mul_right (f' := fun u => g (k*u))
    change HasCompactSupport (fun u => g (k*u) * g (k*u)) at hh
    simpa only [pow_two] using hh
  exact hh.mul_left

theorem scaledProfileDensity_variance (g : ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    (∫ u, (u - (∫ v, v * g v^2)/k)^2 * scaledProfileDensity g k u) =
      (∫ u, (u - ∫ v, v * g v^2)^2 * g u^2) / k^2 := by
  let m : ℝ := ∫ u, u * g u^2
  calc
    _ = k⁻¹ * ∫ u, (k*u - m)^2 * g (k*u)^2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp only [scaledProfileDensity]
      change (u - m / k)^2 * (k * g (k*u)^2) = _
      field_simp
    _ = _ := by
      rw [Measure.integral_comp_mul_left (fun u => (u-m)^2 * g u^2) k,
        abs_of_pos (inv_pos.mpr hk), smul_eq_mul]
      dsimp only [m]
      ring

theorem concentrated_cutoff_mass {p chi : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hpn : ∀ u, 0 ≤ p u) (hpi : (∫ u, p u) = 1)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    {beta d : ℝ} (hd : 0 < d) (hflat : ∀ s ≤ beta, chi s = 1)
    (j : ℕ) (hmean : (j : ℝ) * (∫ u, u*p u) + d ≤ beta) :
    1 - ((j : ℝ) * ∫ u, (u - ∫ v, v*p v)^2 * p u) / d^2 ≤
      ∫ t : Fin j → ℝ, productDensity p j t * chi (coordinateSum t)^2 := by
  let m : ℝ := (j : ℝ) * (∫ u, u*p u)
  have hD := productDensity_integrable hp hpc j
  have hC : Integrable (fun t : Fin j → ℝ =>
      productDensity p j t * chi (coordinateSum t)^2) := by
    simpa only [mul_comm] using
      (poly_productDensity_integrable hp hpc
        (P := fun t : Fin j → ℝ => chi (coordinateSum t)^2) (by
          unfold coordinateSum
          fun_prop))
  have hV : Integrable (fun t : Fin j → ℝ =>
      (coordinateSum t - m)^2 * productDensity p j t) :=
    poly_productDensity_integrable hp hpc (by unfold coordinateSum; fun_prop)
  have hle (t : Fin j → ℝ) :
      productDensity p j t - productDensity p j t * chi (coordinateSum t)^2 ≤
        ((coordinateSum t - m)^2 * productDensity p j t) / d^2 := by
    have hDn := productDensity_nonneg hpn j t
    have hc0 := hchi0 (coordinateSum t)
    have hc1 := hchi1 (coordinateSum t)
    by_cases ht : coordinateSum t ≤ beta
    · rw [hflat _ ht]
      simpa only [one_pow, mul_one, sub_self] using
        (div_nonneg (mul_nonneg (sq_nonneg _) hDn) (sq_nonneg d))
    · have hdm : d ≤ coordinateSum t - m := by dsimp only [m]; linarith
      have hd2 : 0 < d^2 := sq_pos_of_pos hd
      apply (le_div_iff₀ hd2).mpr
      have hc2 : 0 ≤ chi (coordinateSum t)^2 := sq_nonneg _
      have hv2 : d^2 ≤ (coordinateSum t - m)^2 := by nlinarith
      calc
        _ ≤ productDensity p j t * d^2 :=
          mul_le_mul_of_nonneg_right (sub_le_self _ (mul_nonneg hDn hc2)) hd2.le
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hv2 hDn]
  have hint := integral_mono (hD.sub hC) (hV.div_const (d^2)) hle
  dsimp only [Pi.sub_apply] at hint
  rw [integral_sub hD hC, productDensity_integral hpi, integral_div] at hint
  change 1 - _ ≤ (∫ t : Fin j → ℝ,
    (coordinateSum t - (j:ℝ)*(∫ u, u*p u))^2 * productDensity p j t) / d^2 at hint
  rw [coordinateSum_variance hp hpc hpi] at hint
  linarith

theorem cutoff_mass_le_one {p chi : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hpn : ∀ u, 0 ≤ p u) (hpi : (∫ u, p u) = 1)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1) (j : ℕ) :
    (∫ t : Fin j → ℝ, productDensity p j t * chi (coordinateSum t)^2) ≤ 1 := by
  rw [← productDensity_integral hpi j]
  apply integral_mono
  · simpa only [mul_comm] using
      (poly_productDensity_integrable hp hpc
        (P := fun t : Fin j → ℝ => chi (coordinateSum t)^2) (by
          unfold coordinateSum
          fun_prop))
  · exact productDensity_integrable hp hpc j
  · intro t
    have hc0 := hchi0 (coordinateSum t)
    have hc1 := hchi1 (coordinateSum t)
    have hc2 : chi (coordinateSum t)^2 ≤ 1 := by nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc2 (productDensity_nonneg hpn j t)

theorem simplexCutoff_smooth (beta gamma : ℝ) : ContDiff ℝ ∞ (simplexCutoff beta gamma) := by
  unfold simplexCutoff
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _))

theorem simplexCutoff_nonneg (beta gamma s : ℝ) : 0 ≤ simplexCutoff beta gamma s :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem simplexCutoff_le_one (beta gamma s : ℝ) : simplexCutoff beta gamma s ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem simplexCutoff_eq_one {beta gamma s : ℝ} (hbg : beta < gamma) (hs : s ≤ beta) :
    simplexCutoff beta gamma s = 1 := by
  unfold simplexCutoff
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hs) (sub_pos.mpr hbg).le), sub_zero]

theorem simplexCutoff_eq_zero {beta gamma s : ℝ} (hbg : beta < gamma) (hs : gamma ≤ s) :
    simplexCutoff beta gamma s = 0 := by
  unfold simplexCutoff
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hbg)).mpr (by linarith))]
  ring

theorem cutoffDeletion_continuous {g chi : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hchi : Continuous chi) (k : ℝ) :
    Continuous (cutoffDeletion g chi k) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support hgc
  · exact (show Continuous (Function.uncurry fun s u : ℝ => g u * chi (s+u/k)) by
      unfold Function.uncurry
      fun_prop).continuousOn
  · intro s u _ hu
    rw [image_eq_zero_of_notMem_tsupport hu, zero_mul]

theorem cutoffDeletion_integrable {g chi : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hchi : Continuous chi) (k s : ℝ) :
    Integrable (fun u => g u * chi (s+u/k)) :=
  (hg.mul (hchi.comp (by fun_prop))).integrable_of_hasCompactSupport hgc.mul_right

theorem cutoffDeletion_nonneg {g chi : ℝ → ℝ} (hg : ∀ u, 0 ≤ g u)
    (hchi : ∀ s, 0 ≤ chi s) (k s : ℝ) : 0 ≤ cutoffDeletion g chi k s :=
  integral_nonneg fun u => mul_nonneg (hg u) (hchi _)

theorem cutoffDeletion_le_mass {g chi : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hchi : Continuous chi)
    (hgn : ∀ u, 0 ≤ g u) (hchi1 : ∀ s, chi s ≤ 1) (k s : ℝ) :
    cutoffDeletion g chi k s ≤ ∫ u, g u := by
  apply integral_mono (cutoffDeletion_integrable hg hgc hchi k s)
    (hg.integrable_of_hasCompactSupport hgc)
  intro u
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hchi1 _) (hgn u)

theorem cutoffDeletion_eq_mass {g chi : ℝ → ℝ} {k beta B s : ℝ} (hk : 0 < k)
    (hB : ∀ u ∈ Function.support g, u ≤ B)
    (hflat : ∀ x ≤ beta, chi x = 1) (hs : s ≤ beta-B/k) :
    cutoffDeletion g chi k s = ∫ u, g u := by
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : g u = 0
  · simp only [hu, zero_mul]
  · rw [hflat (s+u/k) ?_, mul_one]
    have hub := hB u hu
    have hud := (div_le_div_iff_of_pos_right hk).mpr hub
    linarith

theorem cancellationBracket_continuous {g chi : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hchi : Continuous chi) (lambda k : ℝ) (j : ℕ) :
    Continuous (cancellationBracket g chi lambda k j) :=
  hchi.sub ((cutoffDeletion_continuous hg hgc hchi k).const_mul _)

theorem cancellationBracket_abs_le_one {g chi : ℝ → ℝ} {lambda k : ℝ}
    (hlambda : 0 < lambda) (hk : 0 < k) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : ∀ u, 0 ≤ g u) (hgi : (∫ u, g u) = Real.sqrt lambda)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (j : ℕ) (hjk : (j:ℝ)+1 ≤ k) (s : ℝ) :
    |cancellationBracket g chi lambda k j s| ≤ 1 := by
  have hlr : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  have h0 := cutoffDeletion_nonneg hgn hchi0 k s
  have h1 := cutoffDeletion_le_mass hg hgc hchi hgn hchi1 k s
  rw [hgi] at h1
  have ha0 : 0 ≤ Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda := by positivity
  have ha1 : Real.sqrt (((j:ℝ)+1)/k) ≤ 1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by rw [one_pow]; exact (div_le_one hk).mpr hjk⟩
  have hprod : (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * cutoffDeletion g chi k s ≤ 1 := calc
    _ ≤ (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * Real.sqrt lambda :=
      mul_le_mul_of_nonneg_left h1 ha0
    _ = Real.sqrt (((j:ℝ)+1)/k) := div_mul_cancel₀ _ hlr.ne'
    _ ≤ 1 := ha1
  have hprodn := mul_nonneg ha0 h0
  unfold cancellationBracket
  rw [abs_le]
  constructor <;> linarith [hchi0 s, hchi1 s]

theorem cancellationBracket_flat {g chi : ℝ → ℝ} {lambda k beta B s : ℝ}
    (hlambda : 0 < lambda) (hk : 0 < k)
    (hgi : (∫ u, g u) = Real.sqrt lambda)
    (hB : ∀ u ∈ Function.support g, u ≤ B) (hB0 : 0 ≤ B)
    (hflat : ∀ x ≤ beta, chi x = 1) (hs : s ≤ beta-B/k) (j : ℕ) :
    cancellationBracket g chi lambda k j s = 1 - Real.sqrt (((j:ℝ)+1)/k) := by
  unfold cancellationBracket
  rw [cutoffDeletion_eq_mass hk hB hflat hs, hgi,
    hflat s (by linarith [div_nonneg hB0 hk.le]),
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr hlambda).ne']

theorem concentrated_function_sq {p b : ℝ → ℝ} (hp : Continuous p)
    (hpc : HasCompactSupport p) (hpn : ∀ u, 0 ≤ p u) (hpi : (∫ u, p u) = 1)
    (hb : Continuous b) (hb1 : ∀ s, |b s| ≤ 1)
    {beta d eta : ℝ} (hd : 0 < d) (heta : 0 ≤ eta)
    (hflat : ∀ s ≤ beta, b s^2 ≤ eta) (j : ℕ)
    (hmean : (j : ℝ) * (∫ u, u*p u) + d ≤ beta) :
    (∫ t : Fin j → ℝ, productDensity p j t * b (coordinateSum t)^2) ≤
      eta + ((j : ℝ) * ∫ u, (u - ∫ v, v*p v)^2 * p u) / d^2 := by
  let m : ℝ := (j : ℝ) * (∫ u, u*p u)
  have hD := productDensity_integrable hp hpc j
  have hC : Integrable (fun t : Fin j → ℝ =>
      productDensity p j t * b (coordinateSum t)^2) := by
    simpa only [mul_comm] using
      (poly_productDensity_integrable hp hpc
        (P := fun t : Fin j → ℝ => b (coordinateSum t)^2) (by
          unfold coordinateSum
          fun_prop))
  have hV : Integrable (fun t : Fin j → ℝ =>
      (coordinateSum t - m)^2 * productDensity p j t) :=
    poly_productDensity_integrable hp hpc (by unfold coordinateSum; fun_prop)
  have hle (t : Fin j → ℝ) :
      productDensity p j t * b (coordinateSum t)^2 ≤
        eta * productDensity p j t +
        ((coordinateSum t - m)^2 * productDensity p j t) / d^2 := by
    have hDn := productDensity_nonneg hpn j t
    have hvn : 0 ≤ ((coordinateSum t-m)^2 * productDensity p j t) / d^2 := by positivity
    by_cases ht : coordinateSum t ≤ beta
    · have hb2 := hflat _ ht
      nlinarith [mul_le_mul_of_nonneg_left hb2 hDn]
    · have hdm : d ≤ coordinateSum t - m := by dsimp only [m]; linarith
      have hd2 : 0 < d^2 := sq_pos_of_pos hd
      have hv2 : d^2 ≤ (coordinateSum t - m)^2 := by nlinarith
      have hDle : productDensity p j t ≤
          ((coordinateSum t - m)^2 * productDensity p j t) / d^2 := by
        apply (le_div_iff₀ hd2).mpr
        nlinarith [mul_le_mul_of_nonneg_left hv2 hDn]
      have hb2 : b (coordinateSum t)^2 ≤ 1 := by
        have := abs_le.mp (hb1 (coordinateSum t))
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hb2 hDn, mul_nonneg heta hDn]
  have hint := integral_mono hC ((hD.const_mul eta).add (hV.div_const (d^2))) hle
  dsimp only [Pi.add_apply] at hint
  rw [integral_add (hD.const_mul eta) (hV.div_const (d^2)), integral_const_mul,
    productDensity_integral hpi, mul_one, integral_div] at hint
  change _ ≤ eta + (∫ t : Fin j → ℝ,
    (coordinateSum t - (j:ℝ)*(∫ u, u*p u))^2 * productDensity p j t) / d^2 at hint
  rwa [coordinateSum_variance hp hpc hpi] at hint

theorem profile_first_moment_nonneg {g : ℝ → ℝ}
    (hs : Function.support g ⊆ Ioi 0) : 0 ≤ ∫ u, u * g u^2 := by
  apply integral_nonneg
  intro u
  by_cases hu : g u = 0
  · simp only [hu, zero_pow (by decide : 2 ≠ 0), mul_zero, Pi.zero_apply, le_refl]
  · exact mul_nonneg (hs hu).le (sq_nonneg _)

theorem scaled_level_moment_bound {g : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (hm : 0 ≤ ∫ u, u*g u^2) (j : ℕ) (hjk : (j:ℝ) ≤ k) :
    (j:ℝ) * (∫ u, u * scaledProfileDensity g k u) ≤ ∫ u, u*g u^2 := by
  rw [scaledProfileDensity_moment g hk]
  have : (j:ℝ) / k ≤ 1 := (div_le_one hk).mpr hjk
  have h := mul_le_mul_of_nonneg_right this hm
  simpa only [div_mul_eq_mul_div, mul_div_assoc, one_mul] using h

theorem scaled_level_variance_bound {g : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (j : ℕ) (hjk : (j:ℝ) ≤ k) :
    (j:ℝ) * (∫ u, (u-∫ v, v * scaledProfileDensity g k v)^2 *
      scaledProfileDensity g k u) ≤ (∫ u, (u-∫ v, v*g v^2)^2 * g u^2)/k := by
  rw [scaledProfileDensity_moment g hk, scaledProfileDensity_variance g hk]
  have hv : 0 ≤ ∫ u, (u-∫ v, v*g v^2)^2 * g u^2 :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdiv : (j:ℝ) / k^2 ≤ 1/k := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hk) hk).mpr
    nlinarith
  have h := mul_le_mul_of_nonneg_right hdiv hv
  simpa only [div_mul_eq_mul_div, mul_div_assoc, one_mul] using h

theorem scaled_cutoff_mass_bounds {g chi : ℝ → ℝ} {k beta : ℝ}
    (hk : 0 < k) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hg2 : (∫ u, g u^2) = 1)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta)
    (j : ℕ) (hjk : (j:ℝ) ≤ k) :
    let d := beta - ∫ u, u*g u^2
    let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
    1-v/(k*d^2) ≤ (∫ t : Fin j → ℝ,
      productDensity (scaledProfileDensity g k) j t * chi (coordinateSum t)^2) ∧
    (∫ t : Fin j → ℝ,
      productDensity (scaledProfileDensity g k) j t * chi (coordinateSum t)^2) ≤ 1 := by
  dsimp only
  have hp := scaledProfileDensity_continuous hg k
  have hpc := scaledProfileDensity_compact hgc hk.ne'
  have hpn : ∀ u, 0 ≤ scaledProfileDensity g k u := fun u => mul_nonneg hk.le (sq_nonneg _)
  have hpi := scaledProfileDensity_integral hk hg2
  constructor
  · have hb := concentrated_cutoff_mass hp hpc hpn hpi hchi hchi0 hchi1
      (sub_pos.mpr hmu) hflat j (by
        have := scaled_level_moment_bound hk (profile_first_moment_nonneg hgs) j hjk
        linarith)
    have hv := scaled_level_variance_bound (g := g) hk j hjk
    have hd2 : 0 < (beta - ∫ u, u*g u^2)^2 := sq_pos_of_pos (sub_pos.mpr hmu)
    have hdiv := div_le_div_of_nonneg_right hv hd2.le
    have heq : (∫ u, (u-∫ v, v*g v^2)^2 * g u^2)/k/(beta-∫ u, u*g u^2)^2 =
      (∫ u, (u-∫ v, v*g v^2)^2 * g u^2)/(k*(beta-∫ u, u*g u^2)^2) := by rw [div_div]
    rw [heq] at hdiv
    linarith
  · exact cutoff_mass_le_one hp hpc hpn hpi hchi hchi0 hchi1 j

theorem one_sub_sqrt_level_sq {k r : ℝ} (hk : 0 < k) (hr : 0 ≤ r)
    (j : ℕ) (hupper : (j:ℝ)+1 ≤ k) (hlower : k-r ≤ (j:ℝ)+1) :
    (1-Real.sqrt (((j:ℝ)+1)/k))^2 ≤ (r/k)^2 := by
  have hx : 0 ≤ ((j:ℝ)+1)/k := by positivity
  have hx1 : ((j:ℝ)+1)/k ≤ 1 := (div_le_one hk).mpr hupper
  have hs : Real.sqrt (((j:ℝ)+1)/k)^2 = ((j:ℝ)+1)/k := Real.sq_sqrt hx
  have hs0 := Real.sqrt_nonneg (((j:ℝ)+1)/k)
  have hs1 : Real.sqrt (((j:ℝ)+1)/k) ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using hx1⟩
  have hxs : ((j:ℝ)+1)/k ≤ Real.sqrt (((j:ℝ)+1)/k) := by nlinarith
  have hl : 1-r/k ≤ ((j:ℝ)+1)/k := by
    have := (div_le_div_iff_of_pos_right hk).mpr hlower
    rw [sub_div, div_self hk.ne'] at this
    exact this
  have hrk : 0 ≤ r/k := div_nonneg hr hk.le
  nlinarith

theorem scaled_cancellation_integral_bound {g chi : ℝ → ℝ}
    {lambda k r beta B : ℝ} (hlambda : 0 < lambda) (hk : 0 < k) (hr : 0 ≤ r)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hgn : ∀ u, 0 ≤ g u)
    (hg2 : (∫ u, g u^2) = 1) (hg1 : (∫ u, g u) = Real.sqrt lambda)
    (hB : ∀ u ∈ Function.support g, u ≤ B) (hB0 : 0 ≤ B)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta)
    (hBk : B/k ≤ (beta - ∫ u, u*g u^2)/2)
    (j : ℕ) (hupper : (j:ℝ)+1 ≤ k) (hlower : k-r ≤ (j:ℝ)+1) :
    let d := beta - ∫ u, u*g u^2
    let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
    (∫ t : Fin j → ℝ, productDensity (scaledProfileDensity g k) j t *
      cancellationBracket g chi lambda k j (coordinateSum t)^2) ≤
      (r/k)^2 + 4*v/(k*d^2) := by
  dsimp only
  let d : ℝ := beta - ∫ u, u*g u^2
  have hd : 0 < d := sub_pos.mpr hmu
  have hp := scaledProfileDensity_continuous hg k
  have hpc := scaledProfileDensity_compact hgc hk.ne'
  have hpn : ∀ u, 0 ≤ scaledProfileDensity g k u := fun u => mul_nonneg hk.le (sq_nonneg _)
  have hpi := scaledProfileDensity_integral hk hg2
  have hb := concentrated_function_sq hp hpc hpn hpi
    (cancellationBracket_continuous hg hgc hchi lambda k j)
    (cancellationBracket_abs_le_one hlambda hk hg hgc hgn hg1 hchi hchi0 hchi1 j hupper)
    (beta := beta-B/k) (d := d/2) (div_pos hd (by norm_num)) (sq_nonneg (r/k))
    (fun s hs => by
      rw [cancellationBracket_flat hlambda hk hg1 hB hB0 hflat hs j]
      exact one_sub_sqrt_level_sq hk hr j hupper hlower) j (by
      have := scaled_level_moment_bound hk (profile_first_moment_nonneg hgs) j (by linarith)
      dsimp only [d]
      linarith)
  have hv := scaled_level_variance_bound (g := g) hk j (by linarith)
  have hdiv := div_le_div_of_nonneg_right hv (sq_nonneg (d/2))
  have heq (v : ℝ) : v/k/(d/2)^2 = 4*v/(k*d^2) := by
    field_simp
    norm_num
  rw [heq] at hdiv
  exact hb.trans (add_le_add (le_refl _) hdiv)

theorem alpha_pos {lambda : ℝ} (hlambda : 0 < lambda) (j : ℕ) : 0 < alpha lambda j :=
  div_pos (pow_pos hlambda j) (by exact_mod_cast Nat.factorial_pos j)

theorem alpha_succ (lambda : ℝ) (j : ℕ) :
    alpha lambda (j+1) = alpha lambda j * lambda / ((j:ℝ)+1) := by
  unfold alpha
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  rw [div_mul_eq_mul_div, div_div, mul_comm (j.factorial:ℝ)]

theorem sqrt_alpha_succ_ratio {lambda k : ℝ} (hlambda : 0 < lambda) (hk : 0 < k) (j : ℕ) :
    Real.sqrt (alpha lambda j) * (Real.sqrt k / k) /
      Real.sqrt (alpha lambda (j+1)) = Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda := by
  have ha := alpha_pos hlambda j
  have ha1 := alpha_pos hlambda (j+1)
  have hlr := Real.sqrt_pos.mpr hlambda
  have hkr := Real.sqrt_pos.mpr hk
  have har := Real.sqrt_pos.mpr ha
  have ha1r := Real.sqrt_pos.mpr ha1
  have hj : 0 < (j:ℝ)+1 := by positivity
  have hs : (Real.sqrt (((j:ℝ)+1)/k))^2 = ((j:ℝ)+1)/k :=
    Real.sq_sqrt (div_nonneg hj.le hk.le)
  have heq : (Real.sqrt (alpha lambda j) * (Real.sqrt k / k) /
      Real.sqrt (alpha lambda (j+1)))^2 =
      (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda)^2 := by
    rw [div_pow, mul_pow, div_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hk.le,
      Real.sq_sqrt ha1.le, div_pow, hs, Real.sq_sqrt hlambda.le, alpha_succ]
    field_simp [ha.ne', hk.ne', hlambda.ne', hj.ne']
  have hleft : 0 ≤ Real.sqrt (alpha lambda j) * (Real.sqrt k / k) /
      Real.sqrt (alpha lambda (j+1)) := by positivity
  have hright : 0 ≤ Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda := by positivity
  nlinarith

theorem productProfile_snoc (g : ℝ → ℝ) (k : ℝ) (j : ℕ) (t : Fin j → ℝ) (u : ℝ) :
    productProfile g k (j+1) (Fin.snoc t u) = productProfile g k j t * Real.sqrt k * g (k*u) := by
  unfold productProfile
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem coordinateSum_snoc (j : ℕ) (t : Fin j → ℝ) (u : ℝ) :
    coordinateSum (Fin.snoc t u) = coordinateSum t + u := by
  unfold coordinateSum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem levelFunction_delete {g chi : ℝ → ℝ} {lambda k r : ℝ}
    (hk : 0 < k) (j : ℕ) (t : Fin j → ℝ) :
    deleteCoordinate (levelFunction g chi lambda k r (j+1)) t =
      ((-1:ℝ)^(j+1) / (Real.sqrt r * Real.sqrt (alpha lambda (j+1)))) *
      productProfile g k j t * (Real.sqrt k / k) * cutoffDeletion g chi k (coordinateSum t) := by
  unfold deleteCoordinate levelFunction
  simp only [productProfile_snoc, coordinateSum_snoc]
  let A := ((-1:ℝ)^(j+1) / (Real.sqrt r * Real.sqrt (alpha lambda (j+1)))) *
    productProfile g k j t * Real.sqrt k
  have heq : (fun u => ((-1:ℝ)^(j+1) / (Real.sqrt r * Real.sqrt (alpha lambda (j+1)))) *
      (productProfile g k j t * Real.sqrt k * g (k*u)) * chi (coordinateSum t+u)) =
      fun u => A * (g (k*u) * chi (coordinateSum t+(k*u)/k)) := by
    funext u
    dsimp only [A]
    rw [mul_div_cancel_left₀ _ hk.ne']
    ring
  rw [heq, integral_const_mul]
  rw [Measure.integral_comp_mul_left (fun u => g u * chi (coordinateSum t+u/k)) k,
    abs_of_pos (inv_pos.mpr hk), smul_eq_mul]
  unfold cutoffDeletion
  dsimp only [A]
  ring

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_LevelMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem levelFunction_weighted (g chi : ℝ → ℝ) {lambda r : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (k : ℝ) (j : ℕ) (t : Fin j → ℝ) :
    Real.sqrt (alpha lambda j) * levelFunction g chi lambda k r j t =
      ((-1:ℝ)^j / Real.sqrt r) * productProfile g k j t * chi (coordinateSum t) := by
  have ha : Real.sqrt (alpha lambda j) ≠ 0 := (Real.sqrt_pos.mpr (alpha_pos hlambda j)).ne'
  have hr0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  unfold levelFunction
  field_simp

theorem levelFunction_pair_weighted (g chi : ℝ → ℝ) {lambda k r : ℝ}
    (hlambda : 0 < lambda) (hk : 0 < k) (hr : 0 < r) (j : ℕ) (t : Fin j → ℝ) :
    Real.sqrt (alpha lambda j) *
      (levelFunction g chi lambda k r j t +
        deleteCoordinate (levelFunction g chi lambda k r (j+1)) t) =
      ((-1:ℝ)^j / Real.sqrt r) * productProfile g k j t *
        cancellationBracket g chi lambda k j (coordinateSum t) := by
  rw [mul_add, levelFunction_weighted g chi hlambda hr, levelFunction_delete hk]
  have hr0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have ha1 : Real.sqrt (alpha lambda (j+1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (alpha_pos hlambda (j+1))).ne'
  have hratio := sqrt_alpha_succ_ratio hlambda hk j
  unfold cancellationBracket
  rw [← hratio, pow_succ]
  field_simp
  ring

theorem sign_pow_sq (j : ℕ) : ((-1:ℝ)^j)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  simp

theorem levelFunction_sq (g chi : ℝ → ℝ) {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 ≤ k) (j : ℕ) (t : Fin j → ℝ) :
    alpha lambda j * levelFunction g chi lambda k r j t^2 =
      (1/r) * (productDensity (scaledProfileDensity g k) j t * chi (coordinateSum t)^2) := by
  have h := congrArg (fun x : ℝ => x^2) (levelFunction_weighted g chi hlambda hr k j t)
  simp only [mul_pow, div_pow, Real.sq_sqrt (alpha_pos hlambda j).le,
    Real.sq_sqrt hr.le, productProfile_sq g hk, sign_pow_sq] at h
  simpa only [mul_assoc] using h

theorem levelFunction_pair_sq (g chi : ℝ → ℝ) {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 < k) (j : ℕ) (t : Fin j → ℝ) :
    alpha lambda j * (levelFunction g chi lambda k r j t +
      deleteCoordinate (levelFunction g chi lambda k r (j+1)) t)^2 =
      (1/r) * (productDensity (scaledProfileDensity g k) j t *
        cancellationBracket g chi lambda k j (coordinateSum t)^2) := by
  have h := congrArg (fun x : ℝ => x^2) (levelFunction_pair_weighted g chi hlambda hk hr j t)
  simp only [mul_pow, div_pow, Real.sq_sqrt (alpha_pos hlambda j).le,
    Real.sq_sqrt hr.le, productProfile_sq g hk.le, sign_pow_sq] at h
  simpa only [mul_assoc] using h

theorem l2Mass_nonneg {j : ℕ} (f : (Fin j → ℝ) → ℝ) : 0 ≤ l2Mass f :=
  integral_nonneg fun t => sq_nonneg (f t)

theorem levelFunction_l2Mass (g chi : ℝ → ℝ) {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 ≤ k) (j : ℕ) :
    alpha lambda j * l2Mass (levelFunction g chi lambda k r j) =
      (1/r) * (∫ t : Fin j → ℝ,
        productDensity (scaledProfileDensity g k) j t * chi (coordinateSum t)^2) := by
  unfold l2Mass
  rw [← integral_const_mul, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (levelFunction_sq g chi hlambda hr hk j))

theorem levelFunction_pair_l2Mass (g chi : ℝ → ℝ) {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 < k) (j : ℕ) :
    alpha lambda j * l2Mass (fun t => levelFunction g chi lambda k r j t +
      deleteCoordinate (levelFunction g chi lambda k r (j+1)) t) =
      (1/r) * (∫ t : Fin j → ℝ, productDensity (scaledProfileDensity g k) j t *
        cancellationBracket g chi lambda k j (coordinateSum t)^2) := by
  unfold l2Mass
  rw [← integral_const_mul, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (levelFunction_pair_sq g chi hlambda hr hk j))

theorem levelFunction_delete_sq (g chi : ℝ → ℝ) {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 < k) (j : ℕ) (t : Fin j → ℝ) :
    alpha lambda j * (deleteCoordinate (levelFunction g chi lambda k r (j+1)) t)^2 =
      (1/r) * (productDensity (scaledProfileDensity g k) j t *
        ((Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) *
          cutoffDeletion g chi k (coordinateSum t))^2) := by
  have heq : Real.sqrt (alpha lambda j) *
      deleteCoordinate (levelFunction g chi lambda k r (j+1)) t =
      - (((-1:ℝ)^j / Real.sqrt r) * productProfile g k j t *
        ((Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) *
          cutoffDeletion g chi k (coordinateSum t))) := by
    calc
      _ = Real.sqrt (alpha lambda j) * (levelFunction g chi lambda k r j t +
        deleteCoordinate (levelFunction g chi lambda k r (j+1)) t) -
        Real.sqrt (alpha lambda j) * levelFunction g chi lambda k r j t := by ring
      _ = _ := by
        rw [levelFunction_pair_weighted g chi hlambda hk hr,
          levelFunction_weighted g chi hlambda hr]
        unfold cancellationBracket
        ring
  have h := congrArg (fun x : ℝ => x^2) heq
  rw [mul_pow, Real.sq_sqrt (alpha_pos hlambda j).le, neg_sq] at h
  have hright : (((-1:ℝ)^j / Real.sqrt r) * productProfile g k j t)^2 =
      (1/r) * productDensity (scaledProfileDensity g k) j t := by
    rw [mul_pow, div_pow, Real.sq_sqrt hr.le, productProfile_sq g hk.le, sign_pow_sq]
  rw [mul_pow, hright] at h
  simpa only [mul_assoc] using h

theorem scaled_cutoffDeletion_bounds {g chi : ℝ → ℝ} {lambda k : ℝ}
    (hlambda : 0 < lambda) (hk : 0 < k) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : ∀ u, 0 ≤ g u) (hgi : (∫ u, g u) = Real.sqrt lambda)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (j : ℕ) (hjk : (j:ℝ)+1 ≤ k) (s : ℝ) :
    0 ≤ (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * cutoffDeletion g chi k s ∧
    (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * cutoffDeletion g chi k s ≤ 1 := by
  have hlr : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hlambda
  have h0 := cutoffDeletion_nonneg hgn hchi0 k s
  have h1 := cutoffDeletion_le_mass hg hgc hchi hgn hchi1 k s
  rw [hgi] at h1
  have ha0 : 0 ≤ Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda := by positivity
  refine ⟨mul_nonneg ha0 h0, ?_⟩
  calc
    _ ≤ (Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * Real.sqrt lambda :=
      mul_le_mul_of_nonneg_left h1 ha0
    _ = Real.sqrt (((j:ℝ)+1)/k) := div_mul_cancel₀ _ hlr.ne'
    _ ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using (div_le_one hk).mpr hjk⟩

theorem levelFunction_delete_l2Mass_bound {g chi : ℝ → ℝ} {lambda r k : ℝ}
    (hlambda : 0 < lambda) (hr : 0 < r) (hk : 0 < k)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgn : ∀ u, 0 ≤ g u) (hg2 : (∫ u, g u^2) = 1) (hg1 : (∫ u, g u) = Real.sqrt lambda)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (j : ℕ) (hjk : (j:ℝ)+1 ≤ k) :
    alpha lambda j * l2Mass (deleteCoordinate (levelFunction g chi lambda k r (j+1))) ≤ 1/r := by
  have hp := scaledProfileDensity_continuous hg k
  have hpc := scaledProfileDensity_compact hgc hk.ne'
  have hpi := scaledProfileDensity_integral hk hg2
  have hD := productDensity_integrable hp hpc j
  let P : (Fin j → ℝ) → ℝ := fun t =>
    ((Real.sqrt (((j:ℝ)+1)/k) / Real.sqrt lambda) * cutoffDeletion g chi k (coordinateSum t))^2
  have hP : Continuous P := by
    apply Continuous.pow
    apply Continuous.const_mul
    exact (cutoffDeletion_continuous hg hgc hchi k).comp (by unfold coordinateSum; fun_prop)
  have hPD : Integrable (fun t : Fin j → ℝ => productDensity (scaledProfileDensity g k) j t * P t) := by
    simpa only [mul_comm] using poly_productDensity_integrable hp hpc hP
  have hv : (∫ t : Fin j → ℝ, productDensity (scaledProfileDensity g k) j t * P t) ≤ 1 := by
    rw [← productDensity_integral hpi j]
    apply integral_mono hPD hD
    intro t
    have hb := scaled_cutoffDeletion_bounds hlambda hk hg hgc hgn hg1 hchi hchi0 hchi1 j hjk (coordinateSum t)
    have hP1 : P t ≤ 1 := by dsimp only [P]; nlinarith
    have hpn : ∀ u, 0 ≤ scaledProfileDensity g k u := fun u => mul_nonneg hk.le (sq_nonneg _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hP1 (productDensity_nonneg hpn j t)
  have heq : alpha lambda j * l2Mass (deleteCoordinate (levelFunction g chi lambda k r (j+1))) =
      (1/r) * ∫ t : Fin j → ℝ, productDensity (scaledProfileDensity g k) j t * P t := by
    unfold l2Mass
    rw [← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (levelFunction_delete_sq g chi hlambda hr hk j))
  rw [heq]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (one_div_pos.mpr hr).le

theorem cancellationFamily_of_mem {g chi : ℝ → ℝ} {lambda : ℝ} {k r j : ℕ}
    (hj : j ∈ activeLevels k r) :
    cancellationFamily g chi lambda k r j = levelFunction g chi lambda k r j := ite_eq_left hj

theorem cancellationFamily_of_not_mem {g chi : ℝ → ℝ} {lambda : ℝ} {k r j : ℕ}
    (hj : j ∉ activeLevels k r) : cancellationFamily g chi lambda k r j = 0 := ite_eq_right hj

theorem activeLevels_card {k r : ℕ} (hrk : r ≤ k) : (activeLevels k r).card = r := by
  simp only [activeLevels, Nat.card_Icc]
  omega

theorem activeLevels_subset_range (k r : ℕ) : activeLevels k r ⊆ Finset.range (k+1) := by
  intro j hj
  simp only [activeLevels, Finset.mem_Icc, Finset.mem_range] at *
  omega

theorem cancellationFamily_zero (g chi : ℝ → ℝ) (lambda : ℝ) (k r : ℕ) :
    cancellationFamily g chi lambda k r 0 = 0 := by
  apply cancellationFamily_of_not_mem
  simp [activeLevels]

theorem cancellationFamily_above (g chi : ℝ → ℝ) (lambda : ℝ) (k r : ℕ)
    {j : ℕ} (hj : k < j) : cancellationFamily g chi lambda k r j = 0 := by
  apply cancellationFamily_of_not_mem
  simp only [activeLevels, Finset.mem_Icc, not_and]
  exact fun _ => hj.not_ge

theorem cancellationFamily_W (g chi : ℝ → ℝ) (lambda : ℝ) (k r : ℕ) :
    familyW lambda k (cancellationFamily g chi lambda k r) =
      ∑ j ∈ activeLevels k r, alpha lambda j * l2Mass (levelFunction g chi lambda k r j) := by
  unfold familyW
  calc
    _ = ∑ j ∈ activeLevels k r, alpha lambda j *
      l2Mass (cancellationFamily g chi lambda k r j) := by
      symm
      apply Finset.sum_subset (activeLevels_subset_range k r)
      intro j _ hj
      rw [cancellationFamily_of_not_mem hj, l2Mass_zero, mul_zero]
    _ = _ := Finset.sum_congr rfl fun j hj => by rw [cancellationFamily_of_mem hj]

theorem cancellationFamily_W_bounds {g chi : ℝ → ℝ} {lambda beta : ℝ}
    {k r : ℕ} (hlambda : 0 < lambda) (hr : 0 < r) (hrk : r ≤ k)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hg2 : (∫ u, g u^2) = 1)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta) :
    let d := beta - ∫ u, u*g u^2
    let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
    1-v/((k:ℝ)*d^2) ≤ familyW lambda k (cancellationFamily g chi lambda k r) ∧
    familyW lambda k (cancellationFamily g chi lambda k r) ≤ 1 := by
  dsimp only
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (lt_of_lt_of_le hr hrk)
  rw [cancellationFamily_W]
  have heq (j : ℕ) := levelFunction_l2Mass g chi hlambda hr0 hk0.le j
  simp_rw [heq, ← Finset.mul_sum]
  have hcard : ((activeLevels k r).card:ℝ) = (r:ℝ) := by rw [activeLevels_card hrk]
  constructor
  · have hb := Finset.sum_le_sum (s := activeLevels k r) (fun j hj =>
      (scaled_cutoff_mass_bounds hk0 hg hgc hgs hg2 hchi hchi0 hchi1 hflat hmu j
        (by exact_mod_cast (Finset.mem_Icc.mp hj).2)).1)
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hb
    have h := mul_le_mul_of_nonneg_left hb (one_div_pos.mpr hr0).le
    simpa only [← mul_assoc, one_div_mul_cancel hr0.ne', one_mul] using h
  · have hb := Finset.sum_le_sum (s := activeLevels k r) (fun j hj =>
      (scaled_cutoff_mass_bounds hk0 hg hgc hgs hg2 hchi hchi0 hchi1 hflat hmu j
        (by exact_mod_cast (Finset.mem_Icc.mp hj).2)).2)
    simp only [Finset.sum_const, nsmul_eq_mul, hcard, mul_one] at hb
    have h := mul_le_mul_of_nonneg_left hb (one_div_pos.mpr hr0).le
    simpa only [one_div_mul_cancel hr0.ne'] using h

theorem cancellationFamily_V_split (g chi : ℝ → ℝ) (lambda : ℝ) {k r : ℕ}
    (hr : 0 < r) (hrk : r ≤ k) :
    familyV lambda k (cancellationFamily g chi lambda k r) = lambda *
      (alpha lambda (k-r) * l2Mass (deleteCoordinate (levelFunction g chi lambda k r (k-r+1))) +
       alpha lambda k * l2Mass (levelFunction g chi lambda k r k) +
       ∑ j ∈ Finset.Ioo (k-r) k, alpha lambda j * l2Mass (fun t =>
         levelFunction g chi lambda k r j t +
           deleteCoordinate (levelFunction g chi lambda k r (j+1)) t)) := by
  have hb : k-r < k := by omega
  have hsub : Finset.Icc (k-r) k ⊆ Finset.range (k+1) := by
    intro j hj
    have := (Finset.mem_Icc.mp hj).2
    simpa only [Finset.mem_range] using Nat.lt_succ_of_le this
  let A : ℕ → ℝ := fun j => alpha lambda j * l2Mass (fun t =>
    cancellationFamily g chi lambda k r j t +
      deleteCoordinate (cancellationFamily g chi lambda k r (j+1)) t)
  have hres : ∑ j ∈ Finset.range (k+1), A j = ∑ j ∈ Finset.Icc (k-r) k, A j := by
    symm
    apply Finset.sum_subset hsub
    intro j hj hn
    have h0 : j ∉ activeLevels k r := by
      simp only [activeLevels, Finset.mem_Icc, Finset.mem_range] at *
      omega
    have h1 : j+1 ∉ activeLevels k r := by
      simp only [activeLevels, Finset.mem_Icc, Finset.mem_range] at *
      omega
    simp only [A, cancellationFamily_of_not_mem h0, cancellationFamily_of_not_mem h1,
      deleteCoordinate_zero, Pi.zero_apply, zero_add]
    change alpha lambda j * l2Mass (0 : (Fin j → ℝ) → ℝ) = 0
    rw [l2Mass_zero, mul_zero]
  have hset : Finset.Icc (k-r) k = insert (k-r) (insert k (Finset.Ioo (k-r) k)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  have hn0 : k-r ∉ insert k (Finset.Ioo (k-r) k) := by simp; omega
  have hn1 : k ∉ Finset.Ioo (k-r) k := by simp
  have ha0 : k-r ∉ activeLevels k r := by simp [activeLevels]
  have ha1 : k-r+1 ∈ activeLevels k r := by simp only [activeLevels, Finset.mem_Icc]; omega
  have hak : k ∈ activeLevels k r := by simp only [activeLevels, Finset.mem_Icc]; omega
  have ha2 : k+1 ∉ activeLevels k r := by simp [activeLevels]
  have hbterm : A (k-r) = alpha lambda (k-r) *
      l2Mass (deleteCoordinate (levelFunction g chi lambda k r (k-r+1))) := by
    simp only [A, cancellationFamily_of_not_mem ha0, cancellationFamily_of_mem ha1,
      Pi.zero_apply, zero_add]
  have htterm : A k = alpha lambda k * l2Mass (levelFunction g chi lambda k r k) := by
    simp only [A, cancellationFamily_of_mem hak, cancellationFamily_of_not_mem ha2,
      deleteCoordinate_zero, Pi.zero_apply, add_zero]
  have hmid : ∑ j ∈ Finset.Ioo (k-r) k, A j =
      ∑ j ∈ Finset.Ioo (k-r) k, alpha lambda j * l2Mass (fun t =>
        levelFunction g chi lambda k r j t +
          deleteCoordinate (levelFunction g chi lambda k r (j+1)) t) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : j ∈ activeLevels k r := by
      simp only [activeLevels, Finset.mem_Icc, Finset.mem_Ioo] at *
      omega
    have hj1 : j+1 ∈ activeLevels k r := by
      simp only [activeLevels, Finset.mem_Icc, Finset.mem_Ioo] at *
      omega
    simp only [A, cancellationFamily_of_mem hj0, cancellationFamily_of_mem hj1]
  change lambda * (∑ j ∈ Finset.range (k+1), A j) = _
  rw [hres, hset, Finset.sum_insert hn0, Finset.sum_insert hn1, hbterm, htterm, hmid]
  ring

theorem familyV_nonneg {lambda : ℝ} (hlambda : 0 < lambda) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) : 0 ≤ familyV lambda k f := by
  exact mul_nonneg hlambda.le (Finset.sum_nonneg fun j _ =>
    mul_nonneg (alpha_pos hlambda j).le (l2Mass_nonneg _))

theorem cancellationFamily_V_bound {g chi : ℝ → ℝ} {lambda beta B : ℝ}
    {k r : ℕ} (hlambda : 0 < lambda) (hr : 0 < r) (hrk : r ≤ k)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hgn : ∀ u, 0 ≤ g u)
    (hg2 : (∫ u, g u^2) = 1) (hg1 : (∫ u, g u) = Real.sqrt lambda)
    (hB : ∀ u ∈ Function.support g, u ≤ B) (hB0 : 0 ≤ B)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta)
    (hBk : B/(k:ℝ) ≤ (beta - ∫ u, u*g u^2)/2) :
    let d := beta - ∫ u, u*g u^2
    let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
    familyV lambda k (cancellationFamily g chi lambda k r) ≤
      lambda * (2/(r:ℝ) + ((r:ℝ)/k)^2 + 4*v/((k:ℝ)*d^2)) := by
  dsimp only
  have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (lt_of_lt_of_le hr hrk)
  let E := ((r:ℝ)/k)^2 + 4*(∫ u, (u-∫ v, v*g v^2)^2 * g u^2)/
    ((k:ℝ)*(beta-∫ u, u*g u^2)^2)
  have hE : 0 ≤ E := by
    have hv : 0 ≤ ∫ u, (u-∫ v, v*g v^2)^2 * g u^2 :=
      integral_nonneg (fun u : ℝ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    dsimp only [E]
    positivity
  rw [cancellationFamily_V_split g chi lambda hr hrk]
  have hbot := levelFunction_delete_l2Mass_bound hlambda hr0 hk0 hg hgc hgn hg2 hg1
    hchi hchi0 hchi1 (k-r) (by exact_mod_cast (show k-r+1 ≤ k by omega))
  have htop : alpha lambda k * l2Mass (levelFunction g chi lambda k r k) ≤ 1/(r:ℝ) := by
    rw [levelFunction_l2Mass g chi hlambda hr0 hk0.le]
    have hb := (scaled_cutoff_mass_bounds hk0 hg hgc hgs hg2 hchi hchi0 hchi1 hflat hmu k le_rfl).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (one_div_pos.mpr hr0).le
  have hmidpoint (j : ℕ) (hj : j ∈ Finset.Ioo (k-r) k) :
      alpha lambda j * l2Mass (fun t => levelFunction g chi lambda k r j t +
        deleteCoordinate (levelFunction g chi lambda k r (j+1)) t) ≤ (1/(r:ℝ))*E := by
    rw [levelFunction_pair_l2Mass g chi hlambda hr0 hk0]
    apply mul_le_mul_of_nonneg_left _ (one_div_pos.mpr hr0).le
    apply scaled_cancellation_integral_bound hlambda hk0 hr0.le hg hgc hgs hgn hg2 hg1
      hB hB0 hchi hchi0 hchi1 hflat hmu hBk j
    · exact_mod_cast (show j+1 ≤ k from (Finset.mem_Ioo.mp hj).2)
    · have h1 : k ≤ (j+1)+r := by have := (Finset.mem_Ioo.mp hj).1; omega
      have h2 : (k:ℝ) ≤ ((j+1)+r:ℕ) := by exact_mod_cast h1
      push_cast at h2
      linarith
  have hmid := Finset.sum_le_sum hmidpoint
  have hcard : ((Finset.Ioo (k-r) k).card:ℝ) ≤ (r:ℝ) := by
    exact_mod_cast (show (Finset.Ioo (k-r) k).card ≤ r by rw [Nat.card_Ioo]; omega)
  simp only [Finset.sum_const, nsmul_eq_mul] at hmid
  have hmid' : (∑ j ∈ Finset.Ioo (k-r) k, alpha lambda j * l2Mass (fun t =>
      levelFunction g chi lambda k r j t +
        deleteCoordinate (levelFunction g chi lambda k r (j+1)) t)) ≤ E := by
    calc
      _ ≤ ((Finset.Ioo (k-r) k).card:ℝ) * ((1/(r:ℝ))*E) := hmid
      _ ≤ (r:ℝ)*((1/(r:ℝ))*E) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (one_div_pos.mpr hr0).le hE)
      _ = E := by field_simp
  apply mul_le_mul_of_nonneg_left _ hlambda.le
  calc
    _ ≤ 1/(r:ℝ) + 1/(r:ℝ) + E := add_le_add (add_le_add hbot htop) hmid'
    _ = _ := by dsimp only [E]; ring

theorem productProfile_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (productProfile g k j) := by
  unfold productProfile
  fun_prop

theorem levelFunction_smooth {g chi : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hchi : ContDiff ℝ ∞ chi)
    (lambda k r : ℝ) (j : ℕ) : ContDiff ℝ ∞ (levelFunction g chi lambda k r j) := by
  unfold levelFunction
  exact (contDiff_const.mul (productProfile_smooth hg k j)).mul
    (hchi.comp (by unfold coordinateSum; fun_prop))

theorem productProfile_compact {g : ℝ → ℝ} (hg : HasCompactSupport g)
    {k : ℝ} (hk : k ≠ 0) (j : ℕ) : HasCompactSupport (productProfile g k j) := by
  apply productDensity_compact (p := fun u : ℝ => Real.sqrt k * g (k*u))
  exact (hg.comp_smul hk).mul_left

theorem levelFunction_compact {g : ℝ → ℝ} (hg : HasCompactSupport g)
    (chi : ℝ → ℝ) (lambda r : ℝ) {k : ℝ} (hk : k ≠ 0) (j : ℕ) :
    HasCompactSupport (levelFunction g chi lambda k r j) := by
  exact ((productProfile_compact hg hk j).mul_left).mul_right

theorem productProfile_symmetric (g : ℝ → ℝ) (k : ℝ) (j : ℕ) :
    SymmetricFunction (productProfile g k j) := by
  intro e t
  exact Equiv.prod_comp e (fun i => Real.sqrt k * g (k*t i))

theorem coordinateSum_comp_perm {j : ℕ} (e : Equiv.Perm (Fin j)) (t : Fin j → ℝ) :
    coordinateSum (t ∘ e) = coordinateSum t := Equiv.sum_comp e t

theorem levelFunction_symmetric (g chi : ℝ → ℝ) (lambda k r : ℝ) (j : ℕ) :
    SymmetricFunction (levelFunction g chi lambda k r j) := by
  intro e t
  simp only [levelFunction, productProfile_symmetric g k j e t, coordinateSum_comp_perm]

theorem levelFunction_tsupport_subset {g chi : ℝ → ℝ} {lambda k r gamma : ℝ}
    (hchi : ∀ s, gamma ≤ s → chi s = 0) (j : ℕ) :
    tsupport (levelFunction g chi lambda k r j) ⊆
      {t | (∀ i, k*t i ∈ tsupport g) ∧ coordinateSum t ≤ gamma} := by
  apply closure_minimal
  · intro t ht
    have hQ : productProfile g k j t ≠ 0 := by
      intro h
      exact ht (by simp only [levelFunction, h, mul_zero, zero_mul])
    have hc : chi (coordinateSum t) ≠ 0 := by
      intro h
      exact ht (by simp only [levelFunction, h, mul_zero])
    refine ⟨fun i => subset_closure ?_, ?_⟩
    · have h := (Finset.prod_ne_zero_iff.mp hQ) i (Finset.mem_univ i)
      exact fun he => h (by simp [he])
    · exact (lt_of_not_ge fun h => hc (hchi _ h)).le
  · have hc : IsClosed {t : Fin j → ℝ | ∀ i, k*t i ∈ tsupport g} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter (fun i : Fin j =>
        (isClosed_tsupport g).preimage (show Continuous (fun t : Fin j → ℝ => k*t i) by fun_prop))
    have hs : IsClosed {t : Fin j → ℝ | coordinateSum t ≤ gamma} :=
      isClosed_le (show Continuous (fun t : Fin j → ℝ => coordinateSum t) by
        unfold coordinateSum; fun_prop) continuous_const
    exact hc.inter hs

theorem levelFunction_interior_support {g chi : ℝ → ℝ} {lambda k r gamma tau : ℝ}
    (hk : 0 < k) (hgs : tsupport g ⊆ Ioi 0) (hgt : gamma < tau)
    (hchi : ∀ s, gamma ≤ s → chi s = 0) (j : ℕ) :
    tsupport (levelFunction g chi lambda k r j) ⊆ positiveSimplex j tau := by
  intro t ht
  obtain ⟨hc, hs⟩ := levelFunction_tsupport_subset hchi j ht
  refine ⟨fun i => ?_, hs.trans_lt hgt⟩
  exact (mul_pos_iff_of_pos_left hk).mp (hgs (hc i))

theorem cancellationFamily_properties {g chi : ℝ → ℝ} {lambda gamma tau : ℝ}
    {k r : ℕ} (hk : 0 < k) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ Ioi 0) (hchi : ContDiff ℝ ∞ chi)
    (hgt : gamma < tau) (hchiz : ∀ s, gamma ≤ s → chi s = 0) (j : ℕ) :
    ContDiff ℝ ∞ (cancellationFamily g chi lambda k r j) ∧
    HasCompactSupport (cancellationFamily g chi lambda k r j) ∧
    tsupport (cancellationFamily g chi lambda k r j) ⊆ positiveSimplex j tau ∧
    SymmetricFunction (cancellationFamily g chi lambda k r j) := by
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  by_cases hj : j ∈ activeLevels k r
  · rw [cancellationFamily_of_mem hj]
    exact ⟨levelFunction_smooth hg hchi _ _ _ _, levelFunction_compact hgc _ _ _ hk0.ne' _,
      levelFunction_interior_support hk0 hgs hgt hchiz _, levelFunction_symmetric _ _ _ _ _ _⟩
  · rw [cancellationFamily_of_not_mem hj]
    refine ⟨contDiff_const, ?_, ?_, ?_⟩
    · exact HasCompactSupport.zero
    · simp
    · intro e t
      rfl

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_OrthantIntegrals
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem squareDimension_pos (m : ℕ) : 0 < squareDimension m := by
  unfold squareDimension
  positivity

theorem active_length_le_squareDimension (m : ℕ) : m+1 ≤ squareDimension m := by
  unfold squareDimension
  nlinarith [Nat.zero_le m]

theorem squareDimension_strictMono : StrictMono squareDimension := by
  intro m n hmn
  unfold squareDimension
  nlinarith

theorem tendsto_squareDimension : Tendsto squareDimension atTop atTop :=
  squareDimension_strictMono.tendsto_atTop

theorem tendsto_inverse_squareDimension :
    Tendsto (fun m : ℕ => ((squareDimension m:ℕ):ℝ)⁻¹) atTop (nhds 0) :=
  (tendsto_natCast_atTop_atTop.comp tendsto_squareDimension).inv_tendsto_atTop

theorem tendsto_inverse_active_length :
    Tendsto (fun m : ℕ => (((m+1):ℕ):ℝ)⁻¹) atTop (nhds 0) :=
  (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop

theorem rectangle_error_tendsto_zero (v d : ℝ) :
    Tendsto (fun m : ℕ => v/((squareDimension m:ℝ)*d^2)) atTop (nhds 0) := by
  have h := tendsto_inverse_squareDimension.const_mul (v/(d^2))
  simpa only [mul_zero, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm (d^2)⁻¹] using h

theorem square_ratio_eq_inverse (m : ℕ) :
    ((m+1:ℕ):ℝ)/(squareDimension m:ℝ) = ((m+1:ℕ):ℝ)⁻¹ := by
  have hm : ((m+1:ℕ):ℝ) ≠ 0 := by positivity
  unfold squareDimension
  rw [Nat.cast_pow]
  field_simp

theorem cancellation_bound_tendsto_zero (lambda v d : ℝ) :
    Tendsto (fun m : ℕ => lambda * (2/((m+1:ℕ):ℝ) +
      (((m+1:ℕ):ℝ)/(squareDimension m:ℝ))^2 +
      4*v/((squareDimension m:ℝ)*d^2))) atTop (nhds 0) := by
  have h1 := tendsto_inverse_active_length.const_mul 2
  have h2 := tendsto_inverse_active_length.pow 2
  have h3 := rectangle_error_tendsto_zero (4*v) d
  have h := ((h1.add h2).add h3).const_mul lambda
  simp only [square_ratio_eq_inverse]
  simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_add, div_eq_mul_inv] using h

theorem cancellationFamily_W_tendsto {g chi : ℝ → ℝ} {lambda beta : ℝ}
    (hlambda : 0 < lambda) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hg2 : (∫ u, g u^2) = 1)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta) :
    Tendsto (fun m => familyW lambda (squareDimension m)
      (cancellationFamily g chi lambda (squareDimension m) (m+1))) atTop (nhds 1) := by
  let d := beta - ∫ u, u*g u^2
  let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
  have hlo := (rectangle_error_tendsto_zero v d).const_sub 1
  simp only [sub_zero] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
  · intro m
    exact (cancellationFamily_W_bounds hlambda (Nat.succ_pos m)
      (active_length_le_squareDimension m) hg hgc hgs hg2 hchi hchi0 hchi1 hflat hmu).1
  · intro m
    exact (cancellationFamily_W_bounds hlambda (Nat.succ_pos m)
      (active_length_le_squareDimension m) hg hgc hgs hg2 hchi hchi0 hchi1 hflat hmu).2

theorem cancellationFamily_V_tendsto {g chi : ℝ → ℝ} {lambda beta B : ℝ}
    (hlambda : 0 < lambda) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : Function.support g ⊆ Ioi 0) (hgn : ∀ u, 0 ≤ g u)
    (hg2 : (∫ u, g u^2) = 1) (hg1 : (∫ u, g u) = Real.sqrt lambda)
    (hB : ∀ u ∈ Function.support g, u ≤ B) (hB0 : 0 ≤ B)
    (hchi : Continuous chi) (hchi0 : ∀ s, 0 ≤ chi s) (hchi1 : ∀ s, chi s ≤ 1)
    (hflat : ∀ s ≤ beta, chi s = 1) (hmu : (∫ u, u*g u^2) < beta) :
    Tendsto (fun m => familyV lambda (squareDimension m)
      (cancellationFamily g chi lambda (squareDimension m) (m+1))) atTop (nhds 0) := by
  let d := beta - ∫ u, u*g u^2
  let v := ∫ u, (u-∫ v, v*g v^2)^2 * g u^2
  have hBdiv : Tendsto (fun m => B/(squareDimension m:ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inverse_squareDimension.const_mul B
  have hBk : ∀ᶠ m in atTop, B/(squareDimension m:ℝ) ≤ d/2 := by
    exact ((tendsto_order.mp hBdiv).2 (d/2) (by dsimp only [d]; linarith)).mono (fun _ h => h.le)
  apply squeeze_zero' (Eventually.of_forall fun m => familyV_nonneg hlambda _ _)
    _ (cancellation_bound_tendsto_zero lambda v d)
  filter_upwards [hBk] with m hm
  exact cancellationFamily_V_bound hlambda (Nat.succ_pos m)
    (active_length_le_squareDimension m) hg hgc hgs hgn hg2 hg1 hB hB0 hchi hchi0 hchi1 hflat hmu hm

theorem exists_canceling_families {lambda tau : ℝ} (hlambda : 0 < lambda) (htau : 0 < tau) :
    ∃ f : (m j : ℕ) → (Fin j → ℝ) → ℝ,
      (∀ m, AdmissibleFamily tau (squareDimension m) (f m) ∧ f m 0 = 0) ∧
      Tendsto (fun m => familyW lambda (squareDimension m) (f m)) atTop (nhds 1) ∧
      Tendsto (fun m => familyV lambda (squareDimension m) (f m)) atTop (nhds 0) := by
  let beta := tau/3
  let gamma := 2*tau/3
  have hb : 0 < beta := by dsimp only [beta]; positivity
  have hbg : beta < gamma := by dsimp only [beta, gamma]; linarith
  have hgt : gamma < tau := by dsimp only [gamma]; linarith
  obtain ⟨g, hgsmooth, hgc, hgs, hgn, hg2, hg1, hmu⟩ := exists_small_first_moment_profile hlambda hb
  let chi := simplexCutoff beta gamma
  have hchi : ContDiff ℝ ∞ chi := simplexCutoff_smooth beta gamma
  have hc0 : ∀ s, 0 ≤ chi s := simplexCutoff_nonneg beta gamma
  have hc1 : ∀ s, chi s ≤ 1 := simplexCutoff_le_one beta gamma
  have hcflat : ∀ s ≤ beta, chi s = 1 := fun _ hs => simplexCutoff_eq_one hbg hs
  have hcz : ∀ s, gamma ≤ s → chi s = 0 := fun _ hs => simplexCutoff_eq_zero hbg hs
  obtain ⟨b, hbnd⟩ := hgc.bddAbove
  let B := max b 0
  have hB : ∀ u ∈ Function.support g, u ≤ B := fun u hu =>
    (hbnd (subset_closure hu)).trans (le_max_left b 0)
  have hB0 : 0 ≤ B := le_max_right b 0
  have hsupport : Function.support g ⊆ Ioi 0 := fun _ hu => hgs (subset_closure hu)
  refine ⟨fun m => cancellationFamily g chi lambda (squareDimension m) (m+1), ?_, ?_, ?_⟩
  · intro m
    refine ⟨⟨squareDimension_pos m, ?_, ?_⟩, cancellationFamily_zero _ _ _ _ _⟩
    · intro j _
      exact cancellationFamily_properties (squareDimension_pos m) hgsmooth hgc hgs hchi hgt hcz j
    · intro j hj
      exact cancellationFamily_above _ _ _ _ _ hj
  · exact cancellationFamily_W_tendsto hlambda hgsmooth.continuous hgc hsupport hg2
      hchi.continuous hc0 hc1 hcflat hmu
  · exact cancellationFamily_V_tendsto hlambda hgsmooth.continuous hgc hsupport hgn hg2 hg1
      hB hB0 hchi.continuous hc0 hc1 hcflat hmu

theorem exists_family_small_marked_ratio {lambda tau epsilon : ℝ}
    (hlambda : 0 < lambda) (htau : 0 < tau) (hepsilon : 0 < epsilon) :
    ∃ k : ℕ, ∃ f : (j : ℕ) → (Fin j → ℝ) → ℝ,
      AdmissibleFamily tau k f ∧ f 0 = 0 ∧
      0 < familyW lambda k f ∧ familyV lambda k f / familyW lambda k f ≤ epsilon := by
  obtain ⟨f, hf, hW, hV⟩ := exists_canceling_families hlambda htau
  have hWpos : ∀ᶠ m in atTop, 0 < familyW lambda (squareDimension m) (f m) :=
    (tendsto_order.mp hW).1 0 (by norm_num)
  have hratio : Tendsto (fun m => familyV lambda (squareDimension m) (f m) /
      familyW lambda (squareDimension m) (f m)) atTop (nhds 0) := by
    have hdiv := hV.div hW (by norm_num : (1:ℝ) ≠ 0)
    rw [zero_div] at hdiv
    exact hdiv
  have hsmall := (tendsto_order.mp hratio).2 epsilon hepsilon
  obtain ⟨m, hmW, hmV⟩ := (hWpos.and hsmall).exists
  exact ⟨squareDimension m, f m, (hf m).1, (hf m).2, hmW, hmV.le⟩

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_CumulativeProfiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeExtension_tail {ι : Type*} [Fintype ι]
    (T : ℝ) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀ y, f y≠0 → ∀ i, y i≤T)
    (v : EuclideanSpace ℝ ι) (hv : ∀ i, 0≤v i) :
    cumulativeExtension T f v = cumulativeTail f v := by
  have hs : MeasurableSet {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i} := by
    rw [Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_le (continuous_const (y := v i)) (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)).measurableSet
  unfold cumulativeExtension cumulativeTail
  rw [convolution_def]
  change (∫ t, cubeIndicator T t * f (v-t)) = _
  rw [← integral_sub_left_eq_self (fun t => cubeIndicator T t * f (v-t)) volume v]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [sub_sub_cancel]
  by_cases hfy : f y=0
  · simp [Set.indicator,hfy]
  · by_cases hy : ∀ i, v i≤y i
    · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∈negativeCube T := by
        intro i
        change -T≤v i-y i ∧ v i-y i≤0
        constructor <;> linarith [hf y hfy i,hv i,hy i]
      simp [cubeIndicator,Set.indicator_of_mem hcube]
    · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ ι | ∀ i, v i≤y i}) hy]
      have hcube : v-y∉negativeCube T := by
        intro h
        apply hy
        intro i
        have := (h i).2
        change v i-y i≤0 at this
        linarith
      simp [cubeIndicator,Set.indicator_of_notMem hcube]

theorem profile_coordinate_upper {n : ℕ} {tau : ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf : tsupport f ⊆ positiveSimplex n tau) (y : Fin n → ℝ) (hy : y∈tsupport f)
    (i : Fin n) : y i≤tau := by
  have hh := hf hy
  exact (Finset.single_le_sum (fun j _ => (hh.1 j).le) (Finset.mem_univ i)).trans hh.2.le

theorem cumulativeProfile_tail {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) (v : Fin n → ℝ) (hv : ∀ i, 0≤v i) :
    cumulativeProfile tau f v = ∫ y in Ici v, f y := by
  unfold cumulativeProfile
  rw [cumulativeExtension_tail tau _ _ _ hv]
  · unfold cumulativeTail
    have hm := (PiLp.volume_preserving_ofLp (Fin n)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding f (Ici v)
    exact hm
  · intro y hy i
    exact profile_coordinate_upper hf y.ofLp (subset_tsupport f hy) i

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DensityBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem344

theorem initialCount_le (A : Set ℕ) (N : ℕ) : initialCount A N ≤ N := by
  classical
  unfold initialCount
  calc
    ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card ≤ (Finset.Icc 1 N).card :=
      Finset.card_filter_le _ _
    _ = N := by simp

theorem initialCount_div_le_one (A : Set ℕ) (N : ℕ) :
    (initialCount A N : ℝ) / (N : ℝ) ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (div_le_iff₀ hNpos).2
    simpa using (show (initialCount A N : ℝ) ≤ N by exact_mod_cast initialCount_le A N)

theorem density_witnesses_bddAbove (A : Set ℕ) :
    BddAbove {d : ℝ | ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      d ≤ (initialCount A N : ℝ) / (N : ℝ)} := by
  refine ⟨1, ?_⟩
  rintro d ⟨N0, h⟩
  exact (h (N0 + 1) (by omega)).trans (initialCount_div_le_one A (N0 + 1))

theorem le_lowerAsymptoticDensity_of_linear_count (A : Set ℕ) (c : ℝ)
    (hcount : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c * (N : ℝ) ≤ (initialCount A N : ℝ)) :
    c ≤ lowerAsymptoticDensity A := by
  apply le_csSup (density_witnesses_bddAbove A)
  rcases hcount with ⟨N0, hcount⟩
  refine ⟨max N0 1, ?_⟩
  intro N hN
  have hN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact (le_div_iff₀ hNpos).2 (hcount N hN0)

theorem positive_lowerAsymptoticDensity_of_linear_count (A : Set ℕ)
    (hcount : ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c * (N : ℝ) ≤ (initialCount A N : ℝ)) :
    0 < lowerAsymptoticDensity A := by
  rcases hcount with ⟨c, hc, hcount⟩
  exact hc.trans_le (le_lowerAsymptoticDensity_of_linear_count A c hcount)

end Problem344

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DensityTransport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem344

theorem initialCount_le_add_of_subset_above {A B : Set ℕ} {K : ℕ}
    (hAB : ∀ n : ℕ, K ≤ n → n ∈ A → n ∈ B) (N : ℕ) :
    initialCount A N ≤ initialCount B N + K := by
  classical
  have hsub : (Finset.Icc 1 N).filter (fun n => n ∈ A) ⊆
      (Finset.Icc 1 N).filter (fun n => n ∈ B) ∪ Finset.range K := by
    intro n hn
    obtain ⟨hnI, hnA⟩ := Finset.mem_filter.mp hn
    by_cases hKn : K ≤ n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, hAB n hKn hnA⟩)
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr (Nat.lt_of_not_ge hKn))
  calc
    initialCount A N ≤
        ((Finset.Icc 1 N).filter (fun n => n ∈ B) ∪ Finset.range K).card :=
      Finset.card_le_card hsub
    _ ≤ ((Finset.Icc 1 N).filter (fun n => n ∈ B)).card + (Finset.range K).card :=
      Finset.card_union_le _ _
    _ = initialCount B N + K := by simp [initialCount]

theorem eventual_half_linear_count_of_subset_above {A B : Set ℕ} {K : ℕ} {c : ℝ}
    (hAB : ∀ n : ℕ, K ≤ n → n ∈ A → n ∈ B) (hc : 0 < c)
    (hA : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → c * (N : ℝ) ≤ (initialCount A N : ℝ)) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (c / 2) * (N : ℝ) ≤ (initialCount B N : ℝ) := by
  obtain ⟨NA, hNA⟩ := hA
  obtain ⟨NK, hNK⟩ := exists_nat_ge (2 * (K : ℝ) / c)
  refine ⟨max NA NK, ?_⟩
  intro N hN
  have hNA' : NA ≤ N := (le_max_left NA NK).trans hN
  have hNK' : NK ≤ N := (le_max_right NA NK).trans hN
  have hlarge : 2 * (K : ℝ) ≤ (N : ℝ) * c := by
    apply (div_le_iff₀ hc).mp
    exact hNK.trans (by exact_mod_cast hNK')
  have hcount : (initialCount A N : ℝ) ≤ (initialCount B N : ℝ) + (K : ℝ) := by
    exact_mod_cast initialCount_le_add_of_subset_above hAB N
  have hlinear := hNA N hNA'
  nlinarith

theorem positive_linear_count_of_eventual_subset {A B : Set ℕ}
    (hAB : ∃ K : ℕ, ∀ n : ℕ, K ≤ n → n ∈ A → n ∈ B)
    (hA : ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c * (N : ℝ) ≤ (initialCount A N : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c * (N : ℝ) ≤ (initialCount B N : ℝ) := by
  obtain ⟨K, hK⟩ := hAB
  obtain ⟨c, hc, hA⟩ := hA
  exact ⟨c / 2, half_pos hc, eventual_half_linear_count_of_subset_above hK hc hA⟩

end Problem344

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_TensorProfiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeProfile_budget {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) : HasBudget (cumulativeProfile tau f) tau := by
  intro v hv hsum
  rw [cumulativeProfile_tail tau f hf v hv]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  by_contra hne
  have hh := hf (subset_tsupport f hne)
  have he : tau≤coordinateSum y :=
    hsum.le.trans (Finset.sum_le_sum (fun i _ => hy i))
  exact (not_lt_of_ge he) hh.2

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_EqualityPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem index_density_from_weight_estimates {C : ℝ} (hC : 0<C)
    (W : ℕ → ℕ → ℝ) (a K b M : ℝ)
    (ha : 0<a) (hK : 0<K) (hM : 0<M) (hb : b<a^2/K)
    (hw : ∀ᶠ X : ℕ in atTop, ∀ m ∈ Finset.Ioc X (2*X), 0≤W X m)
    (hfirst : ∀ᶠ X : ℕ in atTop,
      a≤average X (fun m => W X m*detector X (Finset.Ioc 0 (blockLength (C+1) X)) m))
    (hdetect : ∀ᶠ X : ℕ in atTop,
      average X (fun m => W X m*detector X (Finset.Ioc 0 (blockLength (C+1) X)) m^2)≤K)
    (hsuppress : ∀ᶠ X : ℕ in atTop,
      average X (fun m => W X m*detector X
        (Finset.Ioc (blockLength (C+1) X) (2*blockLength (C+1) X)) m)≤b)
    (hsecond : ∀ᶠ X : ℕ in atTop, average X (fun m => W X m^2)≤M) :
    ∃ c : ℝ, 0<c ∧ ∃ N₀ : ℕ, ∀ N≥N₀, c*(N:ℝ)≤((largeGapIndices C N).card:ℝ) := by
  let delta := (a^2/K-b)^2/M
  have hd : 0<delta := div_pos (sq_pos_of_pos (sub_pos.mpr hb)) hM
  let A := 6*(Real.log 4+1)
  have hA : 0<A := by dsimp [A]; positivity
  have hL : 0<C+1 := by linarith
  refine ⟨delta/(A*(C+1)),div_pos hd (mul_pos hA hL),?_⟩
  apply eventually_atTop.mp
  have hstarts : ∀ᶠ X : ℕ in atTop,
      delta*(X:ℝ)≤((goodStarts X (blockLength (C+1) X)).card:ℝ) := by
    filter_upwards [eventually_ge_atTop 2,hw,hfirst,hdetect,hsuppress,hsecond]
      with X hX hW hF hD hS hQ
    exact goodStarts_bound_of_moments hX (W X) a K b M ha hK hM hb hW hF hD hS hQ
  filter_upwards [eventually_scale_comparison,eventually_ge_atTop 1,
    tendsto_indexScale.eventually (eventually_blockLength_le (C+1) hL),
    tendsto_indexScale.eventually (eventually_blockLength_threshold C hC),
    tendsto_indexScale.eventually hstarts] with N hcompare hN hblock hthreshold hcount
  apply index_bound_of_goodStarts hd hL hA hcompare.1 (by omega)
  · have hdiv := Nat.div_mul_le_self (prime N) 3
    change (prime N/3)*3≤prime N at hdiv
    change 2*indexScale N+blockLength (C+1) (indexScale N)≤prime N
    change (indexScale N)*3≤prime N at hdiv
    omega
  · intro p hp
    have hmem := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    exact hthreshold p (by omega) (by omega)
  · exact hcompare.2
  · exact hcount

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Detectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem exists_normalized_singleton_profile {tau : ℝ} (htau : 0<tau) :
    ∃ f : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f⊆positiveSimplex 1 tau ∧ (∀ v,0≤f v) ∧ (∫ v,f v)=1 := by
  have hopen : IsOpen (positiveSimplex 1 tau) := by
    have he : positiveSimplex 1 tau=(fun v : Fin 1 → ℝ => v 0) ⁻¹' Ioo 0 tau := by
      ext v
      simp [positiveSimplex,coordinateSum,Fin.forall_fin_one]
    rw [he]
    exact isOpen_Ioo.preimage (continuous_apply 0)
  have hmem : (fun _ : Fin 1 => tau/2)∈positiveSimplex 1 tau := by
    simp only [positiveSimplex,Set.mem_ofPred_eq,coordinateSum,Fin.sum_univ_one]
    constructor
    · intro i; positivity
    · linarith
  obtain ⟨f,hs,hc,hf,h01,h1⟩ := exists_contDiff_tsupport_subset (n:=(⊤:ℕ∞)) (hopen.mem_nhds hmem)
  have hn : ∀ v,0≤f v := fun v => (h01 (Set.mem_range_self v)).1
  let A := ∫ v,f v
  have hA : 0<A := integral_pos_of_integrable_nonneg_nonzero hf.continuous
    (hf.continuous.integrable_of_hasCompactSupport hc) hn (by rw [h1]; norm_num)
  let g := fun v => f v/A
  have hgc : HasCompactSupport g := hc.comp_left (g:=fun x : ℝ => x/A) (by simp)
  have hgs : tsupport g⊆positiveSimplex 1 tau :=
    (tsupport_comp_subset (g:=fun x : ℝ => x/A) (by simp) f).trans hs
  refine ⟨g,hf.div_const A,hgc,hgs,fun v => div_nonneg (hn v) hA.le,?_⟩
  rw [show g=(fun v => f v/A) from rfl,integral_div]
  exact div_self hA.ne'

theorem exists_detector_profile {tau : ℝ} (htau : 0<tau) :
    ∃ f : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f⊆positiveSimplex 1 tau ∧
      HasBudget (cumulativeProfile tau f) tau ∧
      ContDiff ℝ ∞ (cumulativeProfile tau f) ∧
      HasCompactSupport (cumulativeProfile tau f) ∧
      cumulativeProfile tau f 0=1 := by
  obtain ⟨f,hf,hc,hs,_hn,h1⟩ := exists_normalized_singleton_profile htau
  refine ⟨f,hf,hc,hs,cumulativeProfile_budget tau f hs,
    cumulativeProfile_smooth tau f hc hf,cumulativeProfile_compact tau f hc,?_⟩
  rw [cumulativeProfile_tail tau f hs 0 (fun _ => le_rfl)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,h1]
  intro v hv
  by_contra hne
  apply hv
  intro i
  exact (hs (subset_tsupport f hne)).1 i |>.le

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_WeightMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

@[simp] theorem cumulativeProfile_fin_zero {tau : ℝ} (f : (Fin 0 → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex 0 tau) (v : Fin 0 → ℝ) :
    cumulativeProfile tau f v=f 0 := by
  rw [cumulativeProfile_tail tau f hsf v (fun i => Fin.elim0 i)]
  rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  have he : Ici v=(Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp only [Set.mem_Ici,Set.mem_univ,iff_true]
    exact fun i => Fin.elim0 i
  rw [he,setIntegral_univ]
  exact integral_dirac f 0

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_DetectorMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem index_density_of_bombieriVinogradov (hBV : BombieriVinogradov)
    (C : ℝ) (hC : 0<C) :
    ∃ c : ℝ, 0<c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N →
      c*(N:ℝ)≤((largeGapIndices C N).card:ℝ) := by
  let tau : ℝ := 1/8
  let lam : ℝ := C+1
  have htau : 0<tau := by norm_num [tau]
  have hlam : 0<lam := by dsimp [lam]; linarith
  obtain ⟨g,hgs,hgc,hgt,_hgb,_hGc,_hGcompact,hg0⟩ := exists_detector_profile htau
  let D := lam+lam^2*l2Mass g^2+1
  have hD : 0<D := by dsimp [D]; positivity
  let eps := lam^2/(16*D)
  have heps : 0<eps := by dsimp [eps]; positivity
  obtain ⟨k,f,hf,_hf0,hw,hv⟩ := exists_family_small_marked_ratio hlam htau heps
  let w := familyW lam k f
  have hw' : 0<w := hw
  let a := lam*w/2
  let K := D*w
  let b := 2*(eps*w)
  have ha : 0<a := by dsimp [a]; positivity
  have hK : 0<K := mul_pos hD hw'
  have hab : a^2/K=4*(eps*w) := by
    dsimp [a,K,eps]
    field_simp
    ring
  have hb : b<a^2/K := by
    rw [hab]
    dsimp [b]
    nlinarith [mul_pos heps hw']
  obtain ⟨M,hM,hfourth⟩ := unorderedWeight_fourth_bound f hf htau.le
    (by norm_num [tau] : 4*tau<1) hlam
  apply index_density_from_weight_estimates hC
    (fun X m => unorderedWeight tau lam k f X m^2) a K b M ha hK hM hb
  · exact Eventually.of_forall fun _ _ _ => sq_nonneg _
  · have hlim := unorderedWeight_external_marked_limit hBV f hf htau.le
      (by norm_num [tau] : 2*tau<1/2) hlam
    have hlt : a<lam*familyW lam k f := by
      change lam*w/2<lam*w
      nlinarith [mul_pos hlam hw']
    exact Eventually.mono ((tendsto_order.mp hlim).1 a hlt) fun _ h => h.le
  · exact unorderedWeight_detector_bound hBV f hf htau.le
      (by norm_num [tau] : 6*tau<1) hlam hw g hgc hgs hgt hg0
  · have hlim := unorderedWeight_internal_marked_limit hBV f hf htau.le
      (by norm_num [tau] : 2*tau<1/2) hlam
    have hV : familyV lam k f≤eps*w := (div_le_iff₀ hw).mp hv
    have hlt : familyV lam k f<b := by
      dsimp [b]
      nlinarith [mul_pos heps hw']
    exact Eventually.mono ((tendsto_order.mp hlim).2 b hlt) fun _ h => h.le
  · filter_upwards [hfourth] with X hX
    simpa only [←pow_mul] using hX

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Complex Real Set MeasureTheory Filter Topology

open Complex Filter Topology

open Complex Filter Topology MeasureTheory

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open scoped FourierTransform

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

open Complex Real Set MeasureTheory Filter Topology

theorem main : ∀ C : ℝ, 0 < C →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ ((largeGapIndices C N).card : ℝ) :=
  index_density_of_bombieriVinogradov bombieriVinogradov

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_PrimeGrowth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter

namespace Problem344.PrimeGrowth

lemma primeCounting_nth_prime (n : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
  simp only [Nat.prime_nth_prime, ite_true]
  exact congrArg (fun k => k + 1) (Nat.primeCounting'_nth_eq n)

lemma eventually_log_add_one_le_half_log_two_mul :
    ∀ᶠ x : ℝ in atTop, Real.log (x + 1) ≤ (Real.log 2 / 2) * x := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h := Real.isLittleO_log_id_atTop.bound (show 0 < Real.log 2 / 4 by positivity)
  have ht : Tendsto (fun x : ℝ => x + 1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_id
  filter_upwards [ht.eventually h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  simp only [Function.id_def, Real.norm_eq_abs] at hx
  rw [abs_of_nonneg (Real.log_nonneg (by linarith)), abs_of_nonneg (by linarith)] at hx
  nlinarith

lemma eventually_primeCounting_mul_log_lower :
    ∀ᶠ p : ℕ in atTop,
      (Real.log 2 / 2) * (p : ℝ) ≤ (Nat.primeCounting p : ℝ) * Real.log p := by
  have ht : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually eventually_log_add_one_le_half_log_two_mul,
    eventually_ge_atTop (2 : ℕ)] with p hp hp2
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hpi := (div_le_iff₀ hlog).mp (Chebyshev.pi_ge p)
  nlinarith

lemma eventually_nth_prime_ratio_le_log :
    ∀ᶠ n : ℕ in atTop,
      (Nat.nth Nat.Prime (n - 1) : ℝ) / (n : ℝ) ≤
        (2 / Real.log 2) * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_primeCounting_mul_log_lower
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hnpos : 0 < n := by omega
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hp : N ≤ Nat.nth Nat.Prime (n - 1) := by
    have := Nat.add_two_le_nth_prime (n - 1)
    omega
  have hpi := hN _ hp
  have hc : Nat.primeCounting (Nat.nth Nat.Prime (n - 1)) = n := by
    rw [primeCounting_nth_prime]
    omega
  rw [hc] at hpi
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpbound : (Nat.nth Nat.Prime (n - 1) : ℝ) ≤
      ((n : ℝ) * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ)) / (Real.log 2 / 2) := by
    apply (le_div_iff₀ (show 0 < Real.log (2 : ℝ) / 2 by positivity)).mpr
    nlinarith
  calc
    _ ≤ (((n : ℝ) * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ)) /
        (Real.log 2 / 2)) / (n : ℝ) := div_le_div_of_nonneg_right hpbound hnr.le
    _ = _ := by field_simp

end Problem344.PrimeGrowth

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_RatioAlgebra
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem344

theorem div_lt_div_succ_iff_gap {a b : ℝ} {n : ℕ} (hn : 0 < n) :
    a / (n : ℝ) < b / ((n + 1 : ℕ) : ℝ) ↔
      a / (n : ℝ) < b - a := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [div_lt_div_iff₀ hnR hn1R, div_lt_iff₀ hnR]
  push_cast
  constructor <;> intro h <;> nlinarith

end Problem344

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_RatioReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem344

theorem mem_ratioIncreaseIndices_iff_gap {n : ℕ} :
    n ∈ ratioIncreaseIndices ↔
      1 ≤ n ∧ (primeAt n : ℝ) / (n : ℝ) <
        (primeAt (n + 1) : ℝ) - (primeAt n : ℝ) := by
  constructor
  · rintro ⟨hn, hratio⟩
    exact ⟨hn, (div_lt_div_succ_iff_gap hn).1 hratio⟩
  · rintro ⟨hn, hgap⟩
    exact ⟨hn, (div_lt_div_succ_iff_gap hn).2 hgap⟩

theorem mem_ratioIncreaseIndices_of_mem_largeGapIndices {C : ℝ} {n : ℕ}
    (hbound : (primeAt n : ℝ) / (n : ℝ) ≤ C * Real.log (primeAt n : ℝ))
    (hgap : n ∈ largeGapIndices C) : n ∈ ratioIncreaseIndices := by
  apply mem_ratioIncreaseIndices_iff_gap.2
  exact ⟨hgap.1, lt_of_le_of_lt hbound hgap.2⟩

theorem eventually_largeGapIndices_subset_ratioIncreaseIndices {C : ℝ}
    (hbound : ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      (primeAt n : ℝ) / (n : ℝ) ≤ C * Real.log (primeAt n : ℝ)) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      n ∈ largeGapIndices C → n ∈ ratioIncreaseIndices := by
  obtain ⟨N0, hN0⟩ := hbound
  exact ⟨N0, fun n hn => mem_ratioIncreaseIndices_of_mem_largeGapIndices (hN0 n hn)⟩

end Problem344

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_RatioDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem344

theorem eventually_largeGapIndices_explicit_subset_ratioIncreaseIndices :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      n ∈ largeGapIndices (2 / Real.log 2) → n ∈ ratioIncreaseIndices := by
  apply eventually_largeGapIndices_subset_ratioIncreaseIndices
  apply Filter.eventually_atTop.mp
  simpa only [primeAt] using PrimeGrowth.eventually_nth_prime_ratio_le_log

theorem positive_lower_density_prime_ratio_increases_of_explicit_large_gaps
    (hgap : ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c * (N : ℝ) ≤ (initialCount (largeGapIndices (2 / Real.log 2)) N : ℝ)) :
    0 < lowerAsymptoticDensity ratioIncreaseIndices := by
  apply positive_lowerAsymptoticDensity_of_linear_count
  exact positive_linear_count_of_eventual_subset
    eventually_largeGapIndices_explicit_subset_ratioIncreaseIndices hgap

theorem positive_lower_density_prime_ratio_increases_of_large_gaps
    (hgap : ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N →
        c * (N : ℝ) ≤ (initialCount (largeGapIndices C) N : ℝ)) :
    0 < lowerAsymptoticDensity ratioIncreaseIndices := by
  apply positive_lower_density_prime_ratio_increases_of_explicit_large_gaps
  exact hgap (2 / Real.log 2) (div_pos (by norm_num) (Real.log_pos (by norm_num)))

end Problem344

end OAI
end

section
-- module Solutions.OAIW2_P344.PrimeGaps_RatioCorollary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem344

private theorem largeGap_count_eq (C : ℝ) (N : ℕ) :
    initialCount (largeGapIndices C) N =
      (LargePrimeGaps.largeGapIndices C N).card := by
  classical
  unfold initialCount LargePrimeGaps.largeGapIndices
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  simp only [largeGapIndices, Set.mem_ofPred_eq, primeAt,
    LargePrimeGaps.prime, hn1, true_and]

theorem positive_lower_density_prime_ratio_increases :
    0 < lowerAsymptoticDensity ratioIncreaseIndices := by
  apply positive_lower_density_prime_ratio_increases_of_large_gaps
  intro C hC
  rcases LargePrimeGaps.main C hC with ⟨c, hc, N0, hN0⟩
  refine ⟨c, hc, N0, ?_⟩
  intro N hN
  rw [largeGap_count_eq]
  exact hN0 N hN

theorem large_gaps_and_ratio_density_oai :
    (∀ C : ℝ, 0 < C →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * (N : ℝ) ≤ ((LargePrimeGaps.largeGapIndices C N).card : ℝ)) ∧
    0 < lowerAsymptoticDensity ratioIncreaseIndices :=
  ⟨LargePrimeGaps.main, positive_lower_density_prime_ratio_increases⟩

end Problem344

end OAI
end

theorem solution : type_of% @OAI.Problem344.large_gaps_and_ratio_density_oai := @OAI.Problem344.large_gaps_and_ratio_density_oai
