-- Prove2me | solution 1 for OAI.Problem337.exact_marker_padding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:04:12.769452+00:00
-- url     : https://prove2.me/submissions/d189c349-3e4b-4a0a-8552-72ff4d25d0a1

import Mathlib
import Definitions.Def_EgyptianFractions
import Definitions.Def_OAIQ8EF000

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A finite collection of denominators has a canonical increasing enumeration. -/
theorem finset_increasing_enumeration (s : Finset ℕ) :
    ∃ n : Fin s.card → ℕ, StrictMono n ∧
      (∀ m, (∃ i, n i = m) ↔ m ∈ s) ∧
      (∀ f : ℕ → ℚ, (∑ i, f (n i)) = ∑ m ∈ s, f m) := by
  refine ⟨s.orderEmbOfFin rfl, (s.orderEmbOfFin rfl).strictMono, ?_, ?_⟩
  · intro m
    change m ∈ Set.range (s.orderEmbOfFin rfl) ↔ m ∈ s
    rw [Finset.range_orderEmbOfFin]
    rfl
  · intro f
    calc
      (∑ i, f ((s.orderEmbOfFin rfl) i)) =
          ∑ m ∈ Finset.univ.image (s.orderEmbOfFin rfl), f m := by
        rw [Finset.sum_image (fun a _ b _ h => (s.orderEmbOfFin rfl).injective h)]
      _ = ∑ m ∈ s, f m := by rw [Finset.image_orderEmbOfFin_univ]

/-- Enumeration preserves a lower bound and the sum of unit fractions. -/
theorem finset_unit_fraction_representation (s : Finset ℕ) (a : ℕ) (x : ℚ)
    (hpos : ∀ m ∈ s, a ≤ m) (hsum : (∑ m ∈ s, (1 : ℚ) / m) = x) :
    ∃ n : Fin s.card → ℕ, (∀ i, a ≤ n i) ∧ StrictMono n ∧
      (∑ i, (1 : ℚ) / n i) = x ∧
      (∀ m, (∃ i, n i = m) ↔ m ∈ s) := by
  obtain ⟨n, hmono, hmem, hsum'⟩ := finset_increasing_enumeration s
  refine ⟨n, ?_, hmono, ?_, hmem⟩
  · intro i
    exact hpos (n i) ((hmem _).mp ⟨i, rfl⟩)
  · exact (hsum' (fun m => (1 : ℚ) / m)).trans hsum

/-- Replacing one denominator by two fresh distinct denominators preserves the
unit-fraction total and all other markers, while increasing cardinality by one. -/
theorem finset_replace_unit_fraction (s : Finset ℕ) (d a b L : ℕ)
    (hd : d ∈ s) (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b)
    (hpos : ∀ m ∈ s, L ≤ m) (haL : L ≤ a) (hbL : L ≤ b)
    (hsplit : (1 : ℚ) / a + 1 / b = 1 / d) :
    ∃ t : Finset ℕ, t.card = s.card + 1 ∧
      (∀ m ∈ t, L ≤ m) ∧
      (∑ m ∈ t, (1 : ℚ) / m) = ∑ m ∈ s, (1 : ℚ) / m ∧
      (∀ m ∈ s, m ≠ d → m ∈ t) := by
  let t := insert a (insert b (s.erase d))
  have hae : a ∉ s.erase d := fun h => ha (Finset.mem_of_mem_erase h)
  have hbe : b ∉ s.erase d := fun h => hb (Finset.mem_of_mem_erase h)
  have hai : a ∉ insert b (s.erase d) := by simp [hab, hae]
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · dsimp [t]
    rw [Finset.card_insert_of_notMem hai, Finset.card_insert_of_notMem hbe,
      Finset.card_erase_of_mem hd]
    have := Finset.card_pos.mpr ⟨d, hd⟩
    omega
  · intro m hm
    simp only [t, Finset.mem_insert, Finset.mem_erase] at hm
    rcases hm with rfl | rfl | ⟨_, hm⟩
    · exact haL
    · exact hbL
    · exact hpos m hm
  · dsimp [t]
    rw [Finset.sum_insert hai, Finset.sum_insert hbe]
    have hsum := Finset.sum_erase_add s (fun m => (1 : ℚ) / m) hd
    linarith
  · intro m hm hmd
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hmd, hm⟩))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators
namespace Problem337

lemma prime_dvd_num_of_fraction (p a b : ℕ) (hp : p.Prime)
    (hb : b ≠ 0) (hpb : p ∣ b) (q : ℚ)
    (hq : q = (a : ℚ) / b) (hden : ¬p ∣ q.den) : p ∣ a := by
  have hq' : q = Rat.divInt (a : ℤ) (b : ℤ) := by
    simpa only [Rat.divInt_eq_div, Int.cast_natCast] using hq
  obtain ⟨c, ha, hb'⟩ := Rat.num_den_mk (by exact_mod_cast hb) hq'
  have hbabs : b = c.natAbs * q.den := by
    have h := congrArg Int.natAbs hb'
    simpa only [Int.natAbs_natCast, Int.natAbs_mul] using h
  have habs : a = c.natAbs * q.num.natAbs := by
    have h := congrArg Int.natAbs ha
    simpa only [Int.natAbs_natCast, Int.natAbs_mul] using h
  rw [hbabs] at hpb
  have hpc : p ∣ c.natAbs := (hp.dvd_mul.mp hpb).resolve_right hden
  rw [habs]
  exact dvd_mul_of_dvd_left hpc _

lemma prime_not_dvd_den_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (p : ℕ) (hp : p.Prime) (hf : ∀ i ∈ s, ¬p ∣ (f i).den) :
    ¬p ∣ (∑ i ∈ s, f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      intro hd
      have hprod := hd.trans (Rat.add_den_dvd (f a) (∑ i ∈ s, f i))
      rcases hp.dvd_mul.mp hprod with h | h
      · exact hf a (by simp) h
      · exact ih (fun i hi => hf i (by simp [hi])) h

lemma prime_not_dvd_den_unit_sum {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (p : ℕ) (hp : p.Prime) (hn : ∀ i ∈ s, 0 < n i ∧ n i < p) :
    ¬p ∣ (∑ i ∈ s, (1 : ℚ) / n i).den := by
  apply prime_not_dvd_den_sum s _ p hp
  intro i hi
  have hni := hn i hi
  simpa [one_div, Rat.den_inv, ne_of_gt hni.1] using
    (Nat.not_dvd_of_pos_of_lt hni.1 hni.2)


lemma prime_successor_unit_obstruction (p : ℕ) (hp : p.Prime)
    (x : ℚ) (hx : ¬p ∣ x.den) :
    x + 1 / (p : ℚ) + 1 / ((p + 1 : ℕ) : ℚ) ≠ 1 := by
  intro h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : ((p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hid : 1 / (p : ℚ) + 1 / ((p + 1 : ℕ) : ℚ) =
      ((2 * p + 1 : ℕ) : ℚ) / ((p * (p + 1) : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  have hq : 1 - x = ((2 * p + 1 : ℕ) : ℚ) / ((p * (p + 1) : ℕ) : ℚ) := by
    rw [← hid]
    linarith
  have hd : ¬p ∣ (1 - x).den := by simpa using hx
  have hh := prime_dvd_num_of_fraction p (2*p+1) (p*(p+1)) hp
    (Nat.mul_ne_zero hp.ne_zero (by omega)) (dvd_mul_right _ _) (1-x) hq hd
  exact hp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_mul_left p 2)).mpr hh)

lemma prime_product_unit_obstruction (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (x : ℚ) (hx : ¬p ∣ x.den) :
    x + 1 / (p : ℚ) + 1 / ((p * (p + 1) : ℕ) : ℚ) ≠ 1 := by
  intro h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : ((p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hid : 1 / (p : ℚ) + 1 / ((p * (p + 1) : ℕ) : ℚ) =
      ((p + 2 : ℕ) : ℚ) / ((p * (p + 1) : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  have hq : 1 - x = ((p + 2 : ℕ) : ℚ) / ((p * (p + 1) : ℕ) : ℚ) := by
    rw [← hid]
    linarith
  have hd : ¬p ∣ (1 - x).den := by simpa using hx
  have hh := prime_dvd_num_of_fraction p (p+2) (p*(p+1)) hp
    (Nat.mul_ne_zero hp.ne_zero (by omega)) (dvd_mul_right _ _) (1-x) hq hd
  have hh2 : p ∣ 2 := (Nat.dvd_add_iff_right (dvd_refl p)).mpr hh
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hh2

lemma prime_successor_prefix_obstruction {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (p : ℕ) (hp : p.Prime) (hn : ∀ i ∈ s, 0 < n i ∧ n i < p) :
    (∑ i ∈ s, (1 : ℚ) / n i) + 1 / (p : ℚ) +
      1 / ((p + 1 : ℕ) : ℚ) ≠ 1 :=
  prime_successor_unit_obstruction p hp _ (prime_not_dvd_den_unit_sum s n p hp hn)

lemma prime_product_prefix_obstruction {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hn : ∀ i ∈ s, 0 < n i ∧ n i < p) :
    (∑ i ∈ s, (1 : ℚ) / n i) + 1 / (p : ℚ) +
      1 / ((p * (p + 1) : ℕ) : ℚ) ≠ 1 :=
  prime_product_unit_obstruction p hp hp3 _ (prime_not_dvd_den_unit_sum s n p hp hn)

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SplitArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Splitting a positive unit fraction into the two usual larger fractions. -/
theorem unit_fraction_split (n : ℕ) (hn : 0 < n) :
    (1 : ℚ) / n = 1 / (n + 1 : ℕ) + 1 / (n * (n + 1) : ℕ) := by
  have hq : (n : ℚ) ≠ 0 := by positivity
  have hq1 : (n : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp


/-- A composite denominator admits a split strictly between the two
exceptional denominators for ordinary unit-fraction splitting. -/
theorem composite_unit_fraction_split (n : ℕ) (hn : 2 ≤ n)
    (hp : ¬ Nat.Prime n) :
    ∃ u v : ℕ, n + 1 < u ∧ u < v ∧ v < n * (n + 1) ∧
      (1 : ℚ) / n = 1 / u + 1 / v := by
  obtain ⟨a, b, han, hbn, hab⟩ := (Nat.not_prime_iff_exists_mul_eq hn).mp hp
  have ha : 2 ≤ a := by
    by_contra h
    have : a = 0 ∨ a = 1 := by omega
    rcases this with h | h
    · simp [h] at hab
      omega
    · simp [h] at hab
      omega
  have hb : 2 ≤ b := by
    by_contra h
    have : b = 0 ∨ b = 1 := by omega
    rcases this with h | h
    · simp [h] at hab
      omega
    · simp [h] at hab
      omega
  refine ⟨n + a, b * (n + a), ?_, ?_, ?_, ?_⟩
  · omega
  · nlinarith
  · nlinarith
  · have hna : (n + a : ℕ) ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hqna : ((n + a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hna
    have hqb : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    have hqn : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    have habq : (a : ℚ) * b = n := by exact_mod_cast hab
    push_cast at hqna ⊢
    field_simp
    nlinarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ExactPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A nontrivial distinct expansion of one cannot contain denominator one. -/
theorem one_finset_denominators_ge_two (s : Finset ℕ)
    (hcard : 2 ≤ s.card) (hpos : ∀ b ∈ s, 1 ≤ b)
    (hsum : (∑ b ∈ s, (1 : ℚ) / b) = 1) :
    ∀ b ∈ s, 2 ≤ b := by
  intro b hb
  have hbpos := hpos b hb
  by_contra h
  have hb1 : b = 1 := by omega
  have hother : ∃ c ∈ s, c ≠ b := by
    by_contra hnone
    push Not at hnone
    have hsmall : s.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx y hy
      exact (hnone x hx).trans (hnone y hy).symm)
    omega
  obtain ⟨c, hc, hcb⟩ := hother
  have hlt : (1 : ℚ) / b < ∑ x ∈ s, (1 : ℚ) / x := by
    apply Finset.single_lt_sum hcb hb hc
    · have : 0 < c := by have := hpos c hc; omega
      positivity
    · intro x hx _
      positivity
  rw [hb1, hsum] at hlt
  norm_num at hlt

/-- Choose an unmarked denominator with a collision-free two-term split. -/
theorem exists_marker_split_of_obstruction (hprime : PrimePaddingObstruction)
    (s : Finset ℕ) (hcard : 3 ≤ s.card) (hpos : ∀ x ∈ s, 1 ≤ x)
    (hsum : (∑ x ∈ s, (1 : ℚ) / x) = 1) (m : ℕ) (hm : m ∈ s) :
    ∃ b u v : ℕ, b ∈ s ∧ b ≠ m ∧ 1 ≤ u ∧ 1 ≤ v ∧ u ≠ v ∧
      u ∉ s ∧ v ∉ s ∧
      (1 : ℚ) / b = 1 / u + 1 / v := by
  have htwo := one_finset_denominators_ge_two s (by omega) hpos hsum
  let t := s.erase m
  have htcard : 2 ≤ t.card := by
    dsimp [t]
    rw [Finset.card_erase_of_mem hm]
    omega
  have htne : t.Nonempty := Finset.card_pos.mp (by omega)
  let b := t.max' htne
  have hbt : b ∈ t := Finset.max'_mem t htne
  have hbs : b ∈ s := Finset.mem_of_mem_erase hbt
  have hbm : b ≠ m := (Finset.mem_erase.mp hbt).1
  have hbmax : ∀ x ∈ t, x ≤ b := by
    intro x hx
    exact Finset.le_max' t x hx
  have hb3 : 3 ≤ b := by
    obtain ⟨c, hc, hcb⟩ := Finset.exists_mem_ne (by omega : 1 < t.card) b
    have hc2 := htwo c (Finset.mem_of_mem_erase hc)
    have hcb' := hbmax c hc
    omega
  have avoid : ∀ x : ℕ, b < x → x ≠ m → x ∉ s := by
    intro x hbx hxm hx
    have hxt : x ∈ t := Finset.mem_erase.mpr ⟨hxm, hx⟩
    have := hbmax x hxt
    omega
  have hbpos : 0 < b := by omega
  by_cases hex : m = b + 1 ∨ m = b * (b + 1)
  · have hnotprime : ¬ Nat.Prime b := by
      intro hbp
      have hsmall : ∀ x ∈ t.erase b, 1 ≤ x ∧ x < b := by
        intro x hx
        obtain ⟨hxb, hxt⟩ := Finset.mem_erase.mp hx
        have hxle := hbmax x hxt
        exact ⟨hpos x (Finset.mem_of_mem_erase hxt), by omega⟩
      have hsum' : (∑ x ∈ t.erase b, (1 : ℚ) / x) + 1 / b + 1 / m = 1 := by
        rw [Finset.sum_erase_add t (fun x => (1 : ℚ) / x) hbt]
        change (∑ x ∈ s.erase m, (1 : ℚ) / x) + 1 / m = 1
        rw [Finset.sum_erase_add s (fun x => (1 : ℚ) / x) hm, hsum]
      obtain ⟨h1, h2⟩ := hprime b hbp hb3 (t.erase b) hsmall m hsum'
      exact hex.elim h1 h2
    obtain ⟨u, v, hbu, huv, hvb, heq⟩ :=
      composite_unit_fraction_split b (by omega) hnotprime
    have hum : u ≠ m := by
      rcases hex with h | h
      · omega
      · omega
    have hvm : v ≠ m := by
      rcases hex with h | h
      · omega
      · omega
    exact ⟨b, u, v, hbs, hbm, by omega, by omega, by omega,
      avoid u (by omega) hum, avoid v (by omega) hvm, heq⟩
  · push Not at hex
    have hlt : b + 1 < b * (b + 1) := by nlinarith
    exact ⟨b, b + 1, b * (b + 1), hbs, hbm, by omega, by omega,
      by omega, avoid _ (by omega) (Ne.symm hex.1),
      avoid _ (by omega) (Ne.symm hex.2), unit_fraction_split b hbpos⟩

/-- The prime obstruction follows by clearing rational denominators. -/
theorem prime_padding_obstruction : PrimePaddingObstruction := by
  intro p hp hp3 t ht v hsum
  have ht' : ∀ x ∈ t, 0 < x ∧ x < p := by
    intro x hx
    obtain ⟨h1, h2⟩ := ht x hx
    exact ⟨by omega, h2⟩
  constructor
  · intro hv
    subst v
    exact prime_successor_prefix_obstruction t id p hp ht' hsum
  · intro hv
    subst v
    exact prime_product_prefix_obstruction t id p hp hp3 ht' hsum

/-- Exact marker padding, without analytic or counting hypotheses. -/
theorem exact_marker_padding_proof :
    ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
    ∀ m : ℕ, (∃ i : Fin r, n i = m) →
    ∃ n' : Fin (r + 1) → ℕ,
      IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m := by
  intro r hr n hn m hm
  classical
  let s := Finset.univ.image n
  have hcard : s.card = r := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hn.2.1.injective,
      Finset.card_univ, Fintype.card_fin]
  have hmem (x : ℕ) : x ∈ s ↔ ∃ i, n i = x := by simp [s]
  have hpos : ∀ x ∈ s, 1 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := (hmem x).mp hx
    exact hn.1 i
  have hsum : (∑ x ∈ s, (1 : ℚ) / x) = 1 := by
    dsimp [s]
    rw [Finset.sum_image (fun i _ j _ h => hn.2.1.injective h)]
    exact hn.2.2
  obtain ⟨b, u, v, hb, hbm, hu, hv, huv, hus, hvs, hsplit⟩ :=
    exists_marker_split_of_obstruction prime_padding_obstruction
      s (by omega) hpos hsum m ((hmem m).mpr hm)
  obtain ⟨t, htcard, htpos, htsum, htmem⟩ :=
    finset_replace_unit_fraction s b u v 1 hb hus hvs huv hpos hu hv hsplit.symm
  have htc : t.card = r + 1 := by omega
  obtain ⟨n', hn'pos, hn'mono, hn'sum, hn'mem⟩ :=
    finset_unit_fraction_representation t 1 1 htpos (htsum.trans hsum)
  have hex : ∃ n' : Fin t.card → ℕ, IsOneExpansion n' ∧ ∃ i, n' i = m := by
    refine ⟨n', ⟨hn'pos, hn'mono, hn'sum⟩, ?_⟩
    exact (hn'mem m).mpr (htmem m ((hmem m).mpr hm) hbm.symm)
  rwa [htc] at hex

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

theorem exact_marker_padding_oai :
    ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
  ∀ m : ℕ, (∃ i : Fin r, n i = m) →
    ∃ n' : Fin (r + 1) → ℕ,
      IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m := by
  exact exact_marker_padding_proof

end Problem337

end

end OAI
end

theorem solution : type_of% @OAI.Problem337.exact_marker_padding_oai := @OAI.Problem337.exact_marker_padding_oai
