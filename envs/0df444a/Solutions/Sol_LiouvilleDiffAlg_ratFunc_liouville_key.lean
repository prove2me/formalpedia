-- Prove2me | solution 1 for LiouvilleDiffAlg.ratFunc_liouville_key
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:56:09.832348+00:00
-- url     : https://prove2.me/submissions/1d667c2a-1616-4e81-871b-ad7f747ae870

import Mathlib
import Theorems.Thm_LiouvilleDiffAlg_ratFunc_pole_free
import Theorems.Thm_LiouvilleDiffAlg_ratFunc_residue_not_reg
import Theorems.Thm_LiouvilleDiffAlg_ratFunc_factor

open scoped Differential
open Polynomial

/-- regular at `p` -/
private def RegR {K : Type*} [Field K] (p : K[X]) (hp : Prime p) : Subring (RatFunc K) where
  carrier := {y | ∃ a b : K[X], ¬ p ∣ b ∧ y * algebraMap K[X] (RatFunc K) b = algebraMap K[X] (RatFunc K) a}
  zero_mem' := ⟨0, 1, fun h => hp.not_dvd_one h, by simp⟩
  one_mem' := ⟨1, 1, fun h => hp.not_dvd_one h, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, hx⟩ ⟨a', b', hb', hy⟩
    refine ⟨a * b' + a' * b, b * b', fun h => ?_, ?_⟩
    · rcases hp.dvd_or_dvd h with h | h
      · exact hb h
      · exact hb' h
    · simp only [map_mul, map_add]
      linear_combination (algebraMap K[X] (RatFunc K) b') * hx + (algebraMap K[X] (RatFunc K) b) * hy
  neg_mem' := by
    rintro x ⟨a, b, hb, hx⟩
    exact ⟨-a, b, hb, by simp [← hx]⟩
  mul_mem' := by
    rintro x y ⟨a, b, hb, hx⟩ ⟨a', b', hb', hy⟩
    refine ⟨a * a', b * b', fun h => ?_, ?_⟩
    · rcases hp.dvd_or_dvd h with h | h
      · exact hb h
      · exact hb' h
    · simp only [map_mul]
      rw [← hx, ← hy]; ring

private lemma mem_RegR {K : Type*} [Field K] {p : K[X]} (hp : Prime p) {y : RatFunc K} :
    y ∈ RegR p hp ↔ ∃ a b : K[X], ¬ p ∣ b ∧ y * algebraMap K[X] (RatFunc K) b = algebraMap K[X] (RatFunc K) a :=
  Iff.rfl

/-- simple pole at `p` -/
private def SPR {K : Type*} [Field K] (p : K[X]) (hp : Prime p) : AddSubgroup (RatFunc K) where
  carrier := {y | ∃ r s : K[X], ¬ p ∣ s ∧ y * algebraMap K[X] (RatFunc K) (p * s) = algebraMap K[X] (RatFunc K) r}
  zero_mem' := ⟨0, 1, fun h => hp.not_dvd_one h, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, hx⟩ ⟨a', b', hb', hy⟩
    refine ⟨a * b' + a' * b, b * b', fun h => ?_, ?_⟩
    · rcases hp.dvd_or_dvd h with h | h
      · exact hb h
      · exact hb' h
    · simp only [map_mul, map_add] at hx hy ⊢
      linear_combination (algebraMap K[X] (RatFunc K) b') * hx + (algebraMap K[X] (RatFunc K) b) * hy
  neg_mem' := by
    rintro x ⟨a, b, hb, hx⟩
    exact ⟨-a, b, hb, by simp only [map_neg, neg_mul]; rw [hx]⟩

private lemma mem_SPR {K : Type*} [Field K] {p : K[X]} (hp : Prime p) {y : RatFunc K} :
    y ∈ SPR p hp ↔ ∃ r s : K[X], ¬ p ∣ s ∧ y * algebraMap K[X] (RatFunc K) (p * s) = algebraMap K[X] (RatFunc K) r :=
  Iff.rfl

private lemma RegR_le_SPR {K : Type*} [Field K] {p : K[X]} (hp : Prime p) {y : RatFunc K}
    (hy : y ∈ RegR p hp) : y ∈ SPR p hp := by
  obtain ⟨a, b, hb, h⟩ := hy
  refine ⟨a * p, b, hb, ?_⟩
  simp only [map_mul] at h ⊢
  rw [← h]; ring

private lemma RegR_deriv {K : Type*} [Field K] [Differential K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    (hpoly : ∀ r : K[X], ∃ q : K[X], (algebraMap K[X] (RatFunc K) r)′ = algebraMap K[X] (RatFunc K) q)
    {p : K[X]} (hp : Prime p) {y : RatFunc K} (hy : y ∈ RegR p hp) : y′ ∈ RegR p hp := by
  obtain ⟨a, b, hb, h⟩ := hy
  obtain ⟨qa, hqa⟩ := hpoly a
  obtain ⟨qb, hqb⟩ := hpoly b
  refine ⟨qa * b - a * qb, b * b, fun hh => ?_, ?_⟩
  · rcases hp.dvd_or_dvd hh with hh | hh <;> exact hb hh
  · have h2 := congrArg (fun z => z′) h
    simp only [Derivation.leibniz, smul_eq_mul, hqa, hqb] at h2
    simp only [map_mul, map_sub]
    linear_combination (algebraMap K[X] (RatFunc K) b) * h2 - (algebraMap K[X] (RatFunc K) qb) * h

private lemma RegR_kappa {K : Type*} [Field K] {p : K[X]} (hp : Prime p) (k : K) :
    algebraMap K (RatFunc K) k ∈ RegR p hp :=
  ⟨C k, 1, fun h => hp.not_dvd_one h, by
    simp⟩

private lemma RegR_iota {K : Type*} [Field K] {p : K[X]} (hp : Prime p) (r : K[X]) :
    algebraMap K[X] (RatFunc K) r ∈ RegR p hp :=
  ⟨r, 1, fun h => hp.not_dvd_one h, by simp⟩

private lemma local_analysis {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    (hpoly : ∀ r : K[X], ∃ q : K[X], (algebraMap K[X] (RatFunc K) r)′ = algebraMap K[X] (RatFunc K) q)
    {p q : K[X]} (hp : Irreducible p)
    (hq : (algebraMap K[X] (RatFunc K) p)′ = algebraMap K[X] (RatFunc K) q) (hpq : ¬ p ∣ q)
    (E' : Finset K[X]) (Cc : K[X] → K) (hE' : ∀ p' ∈ E', p' ≠ p → ¬ p ∣ p')
    (R v : RatFunc K) (hR : R ∈ RegR p hp.prime) (h : K)
    (hfe : algebraMap K (RatFunc K) h = R +
      ∑ p' ∈ E', algebraMap K (RatFunc K) (Cc p') *
        ((algebraMap K[X] (RatFunc K) p')′ / algebraMap K[X] (RatFunc K) p') + v′) :
    (∃ a b : K[X], ¬ p ∣ b ∧ v * algebraMap K[X] (RatFunc K) b = algebraMap K[X] (RatFunc K) a) ∧
      (p ∈ E' → Cc p = 0) := by
  classical
  have hP := hp.prime
  have hp0 : algebraMap K[X] (RatFunc K) p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
  have hk : ∀ k : K, algebraMap K (RatFunc K) k = algebraMap K[X] (RatFunc K) (C k) := fun k => by simp
  have hGreg : ∀ p' ∈ E', p' ≠ p → algebraMap K (RatFunc K) (Cc p') *
        ((algebraMap K[X] (RatFunc K) p')′ / algebraMap K[X] (RatFunc K) p') ∈ RegR p hP := by
    intro p' hp' hne
    have hnd := hE' p' hp' hne
    have hp'0 : p' ≠ 0 := fun h0 => hnd (h0 ▸ dvd_zero p)
    obtain ⟨q', hq'⟩ := hpoly p'
    refine Subring.mul_mem _ (RegR_kappa hP _) ⟨q', p', hnd, ?_⟩
    rw [hq']
    exact div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hp'0)
  have hG : ∀ p' ∈ E', algebraMap K (RatFunc K) (Cc p') *
        ((algebraMap K[X] (RatFunc K) p')′ / algebraMap K[X] (RatFunc K) p') ∈ SPR p hP := by
    intro p' hp'
    by_cases hpp : p' = p
    · rw [hpp]
      refine ⟨C (Cc p) * q, 1, fun h => hP.not_dvd_one h, ?_⟩
      rw [hq]
      simp only [mul_one, map_mul]
      rw [hk]
      field_simp
    · exact RegR_le_SPR hP (hGreg p' hp' hpp)
  have hvd : v′ ∈ SPR p hP := by
    have : v′ = algebraMap K (RatFunc K) h - R - ∑ p' ∈ E', algebraMap K (RatFunc K) (Cc p') *
        ((algebraMap K[X] (RatFunc K) p')′ / algebraMap K[X] (RatFunc K) p') := by
      rw [hfe]; ring
    rw [this]
    exact sub_mem (sub_mem (RegR_le_SPR hP (RegR_kappa hP h)) (RegR_le_SPR hP hR))
      (sum_mem hG)
  have hreg : v ∈ RegR p hP :=
    LiouvilleDiffAlg.ratFunc_pole_free hpoly hp hq hpq v hvd
  refine ⟨hreg, fun hpE => ?_⟩
  by_contra hne
  have hvreg := RegR_deriv hpoly hP hreg
  have hsum := (Finset.add_sum_erase E' (fun p' => algebraMap K (RatFunc K) (Cc p') *
        ((algebraMap K[X] (RatFunc K) p')′ / algebraMap K[X] (RatFunc K) p')) hpE)
  have hrest : ∑ p' ∈ E'.erase p, algebraMap K (RatFunc K) (Cc p') *
        ((algebraMap K[X] (RatFunc K) p')′ / algebraMap K[X] (RatFunc K) p') ∈ RegR p hP :=
    Subring.sum_mem _ (fun p' hp' => hGreg p' (Finset.mem_of_mem_erase hp') (Finset.ne_of_mem_erase hp'))
  have hmain : algebraMap K (RatFunc K) (Cc p) *
        ((algebraMap K[X] (RatFunc K) p)′ / algebraMap K[X] (RatFunc K) p) ∈ RegR p hP := by
    have : algebraMap K (RatFunc K) (Cc p) *
        ((algebraMap K[X] (RatFunc K) p)′ / algebraMap K[X] (RatFunc K) p) =
        algebraMap K (RatFunc K) h - R - (∑ p' ∈ E'.erase p, algebraMap K (RatFunc K) (Cc p') *
        ((algebraMap K[X] (RatFunc K) p')′ / algebraMap K[X] (RatFunc K) p')) - v′ := by
      rw [hfe, ← hsum]; ring
    rw [this]
    exact Subring.sub_mem _ (Subring.sub_mem _ (Subring.sub_mem _ (RegR_kappa hP h) hR) hrest) hvreg
  obtain ⟨a, b, hb, hab⟩ := hmain
  rw [hq] at hab
  exact LiouvilleDiffAlg.ratFunc_residue_not_reg hp hpq hne ⟨a, b, hb, hab⟩

private lemma logDeriv_iota_prod {K : Type*} [Field K] [Differential (RatFunc K)] [DecidableEq K[X]]
    (N : Multiset K[X]) (hN : ∀ p ∈ N, Irreducible p) (E' : Finset K[X]) (hE : ∀ p ∈ N, p ∈ E') :
    (algebraMap K[X] (RatFunc K) N.prod)′ / algebraMap K[X] (RatFunc K) N.prod =
      ∑ p ∈ E', N.count p • ((algebraMap K[X] (RatFunc K) p)′ / algebraMap K[X] (RatFunc K) p) := by
  have h1 : Differential.logDeriv (algebraMap K[X] (RatFunc K) N.prod) =
      (N.map fun p => Differential.logDeriv (algebraMap K[X] (RatFunc K) p)).sum := by
    rw [map_multiset_prod]
    exact Differential.logDeriv_multisetProd _ (fun x hx => RatFunc.algebraMap_ne_zero (hN x hx).ne_zero)
  have h2 := Finset.sum_multiset_map_count N (fun p => Differential.logDeriv (algebraMap K[X] (RatFunc K) p))
  unfold Differential.logDeriv at h1 h2
  rw [h1, h2]
  refine Finset.sum_subset (fun p hp => hE p (Multiset.mem_toFinset.mp hp)) ?_
  intro p _ hp
  rw [Multiset.count_eq_zero.mpr (fun h => hp (Multiset.mem_toFinset.mpr h))]
  simp

private lemma decompose {K : Type*} [Field K] [Differential K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    {n : ℕ} (c : Fin n → K) (hc : ∀ i, (c i)′ = 0)
    (u : Fin n → RatFunc K) (hu : ∀ i, u i ≠ 0) :
    ∃ (a : Fin n → K) (E' : Finset K[X]) (Cc : K[X] → K),
      (∀ i, a i ≠ 0) ∧ (∀ p ∈ E', Monic p ∧ Irreducible p) ∧ (∀ p, (Cc p)′ = 0) ∧
      ∑ i, algebraMap K (RatFunc K) (c i) * ((u i)′ / u i) =
        ∑ i, algebraMap K (RatFunc K) (c i) *
          ((algebraMap K (RatFunc K) (a i))′ / algebraMap K (RatFunc K) (a i)) +
        ∑ p ∈ E', algebraMap K (RatFunc K) (Cc p) *
          ((algebraMap K[X] (RatFunc K) p)′ / algebraMap K[X] (RatFunc K) p) := by
  classical
  choose a N D ha hN hD hue using fun i => LiouvilleDiffAlg.ratFunc_factor (u i) (hu i)
  refine ⟨a, Finset.univ.biUnion (fun i => (N i + D i).toFinset),
    fun p => ∑ i, c i * ((Multiset.count p (N i) : K) - (Multiset.count p (D i) : K)),
    ha, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      Multiset.mem_add] at hp
    obtain ⟨i, hi | hi⟩ := hp
    · exact hN i p hi
    · exact hD i p hi
  · intro p
    rw [map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    simp [Derivation.leibniz, hc]
  · set E' : Finset K[X] := Finset.univ.biUnion (fun i => (N i + D i).toFinset) with hE'
    have hNE : ∀ i, ∀ p ∈ N i, p ∈ E' := fun i p hp => by
      simp only [hE', Finset.mem_biUnion, Finset.mem_univ, true_and, Multiset.mem_toFinset,
        Multiset.mem_add]
      exact ⟨i, Or.inl hp⟩
    have hDE : ∀ i, ∀ p ∈ D i, p ∈ E' := fun i p hp => by
      simp only [hE', Finset.mem_biUnion, Finset.mem_univ, true_and, Multiset.mem_toFinset,
        Multiset.mem_add]
      exact ⟨i, Or.inr hp⟩
    have key : ∀ i, (u i)′ / u i =
        (algebraMap K (RatFunc K) (a i))′ / algebraMap K (RatFunc K) (a i) +
        ∑ p ∈ E', (N i).count p • ((algebraMap K[X] (RatFunc K) p)′ / algebraMap K[X] (RatFunc K) p) -
        ∑ p ∈ E', (D i).count p • ((algebraMap K[X] (RatFunc K) p)′ / algebraMap K[X] (RatFunc K) p) := by
      intro i
      have hx : algebraMap K (RatFunc K) (a i) ≠ 0 := by simpa using ha i
      have hy : algebraMap K[X] (RatFunc K) (N i).prod ≠ 0 := by
        refine RatFunc.algebraMap_ne_zero ?_
        rw [Ne, Multiset.prod_eq_zero_iff]
        exact fun h0 => (hN i 0 h0).2.ne_zero rfl
      have hz : algebraMap K[X] (RatFunc K) (D i).prod ≠ 0 := by
        refine RatFunc.algebraMap_ne_zero ?_
        rw [Ne, Multiset.prod_eq_zero_iff]
        exact fun h0 => (hD i 0 h0).2.ne_zero rfl
      have e : Differential.logDeriv (u i) =
          Differential.logDeriv (algebraMap K (RatFunc K) (a i)) +
          Differential.logDeriv (algebraMap K[X] (RatFunc K) (N i).prod) -
          Differential.logDeriv (algebraMap K[X] (RatFunc K) (D i).prod) := by
        rw [hue i, Differential.logDeriv_div _ _ (mul_ne_zero hx hy) hz,
          Differential.logDeriv_mul _ _ hx hy]
      unfold Differential.logDeriv at e
      rw [e, logDeriv_iota_prod (N i) (fun p hp => (hN i p hp).2) E' (hNE i),
        logDeriv_iota_prod (D i) (fun p hp => (hD i p hp).2) E' (hDE i)]
    simp_rw [key]
    simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [add_sub_assoc]
    congr 1
    simp only [map_sum, map_sub, map_mul, map_natCast, Finset.mul_sum, Finset.sum_mul, nsmul_eq_mul,
      sub_mul, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring

private lemma RegR_sum_logDeriv {K : Type*} [Field K] [Differential K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    {p : K[X]} (hp : Prime p) {n : ℕ} (c : Fin n → K) (a : Fin n → K) :
    ∑ i, algebraMap K (RatFunc K) (c i) *
      ((algebraMap K (RatFunc K) (a i))′ / algebraMap K (RatFunc K) (a i)) ∈ RegR p hp := by
  refine Subring.sum_mem _ (fun i _ => Subring.mul_mem _ (RegR_kappa hp _) ?_)
  rw [DifferentialAlgebra.deriv_algebraMap, ← map_div₀]
  exact RegR_kappa hp _

private lemma not_dvd_of_ne {K : Type*} [Field K] {p p' : K[X]} (hp : Monic p) (hpi : Irreducible p)
    (hp' : Monic p') (hpi' : Irreducible p') (hne : p' ≠ p) : ¬ p ∣ p' := fun hd =>
  hne (Polynomial.eq_of_monic_of_associated hp' hp (hpi.associated_of_dvd hpi' hd).symm)

theorem solution {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    (hpoly : ∀ r : K[X], ∃ q : K[X], (algebraMap K[X] (RatFunc K) r)′ = algebraMap K[X] (RatFunc K) q)
    (Exc : K[X] → Prop)
    (hExc : ∀ p q : K[X], Monic p → Irreducible p → ¬ Exc p →
      (algebraMap K[X] (RatFunc K) p)′ = algebraMap K[X] (RatFunc K) q → ¬ p ∣ q)
    {n : ℕ} (c : Fin n → K) (hc : ∀ i, (c i)′ = 0) (h : K)
    (u : Fin n → RatFunc K) (hu : ∀ i, u i ≠ 0) (v : RatFunc K)
    (hfe : algebraMap K (RatFunc K) h = ∑ i, algebraMap K (RatFunc K) (c i) * ((u i)′ / u i) + v′) :
    ∃ (a : Fin n → K) (E : Finset K[X]) (C : K[X] → K) (A B : K[X]),
      (∀ i, a i ≠ 0) ∧ (∀ p ∈ E, Monic p ∧ Irreducible p ∧ Exc p) ∧ (∀ p, (C p)′ = 0) ∧
      B ≠ 0 ∧ v = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) B ∧
      (∀ p, Monic p → Irreducible p → p ∣ B → Exc p) ∧
      algebraMap K (RatFunc K) h =
        ∑ i, algebraMap K (RatFunc K) (c i) * ((algebraMap K (RatFunc K) (a i))′ / algebraMap K (RatFunc K) (a i)) +
        ∑ p ∈ E, algebraMap K (RatFunc K) (C p) * ((algebraMap K[X] (RatFunc K) p)′ / algebraMap K[X] (RatFunc K) p) + v′ := by
  classical
  obtain ⟨a, E', Cc, ha, hE'mi, hC, hdec⟩ := decompose c hc u hu
  rw [hdec] at hfe
  have hloc : ∀ p : K[X], Monic p → Irreducible p → ¬ Exc p →
      (∃ a b : K[X], ¬ p ∣ b ∧ v * algebraMap K[X] (RatFunc K) b = algebraMap K[X] (RatFunc K) a) ∧
      (p ∈ E' → Cc p = 0) := by
    intro p hpm hpi hnE
    obtain ⟨q, hq⟩ := hpoly p
    exact local_analysis hpoly hpi hq (hExc p q hpm hpi hnE hq) E' Cc
      (fun p' hp' hne => not_dvd_of_ne hpm hpi (hE'mi p' hp').1 (hE'mi p' hp').2 hne)
      _ v (RegR_sum_logDeriv hpi.prime c a) h hfe
  refine ⟨a, E'.filter Exc, Cc, v.num, v.denom, ha, ?_, hC, RatFunc.denom_ne_zero v,
    (RatFunc.num_div_denom v).symm, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨(hE'mi p hp.1).1, (hE'mi p hp.1).2, hp.2⟩
  · intro p hpm hpi hpd
    by_contra hnE
    obtain ⟨a', b, hb, hab⟩ := (hloc p hpm hpi hnE).1
    have hP := hpi.prime
    have h1 : algebraMap K[X] (RatFunc K) (v.num * b) =
        algebraMap K[X] (RatFunc K) (a' * v.denom) := by
      rw [map_mul, map_mul, ← hab]
      have hd := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero v)
      have := RatFunc.num_div_denom v
      rw [div_eq_iff hd] at this
      rw [this]; ring
    have h2 := RatFunc.algebraMap_injective K h1
    have h3 : p ∣ v.num * b := h2 ▸ Dvd.dvd.mul_left hpd a'
    rcases hP.dvd_or_dvd h3 with h4 | h4
    · exact hpi.not_isUnit
        ((RatFunc.isCoprime_num_denom v).isUnit_of_dvd' h4 hpd)
    · exact hb h4
  · rw [hfe]
    congr 1
    congr 1
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro p hp hpn
    have hnE : ¬ Exc p := fun hE => hpn (Finset.mem_filter.mpr ⟨hp, hE⟩)
    rw [(hloc p (hE'mi p hp).1 (hE'mi p hp).2 hnE).2 hp]
    simp
