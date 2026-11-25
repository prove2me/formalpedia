-- Prove2me | solution 1 for GlobalTheory.arithmetic_large_sieve_one_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:40.91505+00:00
-- url     : https://prove2.me/submissions/a2923040-4b25-431d-be93-51bfe8cdbfb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultiplicativeLargeSieve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ArithmeticLargeSieveOneResidueClassPerPrime
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_GlobalTheory_MultSieve_farey_spaced
import Theorems.Thm_GlobalTheory_MultSieve_reduced_inj
import Theorems.Thm_GlobalTheory_Square_IsAwayUnit_mul
import Theorems.Thm_GlobalTheory_Square_IsAwayUnit_one
import Theorems.Thm_GlobalTheory_additive_large_sieve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
namespace GlobalTheory
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma squarefree_prod_of_prime (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hx hxx
  have hmem : ∀ t ⊆ s, x ∣ ∏ p ∈ t, p → x ∈ t := by
    intro t ht hdvd
    obtain ⟨p, hp, hxp⟩ := (Prime.dvd_finset_prod_iff hx.prime _).1 hdvd
    rw [(Nat.prime_dvd_prime_iff_eq hx (h p (ht hp))).1 hxp]; exact hp
  have hxs : x ∈ s := hmem s subset_rfl (dvd_trans (dvd_mul_right x x) hxx)
  rw [← Finset.mul_prod_erase s (fun p => p) hxs] at hxx
  have := hmem (s.erase x) (Finset.erase_subset _ _) (Nat.dvd_of_mul_dvd_mul_left hx.pos hxx)
  simp at this
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma dvd_pow_of_prime_dvd_imp (n k : ℕ) (h : ∀ p, p.Prime → p ∣ n → p ∣ k) (hn : n ≠ 0) (hk : k ≠ 0) :
    n ∣ k ^ n := by
  rw [← Nat.factorization_le_iff_dvd hn (pow_ne_zero _ hk)]
  intro p
  rw [Nat.factorization_pow]
  by_cases hp : p.Prime ∧ p ∣ n
  · have h1 : 1 ≤ k.factorization p := (hp.1.dvd_iff_one_le_factorization hk).1 (h p hp.1 hp.2)
    have h2 : n.factorization p < n := Nat.factorization_lt p hn
    simp only [Finsupp.smul_apply, smul_eq_mul]
    nlinarith
  · have : n.factorization p = 0 := by
      by_cases hp' : p.Prime
      · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hp ⟨hp', hd⟩)
      · exact Nat.factorization_eq_zero_of_not_prime _ hp'
    rw [this]; exact Nat.zero_le _
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma sum_inv_divisors_eq_sigma_div (N : ℕ) (hN : N ≠ 0) :
    ∑ m ∈ N.divisors, (1 : ℝ) / m = (ArithmeticFunction.sigma 1 N : ℝ) / N := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.sum_div, ← Nat.sum_div_divisors]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN := Nat.dvd_of_mem_divisors hd
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hN0 : (N:ℝ) ≠ 0 := by exact_mod_cast hN
  rw [Nat.cast_div hdN hd0]
  field_simp
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma totient_mul_sigma_pow_le_pow_succ (K : ℕ) :
    ∀ n : ℕ, 0 < n → n.totient * ArithmeticFunction.sigma 1 (n ^ K) ≤ n ^ (K + 1) := by
  intro n hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    rw [← pow_mul, ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.totient_prime_pow hp ha]
    have key : (p - 1) * ∑ i ∈ Finset.range (a * K + 1), p ^ i = p ^ (a * K + 1) - 1 := by
      have h1 : 1 ≤ p := hp.one_le
      zify [h1, Nat.one_le_pow _ _ hp.pos]
      rw [mul_comm, geom_sum_mul]
    calc p ^ (a - 1) * (p - 1) * ∑ i ∈ Finset.range (a * K + 1), p ^ i
        = p ^ (a - 1) * (p ^ (a * K + 1) - 1) := by rw [mul_assoc, key]
      _ ≤ p ^ (a - 1) * p ^ (a * K + 1) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = p ^ (a * (K + 1)) := by
        rw [← pow_add]; congr 1
        cases a with
        | zero => omega
        | succ a => simp [Nat.succ_sub_one]; ring
      _ ≤ (p ^ a) ^ (K + 1) := by rw [← pow_mul]
  | zero => exact absurd hn (lt_irrefl 0)
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [mul_pow, Nat.totient_mul hab,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow K K hab), mul_pow]
    calc a.totient * b.totient * (ArithmeticFunction.sigma 1 (a ^ K) * ArithmeticFunction.sigma 1 (b ^ K))
        = (a.totient * ArithmeticFunction.sigma 1 (a ^ K)) * (b.totient * ArithmeticFunction.sigma 1 (b ^ K)) := by ring
      _ ≤ a ^ (K + 1) * b ^ (K + 1) := Nat.mul_le_mul (iha (by omega)) (ihb (by omega))
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma sum_inv_le_mul_sum_squarefree_inv_totient (Q q : ℕ) (hq : 1 ≤ q) :
    ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n ≤ ((q:ℝ) / q.totient) *
      ∑ f ∈ (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q), (1:ℝ) / f.totient := by
  set D := (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q) with hD
  set g : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ q), p with hg
  have hgdvd : ∀ n, g n ∣ n := fun n =>
    dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)) (Nat.prod_primeFactors_dvd n)
  have hgD : ∀ n ∈ Finset.Icc 1 Q, g n ∈ D := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [hD, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.pos_of_dvd_of_pos (hgdvd n) (by omega), le_trans (Nat.le_of_dvd (by omega) (hgdvd n)) hn.2⟩,
      squarefree_prod_of_prime _ fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1,
      Nat.Coprime.prod_left fun p hp => (Nat.Prime.coprime_iff_not_dvd
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)).2 (Finset.mem_filter.1 hp).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hgD, Finset.mul_sum]
  refine Finset.sum_le_sum fun f hf => ?_
  rw [hD, Finset.mem_filter, Finset.mem_Icc] at hf
  have hf0 : 0 < f := hf.1.1
  have hq0 : 0 < q := hq
  set N := (f * q) ^ Q with hN
  have hN0 : N ≠ 0 := pow_ne_zero _ (Nat.mul_pos hf0 hq0).ne'
  have hfib : ∀ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), f ∣ n ∧ n ∣ N := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    refine ⟨hn.2 ▸ hgdvd n, dvd_trans (dvd_pow_of_prime_dvd_imp n (f * q) ?_ (by omega)
      (Nat.mul_pos hf0 hq0).ne') (pow_dvd_pow _ hn.1.2)⟩
    intro p hp hpn
    by_cases hpq : p ∣ q
    · exact dvd_mul_of_dvd_right hpq _
    · apply dvd_mul_of_dvd_left
      rw [← hn.2]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hp.mem_primeFactors hpn (by omega), hpq⟩)
  have hf0' : (f:ℝ) ≠ 0 := by exact_mod_cast hf0.ne'
  calc ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), (1:ℝ) / n
      = ∑ m ∈ ((Finset.Icc 1 Q).filter (fun n => g n = f)).image (· / f), (1:ℝ) / (f * m) := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun n hn => ?_
          rw [← Nat.cast_mul, Nat.mul_div_cancel' (hfib n hn).1]
        · intro x hx y hy hxy
          exact (Nat.div_left_inj (hfib x hx).1 (hfib y hy).1).1 hxy
    _ ≤ ∑ m ∈ N.divisors, (1:ℝ) / (f * m) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm
        exact Nat.mem_divisors.2 ⟨dvd_trans (Nat.div_dvd_of_dvd (hfib n hn).1) (hfib n hn).2, hN0⟩
    _ = (1 / f) * ((ArithmeticFunction.sigma 1 N : ℝ) / N) := by
        rw [← sum_inv_divisors_eq_sigma_div N hN0, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [one_div_mul_one_div]
    _ ≤ (q:ℝ) / q.totient * (1 / f.totient) := by
        have hcop : Nat.Coprime (f ^ Q) (q ^ Q) := Nat.Coprime.pow Q Q hf.2.2
        rw [hN, mul_pow, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
        have hA := totient_mul_sigma_pow_le_pow_succ Q f hf0
        have hB := totient_mul_sigma_pow_le_pow_succ Q q hq0
        have hφf : (0:ℝ) < f.totient := by exact_mod_cast Nat.totient_pos.2 hf0
        have hφq : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
        have hA' : (f.totient : ℝ) * ArithmeticFunction.sigma 1 (f ^ Q) ≤ (f:ℝ) ^ (Q + 1) := by exact_mod_cast hA
        have hB' : (q.totient : ℝ) * ArithmeticFunction.sigma 1 (q ^ Q) ≤ (q:ℝ) ^ (Q + 1) := by exact_mod_cast hB
        have hfpos : (0:ℝ) < f := by exact_mod_cast hf0
        have hqpos : (0:ℝ) < q := by exact_mod_cast hq0
        push_cast
        rw [one_div_mul_eq_div, div_div, div_le_iff₀ (by positivity)]
        have hprod := mul_le_mul hA' hB' (by positivity) (by positivity)
        have hrw : (q:ℝ) / q.totient * (1 / f.totient) * (f ^ Q * q ^ Q * f)
            = ((f:ℝ) ^ (Q + 1) * (q:ℝ) ^ (Q + 1)) / (q.totient * f.totient) := by
          field_simp; ring
        rw [hrw, le_div_iff₀ (by positivity)]
        nlinarith [hprod]
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma coprime_mod_mul_iff (d p m : ℕ) : Nat.Coprime d (m % (d * p)) ↔ Nat.Coprime d m := by
  have h : m % (d * p) + (p * (m / (d * p))) * d = m := by
    have := Nat.mod_add_div m (d * p); linarith [mul_comm d p, mul_assoc d p (m / (d*p)), mul_comm (p * (m / (d * p))) d]
  conv_rhs => rw [← h]
  exact (Nat.coprime_add_mul_right_right _ _ _).symm
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma coprime_mul_add_mul_iff (d p a b : ℕ) (h : Nat.Coprime d p) :
    Nat.Coprime d (a * p + b * d) ↔ Nat.Coprime d a := by
  rw [Nat.coprime_add_mul_right_right, Nat.coprime_mul_iff_right]
  exact ⟨fun h => h.1, fun h' => ⟨h', h⟩⟩
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma sum_coprime_range_mul_eq_sum_sum (d p : ℕ) (hd : 0 < d) (hp : p.Prime) (hpd : ¬ p ∣ d)
    (F : ℕ → ℝ) (hF : ∀ m, F m = F (m % (d * p))) :
    ∑ a ∈ (Finset.range (d * p)).filter (d * p).Coprime, F a
      = ∑ a₁ ∈ (Finset.range d).filter d.Coprime, ∑ a₂ ∈ (Finset.range p).filter p.Coprime,
          F (a₁ * p + a₂ * d) := by
  have hp0 := hp.pos
  have hcop : Nat.Coprime d p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd))
  rw [← Finset.sum_product']
  symm
  have hmaps : ∀ x ∈ ((Finset.range d).filter d.Coprime) ×ˢ ((Finset.range p).filter p.Coprime),
      (x.1 * p + x.2 * d) % (d * p) ∈ (Finset.range (d * p)).filter (d * p).Coprime := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx ⊢
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hd hp0), Nat.Coprime.mul ?_ ?_⟩
    · rw [coprime_mod_mul_iff, coprime_mul_add_mul_iff _ _ _ _ hcop]; exact hx.1.2
    · rw [mul_comm d p, coprime_mod_mul_iff, add_comm, coprime_mul_add_mul_iff _ _ _ _ hcop.symm]
      exact hx.2.2
  have hinj : ∀ x ∈ ((Finset.range d).filter d.Coprime) ×ˢ ((Finset.range p).filter p.Coprime),
      ∀ y ∈ ((Finset.range d).filter d.Coprime) ×ˢ ((Finset.range p).filter p.Coprime),
      (x.1 * p + x.2 * d) % (d * p) = (y.1 * p + y.2 * d) % (d * p) → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx hy
    have hmod : x.1 * p + x.2 * d ≡ y.1 * p + y.2 * d [MOD d * p] := hxy
    have h1 : x.1 * p ≡ y.1 * p [MOD d] := by
      have := Nat.ModEq.of_mul_right p hmod
      simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using this
    have h2 : x.2 * d ≡ y.2 * d [MOD p] := by
      have := Nat.ModEq.of_mul_left d hmod
      simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using this
    have e1 : x.1 % d = y.1 % d := Nat.ModEq.cancel_right_of_coprime hcop h1
    have e2 : x.2 % p = y.2 % p := Nat.ModEq.cancel_right_of_coprime hcop.symm h2
    rw [Nat.mod_eq_of_lt hx.1.1, Nat.mod_eq_of_lt hy.1.1] at e1
    rw [Nat.mod_eq_of_lt hx.2.1, Nat.mod_eq_of_lt hy.2.1] at e2
    exact Prod.ext e1 e2
  refine Finset.sum_nbij (fun x => (x.1 * p + x.2 * d) % (d * p)) hmaps (fun x hx y hy h => hinj x hx y hy h) ?_ ?_
  · intro z hz
    obtain ⟨x, hx, hxz⟩ := Finset.surj_on_of_inj_on_of_card_le
      (fun x _ => (x.1 * p + x.2 * d) % (d * p)) hmaps (fun x y hx hy h => hinj x hx y hy h) (le_of_eq (by
        rw [Finset.card_product, ← Nat.totient_eq_card_coprime, ← Nat.totient_eq_card_coprime,
          ← Nat.totient_eq_card_coprime, Nat.totient_mul hcop])) z hz
    exact ⟨x, hx, hxz.symm⟩
  · intro x _; exact hF _
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma cexp_mul_div_eq_of_mod_right (D : ℕ) (hD : 0 < D) (n m : ℕ) :
    cexp (2 * ↑Real.pi * I * n * m / D) = cexp (2 * ↑Real.pi * I * n * ↑(m % D) / D) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  have hD' : (D:ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have h := Nat.div_add_mod m D
  have : (m:ℂ) = D * (m / D : ℕ) + (m % D : ℕ) := by exact_mod_cast h.symm
  generalize m / D = k at this
  refine ⟨(n * k : ℕ), ?_⟩
  rw [this]; push_cast; field_simp; ring
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma cexp_crt_combination_eq_mul (d p n a₁ a₂ : ℕ) (hd : 0 < d) (hp : 0 < p) :
    cexp (2 * ↑Real.pi * I * n * ↑(a₁ * p + a₂ * d) / ↑(d * p))
      = cexp (2 * ↑Real.pi * I * n * a₁ / d) * cexp (2 * ↑Real.pi * I * n * a₂ / p) := by
  rw [← Complex.exp_add]
  congr 1
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp' : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma filter_coprime_range_prime_eq_erase_zero (p : ℕ) (hp : p.Prime) :
    (Finset.range p).filter p.Coprime = (Finset.range p).erase 0 := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    rintro rfl
    simp [Nat.coprime_zero_right] at h2
    exact hp.one_lt.ne' h2
  · rintro ⟨h1, h2⟩
    refine ⟨h2, (Nat.Prime.coprime_iff_not_dvd hp).2 ?_⟩
    intro h
    exact h1 (Nat.eq_zero_of_dvd_of_lt h h2)
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma cexp_mul_div_eq_natMod_left (d : ℕ) (hd : 0 < d) (n a : ℕ) :
    cexp (2 * ↑Real.pi * I * n * a / d) = cexp (2 * ↑Real.pi * I * ↑(n % d) * a / d) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := Nat.div_add_mod n d
  have : (n:ℂ) = d * (n / d : ℕ) + (n % d : ℕ) := by exact_mod_cast h.symm
  generalize n / d = m at this
  refine ⟨(m * a : ℕ), ?_⟩
  rw [this]; push_cast; field_simp; ring
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma sum_range_cexp_eq_ite_dvd (d : ℕ) (hd : 0 < d) (k : ℤ) :
    ∑ a ∈ Finset.range d, cexp (2 * ↑Real.pi * I * k * a / d) = if (d:ℤ) ∣ k then (d:ℂ) else 0 := by
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  set ζ := cexp (2 * ↑Real.pi * I * k / d) with hζ
  have hterm : ∀ a : ℕ, cexp (2 * ↑Real.pi * I * k * a / d) = ζ ^ a := by
    intro a; rw [hζ, ← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [hterm]
  have hζd : ζ ^ d = 1 := by
    rw [hζ, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    exact ⟨k, by field_simp⟩
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    have : ζ = 1 := by
      rw [hζ, Complex.exp_eq_one_iff]; exact ⟨j, by push_cast; field_simp⟩
    simp [this]
  · have hne : ζ ≠ 1 := by
      intro h1
      rw [hζ, Complex.exp_eq_one_iff] at h1
      obtain ⟨j, hj⟩ := h1
      apply h
      refine ⟨j, ?_⟩
      field_simp at hj
      exact_mod_cast hj
    rw [geom_sum_eq hne, hζd, sub_self, zero_div]
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma sum_norm_sq_exp_sum_eq_mul_sum_residues (d : ℕ) (hd : 0 < d) (S : Finset ℕ) (b : ℕ → ℂ) :
    ∑ a ∈ Finset.range d, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2
      = d * ∑ r ∈ Finset.range d, ‖∑ n ∈ S.filter (fun n => n % d = r), b n‖ ^ 2 := by
  set B : ℕ → ℂ := fun r => ∑ n ∈ S.filter (fun n => n % d = r), b n with hB
  have hgroup : ∀ a : ℕ, ∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / d)
      = ∑ r ∈ Finset.range d, B r * cexp (2 * ↑Real.pi * I * r * a / d) := by
    intro a
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % d) (t := Finset.range d)
      (fun n _ => Finset.mem_range.2 (Nat.mod_lt n hd))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hB, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [cexp_mul_div_eq_natMod_left d hd n a, (Finset.mem_filter.1 hn).2]
  have hsq : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  clear_value B
  apply Complex.ofReal_injective
  push_cast
  rw [Finset.mul_sum]
  simp_rw [hgroup, hsq, map_sum, map_mul, Finset.sum_mul_sum]
  have horth : ∀ r ∈ Finset.range d, ∀ s ∈ Finset.range d,
      ∑ a ∈ Finset.range d, B r * cexp (2 * ↑Real.pi * I * r * a / d) *
        ((starRingEnd ℂ) (B s) * (starRingEnd ℂ) (cexp (2 * ↑Real.pi * I * s * a / d)))
        = if r = s then d * (B r * (starRingEnd ℂ) (B s)) else 0 := by
    intro r hr s hs
    have hconj : ∀ a : ℕ, cexp (2 * ↑Real.pi * I * r * a / d) * (starRingEnd ℂ) (cexp (2 * ↑Real.pi * I * s * a / d))
        = cexp (2 * ↑Real.pi * I * ((r:ℤ) - s : ℤ) * a / d) := by
      intro a
      rw [← Complex.exp_conj, ← Complex.exp_add]; congr 1
      simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
      push_cast; ring
    calc _ = B r * (starRingEnd ℂ) (B s) * ∑ a ∈ Finset.range d, cexp (2 * ↑Real.pi * I * ((r:ℤ) - s : ℤ) * a / d) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; rw [← hconj a]; ring
      _ = _ := by
          rw [sum_range_cexp_eq_ite_dvd d hd]
          have hr' := Finset.mem_range.1 hr; have hs' := Finset.mem_range.1 hs
          by_cases hrs : r = s
          · subst hrs; simp; ring
          · have : ¬ (d:ℤ) ∣ ((r:ℤ) - s) := by
              intro ⟨j, hj⟩
              apply hrs
              have h1 : (r:ℤ) - s < d := by omega
              have h2 : -(d:ℤ) < (r:ℤ) - s := by omega
              have : j = 0 := by
                rcases lt_trichotomy j 0 with h | h | h
                · nlinarith
                · exact h
                · nlinarith
              subst this; omega
            simp [this, hrs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.sum_comm, Finset.sum_congr rfl fun s hs => horth r hr s hs, Finset.sum_ite_eq]
  simp only [hr, if_true]
  rw [hB]
  simp [map_sum, Finset.sum_mul_sum]
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma norm_sum_sq_le_pred_mul_of_avoids_class (p : ℕ) (hp : p.Prime) (c : ℕ) (S : Finset ℕ) (b : ℕ → ℂ)
    (hS : ∀ n ∈ S, ¬ n ≡ c [MOD p]) :
    ‖∑ n ∈ S, b n‖ ^ 2 ≤ (p - 1 : ℝ) *
      ∑ a ∈ (Finset.range p).erase 0, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / p)‖ ^ 2 := by
  have hp0 := hp.pos
  have hpar := sum_norm_sq_exp_sum_eq_mul_sum_residues p hp0 S b
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hp0)] at hpar
  simp only [Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one] at hpar
  set B : ℕ → ℝ := fun r => ‖∑ n ∈ S.filter (fun n => n % p = r), b n‖ with hB
  have hc : B (c % p) = 0 := by
    simp only [hB, norm_eq_zero]
    rw [Finset.filter_false_of_mem]; · simp
    intro n hn h; exact hS n hn h
  have hsplit : ∑ n ∈ S, b n = ∑ r ∈ ((Finset.range p).erase (c % p)), ∑ n ∈ S.filter (fun n => n % p = r), b n := by
    rw [Finset.sum_erase]
    · exact (Finset.sum_fiberwise_of_maps_to (g := fun n => n % p) (t := Finset.range p)
        (fun n _ => Finset.mem_range.2 (Nat.mod_lt n hp0)) b).symm
    · rw [← norm_eq_zero]; exact hc
  have hcs : ‖∑ n ∈ S, b n‖ ^ 2 ≤ (p - 1 : ℝ) * ∑ r ∈ Finset.range p, B r ^ 2 := by
    rw [hsplit]
    have hcard : (((Finset.range p).erase (c % p)).card : ℝ) = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.2 (Nat.mod_lt c hp0)), Finset.card_range]
      push_cast [Nat.cast_sub hp.one_le]; ring
    calc _ ≤ (∑ r ∈ (Finset.range p).erase (c % p), B r) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ ≤ (((Finset.range p).erase (c % p)).card : ℝ) * ∑ r ∈ (Finset.range p).erase (c % p), B r ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ (p - 1 : ℝ) * ∑ r ∈ Finset.range p, B r ^ 2 := by
          rw [hcard]
          gcongr
          · have : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
            linarith
          · exact Finset.erase_subset _ _
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hB' : ∑ r ∈ Finset.range p, B r ^ 2 = ∑ r ∈ Finset.range p, ‖∑ n ∈ S.filter (fun n => n % p = r), b n‖ ^ 2 := rfl
  rw [← hB'] at hpar
  nlinarith [hcs, hpar, sq_nonneg ‖∑ n ∈ S, b n‖]
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma norm_sum_sq_le_totient_mul_of_avoids_classes (S : Finset ℕ) :
    ∀ d : ℕ, 0 < d → Squarefree d → (∀ p : ℕ, p.Prime → p ∣ d → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) →
    ∀ b : ℕ → ℂ, ‖∑ n ∈ S, b n‖ ^ 2 ≤ (d.totient : ℝ) *
      ∑ a ∈ (Finset.range d).filter d.Coprime, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd hsq hcl b
  by_cases h1 : d = 1
  · subst h1
    have : (Finset.range 1).filter (Nat.Coprime 1) = {0} := by decide
    simp [this]
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨d₁, rfl⟩ := hpd
  rw [mul_comm p d₁] at hsq hcl ⊢
  have hd₁ : 0 < d₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hd)
  have hpd₁ : ¬ p ∣ d₁ := by
    intro h
    have := hsq p (Nat.mul_dvd_mul h (dvd_refl p))
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
  have hlt : d₁ < d₁ * p := lt_mul_of_one_lt_right hd₁ hp.one_lt
  have ih' := ih d₁ (by rw [mul_comm]; exact hlt) hd₁ (hsq.squarefree_of_dvd (dvd_mul_right _ _))
    (fun q hq hqd => hcl q hq (dvd_mul_of_dvd_left hqd _))
  obtain ⟨c, hc⟩ := hcl p hp (dvd_mul_left _ _)
  have hcop : Nat.Coprime d₁ p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd₁))
  rw [sum_coprime_range_mul_eq_sum_sum d₁ p hd₁ hp hpd₁
    (fun m => ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * m / ↑(d₁ * p))‖ ^ 2)
    (fun m => by
      congr 2
      exact Finset.sum_congr rfl fun n _ => by rw [cexp_mul_div_eq_of_mod_right _ (Nat.mul_pos hd₁ hp.pos) n m])]
  simp_rw [cexp_crt_combination_eq_mul d₁ p _ _ _ hd₁ hp.pos, filter_coprime_range_prime_eq_erase_zero p hp, Nat.totient_mul hcop,
    Nat.totient_prime hp]
  have hstep : ∀ a₁ : ℕ, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)‖ ^ 2 ≤ (p - 1 : ℝ) *
      ∑ a₂ ∈ (Finset.range p).erase 0,
        ‖∑ n ∈ S, b n * (cexp (2 * ↑Real.pi * I * n * a₁ / d₁) * cexp (2 * ↑Real.pi * I * n * a₂ / p))‖ ^ 2 := by
    intro a₁
    have := norm_sum_sq_le_pred_mul_of_avoids_class p hp c S (fun n => b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)) hc
    simpa only [mul_assoc] using this
  calc ‖∑ n ∈ S, b n‖ ^ 2 ≤ (d₁.totient : ℝ) * ∑ a₁ ∈ (Finset.range d₁).filter d₁.Coprime,
        ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)‖ ^ 2 := ih' b
    _ ≤ (d₁.totient : ℝ) * ∑ a₁ ∈ (Finset.range d₁).filter d₁.Coprime, (p - 1 : ℝ) *
        ∑ a₂ ∈ (Finset.range p).erase 0,
        ‖∑ n ∈ S, b n * (cexp (2 * ↑Real.pi * I * n * a₁ / d₁) * cexp (2 * ↑Real.pi * I * n * a₂ / p))‖ ^ 2 := by
        gcongr with a₁ _; exact hstep a₁
    _ = _ := by
        rw [← Finset.mul_sum]; push_cast [Nat.cast_sub hp.one_le]; ring
end GlobalTheory
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (M N Q q : ℕ) (S : Finset ℕ), 1 ≤ Q → 1 ≤ q →
    S ⊆ Finset.Ioc M (M + N) →
    (∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) →
    (S.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  intro M N Q q S hQ hq hS hcl
  set D := (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q) with hD
  set Z : ℝ := (S.card : ℝ) with hZ
  have hZ0 : 0 ≤ Z := Nat.cast_nonneg _
  have hRHS : 0 ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by positivity

  have hφq : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log Q ≤ ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n := by
    have h1 := log_add_one_le_harmonic Q
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    calc Real.log Q ≤ Real.log (Q + 1) := Real.log_le_log (by exact_mod_cast hQ) (by linarith)
      _ ≤ _ := by simpa [one_div] using h1
  have hL : (q.totient : ℝ) / q * Real.log Q ≤ ∑ d ∈ D, (1:ℝ) / d.totient := by
    have h2 := sum_inv_le_mul_sum_squarefree_inv_totient Q q hq
    have h3 : (q.totient : ℝ) / q * ((q:ℝ) / q.totient) = 1 := by field_simp
    calc (q.totient : ℝ) / q * Real.log Q ≤ (q.totient : ℝ) / q * ∑ n ∈ Finset.Icc 1 Q, (1:ℝ) / n := by
          gcongr
      _ ≤ (q.totient : ℝ) / q * (((q:ℝ) / q.totient) * ∑ d ∈ D, (1:ℝ) / d.totient) := by gcongr
      _ = _ := by rw [← mul_assoc, h3, one_mul]

  set U : ℕ → ℝ := fun d => ∑ a ∈ (Finset.range d).filter d.Coprime,
    ‖∑ n ∈ S, (1:ℂ) * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2 with hU
  have hmont : ∀ d ∈ D, Z ^ 2 * ((1:ℝ) / d.totient) ≤ U d := by
    intro d hd
    rw [hD, Finset.mem_filter, Finset.mem_Icc] at hd
    have hd0 : 0 < d := hd.1.1
    have h := norm_sum_sq_le_totient_mul_of_avoids_classes S d hd0 hd.2.1 (fun p hp hpd => hcl p hp
      (le_trans (Nat.le_of_dvd hd0 hpd) hd.1.2)
      (fun hpq => (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpd hd.2.2) hpq)) (fun _ => 1)
    have hφd : (0:ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 hd0
    have hsum : ‖∑ n ∈ S, (1:ℂ)‖ ^ 2 = Z ^ 2 := by simp [hZ]
    rw [hsum] at h
    rw [mul_one_div, div_le_iff₀ hφd]
    linarith [h, mul_comm (d.totient : ℝ) (U d)]
  have hls : ∑ d ∈ D, U d ≤ ((Q:ℝ) ^ 2 + 2 * Real.pi * N) * Z := by
    set P := D.sigma (fun d => (Finset.range d).filter d.Coprime) with hP
    set T : Finset ℝ := P.image (fun x => (x.2:ℝ) / x.1) with hT
    have hmemP : ∀ x ∈ P, 0 < x.1 ∧ x.1 ≤ Q ∧ x.2 < x.1 ∧ Nat.Coprime x.2 x.1 := by
      intro x hx
      rw [hP, Finset.mem_sigma, hD, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter,
        Finset.mem_range] at hx
      exact ⟨hx.1.1.1, hx.1.1.2, hx.2.1, hx.2.2.symm⟩
    have hinj : Set.InjOn (fun x : (Σ _ : ℕ, ℕ) => (x.2:ℝ) / x.1) P := by
      intro x hx y hy hxy
      obtain ⟨h1, -, -, h4⟩ := hmemP x hx
      obtain ⟨g1, -, -, g4⟩ := hmemP y hy
      obtain ⟨e1, e2⟩ := _root_.GlobalTheory.MultSieve.reduced_inj h1 g1 h4 g4 hxy
      exact Sigma.ext e1 (heq_of_eq e2)
    have hsumU : ∑ d ∈ D, U d = ∑ x ∈ T, ‖∑ n ∈ Finset.Ioc M (M + N),
        (if n ∈ S then (1:ℂ) else 0) * cexp (2 * ↑Real.pi * I * ↑n * ↑x)‖ ^ 2 := by
      rw [hT, Finset.sum_image hinj, hP, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => ?_
      simp only [ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]
      congr 2
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 1
      push_cast
      ring
    have hspaced : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∀ k : ℤ, 1 / (Q:ℝ) ^ 2 ≤ |x - y - k| := by
      intro x hx y hy hxy k
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨-, u2, u3, -⟩ := hmemP u hu
      obtain ⟨-, v2, v3, -⟩ := hmemP v hv
      exact _root_.GlobalTheory.MultSieve.farey_spaced Q u.1 v.1 u.2 v.2 u2 v2 u3 v3 hxy k
    have hQpos : (0:ℝ) < Q := by exact_mod_cast hQ
    have h := _root_.GlobalTheory.additive_large_sieve M N (fun n => if n ∈ S then (1:ℂ) else 0) T (1 / (Q:ℝ) ^ 2)
      (by positivity) (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by exact_mod_cast hQ)) hspaced
    rw [one_div_one_div, ← hsumU] at h
    have hnorm : ∑ n ∈ Finset.Ioc M (M + N), ‖(if n ∈ S then (1:ℂ) else 0)‖ ^ 2 = Z := by
      have hpt : ∀ n, ‖(if n ∈ S then (1:ℂ) else 0)‖ ^ 2 = if n ∈ S then (1:ℝ) else 0 := by
        intro n; split_ifs <;> simp
      simp_rw [hpt]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]
      simp [hZ]
    rw [hnorm] at h
    exact h
  have hbig : Z ^ 2 * ∑ d ∈ D, (1:ℝ) / d.totient ≤ ((Q:ℝ) ^ 2 + 2 * Real.pi * N) * Z := by
    rw [Finset.mul_sum]
    exact le_trans (Finset.sum_le_sum hmont) hls
  rcases hZ0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact hRHS
  · calc Z * ((q.totient : ℝ) / q * Real.log Q) ≤ Z * ∑ d ∈ D, (1:ℝ) / d.totient :=
          mul_le_mul_of_nonneg_left hL hZ0
      _ ≤ (Q:ℝ) ^ 2 + 2 * Real.pi * N := by
          refine le_of_mul_le_mul_left ?_ hpos
          nlinarith [hbig]
end _root_.GlobalTheory
end GlobalTheory
