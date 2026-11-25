-- Prove2me | solution 1 for GlobalTheory.card_finite_subgroup_GL_int_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:30:23.531608+00:00
-- url     : https://prove2.me/submissions/5b780e7e-137c-47df-af4e-7240d9f63f19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardFiniteSubgroupGLIntDvd
import Theorems.Thm_GlobalTheory_end_eq_one_of_pow_eq_one_of_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
namespace MinkowskiOrder
end MinkowskiOrder
open Matrix in
private theorem prod_pow_sub_pow_pos (q n : ℕ) (hq : 2 ≤ q) :
    0 < ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) := by
  apply Finset.prod_pos
  intro i _
  have := Nat.pow_lt_pow_right hq i.isLt
  omega
open Matrix in
private theorem prod_pow_sub_pow_succ (q n : ℕ) :
    ∏ i : Fin (n + 1), (q ^ (n + 1) - q ^ (i : ℕ)) =
      (q ^ (n + 1) - 1) * (q ^ n * ∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, pow_zero, Fin.val_succ]
  congr 1
  have h : ∀ i : Fin n, q ^ (n + 1) - q ^ ((i : ℕ) + 1) = q * (q ^ n - q ^ (i : ℕ)) := by
    intro i
    rw [pow_succ', pow_succ', Nat.mul_sub]
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
open Matrix in
private theorem padicValNat_le_padicValNat_of_dvd {p a b : ℕ} [Fact p.Prime] (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a ≤ padicValNat p b :=
  (padicValNat_dvd_iff_le hb).mp (pow_padicValNat_dvd.trans h)
open Matrix in
private theorem padicValNat_two_three_pow_sub_one_le (k : ℕ) (hk : 0 < k) :
    padicValNat 2 (3 ^ k - 1) ≤ 3 + padicValNat 2 k := by
  have hlte := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by norm_num)
    (by norm_num) (n := 2 * k) (by omega) (even_two_mul k)
  have h4 : padicValNat 2 (3 + 1) = 2 := by
    rw [show 3 + 1 = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  rw [h4, show 3 - 1 = 2 by norm_num, padicValNat_self, padicValNat.mul (by norm_num) hk.ne',
    padicValNat_self, one_pow] at hlte
  have hne : 3 ^ (2 * k) - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := 2 * k) (by omega) (by norm_num : 1 < 3)
    omega
  have hdvd : 3 ^ k - 1 ∣ 3 ^ (2 * k) - 1 := by
    have h1 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 1 ≤ 3 ^ (2 * k) := Nat.one_le_pow _ _ (by norm_num)
    refine ⟨3 ^ k + 1, ?_⟩
    zify [h1, h2]
    ring
  have := padicValNat_le_padicValNat_of_dvd (p := 2) hne hdvd
  omega
open Matrix in
private theorem padicValNat_two_prod_three_pow_sub_le (n : ℕ) :
    padicValNat 2 (∏ i : Fin n, (3 ^ n - 3 ^ (i : ℕ))) ≤ 3 * n + padicValNat 2 n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hqn : 0 < 3 ^ (n + 1) - 1 := by
      have := Nat.one_lt_pow (n := n + 1) (by omega) (by norm_num : 1 < 3)
      omega
    have hpow : padicValNat 2 (3 ^ n) = 0 :=
      padicValNat.eq_zero_of_not_dvd fun h => by
        have := Nat.prime_two.dvd_of_dvd_pow h
        omega
    have hq0 : 3 ^ n ≠ 0 := by positivity
    have hP := (prod_pow_sub_pow_pos 3 n (by norm_num)).ne'
    rw [prod_pow_sub_pow_succ, padicValNat.mul hqn.ne' (Nat.mul_ne_zero hq0 hP),
      padicValNat.mul hq0 hP, hpow, zero_add, Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    have := padicValNat_two_three_pow_sub_one_le (n + 1) (by omega)
    omega
open Matrix in
private theorem padicValNat_two_prod_three_pow_sub_le_eight_pow_factorial (n : ℕ) :
    padicValNat 2 (∏ i : Fin n, (3 ^ n - 3 ^ (i : ℕ))) ≤
      padicValNat 2 (8 ^ n * (2 * n).factorial) := by
  rw [padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
    show 8 ^ n = 2 ^ (3 * n) by rw [pow_mul]; norm_num, padicValNat.prime_pow]
  have h1 := padicValNat_two_prod_three_pow_sub_le n
  have h2 := padicValNat_le_padicValNat_of_dvd (p := 2) (Nat.factorial_ne_zero (2 * n))
    (Nat.factorial_dvd_factorial (by omega : n ≤ 2 * n))
  omega
open Matrix in
private theorem exists_prime_gt_order_padicValNat_pow_sub_one (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ q, q.Prime ∧ p < q ∧ (∀ k, 0 < k → p ∣ q ^ k - 1 → (p - 1) ∣ k) ∧
      (∀ j, 0 < j → padicValNat p (q ^ ((p - 1) * j) - 1) = 1 + padicValNat p j) := by
  have hp' := hp.out
  have hp1 : 0 < p - 1 := by have := hp'.two_le; omega
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp'.ne_zero⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp' hp2 2
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod (p ^ 2))ˣ)
  have hord : orderOf u = p * (p - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp' (by norm_num), pow_one]
  obtain ⟨q, hqgt, hq, hqu⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit p
  have hq1 : 1 < q := hq.one_lt
  have hpq : ¬ p ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hp' hq).mp h
    omega
  have key : ∀ m, p ^ 2 ∣ q ^ m - 1 ↔ p * (p - 1) ∣ m := by
    intro m
    rw [← hord, orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff,
      Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), sub_eq_zero, Nat.cast_pow, hqu, Nat.cast_one,
      ← Units.val_pow_eq_pow_val, Units.val_eq_one]
  have hodd : Odd p := hp'.odd_of_ne_two hp2
  refine ⟨q, hq, hqgt, ?_, ?_⟩
  · intro k hk hdvd
    have hqk : 1 < q ^ k := Nat.one_lt_pow hk.ne' hq1
    have hnd : ¬ p ∣ q ^ k := fun h => hpq (hp'.dvd_of_dvd_pow h)
    have hlte := padicValNat.pow_sub_pow (p := p) (y := 1) hodd hqk (by simpa using hdvd) hnd
      (n := p) hp'.ne_zero
    rw [one_pow, ← pow_mul, padicValNat_self] at hlte
    have h1 : 1 ≤ padicValNat p (q ^ k - 1) := one_le_padicValNat_of_dvd (by omega) hdvd
    have hne : q ^ (k * p) - 1 ≠ 0 := by
      have := Nat.one_lt_pow (Nat.mul_ne_zero hk.ne' hp'.ne_zero) hq1
      omega
    have h2 : p ^ 2 ∣ q ^ (k * p) - 1 := (padicValNat_dvd_iff_le hne).mpr (by omega)
    rw [key, mul_comm k p] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hp'.pos h2
  · intro j hj
    have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp').mpr (by omega)
    have hferm : p ∣ q ^ (p - 1) - 1 := by
      have := Nat.ModEq.pow_totient hcop
      rw [Nat.totient_prime hp'] at this
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp this.symm
    have hqp1 : 1 < q ^ (p - 1) := Nat.one_lt_pow hp1.ne' hq1
    have hne : q ^ (p - 1) - 1 ≠ 0 := by omega
    have hv1 : padicValNat p (q ^ (p - 1) - 1) = 1 := by
      have h1 : 1 ≤ padicValNat p (q ^ (p - 1) - 1) := one_le_padicValNat_of_dvd hne hferm
      by_contra hne1
      have h2 : p ^ 2 ∣ q ^ (p - 1) - 1 := (padicValNat_dvd_iff_le hne).mpr (by omega)
      rw [key] at h2
      have := Nat.le_of_dvd hp1 h2
      have : p - 1 < p * (p - 1) := by
        have := hp'.two_le
        nlinarith
      omega
    have hnd : ¬ p ∣ q ^ (p - 1) := fun h => hpq (hp'.dvd_of_dvd_pow h)
    have hlte := padicValNat.pow_sub_pow (p := p) (y := 1) hodd hqp1 (by simpa using hferm) hnd
      (n := j) hj.ne'
    rw [one_pow, ← pow_mul, hv1] at hlte
    exact hlte
open Matrix in
private theorem padicValNat_prod_pow_sub_pow_eq_padicValNat_factorial (p q : ℕ) [hp : Fact p.Prime] (hq : 2 ≤ q)
    (hqp : ¬ p ∣ q) (hdiv : ∀ k, 0 < k → p ∣ q ^ k - 1 → (p - 1) ∣ k)
    (hval : ∀ j, 0 < j → padicValNat p (q ^ ((p - 1) * j) - 1) = 1 + padicValNat p j) (n : ℕ) :
    padicValNat p (∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) =
      padicValNat p (p * (n / (p - 1))).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hqn : 0 < q ^ (n + 1) - 1 := by
      have := Nat.one_lt_pow (n := n + 1) (by omega) (by omega : 1 < q)
      omega
    have hpow : padicValNat p (q ^ n) = 0 :=
      padicValNat.eq_zero_of_not_dvd fun h => hqp (hp.out.dvd_of_dvd_pow h)
    have hq0 : q ^ n ≠ 0 := by positivity
    have hP := (prod_pow_sub_pow_pos q n hq).ne'
    rw [prod_pow_sub_pow_succ, padicValNat.mul hqn.ne' (Nat.mul_ne_zero hq0 hP),
      padicValNat.mul hq0 hP, hpow, zero_add, ih, Nat.succ_div]
    have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
    by_cases hd : (p - 1) ∣ n + 1
    · obtain ⟨j, hj⟩ := hd
      have hj0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · simp [h] at hj
        · exact h
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hdiv' : (n + 1) / (p - 1) = m + 1 := by rw [hj, Nat.mul_div_cancel_left _ hp1]
      have hn : n / (p - 1) = m := by
        rw [Nat.succ_div, if_pos ⟨_, hj⟩] at hdiv'
        omega
      rw [if_pos ⟨_, hj⟩, hn, hj, hval _ hj0, padicValNat_factorial_mul, padicValNat_factorial_mul,
        Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
      ring
    · rw [if_neg hd, add_zero,
        padicValNat.eq_zero_of_not_dvd (fun h => hd (hdiv _ (by omega) h)), zero_add]
open Matrix in
private theorem padicValNat_factorial_le_padicValNat_eight_pow_mul_factorial (p n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * (n / (p - 1))).factorial ≤ padicValNat p (8 ^ n * (2 * n).factorial) := by
  have h2 := hp.out.two_le
  have hle : p * (n / (p - 1)) ≤ 2 * n := by
    have := Nat.mul_div_le n (p - 1)
    have hp' : p ≤ 2 * (p - 1) := by omega
    calc p * (n / (p - 1)) ≤ 2 * (p - 1) * (n / (p - 1)) := Nat.mul_le_mul_right _ hp'
      _ = 2 * ((p - 1) * (n / (p - 1))) := by ring
      _ ≤ 2 * n := by omega
  exact padicValNat_le_padicValNat_of_dvd (by positivity)
    ((Nat.factorial_dvd_factorial hle).trans (Dvd.intro_left _ rfl))
open Matrix in
private theorem eq_one_of_pow_eq_one_of_congr_one_mod {n : ℕ} (g : GL (Fin n) ℤ) (k : ℕ) (hk : 0 < k)
    (hgk : g ^ k = 1) (q : ℕ) (hq : 3 ≤ q)
    (hcong : ∀ i j, (q : ℤ) ∣ (g : Matrix (Fin n) (Fin n) ℤ) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) :
    g = 1 := by
  choose C hC using hcong
  have hg : (g : Matrix (Fin n) (Fin n) ℤ) = 1 + (q : ℤ) • Matrix.of C := by
    ext i j
    have := hC i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linarith
  have key := _root_.GlobalTheory.end_eq_one_of_pow_eq_one_of_congr (Fin n → ℤ)
    (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) ℤ)) k q hk ?_ hq ?_
  · have h1 : (g : Matrix (Fin n) (Fin n) ℤ) = 1 := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [key, map_one]
    exact Units.ext h1
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, hgk, Units.val_one, map_one]
  · intro y
    refine ⟨Matrix.of C *ᵥ y, ?_⟩
    rw [Matrix.toLinAlgEquiv'_apply, hg, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, ← Nat.cast_smul_eq_nsmul ℤ]
open Matrix in
private theorem card_finite_subgroup_dvd_prod_pow_sub_pow {n : ℕ} (G : Subgroup (GL (Fin n) ℤ)) [Finite G]
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) :
    Nat.card G ∣ ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) := by
  have hcard := Matrix.card_GL_field (𝔽 := ZMod q) n
  rw [ZMod.card] at hcard
  rw [← hcard]
  refine Subgroup.card_dvd_of_injective
    ((Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod q))).comp G.subtype) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk, hgk⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
  apply Subtype.ext
  refine eq_one_of_pow_eq_one_of_congr_one_mod (g : GL (Fin n) ℤ) k hk ?_ q hq ?_
  · rw [← Subgroup.coe_pow, hgk]; rfl
  · intro i j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrArg (fun h : GL (Fin n) (ZMod q) => (h : Matrix _ _ (ZMod q)) i j) hg
    by_cases hij : i = j
    · subst hij; simpa [sub_eq_zero, Matrix.one_apply, Matrix.GeneralLinearGroup.map] using this
    · simpa [sub_eq_zero, Matrix.one_apply, hij, Matrix.GeneralLinearGroup.map] using this
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (n : ℕ) (G : Subgroup (GL (Fin n) ℤ)), Finite G → Nat.card G ∣ 8 ^ n * (2 * n).factorial := by
  intro n G hG
  have hB : 8 ^ n * (2 * n).factorial ≠ 0 := by positivity
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rw [← Nat.factorization_prime_le_iff_dvd hG0 hB]
  intro p hp
  haveI := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  obtain ⟨q, hq, hq3, hbound⟩ : ∃ q, q.Prime ∧ 3 ≤ q ∧
      padicValNat p (∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) ≤
        padicValNat p (8 ^ n * (2 * n).factorial) := by
    by_cases hp2 : p = 2
    · subst hp2
      exact ⟨3, Nat.prime_three, le_rfl, padicValNat_two_prod_three_pow_sub_le_eight_pow_factorial n⟩
    · obtain ⟨q, hq, hpq, hdiv, hval⟩ := exists_prime_gt_order_padicValNat_pow_sub_one p hp2
      have h2 := hp.two_le
      refine ⟨q, hq, by omega, ?_⟩
      have hnd : ¬ p ∣ q := fun h => by
        have := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
        omega
      rw [padicValNat_prod_pow_sub_pow_eq_padicValNat_factorial p q hq.two_le hnd hdiv hval n]
      exact padicValNat_factorial_le_padicValNat_eight_pow_mul_factorial p n
  haveI := Fact.mk hq
  haveI := hG
  exact (padicValNat_le_padicValNat_of_dvd (prod_pow_sub_pow_pos q n hq.two_le).ne'
    (card_finite_subgroup_dvd_prod_pow_sub_pow G q hq3)).trans hbound
end _root_.GlobalTheory
end GlobalTheory
