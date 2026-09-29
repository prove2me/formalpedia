-- Prove2me | solution 1 for HeckeEis.exists_binaryForm_eq_mul_of_forall_eval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8fc24207-75e8-53ef-af7b-7fd64a92d0a0

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero

set_option autoImplicit false

namespace ATHRVan

open MvPolynomial HeckeEis Finset

section Monomials

variable (K : Type*) [Field K]

noncomputable def e (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

@[scoped simp] theorem e_zero (i j : ℕ) : e i j 0 = i := by simp [e]

@[scoped simp] theorem e_one (i j : ℕ) : e i j 1 = j := by simp [e]

theorem e_eq_iff {i j i' j' : ℕ} : e i j = e i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 0) h,
      by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem eq_e (d : Fin 2 →₀ ℕ) : d = e (d 0) (d 1) := by
  ext k
  fin_cases k <;> simp

theorem degree_e (i j : ℕ) : Finsupp.degree (e i j) = i + j := by
  rw [e, map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem monomial_e (i j : ℕ) (c : K) :
    (monomial (e i j) c : MvPolynomial (Fin 2) K) = C c * X 0 ^ i * X 1 ^ j := by
  rw [e, mul_assoc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, C_mul_monomial, one_mul, mul_one]

theorem isHomogeneous_monomial_e (i j : ℕ) (c : K) :
    ((monomial (e i j) c : MvPolynomial (Fin 2) K)).IsHomogeneous (i + j) :=
  isHomogeneous_monomial _ (degree_e i j)

theorem deg_two {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n) {d : Fin 2 →₀ ℕ}
    (hd : coeff d F ≠ 0) : d 0 + d 1 = n := by
  have hdeg := hF hd
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at hdeg
  simpa only [Pi.one_apply, smul_eq_mul, mul_one, Fin.sum_univ_two] using hdeg

theorem eq_sum_monomial {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n) :
    F = ∑ i ∈ range (n + 1), monomial (e i (n - i)) (coeff (e i (n - i)) F) := by
  classical
  ext d
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hd : coeff d F = 0
  · rw [hd]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · rw [← h] at hd
      exact hd
    · rfl
  · have hdeg := deg_two K hF hd
    rw [Finset.sum_eq_single (d 0)]
    · have h : e (d 0) (n - d 0) = d := by
        conv_rhs => rw [eq_e d]
        rw [e_eq_iff]
        exact ⟨rfl, by omega⟩
      rw [if_pos h, h]
    · intro i _ hne
      rw [if_neg]
      intro h
      apply hne
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simpa using this
    · intro h
      exfalso
      simp only [mem_range] at h
      omega

theorem coeff_monomial_e_e (i j i' j' : ℕ) (c : K) :
    coeff (e i' j') (monomial (e i j) c : MvPolynomial (Fin 2) K) = if i = i' ∧ j = j' then c else 0 := by
  classical
  rw [coeff_monomial]
  simp only [e_eq_iff]

end Monomials

section Eval

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]

noncomputable def ev (F : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) : K :=
  eval (fun i => ZMod.castHom (dvd_refl p) K (v i)) F

theorem ev_add (F G : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (F + G) v = ev p K F v + ev p K G v := by
  simp [ev]

theorem ev_mul (F G : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (F * G) v = ev p K F v * ev p K G v := by
  simp [ev]

theorem ev_sum {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (∑ i ∈ s, F i) v = ∑ i ∈ s, ev p K (F i) v := by
  simp [ev, map_sum]

theorem ev_monomial (i j : ℕ) (c : K) (v : Fin 2 → ZMod p) :
    ev p K (monomial (e i j) c) v =
      c * (ZMod.castHom (dvd_refl p) K (v 0)) ^ i * (ZMod.castHom (dvd_refl p) K (v 1)) ^ j := by
  rw [monomial_e]
  simp [ev]

theorem castHom_pow_card (x : ZMod p) :
    (ZMod.castHom (dvd_refl p) K x) ^ p = ZMod.castHom (dvd_refl p) K x := by
  rw [← map_pow, ZMod.pow_card]

noncomputable def theta : MvPolynomial (Fin 2) K := X 0 ^ p * X 1 - X 0 * X 1 ^ p

theorem theta_eq : theta p K = monomial (e p 1) 1 - monomial (e 1 p) 1 := by
  rw [theta, monomial_e, monomial_e]
  simp

theorem isHomogeneous_theta : (theta p K).IsHomogeneous (p + 1) := by
  rw [theta_eq]
  refine (isHomogeneous_monomial_e K p 1 1).sub ?_
  rw [add_comm]
  exact isHomogeneous_monomial_e K 1 p 1

theorem ev_theta (v : Fin 2 → ZMod p) : ev p K (theta p K) v = 0 := by
  simp only [theta, ev, map_sub, map_mul, map_pow, eval_X, castHom_pow_card]
  ring

theorem coeffs_eq_zero_of_ev {n : ℕ} (c : ℕ → K)
    (hsupp : ∀ i ∈ range (n + 1), c i ≠ 0 → i = n ∨ i < p)
    (hev : ∀ x y : ZMod p, ∑ i ∈ range (n + 1),
      c i * (ZMod.castHom (dvd_refl p) K x) ^ i * (ZMod.castHom (dvd_refl p) K y) ^ (n - i) = 0) :
    ∀ i ∈ range (n + 1), c i = 0 := by
  set ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K with hι

  have hcn : c n = 0 := by
    have h := hev 1 0
    rw [Finset.sum_eq_single n] at h
    · simpa using h
    · intro i hi hne
      have : n - i ≠ 0 := by
        simp only [mem_range] at hi
        omega
      simp [map_zero, zero_pow this]
    · simp

  set N := min n p with hN
  set q : Polynomial K := ∑ i : Fin N, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) with hq
  have hqdeg : q.degree < N := Polynomial.degree_sum_fin_lt _
  have hvanish : ∀ i ∈ range (n + 1), N ≤ i → c i = 0 := by
    intro i hi hNi
    by_cases hin : i = n
    · rw [hin]
      exact hcn
    by_contra hne
    rcases hsupp i hi hne with h | h
    · exact hin h
    · simp only [mem_range] at hi
      omega
  have hqeval : ∀ x : ZMod p, q.eval (ι x) = 0 := by
    intro x
    have h := hev x 1
    simp only [map_one, one_pow, mul_one] at h
    rw [hq, Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [Fin.sum_univ_eq_sum_range (fun i => c i * ι x ^ i) N]
    have h2 : ∑ i ∈ range N, c i * ι x ^ i = ∑ i ∈ range (n + 1), c i * ι x ^ i := by
      refine Finset.sum_subset (fun i hi => ?_) (fun i hi hi' => ?_)
      · simp only [mem_range] at hi ⊢
        omega
      · rw [hvanish i hi (by simpa using hi'), zero_mul]
    rw [h2]
    exact h
  have hq0 : q = 0 := by
    by_cases hqz : q = 0
    · exact hqz
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q ι.injective hqeval ?_
    rw [ZMod.card]
    have h1 : q.natDegree < N := (Polynomial.natDegree_lt_iff_degree_lt hqz).mpr hqdeg
    omega
  intro i hi
  by_cases hiN : N ≤ i
  · exact hvanish i hi hiN
  · have hcoeff : q.coeff i = c i := by
      rw [hq, Polynomial.finset_sum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin N)]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        apply hb
        exact Fin.ext h.symm
      · simp
    rw [← hcoeff, hq0, Polynomial.coeff_zero]

theorem monomial_sub_monomial_step {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) :
    (monomial (e (j + (p - 1)) m) (1 : K) : MvPolynomial (Fin 2) K) - monomial (e j (m + (p - 1))) 1
      = theta p K * monomial (e (j - 1) (m - 1)) 1 := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hp0 : p ≠ 0 := hp.out.ne_zero
  rw [monomial_e, monomial_e, monomial_e, theta, ← pow_sub_one_mul hp0 (X 0 : MvPolynomial (Fin 2) K),
    ← pow_sub_one_mul hp0 (X 1 : MvPolynomial (Fin 2) K)]
  simp only [map_one, one_mul, Nat.add_sub_cancel]
  ring

theorem monomial_sub_monomial_red {j : ℕ} (hj : 1 ≤ j) (k : ℕ) :
    ∀ {m : ℕ}, 1 ≤ m → ∃ H : MvPolynomial (Fin 2) K, H.IsHomogeneous (j + m + k * (p - 1) - (p + 1)) ∧
      (monomial (e (j + k * (p - 1)) m) (1 : K) : MvPolynomial (Fin 2) K)
        - monomial (e j (m + k * (p - 1))) 1 = theta p K * H := by
  induction k with
  | zero =>
    intro m _
    exact ⟨0, isHomogeneous_zero _ _ _, by simp⟩
  | succ k ih =>
    intro m hm
    have hp2 := hp.out.two_le
    obtain ⟨H, hH, hHeq⟩ := ih (m := m + (p - 1)) (by omega)
    refine ⟨monomial (e (j + k * (p - 1) - 1) (m - 1)) 1 + H, ?_, ?_⟩
    · refine IsHomogeneous.add ?_ ?_
      · have h : j + k * (p - 1) - 1 + (m - 1) = j + m + (k + 1) * (p - 1) - (p + 1) := by
          have : (k + 1) * (p - 1) = k * (p - 1) + (p - 1) := by ring
          omega
        rw [← h]
        exact isHomogeneous_monomial_e K _ _ 1
      · have h : j + (m + (p - 1)) + k * (p - 1) - (p + 1) = j + m + (k + 1) * (p - 1) - (p + 1) := by
          have : (k + 1) * (p - 1) = k * (p - 1) + (p - 1) := by ring
          omega
        rwa [← h]
    · have h1 : j + (k + 1) * (p - 1) = (j + k * (p - 1)) + (p - 1) := by ring
      have h2 : m + (k + 1) * (p - 1) = (m + (p - 1)) + k * (p - 1) := by ring
      rw [h1, h2, mul_add, ← hHeq, ← monomial_sub_monomial_step p K (j := j + k * (p - 1)) (by omega) hm]
      ring

def rd (i : ℕ) : ℕ := 1 + (i - 1) % (p - 1)

theorem one_le_rd (i : ℕ) : 1 ≤ rd p i := Nat.le_add_right _ _

theorem rd_le (i : ℕ) : rd p i ≤ p - 1 := by
  have h1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have := Nat.mod_lt (i - 1) h1
  unfold rd
  omega

theorem rd_le_self {i : ℕ} (hi : 1 ≤ i) : rd p i ≤ i := by
  have := Nat.mod_le (i - 1) (p - 1)
  unfold rd
  omega

theorem rd_spec {i : ℕ} (hi : 1 ≤ i) : i = rd p i + (i - 1) / (p - 1) * (p - 1) := by
  have := Nat.div_add_mod' (i - 1) (p - 1)
  unfold rd
  omega

theorem exists_eq_theta_mul {n : ℕ} {F : MvPolynomial (Fin 2) K} (hF : F.IsHomogeneous n)
    (hvan : ∀ v, ev p K F v = 0) :
    ∃ H : MvPolynomial (Fin 2) K, H.IsHomogeneous (n - (p + 1)) ∧ F = theta p K * H := by
  classical
  set ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K with hι

  set g : ℕ → ℕ := fun i => if i = 0 ∨ i = n then i else rd p i with hg
  have hg_le : ∀ i, i ≤ n → g i ≤ i := by
    intro i hi
    simp only [hg]
    split_ifs with h
    · exact le_rfl
    · push_neg at h
      exact rd_le_self p (by omega)
  have key : ∀ i : ℕ, ∃ H : MvPolynomial (Fin 2) K, i ≤ n → H.IsHomogeneous (n - (p + 1)) ∧
      (monomial (e i (n - i)) (1 : K) : MvPolynomial (Fin 2) K) - monomial (e (g i) (n - g i)) 1
        = theta p K * H := by
    intro i
    by_cases h : i = 0 ∨ i = n
    · refine ⟨0, fun _ => ⟨isHomogeneous_zero _ _ _, ?_⟩⟩
      simp [hg, h]
    · push_neg at h
      by_cases hin : i ≤ n
      · have hi1 : 1 ≤ i := by omega
        obtain ⟨H, hH, hHeq⟩ := monomial_sub_monomial_red p K (j := rd p i) (one_le_rd p i)
          ((i - 1) / (p - 1)) (m := n - i) (by omega)
        refine ⟨H, fun _ => ⟨?_, ?_⟩⟩
        · have := rd_spec p hi1
          have h' : rd p i + (n - i) + (i - 1) / (p - 1) * (p - 1) - (p + 1) = n - (p + 1) := by omega
          rwa [h'] at hH
        · have hgi : g i = rd p i := by simp [hg, h.1, h.2]
          have h1 : e i (n - i) = e (rd p i + (i - 1) / (p - 1) * (p - 1)) (n - i) := by
            rw [← rd_spec p hi1]
          have h2 : e (g i) (n - g i) = e (rd p i) ((n - i) + (i - 1) / (p - 1) * (p - 1)) := by
            rw [hgi, e_eq_iff]
            have := rd_spec p hi1
            exact ⟨rfl, by omega⟩
          rw [h1, h2, hHeq]
      · exact ⟨0, fun h' => absurd h' hin⟩
  choose H hH using key
  set c : ℕ → K := fun i => coeff (e i (n - i)) F with hc

  set Fr : MvPolynomial (Fin 2) K := ∑ i ∈ range (n + 1), monomial (e (g i) (n - g i)) (c i) with hFr
  have hFdecomp : F = Fr + theta p K * ∑ i ∈ range (n + 1), C (c i) * H i := by
    conv_lhs => rw [eq_sum_monomial K hF]
    rw [hFr, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    have h := (hH i hin).2
    have e1 : (monomial (e i (n - i)) (c i) : MvPolynomial (Fin 2) K) = C (c i) * monomial (e i (n - i)) 1 := by
      rw [C_mul_monomial, mul_one]
    have e2 : (monomial (e (g i) (n - g i)) (c i) : MvPolynomial (Fin 2) K)
        = C (c i) * monomial (e (g i) (n - g i)) 1 := by
      rw [C_mul_monomial, mul_one]
    rw [e1, e2]
    linear_combination (C (c i)) * h

  have hFrvan : ∀ v, ev p K Fr v = 0 := by
    intro v
    have h := hvan v
    rw [hFdecomp, ev_add, ev_mul, ev_theta, zero_mul, add_zero] at h
    exact h

  have hmaps : ∀ i ∈ range (n + 1), g i ∈ range (n + 1) := by
    intro i hi
    simp only [mem_range, Nat.lt_succ_iff] at hi ⊢
    exact (hg_le i hi).trans hi
  set d : ℕ → K := fun j => ∑ i ∈ (range (n + 1)).filter (fun i => g i = j), c i with hd
  have hFr' : Fr = ∑ j ∈ range (n + 1), monomial (e j (n - j)) (d j) := by
    rw [hFr, ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hd, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  have hdsupp : ∀ j ∈ range (n + 1), d j ≠ 0 → j = n ∨ j < p := by
    intro j _ hj
    obtain ⟨i, hi, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
    rw [Finset.mem_filter] at hi
    obtain ⟨hi, hgi⟩ := hi
    rw [← hgi, hg]
    dsimp only
    split_ifs with h
    · rcases h with h | h
      · right; rw [h]; exact hp.out.pos
      · left; exact h
    · right
      have := rd_le p i
      have := hp.out.one_le
      omega
  have hdev : ∀ x y : ZMod p, ∑ j ∈ range (n + 1), d j * ι x ^ j * ι y ^ (n - j) = 0 := by
    intro x y
    have h := hFrvan ![x, y]
    rw [hFr', ev_sum] at h
    simpa only [ev_monomial, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  have hd0 := coeffs_eq_zero_of_ev p K d hdsupp hdev
  have hFr0 : Fr = 0 := by
    rw [hFr']
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hd0 j hj, map_zero]
  refine ⟨∑ i ∈ range (n + 1), C (c i) * H i, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hin : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    exact ((hH i hin).1).C_mul _
  · rw [hFdecomp, hFr0, zero_add]

end Eval

end ATHRVan
p2m_reactivate "P2MW.S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero.ATHRVan"

open MvPolynomial in
theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (n : ℕ) (F : MvPolynomial (Fin 2) K)
    (hF : F ∈ HeckeEis.BinaryForm K n)
    (hvan : ∀ v : Fin 2 → ZMod p,
      MvPolynomial.eval (fun i => ZMod.castHom (dvd_refl p) K (v i)) F = 0) :
    ∃ H : MvPolynomial (Fin 2) K, H ∈ HeckeEis.BinaryForm K (n - (p + 1)) ∧
      F = (X 0 ^ p * X 1 - X 0 * X 1 ^ p) * H := by
  obtain ⟨H, hH, hFH⟩ := ATHRVan.exists_eq_theta_mul p K
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hF) hvan
  exact ⟨H, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hH, hFH⟩

end S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero
end P2MW
export P2MW.S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero (solution)
