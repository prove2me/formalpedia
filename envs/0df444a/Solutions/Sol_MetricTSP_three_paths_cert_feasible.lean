-- Prove2me | solution 1 for MetricTSP.three_paths_cert_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T23:10:16.969333+00:00
-- url     : https://prove2.me/submissions/4af46d38-2d87-4fa3-b709-97cefdc23fd1

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths

set_option maxHeartbeats 1000000

namespace MetricTSP

open Finset

variable {k p q m : ℕ}

/-! ### Coordinate toolkit for the three-paths instance -/

lemma nat_dist_def (a b : ℕ) : Nat.dist a b = (a - b) + (b - a) := rfl

lemma tpSpec' (hk : 1 ≤ k) (v : Fin (3*k+2)) :
    (tpPath k v = 3 ∧ (tpPos k v = 0 ∨ tpPos k v = k+1))
    ∨ (tpPath k v < 3 ∧ 1 ≤ tpPos k v ∧ tpPos k v ≤ k) := by
  have hv := v.isLt
  unfold tpPath tpPos
  by_cases h : v.val = 0 ∨ v.val = 3*k+1
  · rw [if_pos h]
    left
    rcases h with h | h <;> rw [h] <;> simp <;> omega
  · rw [if_neg h]
    right
    push_neg at h
    have hmod : (v.val - 1) % k < k := Nat.mod_lt _ (by omega)
    have hdivlt : (v.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    rw [if_neg h.1, if_neg h.2]
    omega

/-- Encoding of an internal city from its coordinates. -/
def tpEnc (k p i : ℕ) : Fin (3*k+2) :=
  ⟨(1 + p*k + (i-1)) % (3*k+2), Nat.mod_lt _ (by omega)⟩

lemma tpEnc_spec (hk : 1 ≤ k) {p i : ℕ} (hp : p < 3) (hi1 : 1 ≤ i) (hik : i ≤ k) :
    (tpEnc k p i).val = 1 + p*k + (i-1)
      ∧ tpPath k (tpEnc k p i) = p ∧ tpPos k (tpEnc k p i) = i := by
  have hpk : p * k ≤ 2 * k := Nat.mul_le_mul_right k (by omega)
  have hlt : 1 + p*k + (i-1) < 3*k+2 := by omega
  have hval : (tpEnc k p i).val = 1 + p*k + (i-1) := by
    unfold tpEnc
    exact Nat.mod_eq_of_lt hlt
  refine ⟨hval, ?_, ?_⟩
  · unfold tpPath
    rw [hval]
    have h0 : ¬(1 + p*k + (i-1) = 0 ∨ 1 + p*k + (i-1) = 3*k+1) := by omega
    rw [if_neg h0]
    have : 1 + p*k + (i-1) - 1 = p*k + (i-1) := by omega
    rw [this, Nat.mul_comm p k, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    omega
  · unfold tpPos
    rw [hval]
    rw [if_neg (by omega), if_neg (by omega)]
    have : 1 + p*k + (i-1) - 1 = p*k + (i-1) := by omega
    rw [this, Nat.mul_comm p k, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The hub `s`. -/
def tpS (k : ℕ) : Fin (3*k+2) := ⟨0, by omega⟩

/-- The hub `t`. -/
def tpT (k : ℕ) : Fin (3*k+2) := ⟨3*k+1, by omega⟩

lemma tpS_spec : tpPath k (tpS k) = 3 ∧ tpPos k (tpS k) = 0 := by
  have h : (tpS k).val = 0 := rfl
  constructor
  · unfold tpPath
    rw [h, if_pos (Or.inl rfl)]
  · unfold tpPos
    rw [h, if_pos rfl]

lemma tpT_spec : tpPath k (tpT k) = 3 ∧ tpPos k (tpT k) = k+1 := by
  have h : (tpT k).val = 3*k+1 := rfl
  constructor
  · unfold tpPath
    rw [h, if_pos (Or.inr rfl)]
  · unfold tpPos
    rw [h, if_neg (by omega), if_pos rfl]

/-- Every city is `s`, `t`, or an encoded internal city. -/
lemma tpCases (hk : 1 ≤ k) (v : Fin (3*k+2)) :
    v = tpS k ∨ v = tpT k ∨
    ∃ p i, p < 3 ∧ 1 ≤ i ∧ i ≤ k ∧ v = tpEnc k p i := by
  have hv := v.isLt
  by_cases h0 : v.val = 0
  · left
    exact Fin.ext h0
  by_cases hT : v.val = 3*k+1
  · right; left
    exact Fin.ext hT
  right; right
  have hmod : (v.val - 1) % k < k := Nat.mod_lt _ (by omega)
  have hdivlt : (v.val - 1) / k < 3 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  refine ⟨(v.val - 1)/k, (v.val - 1) % k + 1, hdivlt, by omega, by omega, ?_⟩
  apply Fin.ext
  have hspec := tpEnc_spec hk hdivlt (i := (v.val - 1) % k + 1) (by omega) (by omega)
  rw [hspec.1]
  have hdm := Nat.div_add_mod (v.val - 1) k
  have hcomm : (v.val - 1)/k * k = k * ((v.val - 1)/k) := Nat.mul_comm _ _
  omega

/-- The coordinates (path, position) determine the city. -/
lemma tpCoord_inj (hk : 1 ≤ k) (u v : Fin (3*k+2))
    (hp : tpPath k u = tpPath k v) (hq : tpPos k u = tpPos k v) : u = v := by
  rcases tpCases hk u with rfl | rfl | ⟨p, i, hpp, hi1, hik, rfl⟩ <;>
    rcases tpCases hk v with rfl | rfl | ⟨q, j, hqq, hj1, hjk, rfl⟩
  · rfl
  · exfalso
    rw [tpS_spec.2, tpT_spec.2] at hq
    omega
  · exfalso
    rw [tpS_spec.1, (tpEnc_spec hk hqq hj1 hjk).2.1] at hp
    omega
  · exfalso
    rw [tpT_spec.2, tpS_spec.2] at hq
    omega
  · rfl
  · exfalso
    rw [tpT_spec.1, (tpEnc_spec hk hqq hj1 hjk).2.1] at hp
    omega
  · exfalso
    rw [tpS_spec.1, (tpEnc_spec hk hpp hi1 hik).2.1] at hp
    omega
  · exfalso
    rw [tpT_spec.1, (tpEnc_spec hk hpp hi1 hik).2.1] at hp
    omega
  · rw [(tpEnc_spec hk hpp hi1 hik).2.1, (tpEnc_spec hk hqq hj1 hjk).2.1] at hp
    rw [(tpEnc_spec hk hpp hi1 hik).2.2, (tpEnc_spec hk hqq hj1 hjk).2.2] at hq
    subst hp
    subst hq
    rfl

/-! ### Evaluations of the certificate -/

/-- Value of the certificate as a function of raw coordinates. -/
noncomputable def certVal (K : ℕ) (Pu pu Pv pv : ℕ) : ℝ :=
  if Pu = Pv ∧ Pu ≠ 3 ∧ Nat.dist pu pv = 1 then 1
  else if ((Pu = 3 ∧ Pv ≠ 3) ∨ (Pu ≠ 3 ∧ Pv = 3)) ∧ Nat.dist pu pv = 1 then 2/3
  else if Pu ≠ 3 ∧ Pv ≠ 3 ∧ Pu ≠ Pv ∧ pu = pv ∧ (pu = 1 ∨ pu = K) then 1/6
  else 0

lemma tpCert_coords (u v : Fin (3*k+2)) :
    tpCert k u v = certVal k (tpPath k u) (tpPos k u) (tpPath k v) (tpPos k v) := rfl

lemma certVal_one {K Pu pu Pv pv : ℕ} (h1 : Pu = Pv) (h2 : Pu ≠ 3)
    (h3 : Nat.dist pu pv = 1) : certVal K Pu pu Pv pv = 1 := by
  unfold certVal
  rw [if_pos ⟨h1, h2, h3⟩]

lemma certVal_hub {K Pu pu Pv pv : ℕ}
    (h1 : (Pu = 3 ∧ Pv ≠ 3) ∨ (Pu ≠ 3 ∧ Pv = 3)) (h3 : Nat.dist pu pv = 1) :
    certVal K Pu pu Pv pv = 2/3 := by
  unfold certVal
  rw [if_neg (by omega), if_pos ⟨h1, h3⟩]

lemma certVal_tri {K Pu pu Pv pv : ℕ} (h1 : Pu ≠ 3) (h2 : Pv ≠ 3) (h3 : Pu ≠ Pv)
    (h4 : pu = pv) (h5 : pu = 1 ∨ pu = K) : certVal K Pu pu Pv pv = 1/6 := by
  unfold certVal
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2, h3, h4, h5⟩]

lemma certVal_zero {K Pu pu Pv pv : ℕ}
    (h1 : ¬(Pu = Pv ∧ Pu ≠ 3 ∧ Nat.dist pu pv = 1))
    (h2 : ¬(((Pu = 3 ∧ Pv ≠ 3) ∨ (Pu ≠ 3 ∧ Pv = 3)) ∧ Nat.dist pu pv = 1))
    (h3 : ¬(Pu ≠ 3 ∧ Pv ≠ 3 ∧ Pu ≠ Pv ∧ pu = pv ∧ (pu = 1 ∨ pu = K))) :
    certVal K Pu pu Pv pv = 0 := by
  unfold certVal
  rw [if_neg h1, if_neg h2, if_neg h3]

/-- Equality of encoded cities from equality of coordinates, packaged. -/
lemma tpEnc_eq (hk : 1 ≤ k) {q j p i : ℕ} (hq : q < 3) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hp : p < 3) (hi1 : 1 ≤ i) (hik : i ≤ k)
    (hqp : q = p) (hji : j = i) : tpEnc k q j = tpEnc k p i := by
  subst hqp; subst hji; rfl

/-! ### The six feasibility conjuncts -/

lemma tpCert_symm' (hk : 1 ≤ k) (u v : Fin (3*k+2)) : tpCert k u v = tpCert k v u := by
  rw [tpCert_coords, tpCert_coords]
  unfold certVal
  have hd : Nat.dist (tpPos k u) (tpPos k v) = Nat.dist (tpPos k v) (tpPos k u) :=
    Nat.dist_comm _ _
  split_ifs with a1 a2 a3 a4 a5 a6 <;> first | rfl | (exfalso; omega)

lemma tpCert_diag' (v : Fin (3*k+2)) : tpCert k v v = 0 := by
  rw [tpCert_coords]
  apply certVal_zero
  · simp [Nat.dist]
  · simp [Nat.dist]
  · intro h
    exact h.2.2.1 rfl

lemma tpCert_nonneg' (u v : Fin (3*k+2)) : 0 ≤ tpCert k u v := by
  rw [tpCert_coords]
  unfold certVal
  split_ifs <;> norm_num

lemma tpCert_le_one' (u v : Fin (3*k+2)) : tpCert k u v ≤ 1 := by
  rw [tpCert_coords]
  unfold certVal
  split_ifs <;> norm_num

/-- Degree at the hub `s`. -/
lemma deg_s (hk : 2 ≤ k) : ∑ u, tpCert k (tpS k) u = 2 := by
  classical
  have hk1 : 1 ≤ k := by omega
  set a0 := tpEnc k 0 1 with ha0
  set a1 := tpEnc k 1 1 with ha1
  set a2 := tpEnc k 2 1 with ha2
  have hs0 := tpEnc_spec hk1 (p := 0) (i := 1) (by omega) (by omega) (by omega)
  have hs1 := tpEnc_spec hk1 (p := 1) (i := 1) (by omega) (by omega) (by omega)
  have hs2 := tpEnc_spec hk1 (p := 2) (i := 1) (by omega) (by omega) (by omega)
  have h01 : a0 ≠ a1 := by
    intro h
    have := congrArg (tpPath k) h
    rw [hs0.2.1, hs1.2.1] at this
    omega
  have h02 : a0 ≠ a2 := by
    intro h
    have := congrArg (tpPath k) h
    rw [hs0.2.1, hs2.2.1] at this
    omega
  have h12 : a1 ≠ a2 := by
    intro h
    have := congrArg (tpPath k) h
    rw [hs1.2.1, hs2.2.1] at this
    omega
  have hzero : ∀ u ∈ (univ : Finset (Fin (3*k+2))),
      u ∉ ({a0, a1, a2} : Finset (Fin (3*k+2))) → tpCert k (tpS k) u = 0 := by
    intro u _ hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    push_neg at hu
    obtain ⟨hu0, hu1, hu2⟩ := hu
    rw [tpCert_coords]
    rcases tpCases hk1 u with rfl | rfl | ⟨q, j, hq, hj1, hjk, rfl⟩
    · rw [tpS_spec.1, tpS_spec.2]
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
    · rw [tpS_spec.1, tpS_spec.2, tpT_spec.1, tpT_spec.2]
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
    · have hspec := tpEnc_spec hk1 hq hj1 hjk
      rw [tpS_spec.1, tpS_spec.2, hspec.2.1, hspec.2.2]
      have hj : j ≠ 1 := by
        intro hj1'
        subst hj1'
        rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
        · exact hu0 rfl
        · exact hu1 rfl
        · exact hu2 rfl
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
  rw [← Finset.sum_subset (Finset.subset_univ {a0, a1, a2}) hzero]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨h01, h02⟩), Finset.sum_insert (by simp only [Finset.mem_singleton]; exact h12),
    Finset.sum_singleton]
  have hev : ∀ (p : ℕ) (hp : p < 3), tpCert k (tpS k) (tpEnc k p 1) = 2/3 := by
    intro p hp
    have hspec := tpEnc_spec hk1 hp (i := 1) (by omega) (by omega)
    rw [tpCert_coords, tpS_spec.1, tpS_spec.2, hspec.2.1, hspec.2.2]
    apply certVal_hub
    · left
      exact ⟨rfl, by omega⟩
    · rfl
  rw [ha0, ha1, ha2, hev 0 (by omega), hev 1 (by omega), hev 2 (by omega)]
  norm_num


/-- Degree at the hub `t`. -/
lemma deg_t (hk : 2 ≤ k) : ∑ u, tpCert k (tpT k) u = 2 := by
  classical
  have hk1 : 1 ≤ k := by omega
  set a0 := tpEnc k 0 k with ha0
  set a1 := tpEnc k 1 k with ha1
  set a2 := tpEnc k 2 k with ha2
  have hs0 := tpEnc_spec hk1 (p := 0) (i := k) (by omega) (by omega) (by omega)
  have hs1 := tpEnc_spec hk1 (p := 1) (i := k) (by omega) (by omega) (by omega)
  have hs2 := tpEnc_spec hk1 (p := 2) (i := k) (by omega) (by omega) (by omega)
  have h01 : a0 ≠ a1 := by
    intro h
    have := congrArg (tpPath k) h
    rw [hs0.2.1, hs1.2.1] at this
    omega
  have h02 : a0 ≠ a2 := by
    intro h
    have := congrArg (tpPath k) h
    rw [hs0.2.1, hs2.2.1] at this
    omega
  have h12 : a1 ≠ a2 := by
    intro h
    have := congrArg (tpPath k) h
    rw [hs1.2.1, hs2.2.1] at this
    omega
  have hzero : ∀ u ∈ (univ : Finset (Fin (3*k+2))),
      u ∉ ({a0, a1, a2} : Finset (Fin (3*k+2))) → tpCert k (tpT k) u = 0 := by
    intro u _ hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    push_neg at hu
    obtain ⟨hu0, hu1, hu2⟩ := hu
    rw [tpCert_coords]
    rcases tpCases hk1 u with rfl | rfl | ⟨q, j, hq, hj1, hjk, rfl⟩
    · rw [tpT_spec.1, tpT_spec.2, tpS_spec.1, tpS_spec.2]
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
    · rw [tpT_spec.1, tpT_spec.2]
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
    · have hspec := tpEnc_spec hk1 hq hj1 hjk
      rw [tpT_spec.1, tpT_spec.2, hspec.2.1, hspec.2.2]
      have hj : j ≠ k := by
        intro hjk'
        subst hjk'
        rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
        · exact hu0 rfl
        · exact hu1 rfl
        · exact hu2 rfl
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
  rw [← Finset.sum_subset (Finset.subset_univ {a0, a1, a2}) hzero]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨h01, h02⟩), Finset.sum_insert (by simp only [Finset.mem_singleton]; exact h12),
    Finset.sum_singleton]
  have hev : ∀ (p : ℕ), p < 3 → tpCert k (tpT k) (tpEnc k p k) = 2/3 := by
    intro p hp
    have hspec := tpEnc_spec hk1 hp (i := k) (by omega) (by omega)
    rw [tpCert_coords, tpT_spec.1, tpT_spec.2, hspec.2.1, hspec.2.2]
    apply certVal_hub
    · left
      exact ⟨rfl, by omega⟩
    · rw [nat_dist_def]
      omega
  rw [ha0, ha1, ha2, hev 0 (by omega), hev 1 (by omega), hev 2 (by omega)]
  norm_num

/-- Degree at a middle internal city. -/
lemma deg_mid (hk : 2 ≤ k) {p i : ℕ} (hp : p < 3) (hi1 : 1 < i) (hik : i < k) :
    ∑ u, tpCert k (tpEnc k p i) u = 2 := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hv := tpEnc_spec hk1 hp (i := i) (by omega) (by omega)
  set a := tpEnc k p (i-1) with ha
  set b := tpEnc k p (i+1) with hb
  have hsa := tpEnc_spec hk1 hp (i := i-1) (by omega) (by omega)
  have hsb := tpEnc_spec hk1 hp (i := i+1) (by omega) (by omega)
  have hab : a ≠ b := by
    intro h
    have := congrArg (tpPos k) h
    rw [hsa.2.2, hsb.2.2] at this
    omega
  have hzero : ∀ u ∈ (univ : Finset (Fin (3*k+2))),
      u ∉ ({a, b} : Finset (Fin (3*k+2))) → tpCert k (tpEnc k p i) u = 0 := by
    intro u _ hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    push_neg at hu
    obtain ⟨hua, hub⟩ := hu
    rw [tpCert_coords]
    rcases tpCases hk1 u with rfl | rfl | ⟨q, j, hq, hj1, hjk, rfl⟩
    · rw [hv.2.1, hv.2.2, tpS_spec.1, tpS_spec.2]
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
    · rw [hv.2.1, hv.2.2, tpT_spec.1, tpT_spec.2]
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
    · have hspec := tpEnc_spec hk1 hq hj1 hjk
      rw [hv.2.1, hv.2.2, hspec.2.1, hspec.2.2]
      have hne1 : ¬(q = p ∧ j = i-1) := by
        rintro ⟨rfl, rfl⟩
        exact hua rfl
      have hne2 : ¬(q = p ∧ j = i+1) := by
        rintro ⟨rfl, rfl⟩
        exact hub rfl
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
  rw [← Finset.sum_subset (Finset.subset_univ {a, b}) hzero]
  rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hab), Finset.sum_singleton]
  have hev1 : tpCert k (tpEnc k p i) a = 1 := by
    rw [tpCert_coords, hv.2.1, hv.2.2, hsa.2.1, hsa.2.2]
    apply certVal_one rfl (by omega)
    rw [nat_dist_def]
    omega
  have hev2 : tpCert k (tpEnc k p i) b = 1 := by
    rw [tpCert_coords, hv.2.1, hv.2.2, hsb.2.1, hsb.2.2]
    apply certVal_one rfl (by omega)
    rw [nat_dist_def]
    omega
  rw [hev1, hev2]
  norm_num

/-- Degree at an internal city at position 1. -/
lemma deg_first (hk : 2 ≤ k) {p : ℕ} (hp : p < 3) :
    ∑ u, tpCert k (tpEnc k p 1) u = 2 := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hv := tpEnc_spec hk1 hp (i := 1) (by omega) (by omega)
  set b := tpEnc k p 2 with hb
  set c1 := tpEnc k ((p+1) % 3) 1 with hc1
  set c2 := tpEnc k ((p+2) % 3) 1 with hc2
  have hsb := tpEnc_spec hk1 hp (i := 2) (by omega) hk
  have hsc1 := tpEnc_spec hk1 (p := (p+1) % 3) (i := 1) (by omega) (by omega) (by omega)
  have hsc2 := tpEnc_spec hk1 (p := (p+2) % 3) (i := 1) (by omega) (by omega) (by omega)
  have hd1 : tpS k ≠ b := by
    intro h
    have := congrArg (tpPath k) h
    rw [tpS_spec.1, hsb.2.1] at this
    omega
  have hd2 : tpS k ≠ c1 := by
    intro h
    have := congrArg (tpPath k) h
    rw [tpS_spec.1, hsc1.2.1] at this
    omega
  have hd3 : tpS k ≠ c2 := by
    intro h
    have := congrArg (tpPath k) h
    rw [tpS_spec.1, hsc2.2.1] at this
    omega
  have hd4 : b ≠ c1 := by
    intro h
    have h1 := congrArg (tpPath k) h
    rw [hsb.2.1, hsc1.2.1] at h1
    omega
  have hd5 : b ≠ c2 := by
    intro h
    have h1 := congrArg (tpPath k) h
    rw [hsb.2.1, hsc2.2.1] at h1
    omega
  have hd6 : c1 ≠ c2 := by
    intro h
    have h1 := congrArg (tpPath k) h
    rw [hsc1.2.1, hsc2.2.1] at h1
    omega
  have hzero : ∀ u ∈ (univ : Finset (Fin (3*k+2))),
      u ∉ ({tpS k, b, c1, c2} : Finset (Fin (3*k+2))) → tpCert k (tpEnc k p 1) u = 0 := by
    intro u _ hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    push_neg at hu
    obtain ⟨hus, hub, huc1, huc2⟩ := hu
    clear hd1 hd2 hd3 hd4 hd5 hd6
    rw [tpCert_coords]
    rcases tpCases hk1 u with rfl | rfl | ⟨q, j, hq, hj1, hjk, rfl⟩
    · exact absurd rfl hus
    · rw [hv.2.1, hv.2.2, tpT_spec.1, tpT_spec.2]
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
    · have hspec := tpEnc_spec hk1 hq hj1 hjk
      rw [hv.2.1, hv.2.2, hspec.2.1, hspec.2.2]
      have hne1 : ¬(q = p ∧ j = 2) := by
        rintro ⟨rfl, rfl⟩
        exact hub rfl
      have hne2 : ¬(q = (p+1) % 3 ∧ j = 1) := by
        rintro ⟨rfl, rfl⟩
        exact huc1 rfl
      have hne3 : ¬(q = (p+2) % 3 ∧ j = 1) := by
        rintro ⟨rfl, rfl⟩
        exact huc2 rfl
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
  rw [← Finset.sum_subset (Finset.subset_univ {tpS k, b, c1, c2}) hzero]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hd1, hd2, hd3⟩), Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hd4, hd5⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hd6), Finset.sum_singleton]
  have hevS : tpCert k (tpEnc k p 1) (tpS k) = 2/3 := by
    rw [tpCert_coords, hv.2.1, hv.2.2, tpS_spec.1, tpS_spec.2]
    apply certVal_hub
    · right
      exact ⟨by omega, rfl⟩
    · rfl
  have hevB : tpCert k (tpEnc k p 1) b = 1 := by
    rw [tpCert_coords, hv.2.1, hv.2.2, hsb.2.1, hsb.2.2]
    apply certVal_one rfl (by omega)
    rfl
  have hevC1 : tpCert k (tpEnc k p 1) c1 = 1/6 := by
    rw [tpCert_coords, hv.2.1, hv.2.2, hsc1.2.1, hsc1.2.2]
    exact certVal_tri (by omega) (by omega) (by omega) rfl (Or.inl rfl)
  have hevC2 : tpCert k (tpEnc k p 1) c2 = 1/6 := by
    rw [tpCert_coords, hv.2.1, hv.2.2, hsc2.2.1, hsc2.2.2]
    exact certVal_tri (by omega) (by omega) (by omega) rfl (Or.inl rfl)
  rw [hevS, hevB, hevC1, hevC2]
  norm_num

/-- Degree at an internal city at position k. -/
lemma deg_last (hk : 2 ≤ k) {p : ℕ} (hp : p < 3) :
    ∑ u, tpCert k (tpEnc k p k) u = 2 := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hv := tpEnc_spec hk1 hp (i := k) (by omega) (by omega)
  set b := tpEnc k p (k-1) with hb
  set c1 := tpEnc k ((p+1) % 3) k with hc1
  set c2 := tpEnc k ((p+2) % 3) k with hc2
  have hsb := tpEnc_spec hk1 hp (i := k-1) (by omega) (by omega)
  have hsc1 := tpEnc_spec hk1 (p := (p+1) % 3) (i := k) (by omega) (by omega) (by omega)
  have hsc2 := tpEnc_spec hk1 (p := (p+2) % 3) (i := k) (by omega) (by omega) (by omega)
  have hd1 : tpT k ≠ b := by
    intro h
    have := congrArg (tpPath k) h
    rw [tpT_spec.1, hsb.2.1] at this
    omega
  have hd2 : tpT k ≠ c1 := by
    intro h
    have := congrArg (tpPath k) h
    rw [tpT_spec.1, hsc1.2.1] at this
    omega
  have hd3 : tpT k ≠ c2 := by
    intro h
    have := congrArg (tpPath k) h
    rw [tpT_spec.1, hsc2.2.1] at this
    omega
  have hd4 : b ≠ c1 := by
    intro h
    have h1 := congrArg (tpPath k) h
    rw [hsb.2.1, hsc1.2.1] at h1
    omega
  have hd5 : b ≠ c2 := by
    intro h
    have h1 := congrArg (tpPath k) h
    rw [hsb.2.1, hsc2.2.1] at h1
    omega
  have hd6 : c1 ≠ c2 := by
    intro h
    have h1 := congrArg (tpPath k) h
    rw [hsc1.2.1, hsc2.2.1] at h1
    omega
  have hzero : ∀ u ∈ (univ : Finset (Fin (3*k+2))),
      u ∉ ({tpT k, b, c1, c2} : Finset (Fin (3*k+2))) → tpCert k (tpEnc k p k) u = 0 := by
    intro u _ hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    push_neg at hu
    obtain ⟨hut, hub, huc1, huc2⟩ := hu
    clear hd1 hd2 hd3 hd4 hd5 hd6
    rw [tpCert_coords]
    rcases tpCases hk1 u with rfl | rfl | ⟨q, j, hq, hj1, hjk, rfl⟩
    · rw [hv.2.1, hv.2.2, tpS_spec.1, tpS_spec.2]
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
    · exact absurd rfl hut
    · have hspec := tpEnc_spec hk1 hq hj1 hjk
      rw [hv.2.1, hv.2.2, hspec.2.1, hspec.2.2]
      have hne1 : ¬(q = p ∧ j = k-1) := by
        rintro ⟨rfl, rfl⟩
        exact hub rfl
      have hne2 : ¬(q = (p+1) % 3 ∧ j = k) := by
        rintro ⟨rfl, rfl⟩
        exact huc1 rfl
      have hne3 : ¬(q = (p+2) % 3 ∧ j = k) := by
        rintro ⟨rfl, rfl⟩
        exact huc2 rfl
      apply certVal_zero
      · rw [nat_dist_def]; omega
      · rw [nat_dist_def]; omega
      · omega
  rw [← Finset.sum_subset (Finset.subset_univ {tpT k, b, c1, c2}) hzero]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hd1, hd2, hd3⟩), Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hd4, hd5⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hd6), Finset.sum_singleton]
  have hevT : tpCert k (tpEnc k p k) (tpT k) = 2/3 := by
    rw [tpCert_coords, hv.2.1, hv.2.2, tpT_spec.1, tpT_spec.2]
    apply certVal_hub
    · right
      exact ⟨by omega, rfl⟩
    · rw [nat_dist_def]
      omega
  have hevB : tpCert k (tpEnc k p k) b = 1 := by
    rw [tpCert_coords, hv.2.1, hv.2.2, hsb.2.1, hsb.2.2]
    apply certVal_one rfl (by omega)
    rw [nat_dist_def]
    omega
  have hevC1 : tpCert k (tpEnc k p k) c1 = 1/6 := by
    rw [tpCert_coords, hv.2.1, hv.2.2, hsc1.2.1, hsc1.2.2]
    exact certVal_tri (by omega) (by omega) (by omega) rfl (Or.inr rfl)
  have hevC2 : tpCert k (tpEnc k p k) c2 = 1/6 := by
    rw [tpCert_coords, hv.2.1, hv.2.2, hsc2.2.1, hsc2.2.2]
    exact certVal_tri (by omega) (by omega) (by omega) rfl (Or.inr rfl)
  rw [hevT, hevB, hevC1, hevC2]
  norm_num

/-- The degree constraint of the certificate. -/
lemma tpCert_degree (hk : 2 ≤ k) (v : Fin (3*k+2)) : ∑ u, tpCert k v u = 2 := by
  have hk1 : 1 ≤ k := by omega
  rcases tpCases hk1 v with rfl | rfl | ⟨p, i, hp, hi1, hik, rfl⟩
  · exact deg_s hk
  · exact deg_t hk
  · rcases (by omega : i = 1 ∨ i = k ∨ (1 < i ∧ i < k)) with rfl | rfl | ⟨h1, h2⟩
    · exact deg_first hk hp
    · exact deg_last hk hp
    · exact deg_mid hk hp h1 h2


/-! ### Cut constraints -/

/-- The `m`-th vertex along path `p`, hubs included. -/
def tpSeq (k p m : ℕ) : Fin (3*k+2) :=
  if m = 0 then tpS k else if m = k+1 then tpT k else tpEnc k p m

lemma tpSeq_zero : tpSeq k p 0 = tpS k := rfl

lemma tpSeq_top : tpSeq k p (k+1) = tpT k := by
  unfold tpSeq
  rw [if_neg (by omega), if_pos rfl]

lemma tpSeq_mid (h1 : 1 ≤ m) (h2 : m ≤ k) : tpSeq k p m = tpEnc k p m := by
  unfold tpSeq
  rw [if_neg (by omega), if_neg (by omega)]

lemma tpSeq_coords (hk : 1 ≤ k) (hp : p < 3) (hm : m ≤ k+1) :
    (tpPath k (tpSeq k p m) = 3 ∨ tpPath k (tpSeq k p m) = p) ∧ tpPos k (tpSeq k p m) = m := by
  rcases (by omega : m = 0 ∨ m = k+1 ∨ (1 ≤ m ∧ m ≤ k)) with rfl | rfl | ⟨h1, h2⟩
  · rw [tpSeq_zero]
    exact ⟨Or.inl tpS_spec.1, tpS_spec.2⟩
  · rw [tpSeq_top]
    exact ⟨Or.inl tpT_spec.1, tpT_spec.2⟩
  · rw [tpSeq_mid h1 h2]
    have := tpEnc_spec hk hp h1 h2
    exact ⟨Or.inr this.2.1, this.2.2⟩

/-- When two `tpSeq` cities coincide, their step indices agree. -/
lemma tpSeq_inj_step (hk1 : 1 ≤ k) {p q m m2 : ℕ} (hp : p < 3) (hq : q < 3)
    (hm : m ≤ k+1) (hm2 : m2 ≤ k+1) (h : tpSeq k p m = tpSeq k q m2) :
    m = m2 :=
  ((tpSeq_coords hk1 hp hm).2).symm.trans
    ((congrArg (tpPos k) h).trans (tpSeq_coords hk1 hq hm2).2)

/-- When two `tpSeq` cities coincide, the paths agree or the step is a hub step. -/
lemma tpSeq_inj3 (hk1 : 1 ≤ k) {p q m m2 : ℕ} (hp : p < 3) (hq : q < 3)
    (hm : m ≤ k+1) (hm2 : m2 ≤ k+1) (h : tpSeq k p m = tpSeq k q m2) :
    m = m2 ∧ (p = q ∨ m = 0 ∨ m = k+1) := by
  have hmm : m = m2 := tpSeq_inj_step hk1 hp hq hm hm2 h
  by_cases hmid : 1 ≤ m ∧ m ≤ k
  · have hb1 : 1 ≤ m2 := by omega
    have hb2 : m2 ≤ k := by omega
    have c1 : p = tpPath k (tpSeq k p m) :=
      ((congrArg (tpPath k) (tpSeq_mid hmid.1 hmid.2)).trans
        (tpEnc_spec hk1 hp hmid.1 hmid.2).2.1).symm
    have c2 : tpPath k (tpSeq k q m2) = q :=
      (congrArg (tpPath k) (tpSeq_mid hb1 hb2)).trans
        (tpEnc_spec hk1 hq hb1 hb2).2.1
    exact ⟨hmm, Or.inl ((c1.trans (congrArg (tpPath k) h)).trans c2)⟩
  · exact ⟨hmm, Or.inr (by omega)⟩

/-- Consecutive cities along a path have certificate weight at least `2/3`,
in both orientations. -/
lemma tpSeq_weight (hk : 2 ≤ k) (hp : p < 3) (hm : m ≤ k) :
    2/3 ≤ tpCert k (tpSeq k p m) (tpSeq k p (m+1)) ∧
    2/3 ≤ tpCert k (tpSeq k p (m+1)) (tpSeq k p m) := by
  have hk1 : 1 ≤ k := by omega
  have hval : tpCert k (tpSeq k p m) (tpSeq k p (m+1)) = 1 ∨
      tpCert k (tpSeq k p m) (tpSeq k p (m+1)) = 2/3 := by
    rcases (by omega : m = 0 ∨ m = k ∨ (1 ≤ m ∧ m + 1 ≤ k)) with rfl | rfl | ⟨h1, h2⟩
    · right
      rw [tpSeq_zero, tpSeq_mid (by omega) (by omega), tpCert_coords, tpS_spec.1,
        tpS_spec.2, (tpEnc_spec hk1 hp (by omega) (by omega)).2.1,
        (tpEnc_spec hk1 hp (by omega) (by omega)).2.2]
      apply certVal_hub
      · left
        exact ⟨rfl, by omega⟩
      · rfl
    · right
      rw [tpSeq_top, tpSeq_mid (by omega) (by omega), tpCert_coords,
        (tpEnc_spec hk1 hp (by omega) (by omega)).2.1,
        (tpEnc_spec hk1 hp (by omega) (by omega)).2.2, tpT_spec.1, tpT_spec.2]
      apply certVal_hub
      · right
        exact ⟨by omega, rfl⟩
      · rw [nat_dist_def]; omega
    · left
      rw [tpSeq_mid h1 (by omega), tpSeq_mid (by omega) h2, tpCert_coords,
        (tpEnc_spec hk1 hp h1 (by omega)).2.1, (tpEnc_spec hk1 hp h1 (by omega)).2.2,
        (tpEnc_spec hk1 hp (by omega) h2).2.1, (tpEnc_spec hk1 hp (by omega) h2).2.2]
      apply certVal_one rfl (by omega)
      rw [nat_dist_def]; omega
  constructor
  · rcases hval with h | h <;> rw [h] <;> norm_num
  · rw [← tpCert_symm' hk1]
    rcases hval with h | h <;> rw [h] <;> norm_num

/-- Discrete intermediate value: a predicate true at `a` and false at `b > a` has an
exit crossing. -/
lemma exists_cross_up (g : ℕ → Prop) [DecidablePred g] (a b : ℕ) (hab : a ≤ b)
    (hga : g a) (hgb : ¬g b) : ∃ m, a ≤ m ∧ m < b ∧ g m ∧ ¬g (m+1) := by
  by_contra hcon
  push_neg at hcon
  apply hgb
  have key : ∀ j, a ≤ j → j ≤ b → g j := by
    intro j hj1 hj2
    induction j with
    | zero =>
        have : a = 0 := by omega
        rw [← this]
        exact hga
    | succ i ih =>
        by_cases hia : a ≤ i
        · have hgi : g i := ih hia (by omega)
          by_cases hib : i < b
          · exact hcon i hia hib hgi
          · omega
        · have : a = i + 1 := by omega
          rw [← this]
          exact hga
  exact key b hab le_rfl

lemma exists_cross_down (g : ℕ → Prop) [DecidablePred g] (a b : ℕ) (hab : a ≤ b)
    (hga : ¬g a) (hgb : g b) : ∃ m, a ≤ m ∧ m < b ∧ ¬g m ∧ g (m+1) := by
  obtain ⟨m, h1, h2, h3, h4⟩ := exists_cross_up (fun j => ¬g j) a b hab hga
    (by simpa using hgb)
  exact ⟨m, h1, h2, h3, by simpa using h4⟩

/-- Lower-bound a cut sum by a collection of crossing pairs. -/
lemma cut_lower (hk : 1 ≤ k) (S : Finset (Fin (3*k+2)))
    (P : Finset (Fin (3*k+2) × Fin (3*k+2))) (hP : P ⊆ S ×ˢ Sᶜ) (r : ℝ)
    (hr : r ≤ ∑ pq ∈ P, tpCert k pq.1 pq.2) :
    r ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, tpCert k u v := by
  calc r ≤ ∑ pq ∈ P, tpCert k pq.1 pq.2 := hr
    _ ≤ ∑ pq ∈ S ×ˢ Sᶜ, tpCert k pq.1 pq.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hP
        intro pq _ _
        exact tpCert_nonneg' _ _
    _ = ∑ u ∈ S, ∑ v ∈ Sᶜ, tpCert k u v := by
        rw [Finset.sum_product']

/-- The cut sum is symmetric under complementation. -/
lemma cut_swap (hk : 1 ≤ k) (S : Finset (Fin (3*k+2))) :
    ∑ u ∈ S, ∑ v ∈ Sᶜ, tpCert k u v = ∑ u ∈ Sᶜ, ∑ v ∈ (Sᶜ)ᶜ, tpCert k u v := by
  rw [compl_compl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  exact tpCert_symm' hk u v


/-- Weight of an internal consecutive pair, forward orientation. -/
lemma tpSeq_unit_fwd (hk : 2 ≤ k) {p m : ℕ} (hp : p < 3) (h1 : 1 ≤ m) (h2 : m + 1 ≤ k) :
    tpCert k (tpSeq k p m) (tpSeq k p (m+1)) = 1 := by
  have hk1 : 1 ≤ k := by omega
  have hm1 : 1 ≤ m + 1 := by omega
  have hmk : m ≤ k := by omega
  have hp3 : p ≠ 3 := by omega
  have hd : Nat.dist m (m+1) = 1 := by rw [nat_dist_def]; omega
  rw [tpSeq_mid h1 hmk, tpSeq_mid hm1 h2, tpCert_coords,
    (tpEnc_spec hk1 hp h1 hmk).2.1, (tpEnc_spec hk1 hp h1 hmk).2.2,
    (tpEnc_spec hk1 hp hm1 h2).2.1, (tpEnc_spec hk1 hp hm1 h2).2.2]
  exact certVal_one rfl hp3 hd

/-- Weight of an internal consecutive pair, backward orientation. -/
lemma tpSeq_unit_bwd (hk : 2 ≤ k) {p m : ℕ} (hp : p < 3) (h1 : 1 ≤ m) (h2 : m + 1 ≤ k) :
    tpCert k (tpSeq k p (m+1)) (tpSeq k p m) = 1 := by
  have hk1 : 1 ≤ k := by omega
  rw [← tpCert_symm' hk1]
  exact tpSeq_unit_fwd hk hp h1 h2

/-- Weight of a near-hub triangle pair. -/
lemma tri_weight (hk : 2 ≤ k) {p q i : ℕ} (hp : p < 3) (hq : q < 3) (hpq : p ≠ q)
    (hio : i = 1 ∨ i = k) :
    tpCert k (tpSeq k p i) (tpSeq k q i) = 1/6 := by
  have hk1 : 1 ≤ k := by omega
  have hi1 : 1 ≤ i := by omega
  have hik : i ≤ k := by omega
  rw [tpSeq_mid hi1 hik, tpSeq_mid hi1 hik, tpCert_coords,
    (tpEnc_spec hk1 hp hi1 hik).2.1, (tpEnc_spec hk1 hp hi1 hik).2.2,
    (tpEnc_spec hk1 hq hi1 hik).2.1, (tpEnc_spec hk1 hq hi1 hik).2.2]
  exact certVal_tri (by omega) (by omega) hpq rfl hio

/-- The cut bound for one deficient path, the other two paths full. -/
lemma one_deficient (hk : 2 ≤ k) (S : Finset (Fin (3*k+2)))
    (hs : tpS k ∈ S) (ht : tpT k ∈ S) {p : ℕ} (hp : p < 3)
    {j m1 m2 : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (h11 : m1 < j) (h21 : j ≤ m2) (h22 : m2 ≤ k)
    (hu1 : tpSeq k p m1 ∈ S) (hu2 : tpSeq k p (m1+1) ∉ S)
    (hd1 : tpSeq k p m2 ∉ S) (hd2 : tpSeq k p (m2+1) ∈ S)
    (hnd : ∀ q j', q < 3 → q ≠ p → 1 ≤ j' → j' ≤ k → tpEnc k q j' ∈ S) :
    2 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, tpCert k u v := by
  classical
  have hk1 : 1 ≤ k := by omega
  set q1 := (p+1) % 3 with hq1
  set q2 := (p+2) % 3 with hq2
  have hq1lt : q1 < 3 := by omega
  have hq2lt : q2 < 3 := by omega
  have hq1p : q1 ≠ p := by omega
  have hq2p : q2 ≠ p := by omega
  have hq12 : q1 ≠ q2 := by omega
  set up : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k p m1, tpSeq k p (m1+1)) with hup
  set dn : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k p (m2+1), tpSeq k p m2) with hdn
  have hupdn : up ≠ dn := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [hup, hdn] at h1 h2
    replace h1 := tpSeq_inj3 hk1 hp hp (by omega) (by omega) h1
    omega
  have hup_mem : up ∈ S ×ˢ Sᶜ := by
    rw [Finset.mem_product]
    exact ⟨hu1, Finset.mem_compl.mpr hu2⟩
  have hdn_mem : dn ∈ S ×ˢ Sᶜ := by
    rw [Finset.mem_product]
    exact ⟨hd2, Finset.mem_compl.mpr hd1⟩
  by_cases hm1z : 1 ≤ m1
  · by_cases hm2k : m2 + 1 ≤ k
    · -- both crossings internal: 1 + 1
      apply cut_lower hk1 S {up, dn} ?_ 2 ?_
      · intro pq hpq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpq
        rcases hpq with rfl | rfl
        · exact hup_mem
        · exact hdn_mem
      · rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hupdn), Finset.sum_singleton]
        have w1 := tpSeq_unit_fwd hk hp hm1z (by omega)
        have w2 := tpSeq_unit_bwd hk hp (by omega) hm2k
        rw [hup, hdn]
        rw [w1, w2]
        norm_num
    · -- m2 = k: down-crossing at the t hub, use the two t-side triangles
      have hm2 : k = m2 := by omega
      subst hm2
      set tr1 : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k q1 k, tpSeq k p k) with htr1
      set tr2 : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k q2 k, tpSeq k p k) with htr2
      have htr1_mem : tr1 ∈ S ×ˢ Sᶜ := by
        rw [Finset.mem_product]
        constructor
        · show tpSeq k q1 k ∈ S
          rw [tpSeq_mid (by omega) (by omega)]
          exact hnd q1 k hq1lt hq1p (by omega) (by omega)
        · show tpSeq k p k ∈ Sᶜ
          exact Finset.mem_compl.mpr hd1
      have htr2_mem : tr2 ∈ S ×ˢ Sᶜ := by
        rw [Finset.mem_product]
        constructor
        · show tpSeq k q2 k ∈ S
          rw [tpSeq_mid (by omega) (by omega)]
          exact hnd q2 k hq2lt hq2p (by omega) (by omega)
        · show tpSeq k p k ∈ Sᶜ
          exact Finset.mem_compl.mpr hd1
      have ne_updn : up ≠ dn := hupdn
      have ne_uptr1 : up ≠ tr1 := by
        intro h
        have h1 := congrArg Prod.fst h
        simp only [hup, htr1] at h1
        replace h1 := tpSeq_inj3 hk1 hp hq1lt (by omega) (by omega) h1
        omega
      have ne_uptr2 : up ≠ tr2 := by
        intro h
        have h1 := congrArg Prod.fst h
        simp only [hup, htr2] at h1
        replace h1 := tpSeq_inj3 hk1 hp hq2lt (by omega) (by omega) h1
        omega
      have ne_dntr1 : dn ≠ tr1 := by
        intro h
        have h1 := congrArg Prod.fst h
        simp only [hdn, htr1] at h1
        replace h1 := tpSeq_inj3 hk1 hp hq1lt (by omega) (by omega) h1
        omega
      have ne_dntr2 : dn ≠ tr2 := by
        intro h
        have h1 := congrArg Prod.fst h
        simp only [hdn, htr2] at h1
        replace h1 := tpSeq_inj3 hk1 hp hq2lt (by omega) (by omega) h1
        omega
      have ne_tr12 : tr1 ≠ tr2 := by
        intro h
        have h1 := congrArg Prod.fst h
        simp only [htr1, htr2] at h1
        replace h1 := tpSeq_inj3 hk1 hq1lt hq2lt (by omega) (by omega) h1
        omega
      apply cut_lower hk1 S {up, dn, tr1, tr2} ?_ 2 ?_
      · intro pq hpq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpq
        rcases hpq with rfl | rfl | rfl | rfl
        · exact hup_mem
        · exact hdn_mem
        · exact htr1_mem
        · exact htr2_mem
      · rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨ne_updn, ne_uptr1, ne_uptr2⟩),
          Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨ne_dntr1, ne_dntr2⟩),
          Finset.sum_insert (by simp only [Finset.mem_singleton]; exact ne_tr12), Finset.sum_singleton]
        have w1 := tpSeq_unit_fwd hk hp hm1z (by omega)
        have w2 := (tpSeq_weight hk hp (m := k) (by omega)).2
        have w3 := tri_weight hk hq1lt hp hq1p (Or.inr rfl)
        have w4 := tri_weight hk hq2lt hp hq2p (Or.inr rfl)
        rw [hup, hdn, htr1, htr2, w1, w3, w4]
        have : tpCert k (tpSeq k p (k+1)) (tpSeq k p k) ≥ 2/3 := w2
        linarith
  · -- m1 = 0: up-crossing at the s hub, use the two s-side triangles
    have hm1' : m1 = 0 := by omega
    subst hm1'
    set tr1 : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k q1 1, tpSeq k p 1) with htr1
    set tr2 : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k q2 1, tpSeq k p 1) with htr2
    have htr1_mem : tr1 ∈ S ×ˢ Sᶜ := by
      rw [Finset.mem_product]
      constructor
      · show tpSeq k q1 1 ∈ S
        rw [tpSeq_mid (by omega) (by omega)]
        exact hnd q1 1 hq1lt hq1p (by omega) (by omega)
      · show tpSeq k p (0+1) ∈ Sᶜ
        exact Finset.mem_compl.mpr hu2
    have htr2_mem : tr2 ∈ S ×ˢ Sᶜ := by
      rw [Finset.mem_product]
      constructor
      · show tpSeq k q2 1 ∈ S
        rw [tpSeq_mid (by omega) (by omega)]
        exact hnd q2 1 hq2lt hq2p (by omega) (by omega)
      · show tpSeq k p (0+1) ∈ Sᶜ
        exact Finset.mem_compl.mpr hu2
    have ne_uptr1 : up ≠ tr1 := by
      intro h
      have h1 := congrArg Prod.fst h
      simp only [hup, htr1] at h1
      replace h1 := tpSeq_inj3 hk1 hp hq1lt (by omega) (by omega) h1
      omega
    have ne_uptr2 : up ≠ tr2 := by
      intro h
      have h1 := congrArg Prod.fst h
      simp only [hup, htr2] at h1
      replace h1 := tpSeq_inj3 hk1 hp hq2lt (by omega) (by omega) h1
      omega
    have ne_dntr1 : dn ≠ tr1 := by
      intro h
      have h1 := congrArg Prod.fst h
      simp only [hdn, htr1] at h1
      replace h1 := tpSeq_inj3 hk1 hp hq1lt (by omega) (by omega) h1
      omega
    have ne_dntr2 : dn ≠ tr2 := by
      intro h
      have h1 := congrArg Prod.fst h
      simp only [hdn, htr2] at h1
      replace h1 := tpSeq_inj3 hk1 hp hq2lt (by omega) (by omega) h1
      omega
    have ne_tr12 : tr1 ≠ tr2 := by
      intro h
      have h1 := congrArg Prod.fst h
      simp only [htr1, htr2] at h1
      replace h1 := tpSeq_inj3 hk1 hq1lt hq2lt (by omega) (by omega) h1
      omega
    by_cases hm2k : m2 + 1 ≤ k
    · apply cut_lower hk1 S {up, dn, tr1, tr2} ?_ 2 ?_
      · intro pq hpq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpq
        rcases hpq with rfl | rfl | rfl | rfl
        · exact hup_mem
        · exact hdn_mem
        · exact htr1_mem
        · exact htr2_mem
      · rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hupdn, ne_uptr1, ne_uptr2⟩),
          Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨ne_dntr1, ne_dntr2⟩),
          Finset.sum_insert (by simp only [Finset.mem_singleton]; exact ne_tr12), Finset.sum_singleton]
        have w1 := (tpSeq_weight hk hp (m := 0) (by omega)).1
        have w2 := tpSeq_unit_bwd hk hp (by omega) hm2k
        have w3 := tri_weight hk hq1lt hp hq1p (Or.inl rfl)
        have w4 := tri_weight hk hq2lt hp hq2p (Or.inl rfl)
        rw [hup, hdn, htr1, htr2, w2, w3, w4]
        have : tpCert k (tpSeq k p 0) (tpSeq k p (0+1)) ≥ 2/3 := w1
        linarith
    · -- m1 = 0 and m2 = k: hub crossings at both ends, all four triangles
      have hm2 : k = m2 := by omega
      subst hm2
      set sr1 : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k q1 k, tpSeq k p k) with hsr1
      set sr2 : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k q2 k, tpSeq k p k) with hsr2
      have hsr1_mem : sr1 ∈ S ×ˢ Sᶜ := by
        rw [Finset.mem_product]
        constructor
        · show tpSeq k q1 k ∈ S
          rw [tpSeq_mid (by omega) (by omega)]
          exact hnd q1 k hq1lt hq1p (by omega) (by omega)
        · show tpSeq k p k ∈ Sᶜ
          exact Finset.mem_compl.mpr hd1
      have hsr2_mem : sr2 ∈ S ×ˢ Sᶜ := by
        rw [Finset.mem_product]
        constructor
        · show tpSeq k q2 k ∈ S
          rw [tpSeq_mid (by omega) (by omega)]
          exact hnd q2 k hq2lt hq2p (by omega) (by omega)
        · show tpSeq k p k ∈ Sᶜ
          exact Finset.mem_compl.mpr hd1
      have ne_upsr1 : up ≠ sr1 := by
        intro h
        have h1 := congrArg Prod.fst h
        simp only [hup, hsr1] at h1
        replace h1 := tpSeq_inj3 hk1 hp hq1lt (by omega) (by omega) h1
        omega
      have ne_upsr2 : up ≠ sr2 := by
        intro h
        have h1 := congrArg Prod.fst h
        simp only [hup, hsr2] at h1
        replace h1 := tpSeq_inj3 hk1 hp hq2lt (by omega) (by omega) h1
        omega
      have ne_dnsr1 : dn ≠ sr1 := by
        intro h
        have h1 := congrArg Prod.fst h
        simp only [hdn, hsr1] at h1
        replace h1 := tpSeq_inj3 hk1 hp hq1lt (by omega) (by omega) h1
        omega
      have ne_dnsr2 : dn ≠ sr2 := by
        intro h
        have h1 := congrArg Prod.fst h
        simp only [hdn, hsr2] at h1
        replace h1 := tpSeq_inj3 hk1 hp hq2lt (by omega) (by omega) h1
        omega
      have ne_trsr11 : tr1 ≠ sr1 := by
        intro h
        have h1 := congrArg Prod.snd h
        simp only [htr1, hsr1] at h1
        replace h1 := tpSeq_inj3 hk1 hp hp (by omega) (by omega) h1
        omega
      have ne_trsr12 : tr1 ≠ sr2 := by
        intro h
        have h1 := congrArg Prod.snd h
        simp only [htr1, hsr2] at h1
        replace h1 := tpSeq_inj3 hk1 hp hp (by omega) (by omega) h1
        omega
      have ne_trsr21 : tr2 ≠ sr1 := by
        intro h
        have h1 := congrArg Prod.snd h
        simp only [htr2, hsr1] at h1
        replace h1 := tpSeq_inj3 hk1 hp hp (by omega) (by omega) h1
        omega
      have ne_trsr22 : tr2 ≠ sr2 := by
        intro h
        have h1 := congrArg Prod.snd h
        simp only [htr2, hsr2] at h1
        replace h1 := tpSeq_inj3 hk1 hp hp (by omega) (by omega) h1
        omega
      have ne_sr12 : sr1 ≠ sr2 := by
        intro h
        have h1 := congrArg Prod.fst h
        simp only [hsr1, hsr2] at h1
        replace h1 := tpSeq_inj3 hk1 hq1lt hq2lt (by omega) (by omega) h1
        omega
      apply cut_lower hk1 S {up, dn, tr1, tr2, sr1, sr2} ?_ 2 ?_
      · intro pq hpq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hpq
        rcases hpq with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hup_mem
        · exact hdn_mem
        · exact htr1_mem
        · exact htr2_mem
        · exact hsr1_mem
        · exact hsr2_mem
      · rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hupdn, ne_uptr1, ne_uptr2, ne_upsr1, ne_upsr2⟩),
          Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨ne_dntr1, ne_dntr2, ne_dnsr1, ne_dnsr2⟩),
          Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨ne_tr12, ne_trsr11, ne_trsr12⟩),
          Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨ne_trsr21, ne_trsr22⟩),
          Finset.sum_insert (by simp only [Finset.mem_singleton]; exact ne_sr12), Finset.sum_singleton]
        have w1 := (tpSeq_weight hk hp (m := 0) (by omega)).1
        have w2 := (tpSeq_weight hk hp (m := k) (by omega)).2
        have w3 := tri_weight hk hq1lt hp hq1p (Or.inl rfl)
        have w4 := tri_weight hk hq2lt hp hq2p (Or.inl rfl)
        have w5 := tri_weight hk hq1lt hp hq1p (Or.inr rfl)
        have w6 := tri_weight hk hq2lt hp hq2p (Or.inr rfl)
        rw [hup, hdn, htr1, htr2, hsr1, hsr2, w3, w4, w5, w6]
        have hw1 : tpCert k (tpSeq k p 0) (tpSeq k p (0+1)) ≥ 2/3 := w1
        have hw2 : tpCert k (tpSeq k p (k+1)) (tpSeq k p k) ≥ 2/3 := w2
        linarith


/-- The cut bound when two paths are deficient. -/
lemma two_deficient (hk : 2 ≤ k) (S : Finset (Fin (3*k+2)))
    (hs : tpS k ∈ S) (ht : tpT k ∈ S) {p q : ℕ} (hp : p < 3) (hq : q < 3) (hpq : p ≠ q)
    {jp jq m1p m2p m1q m2q : ℕ}
    (hjp1 : 1 ≤ jp) (hjpk : jp ≤ k) (hjq1 : 1 ≤ jq) (hjqk : jq ≤ k)
    (hp11 : m1p < jp) (hp21 : jp ≤ m2p) (hp22 : m2p ≤ k)
    (hq11 : m1q < jq) (hq21 : jq ≤ m2q) (hq22 : m2q ≤ k)
    (hpu1 : tpSeq k p m1p ∈ S) (hpu2 : tpSeq k p (m1p+1) ∉ S)
    (hpd1 : tpSeq k p m2p ∉ S) (hpd2 : tpSeq k p (m2p+1) ∈ S)
    (hqu1 : tpSeq k q m1q ∈ S) (hqu2 : tpSeq k q (m1q+1) ∉ S)
    (hqd1 : tpSeq k q m2q ∉ S) (hqd2 : tpSeq k q (m2q+1) ∈ S) :
    2 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, tpCert k u v := by
  classical
  have hk1 : 1 ≤ k := by omega
  set upP : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k p m1p, tpSeq k p (m1p+1)) with hupP
  set dnP : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k p (m2p+1), tpSeq k p m2p) with hdnP
  set upQ : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k q m1q, tpSeq k q (m1q+1)) with hupQ
  set dnQ : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k q (m2q+1), tpSeq k q m2q) with hdnQ
  have ne1 : upP ≠ dnP := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only [hupP, hdnP] at h1
    replace h1 := tpSeq_inj3 hk1 hp hp (by omega) (by omega) h1
    omega
  have ne2 : upP ≠ upQ := by
    intro h
    have h1 := congrArg Prod.snd h
    simp only [hupP, hupQ] at h1
    replace h1 := tpSeq_inj3 hk1 hp hq (by omega) (by omega) h1
    omega
  have ne3 : upP ≠ dnQ := by
    intro h
    have h1 := congrArg Prod.snd h
    simp only [hupP, hdnQ] at h1
    replace h1 := tpSeq_inj3 hk1 hp hq (by omega) (by omega) h1
    omega
  have ne4 : dnP ≠ upQ := by
    intro h
    have h1 := congrArg Prod.snd h
    simp only [hdnP, hupQ] at h1
    replace h1 := tpSeq_inj3 hk1 hp hq (by omega) (by omega) h1
    omega
  have ne5 : dnP ≠ dnQ := by
    intro h
    have h1 := congrArg Prod.snd h
    simp only [hdnP, hdnQ] at h1
    replace h1 := tpSeq_inj3 hk1 hp hq (by omega) (by omega) h1
    omega
  have ne6 : upQ ≠ dnQ := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only [hupQ, hdnQ] at h1
    replace h1 := tpSeq_inj3 hk1 hq hq (by omega) (by omega) h1
    omega
  apply cut_lower hk1 S {upP, dnP, upQ, dnQ} ?_ 2 ?_
  · intro pq hpq'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpq'
    rcases hpq' with rfl | rfl | rfl | rfl <;> rw [Finset.mem_product]
    · exact ⟨hpu1, Finset.mem_compl.mpr hpu2⟩
    · exact ⟨hpd2, Finset.mem_compl.mpr hpd1⟩
    · exact ⟨hqu1, Finset.mem_compl.mpr hqu2⟩
    · exact ⟨hqd2, Finset.mem_compl.mpr hqd1⟩
  · rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨ne1, ne2, ne3⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨ne4, ne5⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact ne6),
      Finset.sum_singleton]
    have w1 := (tpSeq_weight hk hp (m := m1p) (by omega)).1
    have w2 := (tpSeq_weight hk hp (m := m2p) (by omega)).2
    have w3 := (tpSeq_weight hk hq (m := m1q) (by omega)).1
    have w4 := (tpSeq_weight hk hq (m := m2q) (by omega)).2
    rw [hupP, hdnP, hupQ, hdnQ]
    linarith

/-- The main cut bound, given that the hub `s` lies in `S`. -/
lemma tpCert_cut_main (hk : 2 ≤ k) (S : Finset (Fin (3*k+2)))
    (hs : tpS k ∈ S) (hSu : S ≠ univ) :
    2 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, tpCert k u v := by
  classical
  have hk1 : 1 ≤ k := by omega
  by_cases ht : tpT k ∈ S
  · -- both hubs inside: some path is deficient
    have hcrossgen : ∀ p j, p < 3 → 1 ≤ j → j ≤ k → tpEnc k p j ∉ S →
        ∃ m1 m2, m1 < j ∧ j ≤ m2 ∧ m2 ≤ k ∧
          tpSeq k p m1 ∈ S ∧ tpSeq k p (m1+1) ∉ S ∧
          tpSeq k p m2 ∉ S ∧ tpSeq k p (m2+1) ∈ S := by
      intro p j hp hj1 hjk hout
      obtain ⟨m1, h11, h12, h13, h14⟩ := exists_cross_up (fun m => tpSeq k p m ∈ S) 0 j
        (by omega) (by show tpSeq k p 0 ∈ S; rw [tpSeq_zero]; exact hs) (by show tpSeq k p j ∉ S; rw [tpSeq_mid hj1 hjk]; exact hout)
      obtain ⟨m2, h21, h22, h23, h24⟩ := exists_cross_down (fun m => tpSeq k p m ∈ S) j (k+1)
        (by omega) (by show tpSeq k p j ∉ S; rw [tpSeq_mid hj1 hjk]; exact hout) (by show tpSeq k p (k+1) ∈ S; rw [tpSeq_top]; exact ht)
      exact ⟨m1, m2, h12, h21, by omega, h13, h14, h23, h24⟩
    have hdef : ∃ q j, q < 3 ∧ 1 ≤ j ∧ j ≤ k ∧ tpEnc k q j ∉ S := by
      obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
        by_contra hcon
        push_neg at hcon
        exact hSu (Finset.eq_univ_iff_forall.mpr hcon)
      rcases tpCases hk1 w with rfl | rfl | ⟨q, j, hq, hj1, hjk, rfl⟩
      · exact absurd hs hw
      · exact absurd ht hw
      · exact ⟨q, j, hq, hj1, hjk, hw⟩
    by_cases d0 : ∃ j, 1 ≤ j ∧ j ≤ k ∧ tpEnc k 0 j ∉ S <;>
      by_cases d1 : ∃ j, 1 ≤ j ∧ j ≤ k ∧ tpEnc k 1 j ∉ S <;>
      by_cases d2 : ∃ j, 1 ≤ j ∧ j ≤ k ∧ tpEnc k 2 j ∉ S
    · obtain ⟨jp, hjp1, hjpk, hop⟩ := d0
      obtain ⟨jq, hjq1, hjqk, hoq⟩ := d1
      obtain ⟨m1p, m2p, a1, a2, a3, a4, a5, a6, a7⟩ := hcrossgen 0 jp (by omega) hjp1 hjpk hop
      obtain ⟨m1q, m2q, b1, b2, b3, b4, b5, b6, b7⟩ := hcrossgen 1 jq (by omega) hjq1 hjqk hoq
      exact two_deficient hk S hs ht (by omega) (by omega) (by omega)
        hjp1 hjpk hjq1 hjqk a1 a2 a3 b1 b2 b3 a4 a5 a6 a7 b4 b5 b6 b7
    · obtain ⟨jp, hjp1, hjpk, hop⟩ := d0
      obtain ⟨jq, hjq1, hjqk, hoq⟩ := d1
      obtain ⟨m1p, m2p, a1, a2, a3, a4, a5, a6, a7⟩ := hcrossgen 0 jp (by omega) hjp1 hjpk hop
      obtain ⟨m1q, m2q, b1, b2, b3, b4, b5, b6, b7⟩ := hcrossgen 1 jq (by omega) hjq1 hjqk hoq
      exact two_deficient hk S hs ht (by omega) (by omega) (by omega)
        hjp1 hjpk hjq1 hjqk a1 a2 a3 b1 b2 b3 a4 a5 a6 a7 b4 b5 b6 b7
    · obtain ⟨jp, hjp1, hjpk, hop⟩ := d0
      obtain ⟨jq, hjq1, hjqk, hoq⟩ := d2
      obtain ⟨m1p, m2p, a1, a2, a3, a4, a5, a6, a7⟩ := hcrossgen 0 jp (by omega) hjp1 hjpk hop
      obtain ⟨m1q, m2q, b1, b2, b3, b4, b5, b6, b7⟩ := hcrossgen 2 jq (by omega) hjq1 hjqk hoq
      exact two_deficient hk S hs ht (by omega) (by omega) (by omega)
        hjp1 hjpk hjq1 hjqk a1 a2 a3 b1 b2 b3 a4 a5 a6 a7 b4 b5 b6 b7
    · -- only path 0 deficient
      push_neg at d1 d2
      obtain ⟨jp, hjp1, hjpk, hop⟩ := d0
      obtain ⟨m1, m2, a1, a2, a3, a4, a5, a6, a7⟩ := hcrossgen 0 jp (by omega) hjp1 hjpk hop
      apply one_deficient hk S hs ht (p := 0) (by omega) hjp1 hjpk a1 a2 a3 a4 a5 a6 a7
      intro q j' hq hqp hj'1 hj'k
      rcases (by omega : q = 1 ∨ q = 2) with rfl | rfl
      · exact d1 j' hj'1 hj'k
      · exact d2 j' hj'1 hj'k
    · obtain ⟨jp, hjp1, hjpk, hop⟩ := d1
      obtain ⟨jq, hjq1, hjqk, hoq⟩ := d2
      obtain ⟨m1p, m2p, a1, a2, a3, a4, a5, a6, a7⟩ := hcrossgen 1 jp (by omega) hjp1 hjpk hop
      obtain ⟨m1q, m2q, b1, b2, b3, b4, b5, b6, b7⟩ := hcrossgen 2 jq (by omega) hjq1 hjqk hoq
      exact two_deficient hk S hs ht (by omega) (by omega) (by omega)
        hjp1 hjpk hjq1 hjqk a1 a2 a3 b1 b2 b3 a4 a5 a6 a7 b4 b5 b6 b7
    · -- only path 1 deficient
      push_neg at d0 d2
      obtain ⟨jp, hjp1, hjpk, hop⟩ := d1
      obtain ⟨m1, m2, a1, a2, a3, a4, a5, a6, a7⟩ := hcrossgen 1 jp (by omega) hjp1 hjpk hop
      apply one_deficient hk S hs ht (p := 1) (by omega) hjp1 hjpk a1 a2 a3 a4 a5 a6 a7
      intro q j' hq hqp hj'1 hj'k
      rcases (by omega : q = 0 ∨ q = 2) with rfl | rfl
      · exact d0 j' hj'1 hj'k
      · exact d2 j' hj'1 hj'k
    · -- only path 2 deficient
      push_neg at d0 d1
      obtain ⟨jp, hjp1, hjpk, hop⟩ := d2
      obtain ⟨m1, m2, a1, a2, a3, a4, a5, a6, a7⟩ := hcrossgen 2 jp (by omega) hjp1 hjpk hop
      apply one_deficient hk S hs ht (p := 2) (by omega) hjp1 hjpk a1 a2 a3 a4 a5 a6 a7
      intro q j' hq hqp hj'1 hj'k
      rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
      · exact d0 j' hj'1 hj'k
      · exact d1 j' hj'1 hj'k
    · -- no deficient path: contradiction
      exfalso
      obtain ⟨q, j, hq, hj1, hjk, hout⟩ := hdef
      rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
      · exact d0 ⟨j, hj1, hjk, hout⟩
      · exact d1 ⟨j, hj1, hjk, hout⟩
      · exact d2 ⟨j, hj1, hjk, hout⟩
  · -- t outside: each path crosses once
    have hcross : ∀ p, p < 3 → ∃ m, m ≤ k ∧ tpSeq k p m ∈ S ∧ tpSeq k p (m+1) ∉ S := by
      intro p hp
      obtain ⟨m, h1, h2, h3, h4⟩ := exists_cross_up (fun j => tpSeq k p j ∈ S) 0 (k+1)
        (by omega) (by show tpSeq k p 0 ∈ S; rw [tpSeq_zero]; exact hs) (by show tpSeq k p (k+1) ∉ S; rw [tpSeq_top]; exact ht)
      exact ⟨m, by omega, h3, h4⟩
    obtain ⟨m0, hm0, hin0, hout0⟩ := hcross 0 (by omega)
    obtain ⟨m1, hm1, hin1, hout1⟩ := hcross 1 (by omega)
    obtain ⟨m2, hm2, hin2, hout2⟩ := hcross 2 (by omega)
    set e0 : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k 0 m0, tpSeq k 0 (m0+1)) with he0
    set e1 : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k 1 m1, tpSeq k 1 (m1+1)) with he1
    set e2 : Fin (3*k+2) × Fin (3*k+2) := (tpSeq k 2 m2, tpSeq k 2 (m2+1)) with he2
    have pairne : ∀ (pa pb ma mb : ℕ), pa < 3 → pb < 3 → pa ≠ pb → ma ≤ k → mb ≤ k →
        (tpSeq k pa ma, tpSeq k pa (ma+1)) ≠ (tpSeq k pb mb, tpSeq k pb (mb+1)) := by
      intro pa pb ma mb hpa hpb hab hma hmb h
      have h1 := congrArg Prod.snd h
      have h2 := congrArg Prod.fst h
      simp only at h1 h2
      replace h1 := tpSeq_inj3 hk1 hpa hpb (by omega) (by omega) h1
      replace h2 := tpSeq_inj3 hk1 hpa hpb (by omega) (by omega) h2
      omega
    have ne01 : e0 ≠ e1 := pairne 0 1 m0 m1 (by omega) (by omega) (by omega) hm0 hm1
    have ne02 : e0 ≠ e2 := pairne 0 2 m0 m2 (by omega) (by omega) (by omega) hm0 hm2
    have ne12 : e1 ≠ e2 := pairne 1 2 m1 m2 (by omega) (by omega) (by omega) hm1 hm2
    apply cut_lower hk1 S {e0, e1, e2} ?_ 2 ?_
    · intro pq hpq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpq
      rcases hpq with rfl | rfl | rfl <;> rw [Finset.mem_product]
      · exact ⟨hin0, Finset.mem_compl.mpr hout0⟩
      · exact ⟨hin1, Finset.mem_compl.mpr hout1⟩
      · exact ⟨hin2, Finset.mem_compl.mpr hout2⟩
    · rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨ne01, ne02⟩),
        Finset.sum_insert (by simp only [Finset.mem_singleton]; exact ne12),
        Finset.sum_singleton]
      have w0 := (tpSeq_weight hk (p := 0) (by omega) hm0).1
      have w1 := (tpSeq_weight hk (p := 1) (by omega) hm1).1
      have w2 := (tpSeq_weight hk (p := 2) (by omega) hm2).1
      rw [he0, he1, he2]
      linarith

/-- **Feasibility of the classical certificate.** -/
theorem three_paths_cert_feasible_thm (k : ℕ) (hk : 2 ≤ k) : IsHeldKarp (tpCert k) := by
  have hk1 : 1 ≤ k := by omega
  refine ⟨tpCert_symm' hk1, tpCert_diag', tpCert_nonneg', tpCert_le_one',
    tpCert_degree hk, ?_⟩
  intro S hS hSu
  by_cases hs : tpS k ∈ S
  · exact tpCert_cut_main hk S hs hSu
  · rw [cut_swap hk1]
    apply tpCert_cut_main hk Sᶜ (Finset.mem_compl.mpr hs)
    intro h
    obtain ⟨a, ha⟩ := hS
    have hmem : a ∈ Sᶜ := h ▸ Finset.mem_univ a
    exact Finset.mem_compl.mp hmem ha

end MetricTSP

open MetricTSP

theorem solution (k : ℕ) (hk : 2 ≤ k) : IsHeldKarp (tpCert k) :=
  MetricTSP.three_paths_cert_feasible_thm k hk
