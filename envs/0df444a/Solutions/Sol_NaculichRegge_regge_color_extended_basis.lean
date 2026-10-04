-- Prove2me | solution 1 for NaculichRegge.regge_color_extended_basis
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:52:56.314136+00:00
-- url     : https://prove2.me/submissions/7bded1b8-1196-4093-a6ca-df04134dc7ab

import Mathlib
import Definitions.Def_NaculichRegge_TraceBasis

set_option autoImplicit false

open Polynomial

namespace NaculichRegge0c29

open NaculichRegge

def wt (j : Fin 6) : ℕ := if j.val < 3 then 0 else 1

def Good (d w : ℕ) (p : ℂ[X]) : Prop :=
  ∀ e, p.coeff e ≠ 0 → e + w ≤ d ∧ (e + w) % 2 = d % 2

def PV (d : ℕ) (v : ColorVec) : Prop := ∀ j, Good d (wt j) (v j)

def OpDeg (e : ℕ) (A : ColorOp) : Prop := ∀ d v, PV d v → PV (d + e) (A.mulVec v)

lemma good_zero (d w : ℕ) : Good d w 0 := by
  intro e he; simp at he

lemma good_sub {d w : ℕ} {p q : ℂ[X]} (hp : Good d w p) (hq : Good d w q) :
    Good d w (p - q) := by
  intro e he
  rw [coeff_sub] at he
  by_cases h : p.coeff e = 0
  · apply hq; intro h'; apply he; rw [h, h']; simp
  · exact hp e h

lemma good_sum {d w : ℕ} (f : Fin 6 → ℂ[X]) (hf : ∀ c, Good d w (f c)) :
    Good d w (∑ c, f c) := by
  intro e he
  rw [finsetSum_coeff] at he
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  exact hf c e hc

lemma good_mono {d w : ℕ} {p : ℂ[X]} (hp : Good d w p) : Good (d + 2) w p := by
  intro e he; have := hp e he; omega

lemma good_X_mul {d w : ℕ} {p : ℂ[X]} (hp : Good d w p) : Good (d + 1) w (X * p) := by
  intro e he
  rcases e with _ | e
  · simp at he
  · rw [coeff_X_mul] at he; have := hp e he; omega

lemma good_X_pow_mul {d w : ℕ} {p : ℂ[X]} (m : ℕ) (hp : Good d w p) :
    Good (d + m) w (X ^ m * p) := by
  induction m with
  | zero => simpa using hp
  | succ m ih =>
    rw [pow_succ, mul_comm (X ^ m) X, mul_assoc]
    have := good_X_mul ih
    simpa [Nat.add_assoc] using this

lemma good_mul_entry {d wr wc : ℕ} (a p : ℂ[X])
    (ha : ∀ x, a.coeff x ≠ 0 → x + wr ≤ wc + 1 ∧ (x + wr) % 2 = (wc + 1) % 2)
    (hp : Good d wc p) : Good (d + 1) wr (a * p) := by
  intro n hn
  rw [coeff_mul] at hn
  obtain ⟨⟨x, y⟩, hxy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxy
  have hx : a.coeff x ≠ 0 := fun h => hne (by simp [h])
  have hy : p.coeff y ≠ 0 := fun h => hne (by simp [h])
  have h1 := ha x hx
  have h2 := hp y hy
  simp only at hxy
  omega

lemma opdeg1_of_entries (A : ColorOp)
    (hA : ∀ r c, ∀ x, (A r c).coeff x ≠ 0 →
      x + wt r ≤ wt c + 1 ∧ (x + wt r) % 2 = (wt c + 1) % 2) : OpDeg 1 A := by
  intro d v hv r
  simp only [Matrix.mulVec, dotProduct]
  apply good_sum
  intro c
  exact good_mul_entry _ _ (hA r c) (hv c)

lemma Tt2_deg : OpDeg 1 Tt2 := by
  apply opdeg1_of_entries
  intro r c x hx
  rcases x with _ | x <;> fin_cases r <;> fin_cases c <;>
    simp [Tt2, wt, coeff_X, coeff_one, coeff_ofNat_succ, coeff_ofNat_zero] at hx ⊢ <;> omega

lemma Tsu2_deg : OpDeg 1 Tsu2 := by
  apply opdeg1_of_entries
  intro r c x hx
  rcases x with _ | x <;> fin_cases r <;> fin_cases c <;>
    simp [Tsu2, wt, coeff_X, coeff_C, coeff_one, coeff_ofNat_succ, coeff_ofNat_zero] at hx ⊢ <;> omega

lemma pv_sub {d : ℕ} {u v : ColorVec} (hu : PV d u) (hv : PV d v) : PV d (u - v) :=
  fun j => good_sub (hu j) (hv j)

lemma opdeg_mul {a b : ℕ} {A B : ColorOp} (hA : OpDeg a A) (hB : OpDeg b B) :
    OpDeg (a + b) (A * B) := by
  intro d v hv
  rw [← Matrix.mulVec_mulVec]
  have := hA _ _ (hB d v hv)
  rwa [show d + b + a = d + (a + b) by omega] at this

lemma opdeg_sub {e : ℕ} {A B : ColorOp} (hA : OpDeg e A) (hB : OpDeg e B) :
    OpDeg e (A - B) := by
  intro d v hv
  rw [Matrix.sub_mulVec]
  exact pv_sub (hA d v hv) (hB d v hv)

lemma opdeg_comm {a b : ℕ} {A B : ColorOp} (hA : OpDeg a A) (hB : OpDeg b B) :
    OpDeg (a + b) (comm A B) := by
  unfold NaculichRegge.comm
  apply opdeg_sub (opdeg_mul hA hB)
  rw [add_comm]
  exact opdeg_mul hB hA

lemma opdeg_one : OpDeg 0 (1 : ColorOp) := by
  intro d v hv
  rw [Matrix.one_mulVec]
  simpa using hv

lemma opdeg_zero (e : ℕ) : OpDeg e (0 : ColorOp) := by
  intro d v _ j
  rw [Matrix.zero_mulVec]
  exact good_zero _ _

lemma opdeg_pow {A : ColorOp} (hA : OpDeg 1 A) (n : ℕ) : OpDeg n (A ^ n) := by
  induction n with
  | zero => simpa using opdeg_one
  | succ n ih =>
    rw [pow_succ]
    exact opdeg_mul ih hA

lemma iter1 (n : ℕ) : OpDeg (n + 1) ((comm Tt2)^[n] Tsu2) := by
  induction n with
  | zero => simpa using Tsu2_deg
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have := opdeg_comm Tt2_deg ih
    rwa [show 1 + (n + 1) = n + 1 + 1 by omega] at this

lemma iter2 (n : ℕ) : OpDeg (n + 2) ((comm Tsu2)^[n] (comm Tt2 Tsu2)) := by
  induction n with
  | zero => simpa using opdeg_comm Tt2_deg Tsu2_deg
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have := opdeg_comm Tsu2_deg ih
    rwa [show 1 + (n + 2) = n + 1 + 2 by omega] at this

lemma reggeOp_deg (i k : ℕ) (h : IsReggeIndex i k) : OpDeg i (reggeOp i k) := by
  unfold reggeOp
  split_ifs with h0 h1 h2 h3
  · subst h0; exact opdeg_one
  · exact opdeg_pow Tsu2_deg i
  · have := iter1 (i - 1)
    rwa [show i - 1 + 1 = i by omega] at this
  · have hi : 3 ≤ i := by unfold IsReggeIndex at h; omega
    have := iter2 (i - 2)
    rwa [show i - 2 + 2 = i by omega] at this
  · exact opdeg_zero i

lemma pv_C00 : PV 0 C00 := by
  intro j e he
  rcases e with _ | e <;> fin_cases j <;> simp [C00, wt, coeff_one] at he ⊢

lemma pv_regge (i k : ℕ) (h : IsReggeIndex i k) : PV i (reggeColor i k) := by
  have := reggeOp_deg i k h 0 C00 pv_C00
  simpa [reggeColor] using this

lemma pv_smul {d : ℕ} {v : ColorVec} (m : ℕ) (hv : PV d v) :
    PV (d + m) ((X : ℂ[X]) ^ m • v) := by
  intro j
  simp only [Pi.smul_apply, smul_eq_mul]
  exact good_X_pow_mul m (hv j)

lemma term_eq (ℓ lam : ℕ) (hl : 1 ≤ lam ∧ lam ≤ 3 * ℓ + 3) (v : ColorVec) (j : Fin 6)
    (n : ℕ) :
    extCoord ℓ v lam * (extBasisVec ℓ lam j).coeff n =
      if extSlot lam = j ∧ extDegree ℓ lam = n then (v j).coeff n else 0 := by
  unfold extCoord extBasisVec
  rw [if_pos hl, if_pos hl]
  split_ifs with hc
  · obtain ⟨hs, hd⟩ := hc
    subst hs; subst hd
    simp
  · by_cases hs : extSlot lam = j
    · subst hs
      have hd : extDegree ℓ lam ≠ n := fun hd => hc ⟨rfl, hd⟩
      simp [coeff_X_pow, Ne.symm hd]
    · simp [Pi.single_apply, Ne.symm hs]

lemma expand_basis (ℓ : ℕ) (v : ColorVec) (hv : PV ℓ v) :
    v = ∑ lam ∈ Finset.Icc 1 (3 * ℓ + 3), extCoord ℓ v lam • extBasisVec ℓ lam := by
  funext j
  ext n
  rw [Finset.sum_apply, finsetSum_coeff]
  simp only [Pi.smul_apply, coeff_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun lam hlam => term_eq ℓ lam (Finset.mem_Icc.mp hlam) v j n)]
  by_cases hc : (v j).coeff n = 0
  · rw [hc]; simp
  · obtain ⟨h1, h2⟩ := hv j n hc
    have hj := j.isLt
    have hw : (wt j = 0 ∧ j.val < 3) ∨ (wt j = 1 ∧ 3 ≤ j.val) := by
      unfold wt; split_ifs <;> omega
    rw [Finset.sum_eq_single (j.val + 1 + 6 * ((ℓ - n - wt j) / 2))]
    · rw [if_pos]
      constructor
      · rw [Fin.ext_iff]
        simp only [extSlot]
        omega
      · unfold extDegree
        split_ifs <;> omega
    · intro b hb hne
      rw [if_neg]
      rintro ⟨hs, hd⟩
      rw [Finset.mem_Icc] at hb
      rw [Fin.ext_iff] at hs
      simp only [extSlot] at hs
      unfold extDegree at hd
      split_ifs at hd <;> omega
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_Icc]
      omega

end NaculichRegge0c29

open NaculichRegge Polynomial in
theorem solution (ℓ i k : ℕ) (h : IsReggeIndex i k) (hi : i ≤ ℓ) :
    (X : ℂ[X]) ^ (ℓ - i) • reggeColor i k =
      ∑ lam ∈ Finset.Icc 1 (3 * ℓ + 3),
        extCoord ℓ ((X : ℂ[X]) ^ (ℓ - i) • reggeColor i k) lam • extBasisVec ℓ lam := by
  apply NaculichRegge0c29.expand_basis
  have := NaculichRegge0c29.pv_smul (ℓ - i) (NaculichRegge0c29.pv_regge i k h)
  rwa [show i + (ℓ - i) = ℓ by omega] at this
