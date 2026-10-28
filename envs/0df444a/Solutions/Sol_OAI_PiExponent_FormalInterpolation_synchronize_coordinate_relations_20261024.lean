-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.synchronize_coordinate_relations_20261024
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:22:05.983855+00:00
-- url     : https://prove2.me/submissions/cbc67d3a-74a7-42f6-8aca-23abf77d4d5b

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

open scoped BigOperators
open MvPolynomial

namespace S157A

variable {d : ℕ} (w : Fin d → ℚ)

def Sle (c : ℚ) : Set (MvPolynomial (Fin d) ℂ) :=
  {p | ∀ a ∈ p.support, Finsupp.weight w a ≤ c}
def Slt (c : ℚ) : Set (MvPolynomial (Fin d) ℂ) :=
  {p | ∀ a ∈ p.support, Finsupp.weight w a < c}

variable {w}

lemma lt_le {p : MvPolynomial (Fin d) ℂ} {c : ℚ} (h : p ∈ Slt w c) : p ∈ Sle w c :=
  fun a ha => (h a ha).le

lemma mul_le_le {p r : MvPolynomial (Fin d) ℂ} {b c : ℚ} (hp : p ∈ Sle w b) (hr : r ∈ Sle w c) :
    p * r ∈ Sle w (b + c) := by
  classical
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (support_mul p r ha)
  rw [map_add]; exact add_le_add (hp x hx) (hr y hy)

lemma mul_le_lt {p r : MvPolynomial (Fin d) ℂ} {b c : ℚ} (hp : p ∈ Sle w b) (hr : r ∈ Slt w c) :
    p * r ∈ Slt w (b + c) := by
  classical
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (support_mul p r ha)
  rw [map_add]; exact add_lt_add_of_le_of_lt (hp x hx) (hr y hy)

lemma mul_lt_le {p r : MvPolynomial (Fin d) ℂ} {b c : ℚ} (hp : p ∈ Slt w b) (hr : r ∈ Sle w c) :
    p * r ∈ Slt w (b + c) := by
  classical
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (support_mul p r ha)
  rw [map_add]; exact add_lt_add_of_lt_of_le (hp x hx) (hr y hy)

lemma add_lt {p r : MvPolynomial (Fin d) ℂ} {c : ℚ} (hp : p ∈ Slt w c) (hr : r ∈ Slt w c) :
    p + r ∈ Slt w c := by
  classical
  intro a ha
  rcases Finset.mem_union.mp (support_add ha) with h | h
  exacts [hp a h, hr a h]

lemma sub_lt {p r : MvPolynomial (Fin d) ℂ} {c : ℚ} (hp : p ∈ Slt w c) (hr : r ∈ Slt w c) :
    p - r ∈ Slt w c := by
  classical
  intro a ha
  rcases Finset.mem_union.mp (support_sub _ p r ha) with h | h
  exacts [hp a h, hr a h]

lemma add_le {p r : MvPolynomial (Fin d) ℂ} {c : ℚ} (hp : p ∈ Sle w c) (hr : r ∈ Sle w c) :
    p + r ∈ Sle w c := by
  classical
  intro a ha
  rcases Finset.mem_union.mp (support_add ha) with h | h
  exacts [hp a h, hr a h]

lemma weight_cast (a : Fin d →₀ ℕ) :
    ((Finsupp.weight w a : ℚ) : ℝ) = ∑ j, (w j : ℝ) * (a j : ℝ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  push_cast
  simp [nsmul_eq_mul, mul_comm]

lemma X_pow_le (i : Fin d) (m : ℕ) : (X i ^ m : MvPolynomial (Fin d) ℂ) ∈ Sle w (m * w i) := by
  classical
  intro a ha
  rw [X_pow_eq_monomial] at ha
  have := support_monomial_subset ha
  rw [Finset.mem_singleton] at this
  subst this
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

lemma X_pow_hom (i : Fin d) (m : ℕ) :
    (X i ^ m : MvPolynomial (Fin d) ℂ).IsWeightedHomogeneous w (m * w i) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

lemma pow_rel (i : Fin d) (n : ℕ) (q : ℚ) (hnq : (n : ℚ) * w i = q)
    (f : MvPolynomial (Fin d) ℂ) (hf : f ∈ Slt w q) (k : ℕ) :
    ∃ R ∈ Slt w (k * q), (X i ^ n - f) ^ k = X i ^ (n * k) + R := by
  have hP : (X i ^ n : MvPolynomial (Fin d) ℂ) ∈ Sle w q := by
    have := X_pow_le (w := w) i n; rwa [hnq] at this
  induction k with
  | zero => exact ⟨0, fun a ha => by simp at ha, by simp⟩
  | succ j ih =>
    obtain ⟨R, hR, hEq⟩ := ih
    have hPj : (X i ^ (n * j) : MvPolynomial (Fin d) ℂ) ∈ Sle w (j * q) := by
      have := X_pow_le (w := w) i (n * j)
      convert this using 1; rw [← hnq]; push_cast; ring
    refine ⟨R * X i ^ n - X i ^ (n * j) * f - R * f, ?_, ?_⟩
    · have e : ((j + 1 : ℕ) : ℚ) * q = j * q + q := by push_cast; ring
      rw [e]
      refine sub_lt (sub_lt (mul_lt_le hR hP) (mul_le_lt hPj hf)) ?_
      exact mul_lt_le hR (lt_le hf)
    · rw [pow_succ, hEq, Nat.mul_succ, pow_add]; ring

end S157A

open S157A in
theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (eps : Real) (heps : 0 < eps)
    (hcoord : ∀ i : Fin d, ∃ si : Nat, 0 < si ∧
      ∃ qi : Rat, 0 < qi ∧ (qi : Real) < (si : Real) * ((rho : Real) + eps) ∧
        ∃ ni : Nat, 0 < ni ∧ (ni : Rat) * w i = qi ∧
          ∃ fi : MvPolynomial (Fin d) Complex,
            MvPolynomial.X i ^ ni - fi ∈ I ^ si ∧
            ∀ a, a ∈ fi.support →
              ∑ j, (w j : Real) * (a j : Real) < (qi : Real)) :
    ∃ s : Nat, 0 < s ∧
      ∃ q : Rat, 0 < q ∧ (q : Real) < (s : Real) * ((rho : Real) + eps) ∧
        ∃ n : Fin d → Nat, (∀ i, 0 < n i) ∧
          (∀ i, (n i : Rat) * w i = q) ∧
          ∃ f : Fin d → MvPolynomial (Fin d) Complex,
            (∀ i, MvPolynomial.X i ^ n i - f i ∈ I ^ s) ∧
            (∀ i a, a ∈ (f i).support →
              ∑ j, (w j : Real) * (a j : Real) < (q : Real)) := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (show (0 : ℝ) < rho + eps by
      have : (0 : ℝ) ≤ rho := by exact_mod_cast hrho
      linarith)
    exact ⟨1, one_pos, q, by exact_mod_cast hq0, by simpa using hq1, Fin.elim0,
      fun i => i.elim0, fun i => i.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  choose s hs q hq hqlt n hn hnq f hf hsupp using hcoord
  set N : Fin d → ℕ := fun j => (q j).num.natAbs with hN
  have hNq : ∀ j, (N j : ℚ) = (q j).den * q j := by
    intro j
    have h1 : (0 : ℤ) < (q j).num := Rat.num_pos.mpr (hq j)
    simp only [hN]
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast h1)]
    rw [mul_comm]; exact (Rat.mul_den_eq_num (q j)).symm
  have hNpos : ∀ j, 0 < N j := fun j => by
    simp only [hN]; exact Int.natAbs_pos.mpr (Rat.num_pos.mpr (hq j)).ne'
  set Q : ℕ := ∏ j, N j with hQ
  set k : Fin d → ℕ := fun i => (q i).den * ∏ j ∈ Finset.univ.erase i, N j with hk
  have hkq : ∀ i, (k i : ℚ) * q i = Q := by
    intro i
    simp only [hk, hQ]
    rw [← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ i)]
    push_cast
    rw [hNq i]; ring
  have hkpos : ∀ i, 0 < k i := fun i =>
    Nat.mul_pos (q i).den_pos (Finset.prod_pos fun j _ => hNpos j)
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  set S : ℕ := (Finset.univ.image fun i => k i * s i).min' (hne.image _) with hS
  obtain ⟨i0, -, hi0⟩ := Finset.mem_image.mp (Finset.min'_mem _ (hne.image (fun i => k i * s i)))
  replace hi0 : k i0 * s i0 = S := hi0
  have hSle : ∀ i, S ≤ k i * s i := fun i =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hfl : ∀ i, f i ∈ Slt w (q i) := by
    intro i a ha
    have := hsupp i a ha
    rw [← weight_cast] at this
    exact_mod_cast this
  choose R hR hEq using fun i => pow_rel (w := w) i (n i) (q i) (hnq i) (f i) (hfl i) (k i)
  have hQpos : (0 : ℚ) < Q := by rw [← hkq i0]; exact mul_pos (by exact_mod_cast hkpos i0) (hq i0)
  refine ⟨S, ?_, Q, hQpos, ?_, fun i => n i * k i, fun i => Nat.mul_pos (hn i) (hkpos i), ?_,
    fun i => -R i, ?_, ?_⟩
  · rw [← hi0]; exact Nat.mul_pos (hkpos i0) (hs i0)
  · rw [← hi0, ← hkq i0]; push_cast
    have := hqlt i0
    have hk0 : (0 : ℝ) < k i0 := by exact_mod_cast hkpos i0
    nlinarith
  · intro i; push_cast; rw [mul_comm (n i : ℚ), mul_assoc, hnq i, hkq i]
  · intro i
    have hmem : (X i ^ n i - f i) ^ k i ∈ I ^ (k i * s i) := by
      rw [mul_comm, pow_mul]; exact Ideal.pow_mem_pow (hf i) (k i)
    rw [hEq i] at hmem
    rw [sub_neg_eq_add]
    exact Ideal.pow_le_pow_right (hSle i) hmem
  · intro i a ha
    rw [MvPolynomial.support_neg] at ha
    rw [← weight_cast]
    have := hR i a ha
    rw [← hkq i]; exact_mod_cast this
