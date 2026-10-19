-- Prove2me | solution 1 for HamburgerMoment.isMomentSequence_iff_hankelMatrix_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:04:14.988251+00:00
-- url     : https://prove2.me/submissions/bb93f1f4-d295-4622-8d0a-b0c876d41665

import Theorems.Thm_HamburgerMoment_hankelPosDef_of_isMomentSequence
import Theorems.Thm_HamburgerMoment_isMomentSequence_of_hankelPosDef

open HamburgerMoment
open scoped ComplexOrder

private lemma hf_sub (m : ℕ → ℝ) (c : ℕ →₀ ℂ) (S : Finset ℕ) (hS : c.support ⊆ S) :
    hankelForm m c = ∑ j ∈ S, ∑ k ∈ S, (m (j + k) : ℂ) * c j * starRingEnd ℂ (c k) := by
  unfold hankelForm
  have hz : ∀ j, j ∉ c.support → c j = 0 := fun j hj => Finsupp.notMem_support_iff.1 hj
  rw [Finset.sum_subset hS (fun j _ hj => Finset.sum_eq_zero fun k _ => by simp [hz j hj])]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_subset hS (fun k _ hk => by simp [hz k hk])

open scoped ComplexOrder in
private lemma posSemidef (m : ℕ → ℝ) (hm : HankelPosDef m) (n : ℕ) : (hankelMatrix m n).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; simp [hankelMatrix, add_comm]
  · classical
    let f : ℕ → ℂ := fun j => if h : j < n + 1 then ((x ⟨j, h⟩ : ℝ) : ℂ) else 0
    let c : ℕ →₀ ℂ := Finsupp.onFinset (Finset.range (n + 1)) f (fun j hj => by
      by_contra hj'; simp only [Finset.mem_range] at hj'; exact hj (dif_neg hj'))
    have hc : c.support ⊆ Finset.range (n + 1) := Finsupp.support_onFinset_subset
    have key := hm c
    rw [hf_sub m c _ hc] at key
    have e : ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        (m (j + k) : ℂ) * c j * starRingEnd ℂ (c k) = ((dotProduct (star x) (Matrix.mulVec (hankelMatrix m n) x) : ℝ) : ℂ) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ k ∈ Finset.range (n + 1),
        (m (j + k) : ℂ) * c j * starRingEnd ℂ (c k))]
      simp only [dotProduct, Matrix.mulVec, hankelMatrix, Matrix.of_apply, star_trivial,
        Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun k => (m (↑i + k) : ℂ) * c ↑i * starRingEnd ℂ (c k))]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [c, f, Finsupp.onFinset_apply, i.2, j.2, dif_pos, Fin.eta, Complex.conj_ofReal]
      ring
    rw [e, Complex.zero_le_real] at key
    exact key


private lemma real_quad_nonneg (m : ℕ → ℝ) (N : ℕ)
    (h : (hankelMatrix m N).PosSemidef) (a : ℕ → ℝ) :
    0 ≤ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      m (j + k) * a j * a k := by
  have hp := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 (fun i => a i.val)
  have he : dotProduct (star (fun i : Fin (N + 1) => a i.val))
      ((hankelMatrix m N).mulVec (fun i => a i.val)) =
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        m (j + k) * a j * a k := by
    simp only [dotProduct, Matrix.mulVec, hankelMatrix, Matrix.of_apply, star_trivial,
      Finset.mul_sum]
    rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ k ∈ Finset.range (N + 1),
      m (j + k) * a j * a k)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Fin.sum_univ_eq_sum_range (fun k => m (j.val + k) * a j.val * a k)]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rwa [he] at hp

private lemma complex_quad_split (m : ℕ → ℝ) (S : Finset ℕ) (c : ℕ → ℂ) :
    ∑ j ∈ S, ∑ k ∈ S, (m (j+k) : ℂ) * c j * starRingEnd ℂ (c k) =
      ((∑ j ∈ S, ∑ k ∈ S, m (j+k) * (c j).re * (c k).re +
        ∑ j ∈ S, ∑ k ∈ S, m (j+k) * (c j).im * (c k).im : ℝ) : ℂ) := by
  have exchange : (∑ j ∈ S, ∑ k ∈ S, m (j+k) * (c j).im * (c k).re) =
      ∑ j ∈ S, ∑ k ∈ S, m (j+k) * (c j).re * (c k).im := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.add_comm k j]
    ring
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, zero_mul, sub_zero, add_zero, mul_neg, sub_neg_eq_add,
      Finset.sum_add_distrib]
  · simp only [Complex.im_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, zero_mul, sub_zero, add_zero, mul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
    linarith [exchange]

private lemma kernel_of_psd (m : ℕ → ℝ)
    (h : ∀ n, (hankelMatrix m n).PosSemidef) : HankelPosDef m := by
  classical
  intro c
  let N := c.support.sup id
  have hc : c.support ⊆ Finset.range (N+1) := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  rw [hf_sub m c _ hc, complex_quad_split, Complex.zero_le_real]
  exact add_nonneg (real_quad_nonneg m N (h N) (fun j => (c j).re))
    (real_quad_nonneg m N (h N) (fun j => (c j).im))

theorem solution (m : ℕ → ℝ) :
    IsMomentSequence m ↔ ∀ n : ℕ, (hankelMatrix m n).PosSemidef := by
  constructor
  · intro hm n
    exact posSemidef m (HamburgerMoment.hankelPosDef_of_isMomentSequence m hm) n
  · intro h
    exact HamburgerMoment.isMomentSequence_of_hankelPosDef m (kernel_of_psd m h)
