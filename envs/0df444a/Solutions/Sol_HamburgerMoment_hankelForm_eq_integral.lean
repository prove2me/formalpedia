-- Prove2me | solution 1 for HamburgerMoment.hankelForm_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:23:34.672139+00:00
-- url     : https://prove2.me/submissions/2f37aef7-cd14-48e1-abac-0e5568221714

import Mathlib
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory

namespace HMAux
open HamburgerMoment

lemma int_pow {m : ℕ → ℝ} {μ : Measure ℝ} (hμ : IsMomentMeasure m μ) (n : ℕ) :
    Integrable (fun x : ℝ => ((x ^ n : ℝ) : ℂ)) μ := (hμ n).1.ofReal

lemma hankelForm_eq_integral' (m : ℕ → ℝ) (μ : Measure ℝ) (hμ : IsMomentMeasure m μ)
    (c : ℕ →₀ ℂ) :
    hankelForm m c =
      ((∫ x, ‖∑ j ∈ c.support, c j * (x : ℂ) ^ j‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  have h1 : ∀ x : ℝ, (((‖∑ j ∈ c.support, c j * (x : ℂ) ^ j‖ ^ 2 : ℝ)) : ℂ) =
      ∑ j ∈ c.support, ∑ k ∈ c.support, (c j * starRingEnd ℂ (c k)) * (((x ^ (j + k) : ℝ)) : ℂ) := by
    intro x
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, map_pow, Complex.conj_ofReal]
    push_cast; ring
  simp_rw [h1]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ =>
    (int_pow hμ (j + k)).const_mul _)]
  unfold hankelForm
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ => (int_pow hμ (j + k)).const_mul _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_complex_ofReal, (hμ (j + k)).2]
  ring


open scoped ComplexOrder in
lemma posDef_of_seq (m : ℕ → ℝ) (hm : IsMomentSequence m) : HankelPosDef m := by
  obtain ⟨μ, hμ⟩ := hm
  intro c
  rw [hankelForm_eq_integral' m μ hμ c, Complex.zero_le_real]
  exact integral_nonneg fun x => sq_nonneg _

lemma poly_sq (m : ℕ → ℝ) (μ : Measure ℝ) (hμ : IsMomentMeasure m μ) (n : ℕ) (a : ℕ → ℝ) :
    ∫ x, (∑ j ∈ Finset.range (n + 1), a j * x ^ j) ^ 2 ∂μ =
        ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), a j * a k * m (j + k) := by
  have h1 : ∀ x : ℝ, (∑ j ∈ Finset.range (n + 1), a j * x ^ j) ^ 2 =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), (a j * a k) * x ^ (j + k) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [h1]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => (hμ (j + k)).1.const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ => (hμ (j + k)).1.const_mul _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, (hμ (j + k)).2]

lemma convex (m : ℕ → ℝ) (μ ν : Measure ℝ)
    (hμ : IsMomentMeasure m μ) (hν : IsMomentMeasure m ν) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    IsMomentMeasure m (ENNReal.ofReal t • μ + ENNReal.ofReal (1 - t) • ν) := by
  intro n
  have i1 := (hμ n).1.smul_measure (c := ENNReal.ofReal t) ENNReal.ofReal_ne_top
  have i2 := (hν n).1.smul_measure (c := ENNReal.ofReal (1 - t)) ENNReal.ofReal_ne_top
  refine ⟨i1.add_measure i2, ?_⟩
  rw [integral_add_measure i1 i2, integral_smul_measure, integral_smul_measure, (hμ n).2, (hν n).2,
    ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal (by linarith)]
  simp only [smul_eq_mul]; ring

lemma hf_sub (m : ℕ → ℝ) (c : ℕ →₀ ℂ) (S : Finset ℕ) (hS : c.support ⊆ S) :
    hankelForm m c = ∑ j ∈ S, ∑ k ∈ S, (m (j + k) : ℂ) * c j * starRingEnd ℂ (c k) := by
  unfold hankelForm
  have hz : ∀ j, j ∉ c.support → c j = 0 := fun j hj => Finsupp.notMem_support_iff.1 hj
  rw [Finset.sum_subset hS (fun j _ hj => Finset.sum_eq_zero fun k _ => by simp [hz j hj])]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_subset hS (fun k _ hk => by simp [hz k hk])

open scoped ComplexOrder in
lemma posSemidef (m : ℕ → ℝ) (hm : HankelPosDef m) (n : ℕ) : (hankelMatrix m n).PosSemidef := by
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

lemma finite_of {m : ℕ → ℝ} {μ : Measure ℝ} (hμ : IsMomentMeasure m μ) : IsFiniteMeasure μ := by
  have := (hμ 0).1
  simp only [pow_zero] at this
  rcases (integrable_const_iff.1 this) with h | h
  · exact absurd h one_ne_zero
  · exact h

lemma unique_or_infinite (m : ℕ → ℝ) (hm : IsMomentSequence m) :
    (∃! μ : Measure ℝ, IsMomentMeasure m μ) ∨ {μ : Measure ℝ | IsMomentMeasure m μ}.Infinite := by
  by_cases h : ∃! μ : Measure ℝ, IsMomentMeasure m μ
  · exact Or.inl h
  right
  obtain ⟨μ, hμ⟩ := hm
  have : ∃ ν, IsMomentMeasure m ν ∧ ν ≠ μ := by
    by_contra hc; push Not at hc
    exact h ⟨μ, hμ, fun ν hν => hc ν hν⟩
  obtain ⟨ν, hν, hne⟩ := this
  have := finite_of hμ
  have := finite_of hν
  obtain ⟨A, hA, hAne⟩ : ∃ A, MeasurableSet A ∧ μ A ≠ ν A := by
    by_contra hc; push Not at hc
    exact hne (Measure.ext fun A hA => (hc A hA).symm)
  have hAne' : (μ A).toReal ≠ (ν A).toReal := by
    intro he; exact hAne ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 he)
  let F : ℝ → Measure ℝ := fun t => ENNReal.ofReal t • μ + ENNReal.ofReal (1 - t) • ν
  have hF : ∀ t, 0 ≤ t → t ≤ 1 → (F t A).toReal = t * (μ A).toReal + (1 - t) * (ν A).toReal := by
    intro t h0 h1
    simp only [F, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith)]
  refine Set.infinite_of_injOn_mapsTo (s := Set.Icc (0:ℝ) 1) (f := F) ?_ ?_ (Set.Icc_infinite zero_lt_one)
  · intro t ht s hs hts
    have e := congrArg (fun ρ : Measure ℝ => (ρ A).toReal) hts
    rw [hF t ht.1 ht.2, hF s hs.1 hs.2] at e
    have : (t - s) * ((μ A).toReal - (ν A).toReal) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd (by linarith) hAne'
  · intro t ht
    exact convex m μ ν hμ hν t ht.1 ht.2

end HMAux

open HamburgerMoment HMAux in
theorem solution (m : ℕ → ℝ) (μ : Measure ℝ) (hμ : IsMomentMeasure m μ)
    (c : ℕ →₀ ℂ) :
    hankelForm m c =
      ((∫ x, ‖∑ j ∈ c.support, c j * (x : ℂ) ^ j‖ ^ 2 ∂μ : ℝ) : ℂ) :=
  hankelForm_eq_integral' m μ hμ c
