-- Prove2me | solution 1 for GilesMLMC.Complexity.case_c_variance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:49:37.691704+00:00
-- url     : https://prove2.me/submissions/6b701451-977e-4ae4-b5b0-2dce310a59ba

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

set_option autoImplicit false
open GilesMLMC.Complexity

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (β c₂ : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hc₂ : 0 < c₂)
    (Y : ℕ → ℕ → Ω → ℝ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_iii : ∀ l N, 1 ≤ N →
      ProbabilityTheory.variance (Y l N) μ ≤ c₂ * (N : ℝ)⁻¹ * h M T l ^ β)
    (h_indep : ∀ N : ℕ → ℕ, (∀ l, 1 ≤ N l) →
      ProbabilityTheory.iIndepFun (fun l => Y l (N l)) μ)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) :
    ProbabilityTheory.variance (estimator Y (NC M T β c₂ ε L) L) μ < ε ^ 2 / 2 := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (1 - β) / 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have e2 : -(1 - β) / 2 = -δ := by rw [hδ]; ring
  have e3 : (β + 1) / 2 = 1 - δ := by rw [hδ]; ring
  have e4 : β = -δ + (1 - δ) := by rw [hδ]; ring
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (M : ℝ) ^ (-δ) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.rpow_pos_of_pos hMpos _
  have hr1 : r < 1 := by rw [hr]; exact Real.rpow_lt_one_of_one_lt_of_neg hM1 (by linarith)
  have hκ : 0 < 1 - r := by linarith
  have hh : ∀ l, 0 < h M T l := by intro l; unfold h; positivity
  have hε2 : ε ^ (-2 : ℝ) = (ε ^ 2)⁻¹ := by
    rw [Real.rpow_neg hε.le, Real.rpow_two]
  have hTδ : 0 < T ^ (-δ) := Real.rpow_pos_of_pos hT _
  -- h_l^(-δ) = T^(-δ) / r^l
  have hhδ : ∀ l, h M T l ^ (-δ) = T ^ (-δ) / r ^ l := by
    intro l
    have hml : (0 : ℝ) < (M : ℝ) ^ l := by positivity
    have e : r ^ l = ((M : ℝ) ^ l) ^ (-δ) := by
      rw [hr, ← Real.rpow_natCast ((M : ℝ) ^ (-δ)) l, ← Real.rpow_mul hMpos.le,
        ← Real.rpow_natCast (M : ℝ) l, ← Real.rpow_mul hMpos.le]
      congr 1; ring
    rw [e]
    unfold h
    rw [Real.div_rpow hT.le hml.le]
  set a : ℕ → ℝ := fun l => 2 * ε ^ (-2 : ℝ) * c₂ * h M T L ^ (-δ) * (1 - r)⁻¹ *
    h M T l ^ (1 - δ) with ha
  have hapos : ∀ l, 0 < a l := by
    intro l
    have h1 := Real.rpow_pos_of_pos (hh l) (1 - δ)
    have h2 := Real.rpow_pos_of_pos (hh L) (-δ)
    rw [ha]; simp only
    rw [hε2]
    positivity
  have hNC : ∀ l, NC M T β c₂ ε L l = ⌈a l⌉₊ := by
    intro l
    simp only [NC, ha]
    rw [e2, e3, ← hr]
  have hN1 : ∀ l, 1 ≤ NC M T β c₂ ε L l := fun l => by
    rw [hNC]; exact Nat.one_le_ceil_iff.mpr (hapos l)
  have hNge : ∀ l, a l ≤ (NC M T β c₂ ε L l : ℝ) := fun l => by
    rw [hNC]; exact Nat.le_ceil _
  have hterm : ∀ l, l ≤ L → c₂ * ((NC M T β c₂ ε L l : ℕ) : ℝ)⁻¹ * h M T l ^ β ≤
      ε ^ 2 / 2 * (1 - r) * r ^ (L - l) := by
    intro l hl
    have hX := Real.rpow_pos_of_pos (hh l) (1 - δ)
    have hap := hapos l
    have hβh : h M T l ^ β = h M T l ^ (-δ) * h M T l ^ (1 - δ) := by
      rw [e4, Real.rpow_add (hh l)]
    calc c₂ * ((NC M T β c₂ ε L l : ℕ) : ℝ)⁻¹ * h M T l ^ β
        ≤ c₂ * (a l)⁻¹ * h M T l ^ β := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos (hh l) β).le
          exact mul_le_mul_of_nonneg_left (inv_anti₀ hap (hNge l)) hc₂.le
      _ = ε ^ 2 / 2 * (1 - r) * r ^ (L - l) := by
          rw [hβh, hhδ l, ha]
          simp only
          rw [hhδ L, hε2, pow_sub₀ r hr0.ne' hl]
          field_simp
  have hvar : ProbabilityTheory.variance (estimator Y (NC M T β c₂ ε L) L) μ =
      ∑ l ∈ Finset.range (L + 1), ProbabilityTheory.variance (Y l (NC M T β c₂ ε L l)) μ := by
    have : estimator Y (NC M T β c₂ ε L) L =
        ∑ l ∈ Finset.range (L + 1), (fun l => Y l (NC M T β c₂ ε L l)) l := by
      funext ω
      simp [estimator, Finset.sum_apply]
    rw [this]
    apply ProbabilityTheory.IndepFun.variance_sum
    · intro l _
      exact hY l _ (hN1 l)
    · intro i _ j _ hij
      exact (h_indep (NC M T β c₂ ε L) hN1).indepFun hij
  have hrefl : ∑ l ∈ Finset.range (L + 1), r ^ (L - l) = ∑ l ∈ Finset.range (L + 1), r ^ l := by
    have := Finset.sum_range_reflect (fun j => r ^ j) (L + 1)
    simpa using this
  rw [hvar]
  calc ∑ l ∈ Finset.range (L + 1), ProbabilityTheory.variance (Y l (NC M T β c₂ ε L l)) μ
      ≤ ∑ l ∈ Finset.range (L + 1), ε ^ 2 / 2 * (1 - r) * r ^ (L - l) := by
        apply Finset.sum_le_sum
        intro l hl
        exact (h_iii l _ (hN1 l)).trans (hterm l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)))
    _ = ε ^ 2 / 2 * (1 - r) * ∑ l ∈ Finset.range (L + 1), r ^ (L - l) := by
        rw [Finset.mul_sum]
    _ = ε ^ 2 / 2 * (1 - r ^ (L + 1)) := by
        rw [hrefl]
        have := geom_sum_mul_neg r (L + 1)
        calc ε ^ 2 / 2 * (1 - r) * ∑ l ∈ Finset.range (L + 1), r ^ l
            = ε ^ 2 / 2 * ((∑ l ∈ Finset.range (L + 1), r ^ l) * (1 - r)) := by ring
          _ = _ := by rw [this]
    _ < ε ^ 2 / 2 := by
        have : 0 < r ^ (L + 1) := pow_pos hr0 _
        have : 0 < ε ^ 2 / 2 := by positivity
        nlinarith
