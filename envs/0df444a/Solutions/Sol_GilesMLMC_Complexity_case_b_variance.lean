-- Prove2me | solution 1 for GilesMLMC.Complexity.case_b_variance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:48:06.685573+00:00
-- url     : https://prove2.me/submissions/095bf1fc-caeb-41b8-8a19-0fd77d3ad668

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

set_option autoImplicit false
open GilesMLMC.Complexity

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (β c₂ : ℝ) (hβ : 1 < β) (hc₂ : 0 < c₂)
    (Y : ℕ → ℕ → Ω → ℝ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_iii : ∀ l N, 1 ≤ N →
      ProbabilityTheory.variance (Y l N) μ ≤ c₂ * (N : ℝ)⁻¹ * h M T l ^ β)
    (h_indep : ∀ N : ℕ → ℕ, (∀ l, 1 ≤ N l) →
      ProbabilityTheory.iIndepFun (fun l => Y l (N l)) μ)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) :
    ProbabilityTheory.variance (estimator Y (NB M T β c₂ ε) L) μ < ε ^ 2 / 2 := by
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (β - 1) / 2 := ⟨_, rfl⟩
  have hγpos : 0 < γ := by rw [hγ]; linarith
  have e1 : (β - 1) / 2 = γ := hγ.symm
  have e2 : -(β - 1) / 2 = -γ := by rw [hγ]; ring
  have e3 : (β + 1) / 2 = γ + 1 := by rw [hγ]; ring
  have e4 : β = γ + (γ + 1) := by rw [hγ]; ring
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (M : ℝ) ^ (-γ) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.rpow_pos_of_pos hMpos _
  have hr1 : r < 1 := by rw [hr]; exact Real.rpow_lt_one_of_one_lt_of_neg hM1 (by linarith)
  have hκ : 0 < 1 - r := by linarith
  have hh : ∀ l, 0 < h M T l := by intro l; unfold h; positivity
  have hε2 : ε ^ (-2 : ℝ) = (ε ^ 2)⁻¹ := by
    rw [Real.rpow_neg hε.le, Real.rpow_two]
  have hTγ : 0 < T ^ γ := Real.rpow_pos_of_pos hT _
  -- the real number whose ceiling is N_l
  set a : ℕ → ℝ := fun l => 2 * ε ^ (-2 : ℝ) * c₂ * T ^ γ * (1 - r)⁻¹ * h M T l ^ (γ + 1) with ha
  have hapos : ∀ l, 0 < a l := by
    intro l
    have := Real.rpow_pos_of_pos (hh l) (γ + 1)
    rw [ha]; simp only
    rw [hε2]
    positivity
  have hNB : ∀ l, NB M T β c₂ ε l = ⌈a l⌉₊ := by
    intro l
    simp only [NB, ha]
    rw [e1, e2, e3, ← hr]
  have hN1 : ∀ l, 1 ≤ NB M T β c₂ ε l := fun l => by
    rw [hNB]; exact Nat.one_le_ceil_iff.mpr (hapos l)
  have hNge : ∀ l, a l ≤ (NB M T β c₂ ε l : ℝ) := fun l => by
    rw [hNB]; exact Nat.le_ceil _
  -- h^γ = T^γ r^l
  have hhγ : ∀ l, h M T l ^ γ = T ^ γ * r ^ l := by
    intro l
    have hml : (0 : ℝ) < (M : ℝ) ^ l := by positivity
    have e : r ^ l = (((M : ℝ) ^ l) ^ γ)⁻¹ := by
      rw [hr, ← Real.rpow_natCast ((M : ℝ) ^ (-γ)) l, ← Real.rpow_mul hMpos.le,
        ← Real.rpow_natCast (M : ℝ) l, ← Real.rpow_mul hMpos.le]
      rw [show -γ * (l : ℝ) = -((l : ℝ) * γ) by ring, Real.rpow_neg hMpos.le]
    rw [e]
    unfold h
    rw [Real.div_rpow hT.le hml.le, div_eq_mul_inv]
  -- termwise bound
  have hterm : ∀ l, c₂ * ((NB M T β c₂ ε l : ℕ) : ℝ)⁻¹ * h M T l ^ β ≤
      ε ^ 2 / 2 * (1 - r) * r ^ l := by
    intro l
    have hX := Real.rpow_pos_of_pos (hh l) (γ + 1)
    have hH := Real.rpow_pos_of_pos (hh l) γ
    have hap := hapos l
    have hβh : h M T l ^ β = h M T l ^ γ * h M T l ^ (γ + 1) := by
      rw [e4, Real.rpow_add (hh l)]
    have hNpos : (0 : ℝ) < (NB M T β c₂ ε l : ℝ) := lt_of_lt_of_le hap (hNge l)
    calc c₂ * ((NB M T β c₂ ε l : ℕ) : ℝ)⁻¹ * h M T l ^ β
        ≤ c₂ * (a l)⁻¹ * h M T l ^ β := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos (hh l) β).le
          exact mul_le_mul_of_nonneg_left (inv_anti₀ hap (hNge l)) hc₂.le
      _ = ε ^ 2 / 2 * (1 - r) * r ^ l := by
          rw [hβh, hhγ l, ha]
          simp only
          rw [hε2]
          field_simp
  have hvar : ProbabilityTheory.variance (estimator Y (NB M T β c₂ ε) L) μ =
      ∑ l ∈ Finset.range (L + 1), ProbabilityTheory.variance (Y l (NB M T β c₂ ε l)) μ := by
    have : estimator Y (NB M T β c₂ ε) L =
        ∑ l ∈ Finset.range (L + 1), (fun l => Y l (NB M T β c₂ ε l)) l := by
      funext ω
      simp [estimator, Finset.sum_apply]
    rw [this]
    apply ProbabilityTheory.IndepFun.variance_sum
    · intro l _
      exact hY l _ (hN1 l)
    · intro i _ j _ hij
      exact (h_indep (NB M T β c₂ ε) hN1).indepFun hij
  rw [hvar]
  calc ∑ l ∈ Finset.range (L + 1), ProbabilityTheory.variance (Y l (NB M T β c₂ ε l)) μ
      ≤ ∑ l ∈ Finset.range (L + 1), ε ^ 2 / 2 * (1 - r) * r ^ l := by
        apply Finset.sum_le_sum
        intro l _
        exact (h_iii l _ (hN1 l)).trans (hterm l)
    _ = ε ^ 2 / 2 * (1 - r) * ∑ l ∈ Finset.range (L + 1), r ^ l := by
        rw [Finset.mul_sum]
    _ = ε ^ 2 / 2 * (1 - r ^ (L + 1)) := by
        have := geom_sum_mul_neg r (L + 1)
        calc ε ^ 2 / 2 * (1 - r) * ∑ l ∈ Finset.range (L + 1), r ^ l
            = ε ^ 2 / 2 * ((∑ l ∈ Finset.range (L + 1), r ^ l) * (1 - r)) := by ring
          _ = _ := by rw [this]
    _ < ε ^ 2 / 2 := by
        have : 0 < r ^ (L + 1) := pow_pos hr0 _
        have : 0 < ε ^ 2 / 2 := by positivity
        nlinarith
