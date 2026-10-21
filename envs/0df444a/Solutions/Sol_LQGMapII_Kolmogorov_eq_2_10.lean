-- Prove2me | solution 1 for LQGMapII.Kolmogorov.eq_2_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:53:18.933886+00:00
-- url     : https://prove2.me/submissions/8a6d6a6f-f1dc-40b1-810d-643a3818eaf7

import Mathlib
import Definitions.Def_LQGMapII_Kolmogorov_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory LQGMapII.Kolmogorov
open scoped NNReal ENNReal

theorem kc_cheb {d : ℕ} {α β : ℝ} {c₀ : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) 
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Cube d → Ω → ℝ) (hX : IsKolmogorovProcess X P α ((d : ℝ) + β) c₀)
    (u v : Cube d) (δ : ℝ) (hδ : 0 < δ) :
    P {ω | δ ≤ |X u ω - X v ω|} ≤
      ENNReal.ofReal ((c₀ : ℝ) * δ ^ (-α) * dist u v ^ ((d : ℝ) + β)) := by
  set ε : ℝ≥0∞ := ENNReal.ofReal δ ^ α with hε
  have hε0 : ε ≠ 0 := by
    have : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
    exact (ENNReal.rpow_pos this ENNReal.ofReal_ne_top).ne'
  have hεt : ε ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hα.le ENNReal.ofReal_ne_top
  have hmeas : Measurable (fun ω => edist (X u ω) (X v ω)) := hX.measurable_edist
  have hsub : {ω | δ ≤ |X u ω - X v ω|} ⊆
      {ω | ε ≤ edist (X u ω) (X v ω) ^ α} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hε]
    apply ENNReal.rpow_le_rpow _ hα.le
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal hω
  have hmark := mul_meas_ge_le_lintegral₀ (μ := P)
    ((hmeas.pow_const α).aemeasurable) ε
  have hk := hX.kolmogorovCondition u v
  have h1 : ε * P {ω | δ ≤ |X u ω - X v ω|} ≤ (c₀ : ℝ≥0∞) * edist u v ^ ((d : ℝ) + β) :=
    calc ε * P {ω | δ ≤ |X u ω - X v ω|} ≤ ε * P {ω | ε ≤ edist (X u ω) (X v ω) ^ α} := by
          gcongr
      _ ≤ _ := hmark
      _ ≤ _ := hk
  rw [ENNReal.mul_le_iff_le_inv hε0 hεt] at h1
  refine h1.trans (le_of_eq ?_)
  have hdist : edist u v = ENNReal.ofReal (dist u v) := edist_dist u v
  have hq : (0:ℝ) ≤ (d : ℝ) + β := by positivity
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), hdist,
    ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hq, Real.rpow_neg hδ.le,
    ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_rpow_of_pos hδ, ENNReal.ofReal_coe_nnreal,
    hε]
  ring


lemma kc_dist_adj {d k : ℕ} {u v : Cube d} (h : IsAdjacentPair d k u v) :
    dist u v = (2 : ℝ)⁻¹ ^ k := by
  obtain ⟨_, _, i, hi, hd⟩ := h
  rw [Subtype.dist_eq, EuclideanSpace.dist_eq]
  rw [Finset.sum_eq_single i]
  · rw [Real.dist_eq, sq_abs, Real.sqrt_sq_eq_abs, hd]
  · intro j _ hj
    rw [hi j hj]; simp
  · intro h; exact absurd (Finset.mem_univ i) h

theorem solution {d : ℕ} {α β γ : ℝ} {c₀ : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) (hc₀ : 0 < c₀)
    (hγ : 0 < γ) (hγβ : γ < β / α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Cube d → Ω → ℝ) (hX : IsKolmogorovProcess X P α ((d : ℝ) + β) c₀)
    (k : ℕ) (u v : Cube d) (huv : IsAdjacentPair d k u v) (t : ℝ) (ht : 0 < t) :
    P {ω | t * (2 : ℝ) ^ (-(γ * k)) ≤ |X u ω - X v ω|} ≤
      ENNReal.ofReal ((c₀ : ℝ) * t ^ (-α) * (2 : ℝ) ^ (-((k : ℝ) * ((d : ℝ) + β - α * γ)))) := by
  have h2 : (0:ℝ) < (2:ℝ) ^ (-(γ * k)) := by positivity
  have := kc_cheb hα hβ P X hX u v (t * (2 : ℝ) ^ (-(γ * k))) (by positivity)
  refine this.trans (le_of_eq ?_)
  congr 1
  rw [kc_dist_adj huv, Real.mul_rpow ht.le h2.le, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have e1 : ((2:ℝ)⁻¹ ^ k) = (2:ℝ) ^ (-(k:ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  rw [e1, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have e2 : (2:ℝ) ^ (-(γ * k) * -α) * (2:ℝ) ^ (-(k:ℝ) * ((d:ℝ) + β)) = (2:ℝ) ^ (-((k : ℝ) * ((d : ℝ) + β - α * γ))) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1; ring
  rw [← e2]
  ring
