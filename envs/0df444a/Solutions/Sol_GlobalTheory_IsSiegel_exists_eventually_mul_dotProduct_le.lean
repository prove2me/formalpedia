-- Prove2me | solution 1 for GlobalTheory.IsSiegel.exists_eventually_mul_dotProduct_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:40.134313+00:00
-- url     : https://prove2.me/submissions/1b7d1327-b34d-4945-b3b8-ebd28bb13449

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) :
    ∃ c > 0, ∀ᶠ Ω' in 𝓝 Ω, ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Matrix.map Ω' Complex.im *ᵥ x) := by
  obtain ⟨c, hc, hY⟩ := posDef_exists_mul_dotProduct_le h.posDef
  set N : ℝ := Fintype.card ι + 1 with hN
  have hN0 : 0 < N := by positivity
  refine ⟨c / 2, by positivity, ?_⟩
  have hev : ∀ᶠ Ω' in 𝓝 Ω, ∀ i j, |(Ω' i j).im - (Ω i j).im| < c / (2 * N) := by
    simp only [eventually_all]
    intro i j
    have hc' : Continuous fun Ω' : Matrix ι ι ℂ => |(Ω' i j).im - (Ω i j).im| := by
      have : Continuous fun Ω' : Matrix ι ι ℂ => Ω' i j := continuous_id.matrix_elem i j
      fun_prop
    exact hc'.continuousAt.eventually_lt continuousAt_const (by simp; positivity)
  filter_upwards [hev] with Ω' hΩ' x
  have h1 : x ⬝ᵥ (Ω.map Complex.im *ᵥ x) - x ⬝ᵥ (Matrix.map Ω' Complex.im *ᵥ x) ≤
      ∑ i, ∑ j, c / (2 * N) * ((x i * x i + x j * x j) / 2) := by
    simp only [dotProduct, mulVec, map_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    obtain ⟨l, r⟩ := abs_lt.mp (hΩ' i j)
    nlinarith [mul_nonneg (sub_nonneg.mpr l.le) (sq_nonneg (x i - x j)),
      mul_nonneg (sub_nonneg.mpr r.le) (sq_nonneg (x i + x j))]
  have h2 : ∑ i, ∑ j, c / (2 * N) * ((x i * x i + x j * x j) / 2) =
      c / (2 * N) * (Fintype.card ι * (x ⬝ᵥ x)) := by
    simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, dotProduct]
    simp only [mul_left_comm (x _) (Fintype.card ι : ℝ), ← Finset.mul_sum]
    ring
  have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h3 : c / (2 * N) * (Fintype.card ι * (x ⬝ᵥ x)) ≤ c / 2 * (x ⬝ᵥ x) := by
    calc _ ≤ c / (2 * N) * (N * (x ⬝ᵥ x)) := by gcongr; linarith
      _ = _ := by field_simp
  linarith [hY x]
end IsSiegel
end GlobalTheory
