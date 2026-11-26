-- Prove2me | solution 1 for Kyprianou.Ch04.rightContinuousMartingaleCompactBddV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:44:25.804901+00:00
-- url     : https://prove2.me/submissions/d65c59d5-0acd-447d-8a1a-fa665708b5bc

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_dyadicMartingaleL2V1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousDyadicSupV1
import Theorems.Thm_Kyprianou_Ch04_monotoneLIntegralBudgetV1
import Theorems.Thm_Kyprianou_Ch04_ennrealBudgetToRealV1
import Theorems.Thm_Kyprianou_Ch04_finiteExtendedSupToRealV1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a427_dyadic_square_grid_sup_monotone
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Compact-horizon square boundedness of right-continuous square-integrable martingales. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F P) (T : ℝ≥0) (hT : 0 < T)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto (fun s => M s ω)
      (nhdsWithin t (Ioi t)) (nhds (M t ω)))
    (hL2 : Integrable (fun ω => (M T ω)^2) P) :
    ∀ᵐ ω ∂P, BddAbove ((fun t : ℝ≥0 => |M t ω|^2) '' Iic T) := by
  classical
  let g : ℕ → Ω → ℝ := fun k ω =>
    (Finset.range (2^k + 1)).sup' Finset.nonempty_range_add_one
      (fun i => (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)
  let S : Ω → ℝ≥0∞ := fun ω => ⨆ k, ENNReal.ofReal (g k ω)
  let K : ℝ := 4 * ∫ ω, (M T ω)^2 ∂P
  have hg := Kyprianou.Ch04.dyadicMartingaleL2V1 P F M hM T hL2
  have hm (k : ℕ) : Measurable (g k) := by
    dsimp [g]
    apply Finset.measurable_range_sup''
    intro i hi
    exact ((hM.stronglyAdapted _).mono (F.le _)).measurable.pow_const 2
  have hnn (k : ℕ) (ω : Ω) : 0 ≤ g k ω := by
    exact (sq_nonneg _).trans (Finset.le_sup' (f := fun i : ℕ =>
      (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)
      (Finset.mem_range.mpr (by positivity : 0 < 2^k+1)))
  have hmono (ω : Ω) : Monotone (fun k => g k ω) :=
    AvramDividend.Classical.avram_ga_a427_dyadic_square_grid_sup_monotone M T ω
  have hb := Kyprianou.Ch04.monotoneLIntegralBudgetV1 P g K
    (fun k => (hg k).1) hm hnn hmono (fun k => (hg k).2)
  have hSm : Measurable S :=
    Measurable.iSup (fun k => ENNReal.measurable_ofReal.comp (hm k))
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)
  obtain ⟨hSi,hSb,hSf⟩ := Kyprianou.Ch04.ennrealBudgetToRealV1 P S hSm K hK hb
  filter_upwards [hR,hSf] with ω hr hs
  have hc (t : ℝ≥0) : ContinuousWithinAt (fun s => (M s ω)^2) (Ici t) t :=
    (continuousWithinAt_Ioi_iff_Ici.mp (hr t)).pow 2
  have h := Kyprianou.Ch04.rightContinuousDyadicSupV1 (fun t => (M t ω)^2) T hT
    (fun t => sq_nonneg _) hc
  refine ⟨(S ω).toReal,?_⟩
  rintro _ ⟨t,ht,rfl⟩
  have hle : ENNReal.ofReal ((M t ω)^2) ≤ S ω := by
    change ENNReal.ofReal ((M t ω)^2) ≤ ⨆ k, ENNReal.ofReal (g k ω)
    change (⨆ r : Iic T, ENNReal.ofReal ((M r ω)^2)) =
      ⨆ k, ENNReal.ofReal (g k ω) at h
    rw [← h]
    exact le_iSup (fun r : Iic T => ENNReal.ofReal ((M r ω)^2)) ⟨t,ht⟩
  change |M t ω|^2 ≤ (S ω).toReal
  rw [sq_abs]
  simpa [ENNReal.toReal_ofReal (sq_nonneg (M t ω))] using ENNReal.toReal_mono hs.ne hle
