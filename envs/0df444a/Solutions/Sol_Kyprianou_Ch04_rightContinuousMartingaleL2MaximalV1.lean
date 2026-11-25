-- Prove2me | solution 1 for Kyprianou.Ch04.rightContinuousMartingaleL2MaximalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:31:51.817223+00:00
-- url     : https://prove2.me/submissions/ddb3f424-0b4e-48a7-9004-1a4a4ec416f7

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

/-- Doob's L2 maximal estimate for almost surely right-continuous martingales. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M F P) (T : ℝ≥0) (hT : 0 < T)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto (fun s => M s ω)
      (nhdsWithin t (Ioi t)) (nhds (M t ω)))
    (hL2 : Integrable (fun ω => (M T ω)^2) P) :
    Integrable (fun ω => sSup ((fun t : ℝ≥0 => |M t ω|^2) '' Iic T)) P ∧
      (∫ ω, sSup ((fun t : ℝ≥0 => |M t ω|^2) '' Iic T) ∂P) ≤
        4 * ∫ ω, (M T ω)^2 ∂P := by
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
  have heq : (fun ω => sSup ((fun t : ℝ≥0 => |M t ω|^2) '' Iic T)) =ᵐ[P]
      fun ω => (S ω).toReal := by
    filter_upwards [hR,hSf] with ω hr hs
    have hc (t : ℝ≥0) : ContinuousWithinAt (fun s => (M s ω)^2) (Ici t) t :=
      (continuousWithinAt_Ioi_iff_Ici.mp (hr t)).pow 2
    have h := Kyprianou.Ch04.rightContinuousDyadicSupV1 (fun t => (M t ω)^2) T hT
      (fun t => sq_nonneg _) hc
    simp only [sq_abs]
    exact Kyprianou.Ch04.finiteExtendedSupToRealV1 _ T (fun t => sq_nonneg _) (S ω) hs h
  exact ⟨hSi.congr heq.symm, (integral_congr_ae heq).trans_le hSb⟩
