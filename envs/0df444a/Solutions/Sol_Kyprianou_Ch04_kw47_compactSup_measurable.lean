-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_compactSup_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:48:12.897115+00:00
-- url     : https://prove2.me/submissions/99abe78e-9976-4491-81db-3c013d89de0d

import Theorems.Thm_Kyprianou_Ch04_kw47_bounded_primitive_continuous
import Theorems.Thm_Kyprianou_Ch04_kw47_bounded_primitive_sections_measurable
import Theorems.Thm_Kyprianou_Ch04_kw47_bounded_right_continuous_sup_measurable
import Theorems.Thm_Kyprianou_Ch04_kw47_pointwise_envelope
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_bounds
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem measurable_abs_runningSup_aux
    {Omega : Type} [MeasurableSpace Omega]
    (Z U : NNReal → Omega → Real) (psi alpha : Real)
    (hZ : Measurable (fun z : NNReal × Omega => Z z.1 z.2))
    (hU : Measurable (fun z : NNReal × Omega => U z.1 z.2))
    (hZbound : ∀ (r : NNReal) (w : Omega), ‖Z r w‖ ≤ 1)
    (hZright : ∀ w r, ContinuousWithinAt (fun s => Z s w) (Set.Ici r) r)
    (hUright : ∀ w r, ContinuousWithinAt (fun s => U s w) (Set.Ici r) r)
    (t : NNReal)
    (hB : ∀ w : Omega, BddAbove ((fun r : NNReal =>
      |psi * (∫ s in Set.Icc (0 : Real) (r : Real),
        Z s.toNNReal w ∂volume) + 1 - Z r w - alpha * U r w|) '' Set.Iic t)) :
    Measurable (fun w : Omega => sSup ((fun r : NNReal =>
      |psi * (∫ s in Set.Icc (0 : Real) (r : Real),
        Z s.toNNReal w ∂volume) + 1 - Z r w - alpha * U r w|) '' Set.Iic t)) := by
  let J := fun (r : NNReal) (w : Omega) =>
    ∫ s in Set.Icc (0 : Real) (r : Real), Z s.toNNReal w ∂volume
  let M := fun (r : NNReal) (w : Omega) => psi * J r w + 1 - Z r w - alpha * U r w
  have hZ' : Measurable (fun z : Real × Omega => Z z.1.toNNReal z.2) :=
    hZ.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hJ (r : NNReal) : Measurable (J r) :=
    Kyprianou.Ch04.kw47_bounded_primitive_sections_measurable _ hZ' r
  have hMr (w : Omega) (r : NNReal) :
      ContinuousWithinAt (fun s => M s w) (Set.Ici r) r := by
    have hSlice : Measurable (fun s : Real => ((s, w) : Real × Omega)) :=
      measurable_id.prodMk measurable_const
    have hf : Measurable (fun s : Real => Z s.toNNReal w) := hZ'.comp hSlice
    have hj : Continuous (fun q : NNReal =>
        ∫ s in Set.Icc (0 : Real) (q : Real),
          Z s.toNNReal w ∂volume) :=
      Kyprianou.Ch04.kw47_bounded_primitive_continuous
        (fun s => Z s.toNNReal w) hf (fun s => hZbound s.toNNReal w)
    exact (((continuousWithinAt_const.mul hj.continuousWithinAt).add
      continuousWithinAt_const).sub (hZright w r)).sub
      (continuousWithinAt_const.mul (hUright w r))
  have hMm (r : NNReal) : Measurable (M r) :=
    (((measurable_const.mul (hJ r)).add measurable_const).sub
      (hZ.comp (measurable_const.prodMk measurable_id))).sub
      (measurable_const.mul (hU.comp (measurable_const.prodMk measurable_id)))
  change Measurable (fun w => sSup ((fun r => |M r w|) '' Set.Iic t))
  exact Kyprianou.Ch04.kw47_bounded_right_continuous_sup_measurable
    (fun r w => |M r w|)
    (fun r => (hMm r).abs) (fun w r => (hMr w r).abs) t hB

theorem solution :
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha),
    let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let M : NNReal -> Omega -> Real := fun t omega =>
          L.ψ alpha * (∫ s in Set.Icc (0 : Real) (t : Real),
            Real.exp (-alpha * (supX (Real.toNNReal s) omega -
                               L.X (Real.toNNReal s) omega)) ∂volume) +
          1 - Real.exp (-alpha * (supX t omega - L.X t omega)) -
          alpha * supX t omega
        ∀ t : NNReal, Measurable (fun omega : Omega => sSup ((fun s : NNReal => |M s omega|) '' Set.Iic t)) := by
  intro Omega inst P F L alpha hAlpha
  dsimp only; intro t
  let U : NNReal → Omega → Real := fun r w =>
    sSup ((fun s : NNReal => L.X s w) '' Set.Iic r)
  let Z : NNReal → Omega → Real := fun r w =>
    Real.exp (-alpha * (U r w - L.X r w))
  have hU : Measurable (fun z : NNReal × Omega => U z.1 z.2) := by
    simpa only [Kyprianou.Ch04.kw47_runningSup_raw_eq L] using
      levy_runningSup_joint_time_path_measurable L
  have hX := chat04_levy_joint_time_state_measurable L
  have hZ : Measurable (fun z : NNReal × Omega => Z z.1 z.2) :=
    (measurable_const.mul (hU.sub hX)).exp
  have hUright (w : Omega) (r : NNReal) :
      ContinuousWithinAt (fun s => U s w) (Set.Ici r) r := by
    simpa only [Kyprianou.Ch04.kw47_runningSup_raw_eq L] using
      runningSup_right_continuous_actual L w r
  have hZright (w : Omega) (r : NNReal) :
      ContinuousWithinAt (fun s => Z s w) (Set.Ici r) r := by
    have hCore : ContinuousWithinAt
        (fun s : NNReal => (-alpha) * (U s w - L.X s w)) (Set.Ici r) r :=
      continuousWithinAt_const.mul ((hUright w r).sub (L.rightCont w r))
    exact (Real.continuous_exp.tendsto _).comp hCore
  have hZbound (r : NNReal) (w : Omega) : ‖Z r w‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    simpa only [Kyprianou.Ch04.kw47_runningSup_raw_eq L] using
      (Kyprianou.Ch04.kw47_reflected_exp_bounds L alpha hAlpha r w).2
  have hb (w : Omega) : BddAbove ((fun r : NNReal =>
      |L.ψ alpha * (∫ s in Set.Icc (0 : Real) (r : Real),
        Z s.toNNReal w ∂volume) + 1 - Z r w - alpha * U r w|)
      '' Set.Iic t) := by
    refine ⟨|L.ψ alpha| * (t : Real) + 2 + alpha * U t w, ?_⟩
    rintro y ⟨r, hr, rfl⟩
    exact Kyprianou.Ch04.kw47_pointwise_envelope P F L alpha hAlpha t r w hr
  exact measurable_abs_runningSup_aux Z U (L.ψ alpha) alpha
    hZ hU hZbound hZright hUright t hb
