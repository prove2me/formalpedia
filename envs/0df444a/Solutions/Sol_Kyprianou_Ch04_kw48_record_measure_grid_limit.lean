-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_record_measure_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:46:10.704022+00:00
-- url     : https://prove2.me/submissions/361a6aeb-abbd-4b06-8e17-8c619404a6a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_Kyprianou_Ch04_kw48_complex_quadrature
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Convert record-measure quadrature weights to actual record increments. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (w : Ω) (a b : NNReal)
    (f : Real → Complex) (B : Real)
    (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ B)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1):Real)-(u n i:Real) ≤ delta n)
    (right : Bool)
    (hCont : ∀ᵐ x ∂((dividendMeasure (runningSup L) w).restrict
      (Ioc (a:Real) (b:Real))),
      ContinuousWithinAt f (if right then Ici x else Iic x) x) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (runningSup L (u n (i+1)) w-runningSup L (u n i) w) •
        f (if right then (u n (i+1):Real) else (u n i:Real))) atTop
      (nhds (∫ x in Ioc (a:Real) (b:Real), f x
        ∂(dividendMeasure (runningSup L) w))) := by
  let mu := dividendMeasure (runningSup L) w
  letI : IsFiniteMeasure (mu.restrict (Ioc (a:Real) (b:Real))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
        dsimp only [mu]
        rw [runningSup_dividendMeasure_Ioc_eq_record_increment]
        exact ENNReal.ofReal_lt_top⟩
  have hm (r s : NNReal) (hrs : r ≤ s) :
      (mu (Ioc (r:Real) (s:Real))).toReal =
        runningSup L s w - runningSup L r w := by
    dsimp only [mu]
    rw [runningSup_dividendMeasure_Ioc_eq_record_increment,
      Real.toNNReal_coe, Real.toNNReal_coe, ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr ((runningSup_monotone_and_path_le L w).1 hrs)
  have hmono (n : Nat) : Monotone (fun i => (u n i:Real)) :=
    fun i j hij => by exact_mod_cast hu n hij
  have h := Kyprianou.Ch04.kw48_complex_quadrature mu (a:Real) (b:Real)
    f B hf hB (fun n i => (u n i:Real)) N hmono
    (fun n => by rw [h0 n]) (fun n => by rw [hN n])
    delta hDelta hMesh right hCont
  have hcell (n i : Nat) := hm (u n i) (u n (i+1)) (hu n (Nat.le_succ i))
  simpa only [hcell] using h
