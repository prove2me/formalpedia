-- Prove2me | solution 1 for Kyprianou.Ch04.infimumClockWhLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:51:04.579695+00:00
-- url     : https://prove2.me/submissions/9828a8ea-e2a3-4582-9214-bbe0469459e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_positiveRootSequenceWhLimit
import Theorems.Thm_Kyprianou_Ch04_clockRunningInfimumWienerHopfTransform
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The nonsingular product-clock infimum transform converges to the scalar quotient. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator : ¬ (∀ᵐ w : Ω ∂P, Antitone (fun t : NNReal => L.X t w)))
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hq0 : Tendsto q atTop (nhds 0))
    (beta : ℝ) (hb : 0 < beta) (hpsi : L.ψ beta ≠ 0) :
    Tendsto (fun n : ℕ => ∫ z : Ω × ℝ, Real.exp (beta * sInf ((fun s : NNReal => L.X s z.1) '' Iic z.2.toNNReal))
      ∂(P.prod (expMeasure (q n)))) atTop (nhds (max 0 (sInf ((fun theta : ℝ => L.ψ theta / theta) '' Ioi 0)) * beta / L.ψ beta)) := by
  obtain ⟨r,hr,hroot,hW⟩ := Kyprianou.Ch04.positiveRootSequenceWhLimit
    P F L hNotNegativeSubordinator q hq hq0 beta hpsi
  have hevent : ∀ᶠ n in atTop, q n ≠ L.ψ beta := by
    by_cases h : 0 < L.ψ beta
    · filter_upwards [hq0.eventually_lt_const h] with n hn
      exact hn.ne
    · exact Eventually.of_forall (fun n he => h (he ▸ hq n))
  apply hW.congr'
  filter_upwards [hevent] with n hn
  have hne : beta ≠ r n := by
    intro he
    exact hn ((hroot n).symm.trans (congrArg L.ψ he.symm))
  exact (Kyprianou.Ch04.clockRunningInfimumWienerHopfTransform
    P F L (q n) (r n) beta (hq n) (hr n) (hroot n) hb hne).symm
