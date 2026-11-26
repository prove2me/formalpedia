-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_grid_energy_tightness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:15:48.544023+00:00
-- url     : https://prove2.me/submissions/60cc2a24-c8bd-47a6-90af-926fa6e248a9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_localised_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_cosine_mean_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_kernel_measurable_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_joint_version
import Theorems.Thm_Kyprianou_Ch04_ito43_real_measurable_tail
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_event_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_markov_bound
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Uniform tightness of stopped squared-increment sums for an arbitrary real Levy process. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (tr : LevyKhintchineTriple)
    (hc : ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ))
    (T : NNReal) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (P {w | ∃ t : NNReal, t ≤ T ∧
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        C ≤ ∑ k ∈ Finset.range n, (X (v (k+1)) w - X (v k) w)^2}).toReal ≤ η := by
  obtain ⟨Y,hY,hEq,hCad⟩ := Kyprianou.Ch04.ito43_levy_joint_version P X hX
  obtain ⟨M,hM,hm0,hm⟩ := Kyprianou.Ch04.ito43_kernel_measurable_bound P Y hY hCad
    (fun z : ℝ × ℝ => z.2) continuous_snd.continuousOn T
  obtain ⟨r,hr,hrM⟩ := Kyprianou.Ch04.ito43_real_measurable_tail P M hM (η/2) (by positivity)
  let R : NNReal := Real.toNNReal (2*r)
  have hR : (R : ℝ) = 2*r := Real.coe_toNNReal _ (by positivity)
  have hRp : 0 < R := by exact_mod_cast (show 0 < (R : ℝ) by rw [hR]; positivity)
  let ξ : ℝ := 1/(R : ℝ)
  let L : ℝ := ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖
  let K : ℝ := 2*(T : ℝ)*L
  let D : ℝ := 2*K/η+1
  let A : ℝ := Real.pi^2*(R : ℝ)^2/2
  have hK : 0 ≤ K := by dsimp [K,L]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A*D+(R : ℝ)^2+1,by positivity,?_⟩
  have hfine : ∀ᶠ n : ℕ in atTop, (T : ℝ)/(n : ℝ)*L ≤ 1 := by
    have hl := (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).mul_const L
    rw [zero_mul] at hl
    exact (hl.eventually (gt_mem_nhds zero_lt_one)).mono fun n hn => hn.le
  filter_upwards [eventually_gt_atTop (0 : ℕ),hfine] with n hn hfine
  obtain ⟨hFi,hF0,hFmean⟩ := Kyprianou.Ch04.ito43_grid_cosine_mean_bound P X hX tr hc T ξ n hn hfine
  have henv : ∀ᵐ w ∂P, ∀ a ≤ T, |X a w| ≤ M w := by
    filter_upwards [hEq] with w hw
    intro a ha
    have H := hm w 0 ⟨le_rfl,T.coe_nonneg⟩ a ha
    rw [hw a] at H
    exact H
  have hW := Kyprianou.Ch04.ito43_grid_energy_event_bound P X M T R hRp r D hR henv n hn
  have hV := Kyprianou.Ch04.ito43_grid_energy_markov_bound P _ hFi hF0 K η hK hη hFmean
  exact hW.trans (by linarith [hrM,hV])
