-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_excess_small_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:30:49.989713+00:00
-- url     : https://prove2.me/submissions/8f957599-803b-4b09-a7b4-cca0949d382e

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_small_tail_pathwise
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_tightness
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_jump_energy_localisation
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_joint_version
import Theorems.Thm_Kyprianou_Ch04_ito43_kernel_measurable_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_real_measurable_tail
import Theorems.Thm_Kyprianou_Ch04_ito43_localised_two_energy_tail
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Localise path range, stopped grid energy and actual jump energy. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    (f : Real × Real -> Real)
    (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (hfSpaceC2 : forall s : NNReal,
      ContDiff Real 2 (fun x : Real => f ((s : Real), x)))
    (hfSpaceSecondContinuous :
      ContinuousOn
        (fun z : Real × Real =>
          iteratedDeriv 2 (fun x : Real => f (z.1, x)) z.2)
        (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    ∀ (T : NNReal) (epsilon : ℝ), 0 < epsilon → ∀ eta : ℝ, 0 < eta →
      ∃ m : ℕ, ∀ᶠ n : ℕ in atTop,
        (P {omega : Omega | ∃ t : NNReal, t ≤ T ∧
          let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
          let v : ℕ → NNReal := fun k => min t (u k)
          let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
          epsilon ≤ |((∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega)) - (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - ((∑ k ∈ Finset.range n,
          (f ((v k : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v k) omega) -
          deriv (fun x : Real => f ((u k : Real), x)) (X (u k) omega) *
            (X (v (k+1)) omega - X (v k) omega))) - (∑ k ∈ Finset.range n,
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * (X (v (k+1)) omega - X (v k) omega)^2 / 2))) - ((∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
       (f (z.1,Xleft (Real.toNNReal z.1) omega + z.2) -
        f (z.1,Xleft (Real.toNNReal z.1) omega) -
        z.2 * fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) omega) (0,1) -
        iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2)
          * chi z.2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
       let dx := X (v (k+1)) omega - X (v k) omega
       (f ((v k : ℝ),X (v (k+1)) omega) - f ((v k : ℝ),X (v k) omega) -
        deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx -
        iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx^2 / 2)
          * chi dx))|}).toReal ≤ eta := by
  intro T e he eta heta
  let H : NNReal := T+1
  have hTH : T ≤ H := le_self_add
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨Y,hY,hEq,hCad⟩ := Kyprianou.Ch04.ito43_levy_joint_version P X hLevy
  obtain ⟨M,hM,hm0,hm⟩ := Kyprianou.Ch04.ito43_kernel_measurable_bound P Y hY hCad
    (fun z : ℝ × ℝ => z.2) continuous_snd.continuousOn H
  obtain ⟨r,hr,hrM⟩ := Kyprianou.Ch04.ito43_real_measurable_tail P M hM (eta/3) (by positivity)
  obtain ⟨C,hC,hQ⟩ := Kyprianou.Ch04.ito43_grid_energy_tightness P X hLevy
    triplet hTriplet T (eta/3) (by positivity)
  obtain ⟨D,hD,hJ⟩ := (Kyprianou.Ch04.ito43_levy_jump_energy_localisation P X Xleft
    hLevy triplet hTriplet hLeft H hH).2 (eta/3) (by positivity)
  let a := e/(2*(C+D))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨m,hpath⟩ := Kyprianou.Ch04.ito43_spatial_small_tail_pathwise P X hLevy triplet
    hTriplet Xleft hLeft f hfJointC1 hfSpaceC2 hfSpaceSecondContinuous T H hTH r a ha
  refine ⟨m,?_⟩
  let U : Set Omega := {w | r < M w}
  let J : Omega → (Set.Ioc (0 : NNReal) H → ℝ) := fun w s => (X s w-Xleft s w)^2
  let V : Set Omega := {w | ¬ Summable (J w) ∨ D < ∑' s, J w s}
  let Q : ℕ → NNReal → Omega → ℝ := fun n t w =>
    ∑ k ∈ Finset.range n, (X (min t (T*((k+1 : ℕ) : NNReal)/(n : NNReal))) w -
      X (min t (T*(k : NNReal)/(n : NNReal))) w)^2
  have heq : a*(C+D) = e/2 := by dsimp [a]; field_simp
  have hsmall : a*(C+D) < e := by rw [heq]; linarith
  apply Kyprianou.Ch04.ito43_localised_two_energy_tail P T U V Q _
    (fun w => ∑' s, J w s) C D a e eta ha.le hsmall hrM.le hJ hQ
  filter_upwards [hEq,hLevy.cadlag_ae,hLeft] with w hw hcad hl
  intro hU hV
  have hbound (s : NNReal) (hs : s ≤ H) : |X s w| ≤ r := by
    have h := hm w 0 ⟨le_rfl,H.coe_nonneg⟩ s hs
    rw [hw s] at h
    exact h.trans (le_of_not_gt hU)
  have hs : Summable (J w) := by
    by_contra h; exact hV (Or.inl h)
  exact ⟨le_of_not_gt (fun h => hV (Or.inr h)),hpath w hcad hl hbound hs⟩
