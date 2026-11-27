-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_error_path_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:21:29.310401+00:00
-- url     : https://prove2.me/submissions/43241ad3-4493-4f39-9729-d8e8e76c6c3b

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_time_path_regular
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_jump_path_regular
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_grid_path_regular
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_jump_energy_localisation
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution  {Omega : Type} [MeasurableSpace Omega]
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
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :
    ∀ T : NNReal,
    let B : ℕ → NNReal → Omega → ℝ := fun n t omega =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ((triplet.gaussianVariance : ℝ) / 2) *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) omega) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      g (z.1,Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
      g ((u k : ℝ), X (u k) omega) * (X (v (k+1)) omega - X (v k) omega)^2 / 2)
    ∀ᵐ w ∂P, ∀ n,
      (∀ t, ContinuousWithinAt (fun s => |B n s w|) (Set.Ici t) t) ∧
      BddAbove (Set.range (fun t : Set.Iic T => |B n t w|)) := by
  intro T B
  have hE (j : ℕ) := (ito43_levy_jump_energy_localisation P X Xleft hLevy triplet hTriplet hLeft
    ((j:NNReal)+1) (by positivity)).1
  have hAll : ∀ᵐ w ∂P, ∀ j : ℕ, Summable (fun s : Ioc (0:NNReal) ((j:NNReal)+1) =>
      (X s w-Xleft s w)^2) := ae_all_iff.mpr hE
  filter_upwards [hLevy.cadlag_ae,hLeft,hAll] with w hc hl hs
  have hS (H : NNReal) : Summable (fun s : Ioc (0:NNReal) H => (X s w-Xleft s w)^2) := by
    obtain ⟨j,hj⟩ := exists_nat_gt H
    let f : Ioc (0:NNReal) H → Ioc (0:NNReal) ((j:NNReal)+1) :=
      fun s => ⟨s.1,s.2.1,s.2.2.trans (hj.le.trans (le_self_add))⟩
    have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg (fun s : Ioc (0:NNReal) ((j:NNReal)+1) => (s:NNReal)) h)
    have hh := (hs j).comp_injective hf
    exact hh
  let I : NNReal → ℝ := fun t =>
    ∫ s in Icc (0:ℝ) (t:ℝ), g (s,X s.toNNReal w) ∂volume
  let J : NNReal → ℝ := fun t =>
    ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
      g (z.1,Xleft z.1.toNNReal w)*z.2^2/2 ∂(pathJumpMeasure X Xleft w)
  let c : ℝ := (triplet.gaussianVariance:ℝ)/2
  obtain ⟨hI,M,hM⟩ := ito43_weighted_time_path_regular X Xleft w hc hl g hg T
  obtain ⟨hJ,K,hK⟩ := ito43_weighted_jump_path_regular X Xleft w hc hl g hg T hS
  intro n
  let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
  let Q : NNReal → ℝ := fun t => ∑ k ∈ Finset.range n,
    g ((u k:ℝ),X (u k) w)*(X (min t (u (k+1))) w-X (min t (u k)) w)^2/2
  obtain ⟨hQ,R,hR⟩ := ito43_weighted_grid_path_regular X Xleft w hc hl g hg T n
  constructor
  · intro t
    change ContinuousWithinAt (fun s => |c*I s+J s-Q s|) (Ici t) t
    exact (((continuousWithinAt_const.mul hI.continuousWithinAt).add (hJ t)).sub (hQ t)).abs
  · refine ⟨|c| * M+K+R,?_⟩
    rintro _ ⟨t,rfl⟩
    change |c*I t+J t-Q t| ≤ _
    have h1 := abs_add_le (c*I t) (J t)
    have h2 := abs_sub_le (c*I t+J t) 0 (Q t)
    simp only [sub_zero,zero_sub,abs_neg] at h2
    rw [abs_mul] at h1
    linarith [mul_le_mul_of_nonneg_left (hM t t.property) (abs_nonneg c),hK t t.property,hR t t.property]
