-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_grid_kernel_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:03:37.023982+00:00
-- url     : https://prove2.me/submissions/4dea1e19-e340-4e3b-9d99-fc5bb87a127d

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hCad : ∀ᵐ w ∂P, IsCadlag (fun t => X t w))
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
    ∀ (T : NNReal) (m : ℕ),
    let K : NNReal → ℝ → ℝ → ℝ := fun s x z =>
      (f ((s : ℝ),x+z) - f ((s : ℝ),x) -
        deriv (fun y : ℝ => f ((s : ℝ),y)) x*z -
        iteratedDeriv 2 (fun y : ℝ => f ((s : ℝ),y)) x*z^2/2) *
      min 1 (max 0 (|z| * ((m : ℝ)+1)-1))
    let S : ℕ → NNReal → Omega → ℝ := fun n t omega =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
      (∑ k ∈ Finset.range n,
       let dx := X (v (k+1)) omega - X (v k) omega
       (f ((v k : ℝ),X (v (k+1)) omega) - f ((v k : ℝ),X (v k) omega) -
        deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx -
        iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx^2 / 2)
          * chi dx)
    ∀ (n : ℕ) (t : NNReal) (w : Omega),
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      S n t w = ∑ k ∈ Finset.range n, K (u k) (X (u k) w)
        (X (v (k+1)) w-X (v k) w) := by
  intro T m K S n t w u v
  have hu : Monotone u := by
    intro i j hij
    dsimp [u]
    gcongr
  dsimp only [S]
  apply Finset.sum_congr rfl
  intro k hk
  change (f ((v k:ℝ),X (v (k+1)) w)-f ((v k:ℝ),X (v k) w) -
    deriv (fun x : ℝ => f ((u k:ℝ),x)) (X (u k) w) *
      (X (v (k+1)) w-X (v k) w) -
    iteratedDeriv 2 (fun x : ℝ => f ((u k:ℝ),x)) (X (u k) w) *
      (X (v (k+1)) w-X (v k) w)^2/2) *
    min 1 (max 0 (|X (v (k+1)) w-X (v k) w| * ((m:ℝ)+1)-1)) =
    K (u k) (X (u k) w) (X (v (k+1)) w-X (v k) w)
  by_cases h : u k ≤ t
  · have hv : v k = u k := min_eq_right h
    rw [hv]
    have he : X (u k) w + (X (v (k+1)) w-X (u k) w) = X (v (k+1)) w := by ring
    simp only [K,he]
  · have ht : t ≤ u k := le_of_not_ge h
    have hv : v k = t := min_eq_left ht
    have hv1 : v (k+1) = t := min_eq_left (ht.trans (hu (Nat.le_succ k)))
    rw [hv,hv1]
    simp [K]
