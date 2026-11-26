-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_small_tail_grid_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:39:46.498646+00:00
-- url     : https://prove2.me/submissions/a9cc596d-6a31-4d6f-858b-106060ced406

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_cutoff_cell
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Apply the compact cutoff estimate cell by cell. -/
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
        (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (H : NNReal) (M a : ℝ) (ha : 0 < a) (m : ℕ)
    (hcut : ∀ s ∈ Set.Icc (0 : ℝ) (H : ℝ),
      ∀ x ∈ Set.Icc (-M) M, ∀ y ∈ Set.Icc (-M) M,
        |(f (s,y)-f (s,x)-deriv (fun z : ℝ => f (s,z)) x*(y-x) -
          iteratedDeriv 2 (fun z : ℝ => f (s,z)) x*(y-x)^2/2) *
          (1-min 1 (max 0 (|y-x| *((m : ℝ)+1)-1)))| ≤ a*(y-x)^2)
    (omega : Omega)
    (hbounded : ∀ s : NNReal, s ≤ H → |X s omega| ≤ M)
    (T : NNReal) (hTH : T ≤ H) (n : ℕ) (t : NNReal) (ht : t ≤ T) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
    |(∑ k ∈ Finset.range n,
          (f ((v k : Real), X (v (k+1)) omega) -
          f ((v k : Real), X (v k) omega) -
          deriv (fun x : Real => f ((u k : Real), x)) (X (u k) omega) *
            (X (v (k+1)) omega - X (v k) omega))) - (∑ k ∈ Finset.range n,
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * (X (v (k+1)) omega - X (v k) omega)^2 / 2) - (∑ k ∈ Finset.range n,
       let dx := X (v (k+1)) omega - X (v k) omega
       (f ((v k : ℝ),X (v (k+1)) omega) - f ((v k : ℝ),X (v k) omega) -
        deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx -
        iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega) * dx^2 / 2)
          * chi dx)| ≤
      a*∑ k ∈ Finset.range n, (X (v (k+1)) omega-X (v k) omega)^2 := by
  intro u v chi
  let dx : ℕ → ℝ := fun k => X (v (k+1)) omega-X (v k) omega
  let A : ℕ → ℝ := fun k =>
    f ((v k : ℝ),X (v (k+1)) omega)-f ((v k : ℝ),X (v k) omega) -
      deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega)*dx k
  let B : ℕ → ℝ := fun k =>
    iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k) omega)*(dx k)^2/2
  have hu : Monotone u := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by positivity)) (by positivity)
  have hv (k : ℕ) : v k ≤ H := (min_le_left _ _).trans (ht.trans hTH)
  have htime (k : ℕ) : (v k : ℝ) ∈ Set.Icc (0 : ℝ) (H : ℝ) :=
    ⟨NNReal.coe_nonneg _,by exact_mod_cast hv k⟩
  have hspace (k : ℕ) : X (v k) omega ∈ Set.Icc (-M) M :=
    abs_le.mp (hbounded (v k) (hv k))
  change |(∑ k ∈ Finset.range n, A k)-(∑ k ∈ Finset.range n, B k)-
    (∑ k ∈ Finset.range n, (A k-B k)*chi (dx k))| ≤
    a*∑ k ∈ Finset.range n, (dx k)^2
  have hsum : (∑ k ∈ Finset.range n, A k)-(∑ k ∈ Finset.range n, B k)-
      (∑ k ∈ Finset.range n, (A k-B k)*chi (dx k)) =
      ∑ k ∈ Finset.range n, (A k-B k)*(1-chi (dx k)) := by
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum,Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro k hk
  have h := Kyprianou.Ch04.ito43_stopped_grid_cutoff_cell (fun s => X s omega) f u hu t k
  change A k-B k = _ at h
  rw [h]
  exact hcut (v k : ℝ) (htime k) (X (v k) omega) (hspace k)
    (X (v (k+1)) omega) (hspace (k+1))
