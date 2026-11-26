-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_small_tail_jump_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:43:02.595304+00:00
-- url     : https://prove2.me/submissions/c46f638e-db3c-4101-9562-76b44c51758b

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_path_jump_kernel_energy_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_taylor_global_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_cadlag_left_compact_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_integral_cutoff_difference
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_slice_derivative
import Theorems.Thm_Kyprianou_Ch04_exercise41CadlagPhysicalJumpsCountableV17
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_jump_atom_bounds
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Dominate complementary actual jump integrals by the square-summable jump series. -/
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
    (hcad : IsCadlag (fun s : NNReal => X s omega))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun r => X r omega)
      (nhdsWithin s (Set.Iio s)) (nhds (Xleft s omega)))
    (hE : Summable (fun s : Set.Ioc (0 : NNReal) H => (X s omega-Xleft s omega)^2))
    (t : NNReal) (ht : t ≤ H) :
    let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ) + 1) - 1))
    |(∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega) -
           z.2 * fderiv Real f
             (z.1, Xleft (Real.toNNReal z.1) omega) (0, 1))
          ∂(pathJumpMeasure X Xleft omega)) - (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
       (f (z.1,Xleft (Real.toNNReal z.1) omega + z.2) -
        f (z.1,Xleft (Real.toNNReal z.1) omega) -
        z.2 * fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) omega) (0,1) -
        iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega) * z.2^2 / 2)
          * chi z.2 ∂(pathJumpMeasure X Xleft omega))| ≤
      a*(∑' s : Set.Ioc (0 : NNReal) H, (X s omega-Xleft s omega)^2) := by
  intro chi
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ
  let μ := (pathJumpMeasure X Xleft omega).restrict S
  let A : ℝ × ℝ → ℝ := fun z =>
    f (z.1,Xleft (Real.toNNReal z.1) omega+z.2) -
    f (z.1,Xleft (Real.toNNReal z.1) omega) -
    z.2*fderiv ℝ f (z.1,Xleft (Real.toNNReal z.1) omega) (0,1)
  let B : ℝ × ℝ → ℝ := fun z =>
    iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) (Xleft (Real.toNNReal z.1) omega)*z.2^2/2
  let F : ℝ × ℝ → ℝ := fun z => (A z-B z)*(1-chi z.2)
  obtain ⟨C,hC,hbounds⟩ := Kyprianou.Ch04.ito43_compact_jump_atom_bounds f
    hfJointC1 hfSpaceC2 hfSpaceSecondContinuous H M a ha m hcut
  have hlb := Kyprianou.Ch04.ito43_cadlag_left_compact_bound
    (fun s => X s omega) (fun s => Xleft s omega) H M hbounded hl
  have hcount := Kyprianou.Ch04.exercise41CadlagPhysicalJumpsCountableV17
    (fun s => X s omega) (fun s => Xleft s omega) (fun s => (hcad s).1) hl
  have hcoords (s : NNReal) (hs : 0 < s) (hst : s ≤ t) :
      (s : ℝ) ∈ Set.Icc (0 : ℝ) (H : ℝ) ∧
      Xleft s omega ∈ Set.Icc (-M) M ∧ X s omega ∈ Set.Icc (-M) M :=
    ⟨⟨NNReal.coe_nonneg _,by exact_mod_cast hst.trans ht⟩,
      abs_le.mp (hlb s hs (hst.trans ht)),abs_le.mp (hbounded s (hst.trans ht))⟩
  have hABC (s : NNReal) (hs : 0 < s) (hst : s ≤ t) :
      |A ((s : ℝ),X s omega-Xleft s omega)| ≤ (C/2)*(X s omega-Xleft s omega)^2 ∧
      |B ((s : ℝ),X s omega-Xleft s omega)| ≤ (C/2)*(X s omega-Xleft s omega)^2 ∧
      |F ((s : ℝ),X s omega-Xleft s omega)| ≤ a*(X s omega-Xleft s omega)^2 := by
    obtain ⟨hs',hx,hy⟩ := hcoords s hs hst
    have hb := hbounds _ hs' (by exact_mod_cast hs) _ hx _ hy
    simpa only [A,B,F,chi,Real.toNNReal_coe,show Xleft s omega+(X s omega-Xleft s omega) = X s omega by ring] using hb
  obtain ⟨hAi,_⟩ := Kyprianou.Ch04.ito43_path_jump_kernel_energy_bound X Xleft omega
    hcount H t ht (C/2) (by positivity) hE A (fun s hs ht => (hABC s hs ht).1)
  obtain ⟨hBi,_⟩ := Kyprianou.Ch04.ito43_path_jump_kernel_energy_bound X Xleft omega
    hcount H t ht (C/2) (by positivity) hE B (fun s hs ht => (hABC s hs ht).2.1)
  obtain ⟨hFi,hFb⟩ := Kyprianou.Ch04.ito43_path_jump_kernel_energy_bound X Xleft omega
    hcount H t ht a ha.le hE F (fun s hs ht => (hABC s hs ht).2.2)
  change |(∫ z, A z ∂μ)-(∫ z, B z ∂μ)-(∫ z, (A z-B z)*chi z.2 ∂μ)| ≤ _
  rw [Kyprianou.Ch04.ito43_integral_cutoff_difference μ A B (fun z => chi z.2) hAi hBi hFi]
  exact hFb
