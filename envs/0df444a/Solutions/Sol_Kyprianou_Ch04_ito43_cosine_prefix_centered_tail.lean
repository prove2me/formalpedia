-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_prefix_centered_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:58:36.43771+00:00
-- url     : https://prove2.me/submissions/5fe196dc-107b-4235-958c-2a6d1dfe15e8

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_grid_mean_rate
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_deficit_square_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_nat_grid_independent
import Theorems.Thm_Kyprianou_Ch04_ito43_independent_centered_prefix_maximal
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_grid_increment_mean
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
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
          (nhds (Xleft t omega))) :
    ∀ T : NNReal,
    let q : ℕ → ℝ → ℝ := fun m z => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
    let μ : ℕ → ℕ → ℝ := fun m n =>
      ∫ w, q m (X (T/(n:NNReal)) w) ∂P
    let D : ℕ → ℕ → ℕ → Omega → ℝ := fun m n k w =>
      q m (X (T*((k+1:ℕ):NNReal)/(n:NNReal)) w -
        X (T*(k:NNReal)/(n:NNReal)) w) - μ m n
    ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      ∀ᶠ n : ℕ in atTop,
        (P {w | ∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, D m n k w|}).toReal ≤ η := by
  intro T q μ D e he η hη
  let c : ℝ := (triplet.gaussianVariance:ℝ)/2
  let R : ℝ := |c*(T:ℝ)|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hrate := ito43_cosine_grid_mean_rate P X hLevy triplet hTriplet Xleft hLeft T 1 zero_lt_one
  have hf : Tendsto (fun m : ℕ => (2:ℝ)/((m:ℝ)+1)^2) atTop (nhds 0) := by
    have h : Tendsto (fun m : ℕ => (1:ℝ)/((m:ℝ)+1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    convert (h.mul h).const_mul (2:ℝ) using 1
    · funext m
      field_simp
      <;> ring
    · norm_num
  have hη' : 0 < η*e^2/R := by positivity
  filter_upwards [hrate,hf.eventually (gt_mem_nhds hη')] with m hm hsmall
  filter_upwards [hm] with n hn
  let C : ℝ := 2/((m:ℝ)+1)^2
  let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
  let F : ℕ → Omega → ℝ := fun k w => q m (X (u (k+1)) w-X (u k) w)
  have hu : Monotone u := by intro i j hij; dsimp [u]; gcongr
  have hq : Continuous (q m) := by dsimp [q]; fun_prop
  have hx := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hLevy
  have hF (k : ℕ) : AEMeasurable (F k) P :=
    hq.measurable.comp_aemeasurable ((hx _).sub (hx _))
  have hi : iIndepFun F P :=
    (ito43_levy_nat_grid_independent P X hLevy u hu).comp (fun _ => q m) (fun _ => hq.measurable)
  have hb (k : ℕ) : ∀ᵐ w ∂P, 0 ≤ F k w ∧ F k w ≤ C := by
    filter_upwards [] with w
    have h := ito43_cosine_deficit_square_bound ((m:ℝ)+1) (X (u (k+1)) w-X (u k) w) (by positivity)
    exact ⟨h.1,h.2.2⟩
  have hmean (k : ℕ) : (∫ w, F k w ∂P) = μ m n :=
    ito43_cosine_grid_increment_mean P X hLevy triplet hTriplet Xleft hLeft T m n k
  have h := ito43_independent_centered_prefix_maximal P F C (μ m n) (by positivity) hF hi hb hmean n e he
  apply h.trans
  have hr : (n:ℝ)*μ m n ≤ R := by
    have h0 := le_abs_self ((n:ℝ)*μ m n-c*(T:ℝ))
    dsimp [R]
    linarith [le_abs_self (c*(T:ℝ))]
  have hC : 0 ≤ C := by positivity
  have hCR := mul_le_mul_of_nonneg_left hr hC
  have hsmall' : C*R < η*e^2 := (lt_div_iff₀ hR).mp hsmall
  apply (div_le_iff₀ (by positivity : 0 < e^2)).mpr
  nlinarith only [hCR,hsmall']
