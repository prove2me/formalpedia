-- Prove2me | solution 1 for MarkovChainCLT.clt_of_geometric_drift
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T07:59:53.985487+00:00
-- url     : https://prove2.me/submissions/7575e274-f180-48e7-9e5c-f7def0885baa

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovDriftMinorization
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Integral
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.NNRealPreprocessor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_martingaleCLT_chain
import Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_stationary_clt
import Theorems.Thm_MarkovChainCLT_tendstoInMeasure_inv_sqrt_coord_sub
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NumberGeoIntegrability

open MeasureTheory
open scoped ENNReal

namespace DriftTruncation

theorem integrable_of_cutoff_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (V : X → ℝ) (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (B : ℝ)
    (hint : ∀ n : ℕ, Integrable (fun x => if V x ≤ (n : ℝ) then V x else 0) μ)
    (hbound : ∀ n : ℕ, (∫ x, if V x ≤ (n : ℝ) then V x else 0 ∂μ) ≤ B) :
    Integrable V μ := by
  let F : ℕ → X → ℝ := fun n x => if V x ≤ (n : ℝ) then V x else 0
  have hF0 (n : ℕ) (x : X) : 0 ≤ F n x := by
    dsimp [F]
    split_ifs
    · exact hV0 x
    · exact le_rfl
  have hFle (n : ℕ) (x : X) : F n x ≤ V x := by
    dsimp [F]
    split_ifs
    · exact le_rfl
    · exact hV0 x
  have hFm (n : ℕ) : Measurable (F n) :=
    Measurable.ite (measurableSet_le hV measurable_const) hV measurable_const
  have hmono : Monotone (fun n : ℕ => fun x => ENNReal.ofReal (F n x)) := by
    intro n m hnm x
    by_cases hx : V x ≤ (n : ℝ)
    · have hxm : V x ≤ (m : ℝ) := hx.trans (Nat.cast_le.mpr hnm)
      simp only [F, hx, hxm, if_true, le_refl]
    · simp only [F, hx, if_false, ENNReal.ofReal_zero]
      exact bot_le
  have hsup (x : X) : (⨆ n : ℕ, ENNReal.ofReal (F n x)) = ENNReal.ofReal (V x) := by
    apply le_antisymm
    · exact iSup_le (fun n => ENNReal.ofReal_le_ofReal (hFle n x))
    · obtain ⟨n, hn⟩ := exists_nat_ge (V x)
      exact le_iSup_of_le n (by simp only [F, hn, if_true, le_refl])
  have hlin (n : ℕ) : (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) ≤ ENNReal.ofReal B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all μ (hF0 n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hfin : (∫⁻ x, ENNReal.ofReal (V x) ∂μ) < ∞ := by
    calc
      (∫⁻ x, ENNReal.ofReal (V x) ∂μ) = ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (F n x) ∂μ := by
        apply lintegral_congr
        intro x
        exact (hsup x).symm
      _ = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (F n x) ∂μ :=
        lintegral_iSup (fun n => (hFm n).ennreal_ofReal) hmono
      _ ≤ ENNReal.ofReal B := iSup_le hlin
      _ < ∞ := ENNReal.ofReal_lt_top
  exact ⟨hV.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all μ hV0)).mpr hfin⟩

end DriftTruncation

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace DriftBound

theorem cutoff_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (V : X → ℝ)
    (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x) (n : ℕ) :
    Integrable (fun x => if V x ≤ (n : ℝ) then V x else 0) μ := by
  refine (integrable_const (n : ℝ)).mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (Measurable.ite (measurableSet_le hV measurable_const) hV measurable_const).aestronglyMeasurable
  · by_cases hx : V x ≤ (n : ℝ)
    · simpa only [if_pos hx, Real.norm_eq_abs, abs_of_nonneg (hV0 x)] using hx
    · simp only [if_neg hx, norm_zero]
      positivity

theorem cutoff_integral_bound {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : Kernel.Invariant P π) (V : X → ℝ) (hV : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) (d B : ℝ) (hd : 0 < d) (hB : 0 ≤ B)
    (hVi : ∀ x, Integrable V (P x))
    (hdrift : ∀ x, (∫ y, V y ∂P x) - V x ≤ -d * V x + B) (n : ℕ) :
    (∫ x, (if V x ≤ (n : ℝ) then V x else 0) ∂π) ≤ B / d := by
  let F : X → ℝ := fun x => min (V x) (n : ℝ)
  have hF0 : ∀ x, 0 ≤ F x := fun x => le_min (hV0 x) (by positivity)
  have hFn : ∀ x, F x ≤ (n : ℝ) := fun x => min_le_right _ _
  have hFm : Measurable F := hV.min measurable_const
  have hFi : ∀ (μ : Measure X) [IsProbabilityMeasure μ], Integrable F μ := by
    intro μ hμ
    refine (integrable_const (n : ℝ)).mono' hFm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 x)] using hFn x
  have hPF0 : ∀ x, 0 ≤ ∫ y, F y ∂P x := fun x => integral_nonneg hF0
  have hPFn : ∀ x, (∫ y, F y ∂P x) ≤ (n : ℝ) := by
    intro x
    calc
      (∫ y, F y ∂P x) ≤ ∫ _ : X, (n : ℝ) ∂P x :=
        integral_mono_ae (hFi (P x)) (integrable_const _) (ae_of_all _ hFn)
      _ = n := by simp
  have hPFi : Integrable (fun x => ∫ y, F y ∂P x) π := by
    refine (integrable_const (n : ℝ)).mono'
      hFm.stronglyMeasurable.integral_kernel.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hPF0 x)] using hPFn x
  have hcomp : (P ∘ₖ Kernel.const Unit π) () = π := by
    change π.bind P = π
    exact hP
  have hcompFi : Integrable F ((P ∘ₖ Kernel.const Unit π) ()) := by
    rw [hcomp]
    exact hFi π
  have hstationary : (∫ x, ∫ y, F y ∂P x ∂π) = ∫ x, F x ∂π := by
    simpa only [hcomp, Kernel.const_apply] using (Kernel.integral_comp hcompFi).symm
  have hpoint : ∀ x, d * (if V x ≤ (n : ℝ) then V x else 0) ≤
      F x - (∫ y, F y ∂P x) + B := by
    intro x
    by_cases hx : V x ≤ (n : ℝ)
    · have hFV : (∫ y, F y ∂P x) ≤ ∫ y, V y ∂P x :=
        integral_mono_ae (hFi (P x)) (hVi x) (ae_of_all _ fun y => min_le_left _ _)
      have hxF : F x = V x := min_eq_left hx
      rw [if_pos hx, hxF]
      linarith [hdrift x]
    · have hxF : F x = n := min_eq_right (le_of_not_ge hx)
      rw [if_neg hx, mul_zero, hxF]
      linarith [hPFn x]
  have hdiffi : Integrable (fun x => F x - (∫ y, F y ∂P x)) π := (hFi π).sub hPFi
  have hbound := integral_mono_ae
    ((cutoff_integrable π V hV hV0 n).const_mul d)
    (hdiffi.add (integrable_const B)) (ae_of_all _ hpoint)
  simp only [Pi.add_apply] at hbound
  rw [integral_const_mul, integral_add hdiffi (integrable_const B),
    integral_sub (hFi π) hPFi, hstationary] at hbound
  simp only [sub_self, zero_add, integral_const, probReal_univ, smul_eq_mul,
    one_mul] at hbound
  exact (le_div_iff₀ hd).mpr (by nlinarith)

end DriftBound

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π)
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (d b : ℝ) (hd : 0 < d) (hdrift : GeoDriftCondition P V d b C) :
    Integrable V π := by
  have hV0 : ∀ x, 0 ≤ V x := fun x => le_trans zero_le_one (hV1 x)
  apply DriftTruncation.integrable_of_cutoff_bounds π V hV hV0 (max b 0 / d)
    (DriftBound.cutoff_integrable π V hV hV0)
  intro n
  apply DriftBound.cutoff_integral_bound P π hP.1 V hV hV0 d (max b 0) hd
    (le_max_right b 0) hdrift.1
  intro x
  have hb : b * C.indicator (fun _ => (1 : ℝ)) x ≤ max b 0 := by
    by_cases hx : x ∈ C
    · simpa [hx] using le_max_left b (0 : ℝ)
    · simpa [hx] using le_max_right b (0 : ℝ)
  linarith [hdrift.2 x]


end NumberGeoIntegrability
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NumberPort_geo_drift

/- Complete proof of the geometric-drift Poisson equation.
KernelL2 retains its complete namespace body from accepted Prove2Me
submission 5dd37a55-2152-4edc-96ad-dba3c6f11481, with attribution below.
All other local component bodies are included in full; no hidden helper
module is imported. The registered geometric-drift integrability theorem
is the sole proved public dependency. -/

section GeometricPoissonComponent1

/- Complete KernelL2 namespace copied from accepted Prove2Me submission
   5dd37a55-2152-4edc-96ad-dba3c6f11481. Original source SHA256:
   d939e5a556186c21fd1897acdf58fbe65a27e8db7272fdeff7a0172460f2acfd.
   Every namespace-body byte is retained; no hidden source helper is imported. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace KernelL2

variable {X : Type*} [MeasurableSpace X]

theorem integral_sq_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h1 : Integrable f μ := hf.integrable (by norm_num)
  have h2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  let m := ∫ x, f x ∂μ
  have hnonneg : 0 ≤ ∫ x, (f x - m) ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have heq : (fun x => (f x - m) ^ 2) =
      (fun x => f x ^ 2 - (2 * m) * f x + m ^ 2) := by
    funext x
    ring
  rw [heq] at hnonneg
  rw [integral_add (f := fun x => f x ^ 2 - (2 * m) * f x)
      (g := fun _ => m ^ 2) (h2.sub (h1.const_mul (2 * m))) (integrable_const _),
    integral_sub (f := fun x => f x ^ 2) (g := fun x => (2 * m) * f x)
      h2 (h1.const_mul (2 * m)), integral_const_mul, integral_const] at hnonneg
  simp only [probReal_univ, smul_eq_mul, one_mul] at hnonneg
  dsimp [m] at hnonneg
  nlinarith

theorem ae_integrable (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    {f : X → ℝ} (hf : Integrable f π) : ∀ᵐ x ∂π, Integrable f (P x) := by
  change P ∘ₘ π = π at hinv
  apply Measure.ae_integrable_of_integrable_comp
  simpa only [hinv] using hf

theorem integral_invariant (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    {f : X → ℝ} (hf : Integrable f π) :
    (∫ x, ∫ y, f y ∂P x ∂π) = ∫ x, f x ∂π := by
  change P ∘ₘ π = π at hinv
  have hcomp : Integrable f ((P ∘ₖ Kernel.const Unit π) ()) := by
    simpa only [← Measure.comp_eq_comp_const_apply, hinv] using hf
  simpa only [← Measure.comp_eq_comp_const_apply, hinv, Kernel.const_apply] using
    (Kernel.integral_comp hcomp).symm

theorem kernel_memLp_and_sq_bound (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : X → ℝ) (hf : Measurable f) (h2 : MemLp f 2 π) :
    MemLp (fun x => ∫ y, f y ∂P x) 2 π ∧
      (∫ x, (∫ y, f y ∂P x) ^ 2 ∂π) ≤ ∫ x, f x ^ 2 ∂π := by
  have hmeas : Measurable (fun x => ∫ y, f y ∂P x) :=
    hf.stronglyMeasurable.integral_kernel.measurable
  have hsq : Integrable (fun x => f x ^ 2) π := h2.integrable_sq
  have hcomp : Integrable (fun x => f x ^ 2) (P ∘ₘ π) := by
    change P ∘ₘ π = π at hinv
    simpa only [hinv] using hsq
  have hi : Integrable (fun x => ∫ y, f y ^ 2 ∂P x) π := by
    simpa only [Real.norm_eq_abs, abs_sq] using
      Measure.integrable_integral_norm_of_integrable_comp hcomp
  have hj : ∀ᵐ x ∂π, (∫ y, f y ∂P x) ^ 2 ≤ ∫ y, f y ^ 2 ∂P x := by
    filter_upwards [ae_integrable P π hinv hsq] with x hx
    exact integral_sq_bound (P x) f
      ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hx)
  have hi2 : Integrable (fun x => (∫ y, f y ∂P x) ^ 2) π := by
    apply hi.mono' (hmeas.pow_const 2).aestronglyMeasurable
    filter_upwards [hj] with x hx
    simpa only [Real.norm_eq_abs, abs_sq] using hx
  refine ⟨(memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr hi2, ?_⟩
  calc
    (∫ x, (∫ y, f y ∂P x) ^ 2 ∂π) ≤ ∫ x, ∫ y, f y ^ 2 ∂P x ∂π :=
      integral_mono_ae hi2 hi hj
    _ = ∫ x, f x ^ 2 ∂π := integral_invariant P π hinv hsq

theorem kernel_memLp (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : X → ℝ) (hf : Measurable f) (h2 : MemLp f 2 π) :
    MemLp (fun x => ∫ y, f y ∂P x) 2 π :=
  (kernel_memLp_and_sq_bound P π hinv f hf h2).1

theorem norm_sq {π : Measure X} (f : Lp ℝ 2 π) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂π := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [Real.norm_eq_abs, sq_abs]

noncomputable def action (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) : Lp ℝ 2 π :=
  (kernel_memLp P π hinv f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).toLp _

theorem action_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) :
    ⇑(action P π hinv f) =ᵐ[π] (fun x => ∫ y, f y ∂P x) :=
  MemLp.coeFn_toLp _

theorem action_norm_le (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) : ‖action P π hinv f‖ ≤ ‖f‖ := by
  have hsq : ‖action P π hinv f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_sq, norm_sq]
    calc
      (∫ x, action P π hinv f x ^ 2 ∂π) = ∫ x, (∫ y, f y ∂P x) ^ 2 ∂π := by
        apply integral_congr_ae
        filter_upwards [action_ae P π hinv f] with x hx
        rw [hx]
      _ ≤ ∫ x, f x ^ 2 ∂π :=
        (kernel_memLp_and_sq_bound P π hinv f (Lp.stronglyMeasurable f).measurable
          (Lp.memLp f)).2
  nlinarith [norm_nonneg (action P π hinv f), norm_nonneg f]

theorem kernel_congr_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    {f g : X → ℝ} (hfg : f =ᵐ[π] g) :
    (fun x => ∫ y, f y ∂P x) =ᵐ[π] (fun x => ∫ y, g y ∂P x) := by
  change P ∘ₘ π = π at hinv
  have hfg' : f =ᵐ[P ∘ₘ π] g := by simpa only [hinv] using hfg
  filter_upwards [Measure.ae_ae_of_ae_comp hfg'] with x hx
  exact integral_congr_ae hx

theorem action_add (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f g : Lp ℝ 2 π) :
    action P π hinv (f + g) = action P π hinv f + action P π hinv g := by
  apply Lp.ext
  filter_upwards [action_ae P π hinv (f + g), action_ae P π hinv f,
    action_ae P π hinv g, Lp.coeFn_add (action P π hinv f) (action P π hinv g),
    kernel_congr_ae P π hinv (Lp.coeFn_add f g),
    ae_integrable P π hinv ((Lp.memLp f).integrable (by norm_num)),
    ae_integrable P π hinv ((Lp.memLp g).integrable (by norm_num))]
      with x hsum hf hg ha hk hif hig
  rw [hsum, ha, Pi.add_apply, hf, hg, hk]
  exact integral_add hif hig

theorem action_smul (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (c : ℝ) (f : Lp ℝ 2 π) :
    action P π hinv (c • f) = c • action P π hinv f := by
  apply Lp.ext
  filter_upwards [action_ae P π hinv (c • f), action_ae P π hinv f,
    Lp.coeFn_smul c (action P π hinv f),
    kernel_congr_ae P π hinv (Lp.coeFn_smul c f)] with x hcf hf ha hk
  rw [hcf, ha, Pi.smul_apply, hf, hk]
  exact integral_smul c f

noncomputable def markovOp (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) :
    Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π :=
  LinearMap.mkContinuous
    { toFun := action P π hinv
      map_add' := action_add P π hinv
      map_smul' := action_smul P π hinv }
    1 (fun f => by
      change ‖action P π hinv f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using action_norm_le P π hinv f)

theorem markovOp_ae (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) :
    ⇑(markovOp P π hinv f) =ᵐ[π] (fun x => ∫ y, f y ∂P x) :=
  action_ae P π hinv f

theorem markovOp_norm_le (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f : Lp ℝ 2 π) : ‖markovOp P π hinv f‖ ≤ ‖f‖ :=
  action_norm_le P π hinv f

theorem norm_markovOp_le (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) :
    ‖markovOp P π hinv‖ ≤ 1 :=
  (markovOp P π hinv).opNorm_le_bound zero_le_one
    (fun f => by simpa only [one_mul] using markovOp_norm_le P π hinv f)

end KernelL2

end GeometricPoissonComponent1

section GeometricPoissonComponent2

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal ProbabilityTheory

namespace PoissonResolvent

set_option maxHeartbeats 1000000

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

noncomputable def scale (c : ℝ≥0∞) (P : Kernel X Y) : Kernel X Y where
  toFun x := c • P x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    change Measurable (fun x => c * P x A)
    exact measurable_const.mul (P.measurable_coe hA)

@[simp] theorem scale_apply (c : ℝ≥0∞) (P : Kernel X Y) (x : X) :
    scale c P x = c • P x := rfl

@[simp] theorem scale_apply_set (c : ℝ≥0∞) (P : Kernel X Y) (x : X) (A : Set Y) :
    scale c P x A = c * P x A := by simp [scale]

theorem scale_scale (a b : ℝ≥0∞) (P : Kernel X Y) :
    scale a (scale b P) = scale (a * b) P := by
  ext x A hA
  simp [mul_assoc]

theorem scale_sum (c : ℝ≥0∞) (P : ℕ → Kernel X Y) :
    scale c (Kernel.sum P) = Kernel.sum (fun n => scale c (P n)) := by
  ext x A hA
  simp only [scale_apply_set, Kernel.sum_apply' _ _ hA]
  exact ENNReal.tsum_mul_left.symm

theorem comp_scale (c : ℝ≥0∞) (P : Kernel Y Z) (Q : Kernel X Y) :
    P ∘ₖ scale c Q = scale c (P ∘ₖ Q) := by
  ext x A hA
  simp [Kernel.comp_apply' _ _ _ hA, lintegral_smul_measure]

theorem scale_comp (c : ℝ≥0∞) (P : Kernel Y Z) (Q : Kernel X Y) :
    scale c P ∘ₖ Q = scale c (P ∘ₖ Q) := by
  ext x A hA
  simp only [Kernel.comp_apply' _ _ _ hA, scale_apply_set]
  exact lintegral_const_mul c (P.measurable_coe hA)

theorem sum_succ (P : ℕ → Kernel X Y) :
    Kernel.sum P = P 0 + Kernel.sum (fun n => P (n + 1)) := by
  apply Kernel.ext_iff'.mpr
  intro x A hA
  rw [Kernel.add_apply, Measure.add_apply, Kernel.sum_apply' P x hA,
    Kernel.sum_apply' (fun n => P (n + 1)) x hA]
  exact tsum_eq_zero_add'
    (ENNReal.summable : Summable (fun n : ℕ => P (n + 1) x A))

noncomputable def weight (n : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ (n + 1)

@[simp] theorem weight_zero : weight 0 = (2 : ℝ≥0∞)⁻¹ := by simp [weight]

theorem weight_succ (n : ℕ) : weight (n + 1) = (2 : ℝ≥0∞)⁻¹ * weight n := by
  simp [weight, pow_succ, mul_comm]

theorem weight_add (n m : ℕ) :
    weight (n + m) = (2 : ℝ≥0∞)⁻¹ ^ m * weight n := by
  simp [weight, show n + m + 1 = m + (n + 1) by omega, pow_add]

theorem weight_pos (n : ℕ) : 0 < weight n := by
  unfold weight
  exact bot_lt_iff_ne_bot.mpr
    (ENNReal.pow_ne_zero (ne_of_gt (ENNReal.inv_pos.mpr (by finiteness))) _)

theorem weight_ne_top (n : ℕ) : weight n ≠ ∞ := by
  unfold weight
  finiteness

theorem sum_weight : ∑' n, weight n = 1 := by
  simp only [weight, pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
  exact ENNReal.mul_inv_cancel (by norm_num) (by finiteness)

noncomputable def resolvent (P : Kernel X X) : Kernel X X :=
  Kernel.sum (fun n => scale (weight n) (iterKernel P n))

theorem resolvent_apply (P : Kernel X X) (x : X) :
    resolvent P x = Measure.sum (fun n => weight n • iterKernel P n x) := rfl

theorem resolvent_apply_set (P : Kernel X X) (x : X) (A : Set X)
    (hA : MeasurableSet A) :
    resolvent P x A = ∑' n, weight n * iterKernel P n x A := by
  simp [resolvent, Kernel.sum_apply' _ _ hA]

instance resolvent_isMarkov (P : Kernel X X) [IsMarkovKernel P] :
    IsMarkovKernel (resolvent P) where
  isProbabilityMeasure x := by
    constructor
    rw [resolvent_apply_set _ _ _ MeasurableSet.univ]
    simpa using sum_weight

theorem iterKernel_eq_pow (P : Kernel X X) (n : ℕ) : iterKernel P n = P ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterKernel_succ, ih]
    change P * P ^ n = P ^ (n + 1)
    exact (pow_succ' P n).symm

theorem iterKernel_comp (P : Kernel X X) (n m : ℕ) :
    iterKernel P n ∘ₖ iterKernel P m = iterKernel P (n + m) := by
  simp only [iterKernel_eq_pow]
  exact (Kernel.pow_add P n m).symm

theorem resolvent_comm (P : Kernel X X) :
    P ∘ₖ resolvent P = resolvent P ∘ₖ P := by
  rw [resolvent, Kernel.comp_sum_right, Kernel.comp_sum_left]
  congr 1
  funext n
  rw [comp_scale, scale_comp]
  congr 1
  change P * iterKernel P n = iterKernel P n * P
  rw [iterKernel_eq_pow, ← pow_succ', ← pow_succ]

theorem resolvent_eq (P : Kernel X X) :
    resolvent P = scale ((2 : ℝ≥0∞)⁻¹) Kernel.id +
      scale ((2 : ℝ≥0∞)⁻¹) (P ∘ₖ resolvent P) := by
  conv_lhs => rw [resolvent, sum_succ]
  simp only [weight_zero, iterKernel_zero]
  congr 1
  rw [resolvent, Kernel.comp_sum_right, scale_sum]
  congr 1
  funext n
  rw [comp_scale, scale_scale, weight_succ, iterKernel_succ]

end PoissonResolvent

end GeometricPoissonComponent2

section GeometricPoissonComponent3

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal ProbabilityTheory

namespace PoissonResolvent

set_option maxHeartbeats 1000000

variable {X : Type*} [MeasurableSpace X]

theorem iter_invariant (P : Kernel X X) (π : Measure X)
    (hinv : Kernel.Invariant P π) (n : ℕ) :
    Kernel.Invariant (iterKernel P n) π := by
  induction n with
  | zero =>
      change π.bind (fun x => Measure.dirac x) = π
      exact Measure.bind_dirac
  | succ n ih => exact hinv.comp ih

theorem resolvent_invariant (P : Kernel X X) (π : Measure X)
    (hinv : Kernel.Invariant P π) : Kernel.Invariant (resolvent P) π := by
  change π.bind (resolvent P) = π
  ext A hA
  rw [Measure.bind_apply hA (resolvent P).aemeasurable]
  simp_rw [resolvent_apply_set P _ A hA]
  rw [lintegral_tsum (f := fun n x => weight n * iterKernel P n x A) (fun n =>
    (measurable_const.mul ((iterKernel P n).measurable_coe hA)).aemeasurable)]
  calc
    (∑' n, ∫⁻ x, weight n * iterKernel P n x A ∂π) =
        ∑' n, weight n * π A := by
      apply tsum_congr
      intro n
      rw [lintegral_const_mul _ ((iterKernel P n).measurable_coe hA)]
      congr 1
      rw [← Measure.bind_apply hA (iterKernel P n).aemeasurable]
      exact congrArg (fun μ : Measure X => μ A) (iter_invariant P π hinv n)
    _ = π A := by rw [ENNReal.tsum_mul_right, sum_weight, one_mul]

theorem resolvent_tail_le (P : Kernel X X) (m : ℕ) :
    scale ((2 : ℝ≥0∞)⁻¹ ^ m) (iterKernel P m ∘ₖ resolvent P) ≤ resolvent P := by
  rw [resolvent, Kernel.comp_sum_right, scale_sum]
  intro x
  apply Measure.le_iff.mpr
  intro A hA
  simp only [Kernel.sum_apply' _ _ hA]
  have heq (n : ℕ) :
      scale ((2 : ℝ≥0∞)⁻¹ ^ m)
          (iterKernel P m ∘ₖ scale (weight n) (iterKernel P n)) =
        scale (weight (n + m)) (iterKernel P (n + m)) := by
    rw [comp_scale, scale_scale, iterKernel_comp, weight_add, Nat.add_comm m n]
  simp_rw [heq, scale_apply_set]
  exact ENNReal.tsum_comp_le_tsum_of_injective (fun i j h => Nat.add_right_cancel h)
    (fun n => weight n * iterKernel P n x A)

theorem resolvent_minorization (P : Kernel X X) (C : Set X) (hC : MeasurableSet C)
    (m : ℕ) (ε : ℝ≥0∞) (ν : Measure X)
    (hminor : ∀ x ∈ C, ε • ν ≤ iterKernel P m x)
    (x : X) (A : Set X) (hA : MeasurableSet A) :
    ((2 : ℝ≥0∞)⁻¹ ^ m * ε) * resolvent P x C * ν A ≤ resolvent P x A := by
  have hlow : ε * ν A * resolvent P x C ≤
      (iterKernel P m ∘ₖ resolvent P) x A := by
    rw [Kernel.comp_apply' _ _ _ hA]
    calc
      ε * ν A * resolvent P x C =
          ∫⁻ y, C.indicator (fun _ => ε * ν A) y ∂resolvent P x := by
        simp [lintegral_indicator hC, mul_comm]
      _ ≤ ∫⁻ y, iterKernel P m y A ∂resolvent P x := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ C
        · simpa [hy, Measure.smul_apply] using (hminor y hy) A
        · simp [hy]
  calc
    ((2 : ℝ≥0∞)⁻¹ ^ m * ε) * resolvent P x C * ν A =
        (2 : ℝ≥0∞)⁻¹ ^ m * (ε * ν A * resolvent P x C) := by ring
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m * (iterKernel P m ∘ₖ resolvent P) x A :=
      mul_le_mul_right hlow _
    _ ≤ resolvent P x A := (resolvent_tail_le P m x) A

end PoissonResolvent

end GeometricPoissonComponent3

section GeometricPoissonComponent4

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace PoissonResolvent

variable {X : Type*} [MeasurableSpace X]

theorem resolvent_measure_eq (P : Kernel X X) (x : X) :
    resolvent P x = (2 : ℝ≥0∞)⁻¹ • Measure.dirac x +
      (2 : ℝ≥0∞)⁻¹ • ((resolvent P ∘ₖ P) x) := by
  have h := congrArg (fun Q : Kernel X X => Q x) (resolvent_eq P)
  rw [resolvent_comm P] at h
  simpa only [Kernel.add_apply, scale_apply, Kernel.id_apply] using h

theorem integrable_resolvent_comp (P : Kernel X X) [IsMarkovKernel P]
    {G : X → ℝ} (hGR : ∀ x, Integrable G (resolvent P x)) (x : X) :
    Integrable G ((resolvent P ∘ₖ P) x) := by
  have hi := hGR x
  rw [resolvent_measure_eq P x] at hi
  exact (integrable_smul_measure (by norm_num) (by norm_num)).mp hi.right_of_add_measure

theorem integrable_kernel_resolvent (P : Kernel X X) [IsMarkovKernel P]
    {G : X → ℝ} (hGR : ∀ x, Integrable G (resolvent P x)) (x : X) :
    Integrable (fun y => ∫ z, G z ∂resolvent P y) (P x) :=
  (integrable_resolvent_comp P hGR x).integral_comp

theorem resolvent_integral_eq_average (P : Kernel X X) [IsMarkovKernel P]
    {G : X → ℝ} (hGm : Measurable G)
    (hGR : ∀ x, Integrable G (resolvent P x)) (x : X) :
    (∫ y, G y ∂resolvent P x) = (1 / 2 : ℝ) * G x +
      (1 / 2 : ℝ) * (∫ y, ∫ z, G z ∂resolvent P y ∂P x) := by
  have hi := hGR x
  rw [resolvent_measure_eq P x] at hi
  calc
    (∫ y, G y ∂resolvent P x) =
        (∫ y, G y ∂((2 : ℝ≥0∞)⁻¹ • Measure.dirac x)) +
        (∫ y, G y ∂((2 : ℝ≥0∞)⁻¹ • ((resolvent P ∘ₖ P) x))) := by
      rw [resolvent_measure_eq P x,
        integral_add_measure hi.left_of_add_measure hi.right_of_add_measure]
    _ = (1 / 2 : ℝ) * G x +
        (1 / 2 : ℝ) * (∫ y, ∫ z, G z ∂resolvent P y ∂P x) := by
      rw [integral_smul_measure, integral_smul_measure,
        integral_dirac' G x hGm.stronglyMeasurable,
        Kernel.integral_comp (integrable_resolvent_comp P hGR x)]
      norm_num [smul_eq_mul]

theorem exists_poisson_of_resolvent (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (f G : X → ℝ) (hGm : Measurable G) (hG2 : MemLp G 2 π)
    (hGR : ∀ x, Integrable G (resolvent P x))
    (hsolve : ∀ x, G x - ∫ y, G y ∂resolvent P x = f x - ∫ y, f y ∂π) :
    ∃ g : X → ℝ, Measurable g ∧ MemLp g 2 π ∧
      Measurable (fun x => ∫ y, g y ∂P x) ∧
      MemLp (fun x => ∫ y, g y ∂P x) 2 π ∧
      ∀ x, g x - ∫ y, g y ∂P x = f x - ∫ y, f y ∂π := by
  let g : X → ℝ := fun x => ∫ y, G y ∂resolvent P x
  have hgm : Measurable g := hGm.stronglyMeasurable.integral_kernel.measurable
  have hg2 : MemLp g 2 π :=
    KernelL2.kernel_memLp (resolvent P) π (resolvent_invariant P π hinv) G hGm hG2
  refine ⟨g, hgm, hg2, hgm.stronglyMeasurable.integral_kernel.measurable,
    KernelL2.kernel_memLp P π hinv g hgm hg2, ?_⟩
  intro x
  have havg := resolvent_integral_eq_average P hGm hGR x
  have heq := hsolve x
  change g x = (1 / 2 : ℝ) * G x + (1 / 2 : ℝ) * (∫ y, g y ∂P x) at havg
  change G x - g x = f x - ∫ y, f y ∂π at heq
  linarith only [havg, heq]

end PoissonResolvent

end GeometricPoissonComponent4

section GeometricPoissonComponent5

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal ProbabilityTheory

namespace PoissonResolvent

set_option maxHeartbeats 1000000

variable {X : Type*} [MeasurableSpace X]

theorem iter_integrable_growth (P : Kernel X X) [IsMarkovKernel P]
    (U : X → ℝ) (hUm : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    (hUi : ∀ x, Integrable U (P x)) (B : ℝ)
    (hgrowth : ∀ x, (∫ y, U y ∂P x) ≤ U x + B) (n : ℕ) (x : X) :
    Integrable U (iterKernel P n x) ∧
      (∫ y, U y ∂iterKernel P n x) ≤ U x + n * B := by
  induction n with
  | zero =>
      simp only [iterKernel_zero, Kernel.id_apply, Nat.cast_zero, zero_mul, add_zero]
      exact ⟨integrable_dirac' hUm.stronglyMeasurable (by simp),
        le_of_eq (integral_dirac' U x hUm.stronglyMeasurable)⟩
  | succ n ih =>
      have hnorm : (fun y => ‖U y‖) = U := by
        funext y
        exact Real.norm_of_nonneg (hU0 y)
      have hPi : Integrable (fun y => ∫ z, U z ∂P y) (iterKernel P n x) := by
        apply (ih.1.add (integrable_const B)).mono'
          hUm.stronglyMeasurable.integral_kernel.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (integral_nonneg hU0)]
          exact hgrowth y
      have hi : Integrable U ((P ∘ₖ iterKernel P n) x) := by
        apply (integrable_comp_iff hUm.aestronglyMeasurable).mpr
        refine ⟨Filter.Eventually.of_forall hUi, ?_⟩
        simpa only [hnorm] using hPi
      refine ⟨hi, ?_⟩
      rw [iterKernel_succ, Kernel.integral_comp hi]
      calc
        (∫ y, ∫ z, U z ∂P y ∂iterKernel P n x) ≤
            ∫ y, U y + B ∂iterKernel P n x :=
          integral_mono hPi (ih.1.add (integrable_const B)) hgrowth
        _ = (∫ y, U y ∂iterKernel P n x) + B := by
          rw [integral_add ih.1 (integrable_const B)]
          simp
        _ ≤ U x + (n + 1 : ℕ) * B := by push_cast; linarith [ih.2]

theorem weight_toReal (n : ℕ) : (weight n).toReal = (1 / 2 : ℝ) ^ (n + 1) := by
  simp [weight, ENNReal.toReal_pow, ENNReal.toReal_inv]

theorem summable_weight_affine (a b : ℝ) :
    Summable (fun n : ℕ => (weight n).toReal * (a + n * b)) := by
  have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hnat : Summable (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (1 / 2 : ℝ)) (by norm_num))
  convert (hgeo.mul_left (a / 2)).add (hnat.mul_left (b / 2)) using 1 <;>
    first | rfl | (funext n; rw [weight_toReal, pow_succ]; ring)

theorem resolvent_integrable_of_growth (P : Kernel X X) [IsMarkovKernel P]
    (U : X → ℝ) (hUm : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    (hUi : ∀ x, Integrable U (P x)) (B : ℝ)
    (hgrowth : ∀ x, (∫ y, U y ∂P x) ≤ U x + B) (x : X) :
    Integrable U (resolvent P x) := by
  rw [resolvent_apply]
  apply integrable_sum_measure
  · intro n
    exact (iter_integrable_growth P U hUm hU0 hUi B hgrowth n x).1.smul_measure
      (weight_ne_top n)
  · apply Summable.of_nonneg_of_le
      (fun n => integral_nonneg (fun y => norm_nonneg (U y)))
      (f := fun n : ℕ => (weight n).toReal * (U x + n * B))
    · intro n
      rw [integral_smul_measure]
      have hnorm : (fun y => ‖U y‖) = U := by
        funext y
        exact Real.norm_of_nonneg (hU0 y)
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left
        (iter_integrable_growth P U hUm hU0 hUi B hgrowth n x).2
        ENNReal.toReal_nonneg
    · exact summable_weight_affine (U x) B

theorem integral_resolvent_inside (P : Kernel X X) [IsMarkovKernel P]
    {U : X → ℝ} (hUm : Measurable U)
    (hUR : ∀ x, Integrable U (resolvent P x)) (x : X) :
    (∫ y, U y ∂resolvent P x) = (1 / 2 : ℝ) * U x +
      (1 / 2 : ℝ) * (∫ y, ∫ z, U z ∂P y ∂resolvent P x) := by
  have hi := integrable_resolvent_comp P hUR x
  have hi' : Integrable U ((P ∘ₖ resolvent P) x) := by
    rw [resolvent_comm P]
    exact hi
  have heq : (∫ y, ∫ z, U z ∂resolvent P y ∂P x) =
      (∫ y, ∫ z, U z ∂P y ∂resolvent P x) := by
    rw [← Kernel.integral_comp hi, ← Kernel.integral_comp hi', resolvent_comm P]
  simpa only [heq] using resolvent_integral_eq_average P hUm hUR x

theorem resolvent_weighted_drift (P : Kernel X X) [IsMarkovKernel P]
    (U F : X → ℝ) (hUm : Measurable U) (hFm : Measurable F)
    (hU0 : ∀ x, 0 ≤ U x) (hF1 : ∀ x, 1 ≤ F x)
    (hUi : ∀ x, Integrable U (P x))
    (C : Set X) (hC : MeasurableSet C) (B : ℝ) (hB : 0 ≤ B)
    (hdrift : ∀ x, (∫ y, U y ∂P x) ≤ U x - F x + C.indicator (fun _ => B) x) :
    (∀ x, Integrable U (resolvent P x)) ∧
      ∀ x, (∫ y, 2 * U y ∂resolvent P x) ≤
        2 * U x - F x + 2 * B * (resolvent P x).real C := by
  have hF0 : ∀ x, 0 ≤ F x := fun x => (hF1 x).trans' zero_le_one
  have hCB : ∀ x, C.indicator (fun _ => B) x ≤ B := by
    intro x
    by_cases hx : x ∈ C <;> simp [hx, hB]
  have hgrowth : ∀ x, (∫ y, U y ∂P x) ≤ U x + B := by
    intro x
    linarith [hdrift x, hF0 x, hCB x]
  have hUR : ∀ x, Integrable U (resolvent P x) :=
    resolvent_integrable_of_growth P U hUm hU0 hUi B hgrowth
  have hFU : ∀ x, F x ≤ U x + B := by
    intro x
    have hpos : 0 ≤ ∫ y, U y ∂P x := integral_nonneg hU0
    linarith [hdrift x, hCB x]
  have hFR : ∀ x, Integrable F (resolvent P x) := by
    intro x
    apply ((hUR x).add (integrable_const B)).mono' hFm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (hF0 y)]
      exact hFU y
  refine ⟨hUR, ?_⟩
  intro x
  have hPUi : Integrable (fun y => ∫ z, U z ∂P y) (resolvent P x) := by
    have hi := integrable_resolvent_comp P hUR x
    rw [← resolvent_comm P] at hi
    exact hi.integral_comp
  have hCI : Integrable (C.indicator (fun _ => B)) (resolvent P x) :=
    (integrable_const B).indicator hC
  have hmono := integral_mono hPUi (((hUR x).sub (hFR x)).add hCI) hdrift
  change (∫ y, ∫ z, U z ∂P y ∂resolvent P x) ≤
    ∫ y, (U y - F y) + C.indicator (fun _ => B) y ∂resolvent P x at hmono
  rw [integral_add (f := fun y => U y - F y) ((hUR x).sub (hFR x)) hCI,
    integral_sub (hUR x) (hFR x), integral_indicator hC] at hmono
  simp only [setIntegral_const, smul_eq_mul] at hmono
  have hUeq := integral_resolvent_inside P hUm hUR x
  have hFeq := integral_resolvent_inside P hFm hFR x
  have hPFpos : 0 ≤ ∫ y, ∫ z, F z ∂P y ∂resolvent P x :=
    integral_nonneg (fun _ => integral_nonneg hF0)
  rw [integral_const_mul]
  linarith

end PoissonResolvent

end GeometricPoissonComponent5

section GeometricPoissonComponent6

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal ProbabilityTheory

namespace PoissonResolvent

set_option maxHeartbeats 1000000

variable {X : Type*} [MeasurableSpace X]

theorem localized_resolvent (P : Kernel X X) [IsMarkovKernel P]
    (U F : X → ℝ) (hUm : Measurable U) (hFm : Measurable F)
    (hU0 : ∀ x, 0 ≤ U x) (hF1 : ∀ x, 1 ≤ F x)
    (hUi : ∀ x, Integrable U (P x))
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (B : ℝ) (hB : 0 ≤ B)
    (hdrift : ∀ x, (∫ y, U y ∂P x) ≤ U x - F x + C.indicator (fun _ => B) x) :
    (∀ x, Integrable (fun y => 4 * U y) (resolvent P x)) ∧
      ∃ D : Set X, MeasurableSet D ∧ ∃ δ : ℝ≥0, 0 < δ ∧
        ∃ ν : Measure X, IsProbabilityMeasure ν ∧
          (∀ x ∈ D, (δ : ℝ≥0∞) • ν ≤ resolvent P x) ∧
          ∀ x, (∫ y, 4 * U y ∂resolvent P x) ≤
            4 * U x - F x + D.indicator (fun _ => 4 * B) x := by
  classical
  obtain ⟨hUR, hRdrift⟩ := resolvent_weighted_drift P U F hUm hFm hU0 hF1 hUi C hC B hB hdrift
  refine ⟨fun x => (hUR x).const_mul 4, ?_⟩
  let r : ℝ := (4 * (B + 1))⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hrB : 2 * B * r ≤ (1 / 2 : ℝ) := by
    have hi : (4 * (B + 1)) * r = 1 := mul_inv_cancel₀ (by positivity)
    nlinarith
  let D : Set X := {x | r ≤ (resolvent P x).real C}
  have hD : MeasurableSet D :=
    measurableSet_le measurable_const ((resolvent P).measurable_coe hC).ennreal_toReal
  obtain ⟨m, _hm, ε, hε, ν, hν, hm⟩ := hsmall
  letI : IsProbabilityMeasure ν := hν
  let c : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ m * ENNReal.ofReal ε
  let e : ℝ≥0∞ := c * ENNReal.ofReal r
  have hc0 : c ≠ 0 := by
    exact (ENNReal.mul_pos
      (ENNReal.pow_ne_zero (ne_of_gt (ENNReal.inv_pos.mpr (by finiteness))) m)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hε))).ne'
  have he0 : e ≠ 0 :=
    (ENNReal.mul_pos hc0 (ne_of_gt (ENNReal.ofReal_pos.mpr hr))).ne'
  have heT : e ≠ ∞ := by dsimp [e, c]; finiteness
  let δ : ℝ≥0 := e.toNNReal
  have hδ : 0 < δ := ENNReal.toNNReal_pos he0 heT
  have hδcoe : (δ : ℝ≥0∞) = e := ENNReal.coe_toNNReal heT
  refine ⟨D, hD, δ, hδ, ν, hν, ?_, ?_⟩
  · intro x hx
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, hδcoe]
    have hrC : ENNReal.ofReal r ≤ resolvent P x C :=
      ENNReal.ofReal_le_of_le_toReal hx
    have hmin : ∀ y ∈ C, ENNReal.ofReal ε • ν ≤ iterKernel P m y := by
      intro y hy
      apply Measure.le_iff.mpr
      intro S hS
      simpa only [Measure.smul_apply, smul_eq_mul] using hm y hy S hS
    calc
      e * ν A = c * ENNReal.ofReal r * ν A := rfl
      _ ≤ c * resolvent P x C * ν A :=
        mul_le_mul_left (mul_le_mul_right hrC c) _
      _ ≤ resolvent P x A := resolvent_minorization P C hC m (ENNReal.ofReal ε) ν hmin x A hA
  · intro x
    have herr : 2 * B * (resolvent P x).real C ≤
        F x / 2 + D.indicator (fun _ => 2 * B) x := by
      by_cases hx : x ∈ D
      · simp only [Set.indicator_of_mem hx]
        have hmass : (resolvent P x).real C ≤ 1 := measureReal_le_one
        nlinarith [hF1 x, mul_le_mul_of_nonneg_left hmass (show 0 ≤ 2 * B by positivity)]
      · simp only [Set.indicator_of_notMem hx, add_zero]
        have hmass : (resolvent P x).real C < r := lt_of_not_ge hx
        calc
          2 * B * (resolvent P x).real C ≤ 2 * B * r :=
            mul_le_mul_of_nonneg_left hmass.le (by positivity)
          _ ≤ (1 / 2 : ℝ) := hrB
          _ ≤ F x / 2 := by linarith [hF1 x]
    have hi := hRdrift x
    rw [integral_const_mul] at hi ⊢
    by_cases hx : x ∈ D
    · simp only [Set.indicator_of_mem hx] at herr ⊢
      linarith
    · simp only [Set.indicator_of_notMem hx] at herr ⊢
      linarith

end PoissonResolvent

end GeometricPoissonComponent6

section GeometricPoissonComponent7

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace WeightedPoisson

variable {X : Type*} [MeasurableSpace X]

noncomputable def subKernel (R S : Kernel X X) [IsFiniteKernel S]
    (h : S ≤ R) : Kernel X X where
  toFun x := R x - S x
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have heq : (fun x => (R x - S x) A) = fun x => R x A - S x A := by
      funext x
      exact Measure.sub_apply hA (h x)
    rw [heq]
    exact (R.measurable_coe hA).sub (S.measurable_coe hA)

theorem subKernel_apply (R S : Kernel X X) [IsFiniteKernel S]
    (h : S ≤ R) (x : X) : subKernel R S h x = R x - S x := rfl

theorem subKernel_le (R S : Kernel X X) [IsFiniteKernel S]
    (h : S ≤ R) : subKernel R S h ≤ R := fun _ => Measure.sub_le

instance subKernel_isFinite (R S : Kernel X X) [IsFiniteKernel R]
    [IsFiniteKernel S] (h : S ≤ R) : IsFiniteKernel (subKernel R S h) :=
  isFiniteKernel_of_le (subKernel_le R S h)

theorem subKernel_add (R S : Kernel X X) [IsFiniteKernel S]
    (h : S ≤ R) (x : X) : subKernel R S h x + S x = R x :=
  Measure.sub_add_cancel_of_le (h x)

noncomputable def iterate (K : Kernel X X) (f : X → ℝ) : ℕ → X → ℝ
  | 0 => f
  | n + 1 => fun x => ∫ y, iterate K f n y ∂K x

theorem iterate_zero (K : Kernel X X) (f : X → ℝ) : iterate K f 0 = f := rfl

theorem iterate_succ (K : Kernel X X) (f : X → ℝ) (n : ℕ) (x : X) :
    iterate K f (n + 1) x = ∫ y, iterate K f n y ∂K x := rfl

theorem measurable_iterate (K : Kernel X X) {f : X → ℝ}
    (hf : Measurable f) (n : ℕ) : Measurable (iterate K f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.stronglyMeasurable.integral_kernel.measurable

theorem integrable_of_bound (μ : Measure X) {W f : X → ℝ}
    (hW : Integrable W μ) (hf : Measurable f) (h : ∀ x, |f x| ≤ W x) :
    Integrable f μ := by
  apply hW.mono' hf.aestronglyMeasurable
  exact ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using h x

theorem iterate_weight_bounds (K : Kernel X X) {W F : X → ℝ}
    (_hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWi : ∀ x, Integrable W (K x)) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x)
    (hdrift : ∀ x, (∫ y, W y ∂K x) ≤ W x - F x) :
    ∀ n x, 0 ≤ iterate K F n x ∧ iterate K F n x ≤ W x := by
  have hFW : ∀ x, F x ≤ W x := by
    intro x
    have hnonneg : 0 ≤ ∫ y, W y ∂K x := integral_nonneg hW0
    linarith [hdrift x]
  intro n
  induction n with
  | zero => intro x; exact ⟨hF0 x, hFW x⟩
  | succ n ih =>
    intro x
    have hi : Integrable (iterate K F n) (K x) :=
      integrable_of_bound _ (hWi x) (measurable_iterate K hF n)
        (fun y => by rw [abs_of_nonneg (ih y).1]; exact (ih y).2)
    refine ⟨integral_nonneg (fun y => (ih y).1), ?_⟩
    have hle := integral_mono hi (hWi x) (fun y => (ih y).2)
    change (∫ y, iterate K F n y ∂K x) ≤ W x
    linarith [hdrift x, hF0 x]

theorem iterate_weight_integrable (K : Kernel X X) {W F : X → ℝ}
    (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWi : ∀ x, Integrable W (K x)) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x)
    (hdrift : ∀ x, (∫ y, W y ∂K x) ≤ W x - F x) (n : ℕ) (x : X) :
    Integrable (iterate K F n) (K x) := by
  have hb := iterate_weight_bounds K hW hW0 hWi hF hF0 hdrift n
  exact integrable_of_bound _ (hWi x) (measurable_iterate K hF n)
    (fun y => by rw [abs_of_nonneg (hb y).1]; exact (hb y).2)

theorem sum_iterate_weight_le (K : Kernel X X) {W F : X → ℝ}
    (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWi : ∀ x, Integrable W (K x)) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x)
    (hdrift : ∀ x, (∫ y, W y ∂K x) ≤ W x - F x) :
    ∀ n x, ∑ i ∈ Finset.range n, iterate K F i x ≤ W x := by
  intro n
  induction n with
  | zero => simpa using hW0
  | succ n ih =>
    intro x
    have hi : ∀ i ∈ Finset.range n, Integrable (iterate K F i) (K x) :=
      fun i _ => iterate_weight_integrable K hW hW0 hWi hF hF0 hdrift i x
    have hs : Integrable (fun y => ∑ i ∈ Finset.range n, iterate K F i y) (K x) :=
      integrable_finsetSum _ hi
    calc
      ∑ i ∈ Finset.range (n + 1), iterate K F i x
          = F x + ∫ y, ∑ i ∈ Finset.range n, iterate K F i y ∂K x := by
              rw [Finset.sum_range_succ', integral_finsetSum _ hi]
              simp only [iterate_zero, iterate_succ]
              ring
      _ ≤ F x + ∫ y, W y ∂K x := add_le_add le_rfl (integral_mono hs (hWi x) ih)
      _ ≤ W x := by linarith [hdrift x]

theorem summable_iterate_weight (K : Kernel X X) {W F : X → ℝ}
    (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWi : ∀ x, Integrable W (K x)) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x)
    (hdrift : ∀ x, (∫ y, W y ∂K x) ≤ W x - F x) (x : X) :
    Summable (fun n => iterate K F n x) :=
  summable_of_sum_range_le
    (fun n => (iterate_weight_bounds K hW hW0 hWi hF hF0 hdrift n x).1)
    (fun n => sum_iterate_weight_le K hW hW0 hWi hF hF0 hdrift n x)

end WeightedPoisson

end GeometricPoissonComponent7

section GeometricPoissonComponent8

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace WeightedPoisson

variable {X : Type*} [MeasurableSpace X]

theorem iterate_dominated (K : Kernel X X) {W F h : X → ℝ}
    (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWi : ∀ x, Integrable W (K x)) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x)
    (hdrift : ∀ x, (∫ y, W y ∂K x) ≤ W x - F x)
    (hh : Measurable h) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ x, |h x| ≤ L * F x) :
    ∀ n x, |iterate K h n x| ≤ L * iterate K F n x := by
  have hFW := iterate_weight_bounds K hW hW0 hWi hF hF0 hdrift
  intro n
  induction n with
  | zero => exact hbound
  | succ n ih =>
    intro x
    have hih : Integrable (iterate K h n) (K x) :=
      integrable_of_bound _ ((hWi x).const_mul L) (measurable_iterate K hh n)
        (fun y => (ih y).trans (mul_le_mul_of_nonneg_left (hFW n y).2 hL))
    have hiF := iterate_weight_integrable K hW hW0 hWi hF hF0 hdrift n x
    calc
      |iterate K h (n + 1) x|
          ≤ ∫ y, |iterate K h n y| ∂K x := by
            simpa [iterate_succ, Real.norm_eq_abs] using
              norm_integral_le_integral_norm (iterate K h n) (μ := K x)
      _ ≤ ∫ y, L * iterate K F n y ∂K x :=
        integral_mono hih.abs (hiF.const_mul L) ih
      _ = L * iterate K F (n + 1) x := by rw [integral_const_mul]; rfl

theorem sum_iterate_abs_le (K : Kernel X X) {W F h : X → ℝ}
    (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWi : ∀ x, Integrable W (K x)) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x)
    (hdrift : ∀ x, (∫ y, W y ∂K x) ≤ W x - F x)
    (hh : Measurable h) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ x, |h x| ≤ L * F x) (n : ℕ) (x : X) :
    |∑ i ∈ Finset.range n, iterate K h i x| ≤ L * W x := by
  calc
    |∑ i ∈ Finset.range n, iterate K h i x|
        ≤ ∑ i ∈ Finset.range n, |iterate K h i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, L * iterate K F i x :=
      Finset.sum_le_sum (fun i _ => iterate_dominated K hW hW0 hWi hF hF0 hdrift
        hh L hL hbound i x)
    _ = L * ∑ i ∈ Finset.range n, iterate K F i x := by rw [Finset.mul_sum]
    _ ≤ L * W x := mul_le_mul_of_nonneg_left
      (sum_iterate_weight_le K hW hW0 hWi hF hF0 hdrift n x) hL

theorem killed_potential (K : Kernel X X) {W F h : X → ℝ}
    (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWi : ∀ x, Integrable W (K x)) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x)
    (hdrift : ∀ x, (∫ y, W y ∂K x) ≤ W x - F x)
    (hh : Measurable h) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ x, |h x| ≤ L * F x) :
    ∃ G : X → ℝ, Measurable G ∧ (∀ x, |G x| ≤ L * W x) ∧
      (∀ x, Integrable G (K x)) ∧
      ∀ x, G x - ∫ y, G y ∂K x = h x := by
  have hd := iterate_dominated K hW hW0 hWi hF hF0 hdrift hh L hL hbound
  have hb := sum_iterate_abs_le K hW hW0 hWi hF hF0 hdrift hh L hL hbound
  have hs : ∀ x, Summable (fun n => iterate K h n x) := by
    intro x
    apply ((summable_iterate_weight K hW hW0 hWi hF hF0 hdrift x).mul_left L).of_norm_bounded
    intro n
    simpa [Real.norm_eq_abs] using hd n x
  let G : X → ℝ := fun x => ∑' n, iterate K h n x
  have hG : Measurable G := Measurable.tsum (fun n => measurable_iterate K hh n)
  have hGb : ∀ x, |G x| ≤ L * W x := by
    intro x
    have ht := (hs x).hasSum.tendsto_sum_nat.norm
    apply le_of_tendsto ht
    exact Eventually.of_forall (fun n => by simpa [Real.norm_eq_abs] using hb n x)
  have hGi : ∀ x, Integrable G (K x) := fun x =>
    integrable_of_bound _ ((hWi x).const_mul L) hG hGb
  refine ⟨G, hG, hGb, hGi, ?_⟩
  intro x
  have hm : ∀ n, Measurable (fun y => ∑ i ∈ Finset.range n, iterate K h i y) := by
    intro n
    exact Finset.measurable_sum _ (fun i _ => measurable_iterate K hh i)
  have hlim := tendsto_integral_of_dominated_convergence (μ := K x)
    (fun y => L * W y) (fun n => (hm n).aestronglyMeasurable)
    ((hWi x).const_mul L)
    (fun n => ae_of_all _ (fun y => by simpa [Real.norm_eq_abs] using hb n y))
    (ae_of_all _ (fun y => (hs y).hasSum.tendsto_sum_nat))
  have hint : ∀ n, Integrable (iterate K h n) (K x) := by
    intro n
    apply integrable_of_bound _ ((hWi x).const_mul L) (measurable_iterate K hh n)
    intro y
    exact (hd n y).trans (mul_le_mul_of_nonneg_left
      (iterate_weight_bounds K hW hW0 hWi hF hF0 hdrift n y).2 hL)
  have heq : (fun n => ∫ y, ∑ i ∈ Finset.range n, iterate K h i y ∂K x) =
      fun n => ∑ i ∈ Finset.range n, iterate K h (i + 1) x := by
    funext n
    rw [integral_finsetSum _ (fun i _ => hint i)]
    rfl
  rw [heq] at hlim
  have htail : Summable (fun n => iterate K h (n + 1) x) :=
    (hs x).comp_injective (fun _ _ h => Nat.succ.inj h)
  have hKG : (∫ y, G y ∂K x) = ∑' n, iterate K h (n + 1) x :=
    tendsto_nhds_unique hlim htail.hasSum.tendsto_sum_nat
  have hadd := (hs x).sum_add_tsum_nat_add 1
  simp only [Finset.range_one, Finset.sum_singleton, iterate_zero] at hadd
  change h x + (∑' n, iterate K h (n + 1) x) = G x at hadd
  linarith

end WeightedPoisson

end GeometricPoissonComponent8

section GeometricPoissonComponent9

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace WeightedPoisson

variable {X : Type*} [MeasurableSpace X]

theorem integral_subKernel_add (R S : Kernel X X) [IsFiniteKernel S]
    (hle : S ≤ R) {f : X → ℝ} (x : X) (hf : Integrable f (R x)) :
    (∫ y, f y ∂subKernel R S hle x) + (∫ y, f y ∂S x) = ∫ y, f y ∂ R x := by
  rw [← integral_add_measure (hf.mono_measure (subKernel_le R S hle x))
    (hf.mono_measure (hle x)), subKernel_add]

theorem oneStep_poisson (R : Kernel X X) [IsMarkovKernel R]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant R π)
    (U F f : X → ℝ) (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    (hU2 : MemLp U 2 π) (hUi : ∀ x, Integrable U (R x))
    (hF : Measurable F) (hF1 : ∀ x, 1 ≤ F x)
    (hf : Measurable f) (hfF : ∀ x, |f x| ≤ F x)
    (D : Set X) (hD : MeasurableSet D) (B : ℝ) (hB : 0 ≤ B)
    (hdrift : ∀ x, (∫ y, U y ∂ R x) ≤ U x - F x + D.indicator (fun _ => B) x)
    (δ : ℝ≥0) (hδ : 0 < δ) (ν : Measure X) [IsProbabilityMeasure ν]
    (hminor : ∀ x ∈ D, (δ : ℝ≥0∞) • ν ≤ R x) :
    ∃ G : X → ℝ, Measurable G ∧ MemLp G 2 π ∧
      (∀ x, Integrable G (R x)) ∧
      (∃ A : ℝ, 0 ≤ A ∧ ∀ x, |G x| ≤ A * (U x + 1)) ∧
      ∀ x, G x - ∫ y, G y ∂ R x = f x - ∫ y, f y ∂π := by
  classical
  have hF0 : ∀ x, 0 ≤ F x := fun x => (by norm_num : (0 : ℝ) ≤ 1).trans (hF1 x)
  have hUπ : Integrable U π := hU2.integrable (by norm_num)
  have hFupper : ∀ x, F x ≤ U x + B := by
    intro x
    have hnonneg : 0 ≤ ∫ y, U y ∂ R x := integral_nonneg hU0
    have hi : D.indicator (fun _ => B) x ≤ B := by
      by_cases hx : x ∈ D <;> simp [hx, hB]
    linarith only [hnonneg, hi, hdrift x]
  have hFπ : Integrable F π :=
    integrable_of_bound _ (hUπ.add (integrable_const B)) hF
      (fun x => by rw [abs_of_nonneg (hF0 x)]; exact hFupper x)
  have hfπ : Integrable f π := integrable_of_bound _ hFπ hf hfF
  have hFmean : 1 ≤ ∫ x, F x ∂π := by
    simpa using integral_mono (integrable_const (1 : ℝ)) hFπ hF1
  have hRUi : Integrable (fun x => ∫ y, U y ∂ R x) π :=
    (KernelL2.kernel_memLp R π hinv U hU hU2).integrable (by norm_num)
  have hID : Integrable (D.indicator (fun _ : X => B)) π :=
    (integrable_const B).indicator hD
  have hmean := integral_mono hRUi ((hUπ.sub hFπ).add hID) hdrift
  change (∫ x, ∫ y, U y ∂ R x ∂π) ≤
    ∫ x, U x - F x + D.indicator (fun _ => B) x ∂π at hmean
  rw [KernelL2.integral_invariant R π hinv hUπ,
    integral_add (f := fun x => U x - F x) (g := D.indicator (fun _ => B))
      (hUπ.sub hFπ) hID, integral_sub hUπ hFπ,
    integral_indicator_const B hD, smul_eq_mul] at hmean
  have hDpos : 0 < π.real D := by
    by_contra hn
    have hz : π.real D = 0 := le_antisymm (not_lt.mp hn) measureReal_nonneg
    rw [hz, zero_mul] at hmean
    linarith only [hmean, hFmean]
  have hDne : π D ≠ 0 := by
    intro hz
    simp [measureReal_def, hz] at hDpos
  obtain ⟨x0, hx0⟩ := nonempty_of_measure_ne_zero hDne
  have hδreal : 0 < (δ : ℝ) := hδ
  have hδenn : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hδ.ne'
  have hνU : Integrable U ν :=
    (integrable_smul_measure hδenn ENNReal.coe_ne_top).mp
      ((hUi x0).mono_measure (hminor x0 hx0))
  let S : Kernel X X := Kernel.piecewise hD (Kernel.const X ((δ : ℝ≥0∞) • ν)) 0
  have hSle : S ≤ R := by
    intro x
    by_cases hx : x ∈ D
    · simpa [S, Kernel.piecewise_apply, hx] using hminor x hx
    · simpa [S, Kernel.piecewise_apply, hx] using Measure.zero_le (R x)
  letI : IsFiniteKernel S := isFiniteKernel_of_le hSle
  let K : Kernel X X := subKernel R S hSle
  have hKle : K ≤ R := subKernel_le R S hSle
  let c : ℝ := B / (δ : ℝ)
  have hc : 0 ≤ c := div_nonneg hB hδreal.le
  have hδc : (δ : ℝ) * c = B := by dsimp [c]; field_simp
  let W : X → ℝ := fun x => U x + c
  have hW : Measurable W := hU.add_const c
  have hW0 : ∀ x, 0 ≤ W x := fun x => add_nonneg (hU0 x) hc
  have hWRi : ∀ x, Integrable W (R x) := fun x => (hUi x).add (integrable_const c)
  have hWKi : ∀ x, Integrable W (K x) := fun x => (hWRi x).mono_measure (hKle x)
  have hWν : Integrable W ν := hνU.add (integrable_const c)
  have hWνmean : 0 ≤ ∫ y, U y ∂ν := integral_nonneg hU0
  have hKW : ∀ x, (∫ y, W y ∂K x) ≤ W x - F x := by
    intro x
    have hadd := integral_subKernel_add R S hSle x (hWRi x)
    have hRW : (∫ y, W y ∂ R x) = (∫ y, U y ∂ R x) + c := by
      simp [W, integral_add (hUi x) (integrable_const c)]
    rw [hRW] at hadd
    by_cases hx : x ∈ D
    · have hSW : (∫ y, W y ∂S x) = (δ : ℝ) * ((∫ y, U y ∂ν) + c) := by
        simp [S, Kernel.piecewise_apply, hx, W,
          integral_add hνU (integrable_const c), NNReal.smul_def, smul_eq_mul, mul_add]
      rw [hSW] at hadd
      have hdx := hdrift x
      simp only [Set.indicator_of_mem hx] at hdx
      change (∫ y, W y ∂subKernel R S hSle x) ≤ U x + c - F x
      nlinarith only [hadd, hdx, hδc, mul_nonneg hδreal.le hWνmean]
    · have hSW : (∫ y, W y ∂S x) = 0 := by simp [S, Kernel.piecewise_apply, hx]
      rw [hSW] at hadd
      have hdx := hdrift x
      simp only [Set.indicator_of_notMem hx] at hdx
      change (∫ y, W y ∂subKernel R S hSle x) ≤ U x + c - F x
      linarith only [hadd, hdx]
  let h : X → ℝ := fun x => f x - ∫ y, f y ∂π
  let L : ℝ := 1 + |∫ y, f y ∂π|
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hh : Measurable h := hf.sub_const _
  have hhF : ∀ x, |h x| ≤ L * F x := by
    intro x
    have habs := abs_sub (f x) (∫ y, f y ∂π)
    have hm := mul_le_mul_of_nonneg_left (hF1 x) (abs_nonneg (∫ y, f y ∂π))
    dsimp [h, L]
    nlinarith only [habs, hm, hfF x]
  obtain ⟨G, hG, hGb, hGKi, hGK⟩ := killed_potential K hW hW0 hWKi hF hF0 hKW hh L hL hhF
  have hGRi : ∀ x, Integrable G (R x) := fun x =>
    integrable_of_bound _ ((hWRi x).const_mul L) hG hGb
  have hGν : Integrable G ν := integrable_of_bound _ (hWν.const_mul L) hG hGb
  have hW2 : MemLp W 2 π := hU2.add (memLp_const c)
  have hG2 : MemLp G 2 π :=
    (hW2.const_mul L).mono' hG.aestronglyMeasurable
      (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using hGb x))
  have hGπ : Integrable G π := hG2.integrable (by norm_num)
  have hRGπ : Integrable (fun x => ∫ y, G y ∂ R x) π :=
    (KernelL2.kernel_memLp R π hinv G hG hG2).integrable (by norm_num)
  have hRK : ∀ x, G x - ∫ y, G y ∂ R x =
      h x - D.indicator (fun _ => (δ : ℝ) * ∫ y, G y ∂ν) x := by
    intro x
    have hadd := integral_subKernel_add R S hSle x (hGRi x)
    have hSW : (∫ y, G y ∂S x) =
        D.indicator (fun _ => (δ : ℝ) * ∫ y, G y ∂ν) x := by
      by_cases hx : x ∈ D <;>
        simp [S, Kernel.piecewise_apply, hx, NNReal.smul_def, smul_eq_mul]
    rw [hSW] at hadd
    have hk := hGK x
    dsimp [K] at hk
    linarith only [hadd, hk]
  have hhπ : Integrable h π := hfπ.sub (integrable_const _)
  have hhmean : (∫ x, h x ∂π) = 0 := by simp [h, integral_sub hfπ (integrable_const _)]
  have hconsti : Integrable
      (D.indicator (fun _ : X => (δ : ℝ) * ∫ y, G y ∂ν)) π :=
    (integrable_const _).indicator hD
  have heqmean := integral_congr_ae (ae_of_all π hRK)
  rw [integral_sub hGπ hRGπ, KernelL2.integral_invariant R π hinv hGπ,
    sub_self, integral_sub hhπ hconsti, hhmean,
    integral_indicator_const _ hD, smul_eq_mul] at heqmean
  have hνG : (∫ y, G y ∂ν) = 0 := by
    have hz : π.real D * ((δ : ℝ) * ∫ y, G y ∂ν) = 0 := by linarith only [heqmean]
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hDpos.ne')).resolve_left hδreal.ne'
  refine ⟨G, hG, hG2, hGRi, ?_, ?_⟩
  · refine ⟨L * (1 + c), mul_nonneg hL (by linarith), ?_⟩
    intro x
    have hw : W x ≤ (1 + c) * (U x + 1) := by
      dsimp [W]
      nlinarith [mul_nonneg hc (hU0 x)]
    calc
      |G x| ≤ L * W x := hGb x
      _ ≤ L * ((1 + c) * (U x + 1)) := mul_le_mul_of_nonneg_left hw hL
      _ = (L * (1 + c)) * (U x + 1) := by ring
  · intro x
    simpa only [hνG, mul_zero, Set.indicator_zero, sub_zero, h] using hRK x

end WeightedPoisson

end GeometricPoissonComponent9

section GeometricPoissonComponent10

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace GeometricPoisson

variable {X : Type*} [MeasurableSpace X]

noncomputable def sqrtWeight (V : X → ℝ) (x : X) : ℝ := Real.sqrt (V x)

noncomputable def scaledSqrtWeight (d : ℝ) (V : X → ℝ) (x : X) : ℝ :=
  (2 / d) * sqrtWeight V x

theorem measurable_sqrtWeight {V : X → ℝ} (hV : Measurable V) :
    Measurable (sqrtWeight V) := hV.sqrt

omit [MeasurableSpace X] in
theorem sqrtWeight_nonneg (V : X → ℝ) (x : X) : 0 ≤ sqrtWeight V x :=
  Real.sqrt_nonneg (V x)

omit [MeasurableSpace X] in
theorem one_le_sqrtWeight {V : X → ℝ} (hV1 : ∀ x, 1 ≤ V x) (x : X) :
    1 ≤ sqrtWeight V x := Real.one_le_sqrt.mpr (hV1 x)

omit [MeasurableSpace X] in
theorem sqrtWeight_sq {V : X → ℝ} (hV0 : ∀ x, 0 ≤ V x) (x : X) :
    sqrtWeight V x ^ 2 = V x := Real.sq_sqrt (hV0 x)

omit [MeasurableSpace X] in
theorem abs_le_sqrtWeight {f V : X → ℝ} (hfV : ∀ x, f x ^ 2 ≤ V x) (x : X) :
    |f x| ≤ sqrtWeight V x := Real.abs_le_sqrt (hfV x)

theorem memLp_sqrtWeight {V : X → ℝ} (hV : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) {μ : Measure X} (hi : Integrable V μ) :
    MemLp (sqrtWeight V) 2 μ := by
  apply (memLp_two_iff_integrable_sq (measurable_sqrtWeight hV).aestronglyMeasurable).mpr
  have heq : (fun x => sqrtWeight V x ^ 2) = V := funext (sqrtWeight_sq hV0)
  rw [heq]
  exact hi

theorem integrable_sqrtWeight {V : X → ℝ} (hV : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) {μ : Measure X} [IsFiniteMeasure μ]
    (hi : Integrable V μ) : Integrable (sqrtWeight V) μ :=
  (memLp_sqrtWeight hV hV0 hi).integrable (by norm_num)

theorem measurable_kernel_sqrtWeight (P : Kernel X X) [IsMarkovKernel P]
    {V : X → ℝ} (hV : Measurable V) :
    Measurable (fun x => ∫ y, sqrtWeight V y ∂P x) := by
  have h : StronglyMeasurable (fun x => ∫ y, sqrtWeight V y ∂P x) :=
    (measurable_sqrtWeight hV).stronglyMeasurable.integral_kernel
  exact h.measurable

theorem sqrtWeight_geoDrift (P : Kernel X X) [IsMarkovKernel P]
    {V : X → ℝ} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    {d b : ℝ} {C : Set X} (hdrift : MarkovChainCLT.GeoDriftCondition P V d b C) :
    MarkovChainCLT.GeoDriftCondition P (sqrtWeight V) (d / 2) (max b 0 / 2) C := by
  have hV0 : ∀ x, 0 ≤ V x := fun x => le_trans zero_le_one (hV1 x)
  have hi : ∀ x, Integrable (sqrtWeight V) (P x) :=
    fun x => integrable_sqrtWeight hV hV0 (hdrift.1 x)
  refine ⟨hi, ?_⟩
  intro x
  have hW1 := one_le_sqrtWeight hV1 x
  have hWpos : 0 < (2 : ℝ) * sqrtWeight V x :=
    mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hW1)
  -- Integrating the square inequality is the tangent bound for the square root.
  have htangent : ∀ y, (2 * sqrtWeight V x) * sqrtWeight V y ≤ V y + V x := by
    intro y
    nlinarith only [sq_nonneg (sqrtWeight V y - sqrtWeight V x),
      sqrtWeight_sq hV0 x, sqrtWeight_sq hV0 y]
  have hmean : (2 * sqrtWeight V x) * (∫ y, sqrtWeight V y ∂P x) ≤
      (∫ y, V y ∂P x) + V x := by
    have hint := integral_mono ((hi x).const_mul (2 * sqrtWeight V x))
      ((hdrift.1 x).add (integrable_const (V x))) htangent
    simpa [integral_const_mul, integral_add (hdrift.1 x) (integrable_const (V x))] using hint
  have hdx := hdrift.2 x
  rw [← sqrtWeight_sq hV0 x] at hmean hdx
  apply (mul_le_mul_iff_of_pos_left hWpos).mp
  by_cases hx : x ∈ C
  · simp only [Set.indicator_of_mem hx, mul_one] at hdx ⊢
    have hbW : b ≤ max b 0 * sqrtWeight V x := calc
      b ≤ max b 0 := le_max_left b 0
      _ ≤ max b 0 * sqrtWeight V x := by
        simpa using mul_le_mul_of_nonneg_left hW1 (le_max_right b 0)
    nlinarith only [hmean, hdx, hbW]
  · simp only [Set.indicator_of_notMem hx, mul_zero, add_zero] at hdx ⊢
    nlinarith only [hmean, hdx]

theorem measurable_scaledSqrtWeight (d : ℝ) {V : X → ℝ} (hV : Measurable V) :
    Measurable (scaledSqrtWeight d V) :=
  measurable_const.mul (measurable_sqrtWeight hV)

omit [MeasurableSpace X] in
theorem scaledSqrtWeight_nonneg {d : ℝ} (hd : 0 < d) (V : X → ℝ) (x : X) :
    0 ≤ scaledSqrtWeight d V x :=
  mul_nonneg (div_nonneg (by norm_num) hd.le) (sqrtWeight_nonneg V x)

theorem memLp_scaledSqrtWeight (d : ℝ) {V : X → ℝ} (hV : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) {μ : Measure X} (hi : Integrable V μ) :
    MemLp (scaledSqrtWeight d V) 2 μ :=
  (memLp_sqrtWeight hV hV0 hi).const_mul (2 / d)

theorem measurable_kernel_scaledSqrtWeight (P : Kernel X X) [IsMarkovKernel P]
    (d : ℝ) {V : X → ℝ} (hV : Measurable V) :
    Measurable (fun x => ∫ y, scaledSqrtWeight d V y ∂P x) := by
  have h : StronglyMeasurable (fun x => ∫ y, scaledSqrtWeight d V y ∂P x) :=
    (measurable_scaledSqrtWeight d hV).stronglyMeasurable.integral_kernel
  exact h.measurable

theorem scaledSqrtWeight_drift (P : Kernel X X) [IsMarkovKernel P]
    {V : X → ℝ} (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    {d b : ℝ} (hd : 0 < d) {C : Set X}
    (hdrift : MarkovChainCLT.GeoDriftCondition P V d b C) :
    (∀ x, Integrable (scaledSqrtWeight d V) (P x)) ∧
      ∀ x, (∫ y, scaledSqrtWeight d V y ∂P x) ≤ scaledSqrtWeight d V x -
        sqrtWeight V x + (max b 0 / d) * C.indicator (fun _ => (1 : ℝ)) x := by
  have hsqrt := sqrtWeight_geoDrift P hV hV1 hdrift
  refine ⟨fun x => (hsqrt.1 x).const_mul (2 / d), ?_⟩
  intro x
  have hbound : (∫ y, sqrtWeight V y ∂P x) ≤ sqrtWeight V x -
      (d / 2) * sqrtWeight V x + (max b 0 / 2) * C.indicator (fun _ => (1 : ℝ)) x := by
    linarith only [hsqrt.2 x]
  calc
    (∫ y, scaledSqrtWeight d V y ∂P x) = (2 / d) * (∫ y, sqrtWeight V y ∂P x) := by
      exact integral_const_mul (2 / d) (sqrtWeight V)
    _ ≤ (2 / d) * (sqrtWeight V x - (d / 2) * sqrtWeight V x +
        (max b 0 / 2) * C.indicator (fun _ => (1 : ℝ)) x) :=
      mul_le_mul_of_nonneg_left hbound (div_nonneg (by norm_num) hd.le)
    _ = scaledSqrtWeight d V x - sqrtWeight V x +
        (max b 0 / d) * C.indicator (fun _ => (1 : ℝ)) x := by
      unfold scaledSqrtWeight
      field_simp [ne_of_gt hd]

theorem sqrtWeight_memLp_of_geoDrift [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π) (V : X → ℝ)
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (C : Set X)
    (hC : MeasurableSet C) (hsmall : MarkovChainCLT.IsSmallSet P C)
    (d b : ℝ) (hd : 0 < d) (hdrift : MarkovChainCLT.GeoDriftCondition P V d b C) :
    MemLp (sqrtWeight V) 2 π := by
  exact memLp_sqrtWeight hV (fun x => le_trans zero_le_one (hV1 x))
    (_root_.NumberGeoIntegrability.solution P π hP V hV hV1 C hC hsmall d b hd hdrift)

theorem scaledSqrtWeight_memLp_of_geoDrift [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π) (V : X → ℝ)
    (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x) (C : Set X)
    (hC : MeasurableSet C) (hsmall : MarkovChainCLT.IsSmallSet P C)
    (d b : ℝ) (hd : 0 < d) (hdrift : MarkovChainCLT.GeoDriftCondition P V d b C) :
    MemLp (scaledSqrtWeight d V) 2 π :=
  (sqrtWeight_memLp_of_geoDrift P π hP V hV hV1 C hC hsmall d b hd hdrift).const_mul (2 / d)

end GeometricPoisson

end GeometricPoissonComponent10

section GeometricPoissonComponent11

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal ProbabilityTheory

namespace PoissonResolvent

variable {X : Type*} [MeasurableSpace X]

theorem exists_poisson_of_weighted_drift (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (U F f : X → ℝ) (hUm : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    (hU2 : MemLp U 2 π) (hUi : ∀ x, Integrable U (P x))
    (hFm : Measurable F) (hF1 : ∀ x, 1 ≤ F x)
    (hfm : Measurable f) (hfF : ∀ x, |f x| ≤ F x)
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (B : ℝ) (hB : 0 ≤ B)
    (hdrift : ∀ x, (∫ y, U y ∂P x) ≤
      U x - F x + C.indicator (fun _ => B) x) :
    ∃ g : X → ℝ, Measurable g ∧ MemLp g 2 π ∧
      Measurable (fun x => ∫ y, g y ∂P x) ∧
      MemLp (fun x => ∫ y, g y ∂P x) 2 π ∧
      ∀ x, g x - ∫ y, g y ∂P x = f x - ∫ y, f y ∂π := by
  obtain ⟨hUR, D, hD, δ, hδ, ν, hν, hminor, hRdrift⟩ :=
    localized_resolvent P U F hUm hFm hU0 hF1 hUi C hC hsmall B hB hdrift
  letI : IsProbabilityMeasure ν := hν
  obtain ⟨G, hGm, hG2, hGR, _, hsolve⟩ :=
    WeightedPoisson.oneStep_poisson (resolvent P) π (resolvent_invariant P π hinv)
      (fun x => 4 * U x) F f (measurable_const.mul hUm)
      (fun x => mul_nonneg (by norm_num) (hU0 x)) (hU2.const_mul 4) hUR
      hFm hF1 hfm hfF D hD (4 * B) (mul_nonneg (by norm_num) hB) hRdrift
      δ hδ ν hminor
  exact exists_poisson_of_resolvent P π hinv f G hGm hG2 hGR hsolve

end PoissonResolvent

end GeometricPoissonComponent11

section GeometricPoissonComponent12

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT GeometricPoisson
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (d b : ℝ) (hd : 0 < d) (hdrift : GeoDriftCondition P V d b C)
    (hfV : ∀ x, f x ^ 2 ≤ V x) :
    ∃ g : X → ℝ, Measurable g ∧ MemLp g 2 π ∧
      Measurable (fun x => ∫ y, g y ∂(P x)) ∧
      MemLp (fun x => ∫ y, g y ∂(P x)) 2 π ∧
      ∀ᵐ x ∂π, g x - ∫ y, g y ∂(P x) = f x - ∫ x, f x ∂π := by
  obtain ⟨hUi, hscaled⟩ := scaledSqrtWeight_drift P hV hV1 hd hdrift
  have hbound : ∀ x, (∫ y, scaledSqrtWeight d V y ∂P x) ≤
      scaledSqrtWeight d V x - sqrtWeight V x + C.indicator (fun _ => max b 0 / d) x := by
    intro x
    by_cases hx : x ∈ C
    · simpa only [Set.indicator_of_mem hx, mul_one] using hscaled x
    · simpa only [Set.indicator_of_notMem hx, mul_zero] using hscaled x
  obtain ⟨g, hgm, hg2, hPgm, hPg2, hsolve⟩ :=
    PoissonResolvent.exists_poisson_of_weighted_drift P π hP.1
      (scaledSqrtWeight d V) (sqrtWeight V) f
      (measurable_scaledSqrtWeight d hV) (scaledSqrtWeight_nonneg hd V)
      (scaledSqrtWeight_memLp_of_geoDrift P π hP V hV hV1 C hC hsmall d b hd hdrift)
      hUi (measurable_sqrtWeight hV) (one_le_sqrtWeight hV1) hf (abs_le_sqrtWeight hfV)
      C hC hsmall (max b 0 / d) (div_nonneg (le_max_right b 0) hd.le) hbound
  exact ⟨g, hgm, hg2, hPgm, hPg2, Filter.Eventually.of_forall hsolve⟩

end GeometricPoissonComponent12


end NumberPort_geo_drift
section MainCandidate

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (d b : ℝ) (hd : 0 < d) (hdrift : GeoDriftCondition P V d b C)
    (hfV : ∀ x, f x ^ 2 ≤ V x) :
    SatisfiesCLT P π f := by
  obtain ⟨g, hgm, hgL2, hGm, hPgL2, hpois⟩ :=
    _root_.NumberPort_geo_drift.solution P π hP f hf V hV hV1 C hC hsmall d b hd hdrift hfV
  obtain ⟨v, hmart⟩ := martingaleCLT_chain P π hP g hgm hgL2
  set G : X → ℝ := fun x => ∫ y, g y ∂(P x) with hG
  -- lift the π-a.e. Poisson identity to: a.s. it holds at *every* coordinate at once
  have hae : ∀ᵐ ω ∂(chainMeasure P π), ∀ i : ℕ,
      g (ω i) - G (ω i) = f (ω i) - ∫ x, f x ∂π := by
    rw [ae_all_iff]
    intro i
    refine ae_of_ae_map (f := fun ω : ℕ → X => ω i)
      (p := fun y => g y - G y = f y - ∫ x, f x ∂π) (measurable_pi_apply i).aemeasurable ?_
    rw [map_coord_chainMeasure P π hP.1 i]
    exact hpois
  -- the martingale approximation, pointwise on each path
  have hdecomp : ∀ᵐ ω ∂(chainMeasure P π), ∀ (n : ℕ),
      Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π)
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (g (ω (i + 1)) - G (ω i))
        = (Real.sqrt n)⁻¹ * (G (ω 0) - G (ω n)) := by
    filter_upwards [hae] with ω hω n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [sampleAvg]
    · have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hsn : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
      have hnn : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      have key : ∑ i ∈ Finset.range n, ((f (ω (i + 1)) - ∫ x, f x ∂π) - (g (ω (i+1)) - G (ω i)))
          = G (ω 0) - G (ω n) := by
        have : ∀ i, ((f (ω (i + 1)) - ∫ x, f x ∂π) - (g (ω (i+1)) - G (ω i)))
            = G (ω i) - G (ω (i + 1)) := by
          intro i
          have := hω (i + 1)
          simp only [hG] at this ⊢
          linarith
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_range_sub' (fun i => G (ω i)) n]
      have hsamp : Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π)
          = (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (f (ω (i + 1)) - ∫ x, f x ∂π) := by
        rw [sampleAvg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
        field_simp
        rw [Real.sq_sqrt (by positivity)]
        ring
      rw [hsamp, ← mul_sub, ← Finset.sum_sub_distrib, key]
  -- the remainder vanishes in probability
  have hGL1 : Integrable G π := hPgL2.integrable (by norm_num)
  have hD := tendstoInMeasure_inv_sqrt_coord_sub P π hP G hGm hGL1
  have hsub : ∀ n : ℕ, (fun ω : ℕ → X => (Real.sqrt n)⁻¹ * (G (ω 0) - G (ω n)))
      =ᵐ[chainMeasure P π]
      ((fun (m : ℕ) (ω : ℕ → X) => Real.sqrt m * (sampleAvg f m ω - ∫ x, f x ∂π))
        - (fun (m : ℕ) (ω : ℕ → X) =>
            (Real.sqrt m)⁻¹ * ∑ i ∈ Finset.range m, (g (ω (i + 1)) - G (ω i)))) n := by
    intro n
    filter_upwards [hdecomp] with ω hω
    exact (hω n).symm
  -- Slutsky
  refine satisfiesCLT_of_stationary_clt P π hP f hf v ?_
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hmart
    (TendstoInMeasure.congr hsub (by rfl) hD) (fun n => ?_)
  exact (((Finset.measurable_fun_sum _
    (fun i _ => hf.comp (measurable_pi_apply (i + 1)))).const_mul _).sub_const _).const_mul _
    |>.aemeasurable

end MainCandidate
#print axioms solution
