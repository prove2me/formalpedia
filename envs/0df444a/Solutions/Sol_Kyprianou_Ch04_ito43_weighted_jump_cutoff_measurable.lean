-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_jump_cutoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:16:11.706929+00:00
-- url     : https://prove2.me/submissions/a05a7441-e4b1-4385-89c6-1afa792f054c

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_general_kernel_jump_series
import Theorems.Thm_Kyprianou_Ch04_ito43_cadlag_stopped_cutoff_kernel_uniform
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set
theorem solution    {Omega : Type} [MeasurableSpace Omega]
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
    ∀ (t : NNReal) (m : ℕ), AEMeasurable (fun w =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        g (z.1,Xleft z.1.toNNReal w)*z.2^2/2 *
          min 1 (max 0 (|z.2| * ((m:ℝ)+1)-1))
          ∂(pathJumpMeasure X Xleft w)) P := by
  intro t m
  let K : NNReal → ℝ → ℝ → ℝ := fun s x z =>
    g ((s:ℝ),x)*z^2/2*min 1 (max 0 (|z| * ((m:ℝ)+1)-1))
  have hG : Continuous (fun p : NNReal × ℝ × ℝ => g ((p.1:ℝ),p.2.1)) :=
    hg.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))
      (fun p => ⟨p.1.coe_nonneg,Set.mem_univ _⟩)
  have hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2) := by
    let Z : NNReal × ℝ × ℝ → ℝ := fun p => p.2.2
    have hZ : Continuous Z := continuous_snd.comp continuous_snd
    exact ((hG.mul (hZ.pow 2)).div_const 2).mul
      (continuous_const.min (continuous_const.max ((hZ.abs.mul continuous_const).sub continuous_const)))
  have hρ : 0 < 1/((m:ℝ)+1) := by positivity
  have hzero (s : NNReal) (x z : ℝ) (hz : |z| ≤ 1/((m:ℝ)+1)) : K s x z = 0 := by
    have hh := (le_div_iff₀ (by positivity : 0 < (m:ℝ)+1)).mp hz
    dsimp [K]
    rw [max_eq_left (by linarith : |z| * ((m:ℝ)+1)-1 ≤ 0),min_eq_right zero_le_one,mul_zero]
  let F : ℕ → Omega → ℝ := fun n w =>
    ∑ k ∈ Finset.range n, K (t*(k:NNReal)/(n:NNReal)) (X (t*(k:NNReal)/(n:NNReal)) w)
      (X (min t (t*((k+1:ℕ):NNReal)/(n:NNReal))) w-X (min t (t*(k:NNReal)/(n:NNReal))) w)
  have hx := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hLevy
  have hm (n : ℕ) : AEMeasurable (F n) P := by
    apply Finset.aemeasurable_fun_sum
    intro k hk
    exact hK.measurable.comp_aemeasurable (aemeasurable_const.prodMk
      ((hx _).prodMk ((hx _).sub (hx _))))
  refine aemeasurable_of_tendsto_metrizable_ae atTop hm ?_
  filter_upwards [hLevy.cadlag_ae,hLeft] with w hc hl
  have h := ito43_cadlag_stopped_cutoff_kernel_uniform (fun s => X s w)
    (fun s => Xleft s w) hc hl K hK _ hρ hzero t
  have h0 (s : NNReal) (x : ℝ) : K s x 0 = 0 := by simp [K]
  have heq := ito43_general_kernel_jump_series X Xleft w hc hl K h0 t
  have heq' : (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
      g (z.1,Xleft z.1.toNNReal w)*z.2^2/2 *
        min 1 (max 0 (|z.2| * ((m:ℝ)+1)-1)) ∂(pathJumpMeasure X Xleft w)) =
      ∑' s : Ioc (0:NNReal) t, K s (Xleft s w) (X s w-Xleft s w) := by
    rw [← heq]
    apply setIntegral_congr_fun (measurableSet_Icc.prod MeasurableSet.univ)
    intro z hz
    dsimp [K]
    rw [max_eq_left hz.1.1]
  rw [heq']
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨N,hN⟩ := eventually_atTop.mp (h e he)
  exact ⟨N,fun n hn => by rw [Real.dist_eq]; exact hN n hn t le_rfl⟩
