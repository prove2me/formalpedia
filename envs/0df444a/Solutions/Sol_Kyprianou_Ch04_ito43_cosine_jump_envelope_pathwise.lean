-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_jump_envelope_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:42:18.89798+00:00
-- url     : https://prove2.me/submissions/d79fb8e8-d8d7-4d27-b3dd-f28f157b2f02

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_jump_energy_localisation
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_deficit_square_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_deficit_frequency_limit
import Theorems.Thm_Kyprianou_Ch04_exercise41CadlagPhysicalJumpsCountableV17
import Theorems.Thm_Kyprianou_Ch04_ito43_path_jump_kernel_energy_bound
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Omega : Type} [MeasurableSpace Omega]
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
    let J : ℕ → NNReal → Omega → ℝ := fun m t w =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        q m z.2 ∂(pathJumpMeasure X Xleft w)
    (∀ᵐ w ∂P, Tendsto (fun m => J m (T+1) w) atTop (nhds 0)) ∧
    (∀ᵐ w ∂P, ∀ m t, t ≤ T → |J m t w| ≤ |J m (T+1) w|) := by 
  intro T q J
  have henergy := (ito43_levy_jump_energy_localisation P X Xleft hLevy triplet hTriplet hLeft (T+1) (by positivity)).1
  have H : ∀ᵐ w ∂P, (Tendsto (fun m => J m (T+1) w) atTop (nhds 0)) ∧
      ∀ m t, t ≤ T → |J m t w| ≤ |J m (T+1) w| := by
    filter_upwards [hLevy.cadlag_ae,hLeft,henergy] with w hc hl hs
    have hcount := exercise41CadlagPhysicalJumpsCountableV17
      (fun s => X s w) (fun s => Xleft s w) (fun s => (hc s).1) hl
    let S : Set (ℝ × ℝ) := Icc (0:ℝ) ((T+1:NNReal):ℝ) ×ˢ univ
    let μ := (pathJumpMeasure X Xleft w).restrict S
    have hi : Integrable (fun z : ℝ × ℝ => z.2^2/2) μ :=
      (ito43_path_jump_kernel_energy_bound X Xleft w hcount (T+1) (T+1)
        le_rfl (1/2) (by norm_num) hs _ (by
          intro s hs hst
          rw [abs_of_nonneg (by positivity)]
          ring_nf
          exact le_rfl)).1
    have hq (m : ℕ) (z : ℝ) := ito43_cosine_deficit_square_bound ((m:ℝ)+1) z (by positivity)
    have hm (m : ℕ) : AEStronglyMeasurable (fun z : ℝ × ℝ => q m z.2) μ :=
      (show Continuous (fun z : ℝ × ℝ => q m z.2) by dsimp [q]; fun_prop).aestronglyMeasurable
    have hdom (m : ℕ) : ∀ᵐ z ∂μ, ‖q m z.2‖ ≤ z.2^2/2 :=
      Eventually.of_forall fun z => by rw [Real.norm_of_nonneg (hq m z.2).1]; exact (hq m z.2).2.1
    have hlim : ∀ᵐ z ∂μ, Tendsto (fun m => q m z.2) atTop (nhds 0) :=
      Eventually.of_forall fun z => ito43_cosine_deficit_frequency_limit z.2
    constructor
    · simpa [J,μ,S] using MeasureTheory.tendsto_integral_of_dominated_convergence _ hm hi hdom hlim
    · intro m t ht
      have hqi : Integrable (fun z : ℝ × ℝ => q m z.2) μ := hi.mono' (hm m) (hdom m)
      have hpos : ∀ z : ℝ × ℝ, 0 ≤ q m z.2 := fun z => (hq m z.2).1
      have hsub : Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ) ⊆ S := by
        intro z hz
        exact ⟨⟨hz.1.1,hz.1.2.trans (by exact_mod_cast ht.trans (by simp : T ≤ T+1))⟩,hz.2⟩
      have hle := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (Eventually.of_forall hpos) hqi
      dsimp [J]
      rw [abs_of_nonneg (integral_nonneg hpos),abs_of_nonneg (integral_nonneg hpos)]
      exact hle
  exact ⟨H.mono fun _ h => h.1,H.mono fun _ h => h.2⟩
