-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_residual_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:42:19.034475+00:00
-- url     : https://prove2.me/submissions/5c3e8eee-04a9-4046-9207-1f2abce05f97

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_jump_energy_localisation
import Theorems.Thm_Kyprianou_Ch04_exercise41CadlagPhysicalJumpsCountableV17
import Theorems.Thm_Kyprianou_Ch04_ito43_path_jump_kernel_energy_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_deficit_square_bound
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
    let E : ℕ → NNReal → Omega → ℝ := fun n t omega =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ((triplet.gaussianVariance : ℝ) / 2) *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), (1 : ℝ) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
      (X (v (k+1)) omega - X (v k) omega)^2 / 2)
    let A : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t omega =>
      let a : ℝ := (m:ℝ)+1
      let r : ℝ → ℝ := fun z => z^2/2-(1-Real.cos (a*z))/a^2
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
        r z.2 ∂(pathJumpMeasure X Xleft omega)) -
      (∑ k ∈ Finset.range n, r (X (v (k+1)) omega-X (v k) omega))
    let B : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w => E n t w-A m n t w
    let q : ℕ → ℝ → ℝ := fun m z => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
    let G : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ((triplet.gaussianVariance:ℝ)/2)*(t:ℝ) -
        ∑ k ∈ Finset.range n, q m (X (v (k+1)) w-X (v k) w)
    let J : ℕ → NNReal → Omega → ℝ := fun m t w =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        q m z.2 ∂(pathJumpMeasure X Xleft w)
    ∀ᵐ w ∂P, ∀ m n t, t ≤ T → B m n t w = G m n t w+J m t w := by 
  intro T E A B q G J
  have henergy := (ito43_levy_jump_energy_localisation P X Xleft hLevy triplet hTriplet hLeft (T+1) (by positivity)).1
  filter_upwards [hLevy.cadlag_ae,hLeft,henergy] with w hc hl hsum
  intro m n t ht
  have hcount := exercise41CadlagPhysicalJumpsCountableV17
    (fun s => X s w) (fun s => Xleft s w) (fun s => (hc s).1) hl
  let S : Set (ℝ × ℝ) := Icc (0:ℝ) (t:ℝ) ×ˢ univ
  let μ := (pathJumpMeasure X Xleft w).restrict S
  let F : ℝ × ℝ → ℝ := fun z => z.2^2/2
  let Q : ℝ × ℝ → ℝ := fun z => q m z.2
  have hiF : Integrable F μ :=
    (ito43_path_jump_kernel_energy_bound X Xleft w hcount (T+1) t
      (ht.trans (by simp)) (1/2) (by norm_num) hsum F (by
        intro s hs hst
        dsimp [F]
        rw [abs_of_nonneg (by positivity)]
        ring_nf
        exact le_rfl
        )).1
  have hiQ : Integrable Q μ :=
    (ito43_path_jump_kernel_energy_bound X Xleft w hcount (T+1) t
      (ht.trans (by simp)) (1/2) (by norm_num) hsum Q (by
        intro s hs hst
        have h := ito43_cosine_deficit_square_bound ((m:ℝ)+1) (X s w-Xleft s w) (by positivity)
        change |q m (X s w-Xleft s w)| ≤ _
        rw [abs_of_nonneg h.1]
        linarith [h.2.1]
        )).1
  have htime : (∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) = (t:ℝ) := by
    simp [Measure.real,Real.volume_Icc,NNReal.coe_nonneg]
  dsimp only [B,E,A,G,J]
  rw [htime]
  change _ - ((∫ z, (F z-Q z) ∂μ) - _) = _
  rw [integral_sub hiF hiQ, Finset.sum_sub_distrib]
  let v : ℕ → NNReal := fun k => min t (T*(k:NNReal)/(n:NNReal))
  let d : ℕ → ℝ := fun k => X (v (k+1)) w-X (v k) w
  change (((triplet.gaussianVariance:ℝ)/2)*(t:ℝ)+(∫ z,F z ∂μ)-∑ k ∈ Finset.range n,(d k)^2/2) - (((∫ z,F z ∂μ)-(∫ z,Q z ∂μ))-( (∑ k ∈ Finset.range n,(d k)^2/2)-(∑ k ∈ Finset.range n,q m (d k)))) = ((triplet.gaussianVariance:ℝ)/2)*(t:ℝ)-(∑ k ∈ Finset.range n,q m (d k))+(∫ z,Q z ∂μ)
  ring
