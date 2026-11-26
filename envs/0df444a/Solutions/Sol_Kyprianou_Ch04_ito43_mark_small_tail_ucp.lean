-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_mark_small_tail_ucp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:25:38.639808+00:00
-- url     : https://prove2.me/submissions/75a205cd-799f-4114-80f3-d1c9d105e24d

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_jump_energy_localisation
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_tightness
import Theorems.Thm_Kyprianou_Ch04_ito43_localised_two_energy_tail
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_zero_near_origin
import Theorems.Thm_Kyprianou_Ch04_ito43_mark_cutoff_small_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_mark_difference_energy_bound
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
          (nhds (Xleft t omega)))
    (r : ℝ → ℝ) (hr : Continuous r) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z, |r z| ≤ C*z^2)
    (hs : ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ z, |z| ≤ δ → |r z| ≤ e*z^2) :
    ∀ T : NNReal,
    let E : ℕ → NNReal → Omega → ℝ := fun n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), r z.2 ∂(pathJumpMeasure X Xleft w)) -
        ∑ k ∈ Finset.range n, r (X (v (k+1)) w-X (v k) w)
    let A : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      let c : ℝ → ℝ := fun z => r z * min 1 (max 0 (|z| * ((m:ℝ)+1)-1))
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), c z.2 ∂(pathJumpMeasure X Xleft w)) -
        ∑ k ∈ Finset.range n, c (X (v (k+1)) w-X (v k) w)
    ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∃ m : ℕ,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, e ≤ |E n t w-A m n t w|}).toReal ≤ η := by
  intro T E A e he η hη
  let H : NNReal := T+1
  have hTH : T ≤ H := le_self_add
  have hH : 0 < H := by dsimp [H]; positivity
  obtain ⟨D,hD,hJ⟩ := (Kyprianou.Ch04.ito43_levy_jump_energy_localisation P X Xleft
    hLevy triplet hTriplet hLeft H hH).2 (η/3) (by positivity)
  obtain ⟨G,hG,hQ⟩ := Kyprianou.Ch04.ito43_grid_energy_tightness P X hLevy
    triplet hTriplet T (η/3) (by positivity)
  let b := e/(2*(G+D))
  have hb0 : 0 < b := by dsimp [b]; positivity
  obtain ⟨m,hm⟩ := Kyprianou.Ch04.ito43_mark_cutoff_small_bound r hs b hb0
  refine ⟨m,?_⟩
  let c : ℝ → ℝ := fun z => r z*min 1 (max 0 (|z| * ((m:ℝ)+1)-1))
  have hc (z : ℝ) : |c z| ≤ C*z^2 := by
    have hh := (Kyprianou.Ch04.ito43_cutoff_zero_near_origin m).2.1 z
    dsimp [c]
    rw [abs_mul,abs_of_nonneg hh.1]
    exact (mul_le_mul_of_nonneg_left hh.2 (abs_nonneg _)).trans (by simpa using hb z)
  let J : Omega → (Ioc (0:NNReal) H → ℝ) := fun w s => (X s w-Xleft s w)^2
  let V : Set Omega := {w | ¬ Summable (J w) ∨ D < ∑' s, J w s}
  let Q : ℕ → NNReal → Omega → ℝ := fun n t w =>
    ∑ k ∈ Finset.range n, (X (min t (T*((k+1:ℕ):NNReal)/(n:NNReal))) w-
      X (min t (T*(k:NNReal)/(n:NNReal))) w)^2
  have heq : b*(G+D) = e/2 := by dsimp [b]; field_simp
  have hsm : b*(G+D) < e := by rw [heq]; linarith
  apply Kyprianou.Ch04.ito43_localised_two_energy_tail P T ∅ V Q
    (fun n t w => E n t w-A m n t w) (fun w => ∑' s, J w s) G D b e η
    hb0.le hsm (by simp; positivity) hJ hQ
  filter_upwards [hLevy.cadlag_ae,hLeft] with w hw hl
  intro _ hv
  have hs' : Summable (J w) := by
    by_contra h
    exact hv (Or.inl h)
  refine ⟨le_of_not_gt (fun h => hv (Or.inr h)),fun n t ht => ?_⟩
  exact Kyprianou.Ch04.ito43_mark_difference_energy_bound X Xleft w hw hl H T hTH
    hs' r c C b hC hb0.le hb hc hm n t ht
