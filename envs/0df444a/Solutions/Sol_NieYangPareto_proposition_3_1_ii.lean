-- Prove2me | solution 1 for NieYangPareto.proposition_3_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-10T12:30:24.058714+00:00
-- url     : https://prove2.me/submissions/2c6c813b-8a2c-4ec5-a553-19582a9f378c

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_ParetoNotions
import Definitions.Def_NieYangPareto_MOP_U

set_option autoImplicit false

open NieYangPareto
open scoped BigOperators

theorem solution {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (v : Fin m → ℝ) (hv : v ∈ P.obj '' P.K) (hU : Convex ℝ P.U)
    (hWPV : P.IsWeaklyParetoValue v) :
    ∃ w : Fin m → ℝ, w ≠ 0 ∧ 0 ≤ w ∧ ∀ u ∈ P.U, w ⬝ᵥ v ≤ w ⬝ᵥ u := by
  obtain ⟨x, ⟨hx, hweak⟩, rfl⟩ := hWPV
  have hboundary : P.obj x ∉ interior P.U := by
    intro hi
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
    let p : Fin m → ℝ := fun i => P.obj x i - ε / 2
    have hp : p ∈ Metric.ball (P.obj x) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
      refine (pi_norm_le_iff_of_nonneg (show 0 ≤ ε / 2 by positivity)).mpr (fun i => ?_)
      change ‖P.obj x i - ε / 2 - P.obj x i‖ ≤ ε / 2
      rw [show P.obj x i - ε / 2 - P.obj x i = -(ε / 2) by ring, norm_neg, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    obtain ⟨z, hz, hle⟩ := hball hp
    exact hweak ⟨z, hz, fun i => (hle i).trans_lt (show p i < P.obj x i by dsimp [p]; linarith)⟩
  have hint : (interior P.U).Nonempty := by
    let O : Set (Fin m → ℝ) :=
      ⋂ i : Fin m, (fun u : Fin m → ℝ => u i) ⁻¹' Set.Ioi (P.obj x i)
    have hO : IsOpen O := isOpen_iInter_of_finite fun i =>
      isOpen_Ioi.preimage (continuous_apply i)
    have hsubset : O ⊆ P.U := fun u hu =>
      ⟨x, hx, fun i => (show P.obj x i < u i from Set.mem_iInter.mp hu i).le⟩
    refine ⟨fun i => P.obj x i + 1, interior_maximal hsubset hO ?_⟩
    exact Set.mem_iInter.mpr fun i => lt_add_one (P.obj x i)
  obtain ⟨f, hf, hsupport⟩ := geometric_hahn_banach_of_nonempty_interior_point hU hboundary hint
  let g := -f
  have hg : ∀ u ∈ P.U, g (P.obj x) ≤ g u := by
    intro u hu
    change -(f (P.obj x)) ≤ -(f u)
    exact neg_le_neg (hsupport u hu)
  let w : Fin m → ℝ := fun i => g (Pi.single i 1)
  have hdot (u : Fin m → ℝ) : g u = w ⬝ᵥ u := by
    have hu : (∑ i, u i • (Pi.single i (1 : ℝ) : Fin m → ℝ)) = u := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]
    conv_lhs => rw [← hu]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct, w, mul_comm]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro hzero
    apply hf
    ext u
    have hgu := hdot u
    rw [hzero] at hgu
    simpa [g, dotProduct] using hgu
  · intro i
    let e : Fin m → ℝ := Pi.single i 1
    have heU : P.obj x + e ∈ P.U := by
      refine ⟨x, hx, fun j => ?_⟩
      change P.obj x j ≤ P.obj x j + e j
      have he : 0 ≤ e := Pi.single_nonneg.mpr zero_le_one
      exact le_add_of_nonneg_right (show 0 ≤ e j from he j)
    have h := hg _ heU
    rw [map_add] at h
    change 0 ≤ g e
    linarith
  · intro u hu
    rw [← hdot, ← hdot]
    exact hg u hu

#print axioms solution