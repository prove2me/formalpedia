-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_translated_killed_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T09:43:19.193965+00:00
-- url     : https://prove2.me/submissions/138a90c2-2cbd-4e1c-9690-9e8cbdae831c

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_halfline_occupation_qpos_set_identity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) (x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) :
    (∫⁻ y in A, if 0 ≤ y + (n : ℝ) - x then
      ENNReal.ofReal (Real.exp (-(Phi ψ q) * (y - x)) *
        (Real.exp (-(Phi ψ q) * (n : ℝ)) * W q n) - W q (x - y))
      else 0) = (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
      P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X (n : ℝ)) 0 ω ∧
        shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) := by
  classical
  let c : ℝ := (n : ℝ) - x
  let B : Set ℝ := (fun y : ℝ => y - c) ⁻¹' A
  have hB : MeasurableSet B := (measurable_id.sub measurable_const) hA
  have h := p2m88_halfline_occupation_qpos_set_identity Ω P D ψ W hψ hW q n hq
    (Nat.cast_nonneg n) B hB
  rw [withDensity_apply _ hB, Measure.restrict_restrict hB] at h
  let g (z : ℝ) := ENNReal.ofReal (killedHalflineDensity ψ q (W q) n z)
  let G (z : ℝ) : ℝ≥0∞ := if 0 ≤ z then g z else 0
  have hG : (∫⁻ z in B, G z) = ∫⁻ z in B ∩ Ici 0, g z := by
    have he : G = (Ici (0 : ℝ)).indicator g := by
      funext z; simp [G, Set.indicator]
    rw [he, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    rw [inter_comm]
  have hmp := (measurePreserving_add_right (volume : Measure ℝ) c)
    |>.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight c) G B
  have hp : (fun y : ℝ => y+c) ⁻¹' B = A := by
    ext y; simp [B]
  rw [hp, hG] at hmp
  calc
    _ = ∫⁻ y in A, G (y+c) := by
      apply lintegral_congr
      intro y
      have h1 : y + c = y + (n : ℝ) - x := by dsimp [c]; ring
      have h2 : -(Phi ψ q) * (y+c) =
        -(Phi ψ q) * (y-x) + -(Phi ψ q) * (n : ℝ) := by dsimp [c]; ring
      have h3 : (n : ℝ) - (y+c) = x-y := by dsimp [c]; ring
      simp only [G, g, killedHalflineDensity, h2, h3, Real.exp_add, mul_assoc]
      rw [h1]
    _ = _ := by
      rw [hmp, h]
      apply lintegral_congr
      intro t
      congr 1
      congr 1
      ext ω
      simp only [B, mem_preimage, mem_setOf_eq, shifted]
      have he : (n : ℝ) + D.X t ω - c = x + D.X t ω := by dsimp [c]; ring
      rw [he]
