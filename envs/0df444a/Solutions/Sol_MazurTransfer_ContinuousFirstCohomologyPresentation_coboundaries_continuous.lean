-- Prove2me | solution 1 for MazurTransfer.ContinuousFirstCohomologyPresentation.coboundaries_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T23:30:31.297457+00:00
-- url     : https://prove2.me/submissions/c120db8c-bfa6-4c65-8a0e-54feee641932

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous H1 is continuous 1-cocycles modulo
1-coboundaries, presented inside Mathlib algebraic group cohomology.
The forgetful map is checked injective; comparison to Mathlib homological
continuous cohomology is a separate boundary. Named downstream consumer:
the actual norm Kummer injection and the local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyPresentationData
noncomputable section
open MazurTransfer.ContinuousFirstCohomologyPresentation
theorem solution (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] [ContinuousSMul G M] (z : G → Additive M)
    (hz : z ∈ groupCohomology.coboundaries₁ (rep G M)) :
    Continuous (fun g : G => (Additive.toMul (z g) : M)) := by
  obtain ⟨m, hm⟩ := groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁
    (fun g : G => (Additive.toMul (z g) : M)) hz
  have heq : (fun g : G => (Additive.toMul (z g) : M)) = (fun g : G => g • m / m) := by
    funext g
    exact (hm g).symm
  rw [heq]
  simp only [div_eq_mul_inv]
  exact ((continuous_id : Continuous (fun g : G => g)).smul
    (continuous_const : Continuous (fun _ : G => (m : M)))).mul continuous_const

#print axioms solution
