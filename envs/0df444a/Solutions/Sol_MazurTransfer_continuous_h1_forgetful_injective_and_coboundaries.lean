-- Prove2me | solution 1 for MazurTransfer.continuous_h1_forgetful_injective_and_coboundaries
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T19:54:32.914604+00:00
-- url     : https://prove2.me/submissions/47a9823b-4a39-4644-8ead-eefdbd957c85

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0. -/
import Definitions.Def_mazur_continuous_h1_cocycle_quotient
open MazurTransfer.PublicContinuousFirstCohomologyPresentation
theorem solution
    (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] [ContinuousSMul G M] :
    Function.Injective (forgetH1 G M) ∧
      (∀ z : continuousCocycles G M, classMap G M z = 0 ↔
        (z.val : G → Additive M) ∈ groupCohomology.coboundaries₁ (rep G M)) ∧
      (∀ f : G → Additive M, f ∈ groupCohomology.coboundaries₁ (rep G M) →
        Continuous (fun g : G => (Additive.toMul (f g) : M))) := by
  refine ⟨QuotientAddGroup.kerLift_injective (forgetCocycles G M), ?_, ?_⟩
  · intro z
    rw [← (QuotientAddGroup.kerLift_injective (forgetCocycles G M)).eq_iff, map_zero]
    change groupCohomology.H1π (rep G M) z.val = 0 ↔ _
    exact groupCohomology.H1π_eq_zero_iff z.val
  · intro f hf
    obtain ⟨m, hm⟩ := groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁
      (fun g : G => (Additive.toMul (f g) : M)) hf
    have heq : (fun g : G => (Additive.toMul (f g) : M)) = (fun g : G => g • m / m) := by
      funext g
      exact (hm g).symm
    rw [heq]
    simp only [div_eq_mul_inv]
    exact ((continuous_id : Continuous (fun g : G => g)).smul
      (continuous_const : Continuous (fun _ : G => (m : M)))).mul continuous_const

#print axioms solution
