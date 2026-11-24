-- Prove2me | solution 1 for GlobalTheory.T.exists_fourier_expansion_holomorphic_tube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:49.604812+00:00
-- url     : https://prove2.me/submissions/6154d249-df61-4fc3-8532-c7b456979a2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTube
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTubeStatement
import Theorems.Thm_GlobalTheory_exists_fourier_expansion_tube


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)) (f : (ι → ℂ) → ℂ), IsOpen Ω → Convex ℝ Ω → DifferentiableOn ℂ f {z | (fun i => (z i).im) ∈ Ω} → (∀ z, (fun i => (z i).im) ∈ Ω → ∀ m : ι → ℤ, f (z + fun i => (m i : ℂ)) = f z) → ∃ a : (ι → ℤ) → ℂ, (∀ z, (fun i => (z i).im) ∈ Ω → HasSum (fun ν : ι → ℤ => a ν * cexp (2 * π * I * ∑ i, (ν i : ℂ) * z i)) (f z)) ∧ ∀ y ∈ Ω, ∀ ν : ι → ℤ, a ν = ∫ x in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1), f (fun i => (x i : ℂ) + I * y i) * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + I * y i))) := by
  first | exact @GlobalTheory.exists_fourier_expansion_tube | exact GlobalTheory.exists_fourier_expansion_tube | (intros; apply GlobalTheory.exists_fourier_expansion_tube <;> assumption)
end _root_.GlobalTheory.T
