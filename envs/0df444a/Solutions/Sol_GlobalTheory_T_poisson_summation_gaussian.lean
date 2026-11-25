-- Prove2me | solution 1 for GlobalTheory.T.poisson_summation_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:13.549473+00:00
-- url     : https://prove2.me/submissions/825630ba-b577-490b-b3eb-83d51b16ed56

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PoissonSummationGaussian
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PoissonSummationGaussianStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_PoiLat_poisson_shifted_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Z : Matrix κ κ ℂ), Z.IsSymm → (Z.map Complex.im).PosDef → ∀ (g : Matrix κ κ ℝ), g.det ≠ 0 → ∀ a : κ → ℝ, let f : (κ → ℝ) → ℂ := fun x => Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ)))); let fh : (κ → ℝ) → ℂ := fun y => ∫ x, f x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ)); Summable (fun n : κ → ℤ => ‖f (a + g *ᵥ fun i => (n i : ℝ))‖) ∧ Summable (fun n : κ → ℤ => ‖fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ))‖) ∧ ∑' n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) = ((|g.det|⁻¹ : ℝ) : ℂ) * ∑' n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.PoiLat.poisson_shifted_lattice | exact GlobalTheory.CompanionTheory.SW.Core.PoiLat.poisson_shifted_lattice | (intros; apply GlobalTheory.CompanionTheory.SW.Core.PoiLat.poisson_shifted_lattice <;> assumption)
end _root_.GlobalTheory.T
