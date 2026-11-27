-- Prove2me | solution 1 for GlobalTheory.T.thetaChar_half_differentiable_ne_zero_families
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:34:48.836228+00:00
-- url     : https://prove2.me/submissions/de50d3ea-b1e0-482c-b7d6-9fbd7478e976

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaCharHalfDifferentiableNeZeroFamilies
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaCharHalfDifferentiableNeZeroFamiliesStatement
import Theorems.Thm_GlobalTheory_ThetaHalf_thetaChar_holomorphic_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (c₁ c₂ : Fin g → ℂ), (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → (∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → (τ.map Complex.im).PosDef → Differentiable ℂ (thetaChar τ c₁ c₂) ∧ ∃ z, thetaChar τ c₁ c₂ z ≠ 0) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B ∧ DifferentiableOn ℂ (fun b => τ b i j) B) → DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2)) (B ×ˢ Set.univ) := by
  first | exact @GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero | exact GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero | (intros; apply GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero <;> assumption)
end _root_.GlobalTheory.T
