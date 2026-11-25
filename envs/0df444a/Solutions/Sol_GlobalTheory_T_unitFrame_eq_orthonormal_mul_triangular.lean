-- Prove2me | solution 1 for GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:29:40.871413+00:00
-- url     : https://prove2.me/submissions/12f51545-3086-416e-93c8-c1a9ed0fd130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitFrameEqOrthonormalMulTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitFrameEqOrthonormalMulTriangularStatement
import Theorems.Thm_GlobalTheory_UnitFrames_unit_frame_eq_orthonormal_mul_triangular


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, (∀ τ i, ‖dmin Gm x τ i‖ = 1) → ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ x = rmul x₀ b) ∧ (∀ x₀ : Frame Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → x₀ ∈ GG Ψ Gm p0 ∧ ∀ τ i, ‖dmin Gm x₀ τ i‖ = 1) ∧ ∀ (τ : E →+* ℂ) (u x₀ : Matrix (Fin r) (Fin r) ℂ), uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ → gram τ Gm (u * x₀) = gram τ Gm x₀ := by
  first | exact @GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular | exact GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular | (intros; apply GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular <;> assumption)
end _root_.GlobalTheory.T
