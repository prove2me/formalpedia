-- Prove2me | solution 1 for GlobalTheory.T.cuspFlow_eq_torusAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:16:36.57277+00:00
-- url     : https://prove2.me/submissions/454f8446-51d8-4a93-b43f-b3c9ea5a5073

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CuspFlowEqTorusAction
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CuspFlowEqTorusActionStatement
import Theorems.Thm_GlobalTheory_CuspFlow_flow_eq_zAct


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ η : Fin ρ → E, (∑ a, η a • cu.e a) ∈ X.Λ → ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ), (∀ s x, X.flow (∑ a, η a • cu.e a) (fun τ => (s τ : ℂ)) x = zAct X cu (L s) x) ∧ (∀ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ → ∀ s, ∑ k, phZ X cu χ k * L s k = 2 * ∑ τ : X.Ψ, (τ.1 (hq χ η)).re * s τ) ∧ ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  first | exact @GlobalTheory.CuspFlow.flow_eq_zAct | exact GlobalTheory.CuspFlow.flow_eq_zAct | (intros; apply GlobalTheory.CuspFlow.flow_eq_zAct <;> assumption)
end _root_.GlobalTheory.T
