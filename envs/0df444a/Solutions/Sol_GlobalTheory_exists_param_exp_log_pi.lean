-- Prove2me | solution 1 for GlobalTheory.exists_param_exp_log_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:18.568062+00:00
-- url     : https://prove2.me/submissions/df896f66-eb4d-4c0c-932c-131c9bb31d75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticParamInverse
import Theorems.Thm_GlobalTheory_exists_param_exp_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory
theorem _root_.solution : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)) :=
  fun _ _ _ _ hM hu hc hs => exists_param_exp_log hM hu hc hs
end GlobalTheory
