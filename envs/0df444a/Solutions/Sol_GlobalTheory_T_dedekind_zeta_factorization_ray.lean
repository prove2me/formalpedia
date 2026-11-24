-- Prove2me | solution 1 for GlobalTheory.T.dedekind_zeta_factorization_ray
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:05.962445+00:00
-- url     : https://prove2.me/submissions/4675744d-b2df-4acc-a18f-e9cb49ac1d8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRayStatement
import Theorems.Thm_GlobalTheory_Mem_ray_prod_LSeries_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) [Fintype (D.G →* ℂˣ)], ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧ ∀ s : ℂ, 1 < s.re → LSeries b s = ∏ χ : D.G →* ℂˣ, LSeries (D.coef χ) s := by
  first | exact @GlobalTheory.Mem.ray_prod_LSeries_nonneg | exact GlobalTheory.Mem.ray_prod_LSeries_nonneg | (intros; apply GlobalTheory.Mem.ray_prod_LSeries_nonneg <;> assumption)
end _root_.GlobalTheory.T
