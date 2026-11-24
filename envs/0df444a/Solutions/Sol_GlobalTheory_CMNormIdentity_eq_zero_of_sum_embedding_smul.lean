-- Prove2me | solution 1 for GlobalTheory.CMNormIdentity.eq_zero_of_sum_embedding_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:18:00.065197+00:00
-- url     : https://prove2.me/submissions/c44a4257-cd5d-411b-9c35-e60234a3e7db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingSmul
import Theorems.Thm_GlobalTheory_EigenNorm_eq_zero_of_sum_embedding_mul
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CMNormIdentity
namespace GlobalTheory.CMNormIdentity
theorem _root_.solution {E : Type} [Field E] [NumberField E] {g : ℕ} (f : (E →+* ℂ) → Fin g → ℂ)
    (hf : ∀ s : 𝓞 E, ∑ τ : E →+* ℂ, τ (s : E) • f τ = 0) (τ : E →+* ℂ) : f τ = 0 := by
  funext k
  exact EigenNorm.eq_zero_of_sum_embedding_mul (fun τ => f τ k) (fun s => by simpa using congrFun (hf s) k) τ
end GlobalTheory.CMNormIdentity
