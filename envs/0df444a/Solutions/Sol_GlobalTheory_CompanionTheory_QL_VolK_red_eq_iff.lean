-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.VolK.red_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:19.603121+00:00
-- url     : https://prove2.me/submissions/fe40894c-33a4-4185-aa5b-184a1ac6cfff

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatrices
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_VolK_red_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.VolK
variable {F : Type} [Field F] [ValuativeRel F]
namespace GlobalTheory.CompanionTheory.QL.VolK
theorem _root_.solution {ϖ : F} (hlt : ∀ x : F, ValuativeRel.valuation F x < 1 ↔ ∃ o ∈ 𝒪[F], x = ϖ * o)
    {x y : F} (hx : x ∈ 𝒪[F]) (hy : y ∈ 𝒪[F]) : red x = red y ↔ ∃ o ∈ 𝒪[F], x - y = ϖ * o := by
  rw [← hlt, red_of_mem hx, red_of_mem hy, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := ValuativeRel.valuation F)]
  rfl
end GlobalTheory.CompanionTheory.QL.VolK
