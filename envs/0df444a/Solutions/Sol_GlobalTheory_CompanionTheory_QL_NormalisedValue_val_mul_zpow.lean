-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.NormalisedValue.val_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:16:33.386095+00:00
-- url     : https://prove2.me/submissions/5351bdb0-107e-4297-a74a-5d81f917f5f8

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_val_pi_pos

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
theorem _root_.solution (h : LF O ϖ nrm q) {x : F} {e : ℤ}
    (he : ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e) :
    ValuativeRel.valuation F (x * ϖ ^ (-e)) = 1 := by
  rw [map_mul, map_zpow₀, he, ← zpow_add₀ (val_pi_pos h).ne']
  simp
end GlobalTheory.CompanionTheory.QL.NormalisedValue
