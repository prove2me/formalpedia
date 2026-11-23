-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.NormalisedValue.mem_iff_val_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:57.199582+00:00
-- url     : https://prove2.me/submissions/67cbc1a1-541b-4273-afaf-1c3b4c1cf075

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties

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
theorem _root_.solution (h : LF O ϖ nrm q) (x : F) : x ∈ O ↔ ValuativeRel.valuation F x ≤ 1 := by
  rw [h.O_eq]
  exact Valuation.mem_integer_iff _ _
end GlobalTheory.CompanionTheory.QL.NormalisedValue
