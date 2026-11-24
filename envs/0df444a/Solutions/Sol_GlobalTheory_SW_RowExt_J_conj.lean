-- Prove2me | solution 1 for GlobalTheory.SW.RowExt.J_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:28:28.840229+00:00
-- url     : https://prove2.me/submissions/ca94eb46-6250-42ce-9a9e-415ec4e26164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.RowExt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {α β γ : Type}
namespace GlobalTheory.SW.RowExt
theorem _root_.solution [DecidableEq α] : (Matrix.J α E)ᴴ = -Matrix.J α E := by
  simp [Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
end GlobalTheory.SW.RowExt
