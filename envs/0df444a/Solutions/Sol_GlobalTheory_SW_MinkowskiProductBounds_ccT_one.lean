-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.ccT_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:27.903376+00:00
-- url     : https://prove2.me/submissions/2de2ab1f-ccfa-4e5b-a03d-e94397861681

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution {α : Type} [DecidableEq α] : ccT (1 : Matrix α α E) = 1 := by
  ext i j
  simp [ccT, cc, Matrix.one_apply, apply_ite, eq_comm]
end GlobalTheory.SW.MinkowskiProductBounds
