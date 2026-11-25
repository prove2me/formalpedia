-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.ccT_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:29.82866+00:00
-- url     : https://prove2.me/submissions/006c0e8a-24ac-4d9c-9f52-822828315ff7

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
theorem _root_.solution {α β : Type} (k : ℤ) (A : Matrix α β E) :
    ccT ((k : E) • A) = (k : E) • ccT A := by
  ext i j
  simp [ccT, cc]
end GlobalTheory.SW.MinkowskiProductBounds
