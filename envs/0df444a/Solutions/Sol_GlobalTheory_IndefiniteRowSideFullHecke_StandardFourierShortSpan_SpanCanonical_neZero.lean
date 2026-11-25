-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan.SpanCanonical.neZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:15.018352+00:00
-- url     : https://prove2.me/submissions/cd4690c9-aede-43f5-bd64-9e7479379cb7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ShortRuleRepresentationChange
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_StandardFourierShortSpan
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_StandardFourierShortSpan_CuspLeSpan_genNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c}
variable {Δ : DeltaDatum Xo c nab} {hK : ReflexLe Dw c} {nV : ℕ}
  {cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)}
namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
namespace SpanCanonical
theorem _root_.solution (h : SpanCanonical Xo c) : NeZeroCanonical Xo c :=
  fun nab hn r U hU Δ hK nV => (h nab hn r U hU Δ hK nV).1.genNeZero
end SpanCanonical
end GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
