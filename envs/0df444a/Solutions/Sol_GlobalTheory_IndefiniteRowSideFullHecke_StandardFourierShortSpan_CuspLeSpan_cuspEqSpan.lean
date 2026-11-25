-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan.CuspLeSpan.cuspEqSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:56:46.355642+00:00
-- url     : https://prove2.me/submissions/75f0354a-ce25-443a-9b30-19a53a5091c4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ShortRuleRepresentationChange
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_StandardFourierShortSpan

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
namespace CuspLeSpan
theorem _root_.solution (h : CuspLeSpan Δ hK nV cusp) (h' : ShortInCusp Δ hK nV cusp) :
    CuspEqSpan Δ hK nV cusp :=
  fun a n hr hp => le_antisymm (h a n hr) (Submodule.span_le.2 (h' a n hr.2.1 hp))
end CuspLeSpan
end GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
