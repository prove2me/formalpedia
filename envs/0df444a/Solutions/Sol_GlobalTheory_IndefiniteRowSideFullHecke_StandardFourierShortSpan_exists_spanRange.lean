-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan.exists_spanRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:46.431847+00:00
-- url     : https://prove2.me/submissions/4e6f016f-cc06-4a9b-8a5e-a5cae551bda1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ShortRuleRepresentationChange
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_StandardFourierShortSpan
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_RamifiedCoverPairIsomorphism_exists_inPsi


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
theorem _root_.solution (hr : 3 ≤ Dw.p + Dw.q) (hA : l.A = 1) : ∃ a n, SpanRange Dw l a n ∧ OnePos Dw a := by
  obtain ⟨τ, hτ⟩ := exists_inPsi H
  refine ⟨fun _ => 1, 8 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 4,
    ⟨hA, ⟨fun _ => antitone_const, ⟨4 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 2, by ring⟩⟩, hr, le_rfl⟩,
    τ, hτ, fun _ => le_rfl⟩
end GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
