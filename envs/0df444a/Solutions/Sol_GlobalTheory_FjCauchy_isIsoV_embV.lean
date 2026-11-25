-- Prove2me | solution 1 for GlobalTheory.FjCauchy.isIsoV_embV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:15.595915+00:00
-- url     : https://prove2.me/submissions/515e9acf-1817-417c-8c29-17ab74d27358

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FjCauchyBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_emb_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.FjCauchy
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open NumberField Complex Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
namespace GlobalTheory.FjCauchy
namespace _root_.GlobalTheory.FjCauchy
theorem _root_.solution {ξ : Fin r → E} (hξ : X.IsIso ξ) :
    X.IsIsoV (X.embV ξ) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsIsoV
  intro τ
  refine ⟨?_, _root_.ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero (τ : E →+* ℂ) hξ.2.2⟩
  show _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ ξ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ ξ) = 0
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_emb, hξ.2.1, map_zero]
end _root_.GlobalTheory.FjCauchy
end GlobalTheory.FjCauchy
