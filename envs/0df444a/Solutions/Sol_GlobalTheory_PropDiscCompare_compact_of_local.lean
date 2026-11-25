-- Prove2me | solution 1 for GlobalTheory.PropDiscCompare.compact_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:10:39.453161+00:00
-- url     : https://prove2.me/submissions/c6ca3b72-2730-43b4-8549-9c8b3a5a4e01

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ProperlyDiscontinuousFlags
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteOfLocallyFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PropDiscCompare
open NumberField Topology ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.PropDiscCompare
namespace _root_.GlobalTheory.PropDiscCompare
theorem _root_.solution (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags.ProperlyDiscontinuousOnFlags X := by
  intro K hK hKdom
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc at h
  choose! U hU U' hU' hfin using h
  obtain ⟨t, ht, hcover⟩ := (hK.prod hK).elim_nhds_subcover
    (fun q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => U q.1 q.2 ×ˢ U' q.1 q.2)
    (fun q hq => prod_mem_nhds (hU q.1 (hKdom hq.1) q.2 (hKdom hq.2))
      (hU' q.1 (hKdom hq.1) q.2 (hKdom hq.2)))
  refine (t.finite_toSet.biUnion fun q hq =>
    hfin q.1 (hKdom (ht q hq).1) q.2 (hKdom (ht q hq).2)).subset ?_
  rintro γ ⟨hγ, x, hx, y, hy, b, hb, hxy⟩
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (hcover (Set.mk_mem_prod hx hy))
  exact Set.mem_iUnion₂.mpr ⟨q, hq, hγ, x, hxq.1, y, hxq.2, b, hb, hxy⟩
end _root_.GlobalTheory.PropDiscCompare
end GlobalTheory.PropDiscCompare
