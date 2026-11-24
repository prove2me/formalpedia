-- Prove2me | solution 1 for GlobalTheory.span_image_inf_span_image_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:44.160637+00:00
-- url     : https://prove2.me/submissions/ee2abed0-4027-43dc-b7fc-3725dbe81a26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SpanImageInfSpanImageOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R V ι : Type} [CommRing R]
    [AddCommGroup V] [Module R V] {w : ι → V} (hw : LinearIndependent R w) (s t : Set ι) :
    Submodule.span R (w '' s) ⊓ Submodule.span R (w '' t) = Submodule.span R (w '' (s ∩ t)) := by
  apply le_antisymm
  · rintro x ⟨hs, ht⟩
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 hs
    obtain ⟨m, hm, hmx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 ht
    have hlm : l = m := hw (hlx.trans hmx.symm)
    subst hlm
    refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨l, ?_, hlx⟩
    rw [Finsupp.mem_supported] at hl hm ⊢
    exact Set.subset_inter hl hm
  · exact le_inf (Submodule.span_mono (Set.image_mono Set.inter_subset_left))
      (Submodule.span_mono (Set.image_mono Set.inter_subset_right))
end GlobalTheory
