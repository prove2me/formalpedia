-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.isRelevant_map_redMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:36:04.605065+00:00
-- url     : https://prove2.me/submissions/924ae1d3-b030-4115-a0b3-5647061fb39f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_IsMultiHomogIdealMapRedMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Pub
theorem _root_.solution {p : ℕ} {W : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ W)
    (h : IsRelevant W) : IsRelevant (W.map (redMap ι p)) := by
  intro k
  obtain ⟨i, hi⟩ := h k
  refine ⟨i, fun hx => hi ?_⟩
  rw [← comap_map_redMap hp, Ideal.mem_comap]
  simpa [redMap] using hx
end GlobalTheory.CompanionTheory.Ar.Pub
