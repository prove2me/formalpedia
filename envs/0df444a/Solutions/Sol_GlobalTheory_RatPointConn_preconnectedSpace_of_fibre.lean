-- Prove2me | solution 1 for GlobalTheory.RatPointConn.preconnectedSpace_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:45.650071+00:00
-- url     : https://prove2.me/submissions/f25cd596-2557-4818-9387-122e0194c450

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfRatPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.RatPointConn
universe u
namespace GlobalTheory.RatPointConn
theorem _root_.solution {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X]
    [PreconnectedSpace X] {p : Z → X} (ho : IsOpenMap p) (hc : IsClosedMap p) (x : X)
    (hx : ∀ a b, p a = x → p b = x → a = b) : PreconnectedSpace Z := by
  have key : ∀ U : Set Z, IsClopen U → U.Nonempty → ∃ a ∈ U, p a = x := by
    intro U hU hne
    have h1 : IsClopen (p '' U) := ⟨hc _ hU.1, ho _ hU.2⟩
    have h2 := h1.eq_univ (hne.image _)
    exact h2.ge (Set.mem_univ x)
  refine ⟨(isPreconnected_iff_subset_of_disjoint).2 fun U V hU hV hUV hd => ?_⟩
  rw [Set.univ_inter] at hd
  have hdis : Disjoint U V := Set.disjoint_iff_inter_eq_empty.2 hd
  have hcompl : IsCompl U V := ⟨hdis, codisjoint_iff.2 (Set.univ_subset_iff.1 hUV)⟩
  have cU : IsClopen U := ⟨⟨by rw [hcompl.compl_eq]; exact hV⟩, hU⟩
  have cV : IsClopen V := ⟨⟨by rw [hcompl.symm.compl_eq]; exact hU⟩, hV⟩
  rcases U.eq_empty_or_nonempty with rfl | nU
  · right; simpa using hUV
  rcases V.eq_empty_or_nonempty with rfl | nV
  · left; simpa using hUV
  obtain ⟨a, ha, hax⟩ := key U cU nU
  obtain ⟨b, hb, hbx⟩ := key V cV nV
  obtain rfl := hx a b hax hbx
  exact absurd hb (Set.disjoint_left.1 hdis ha)
end GlobalTheory.RatPointConn
