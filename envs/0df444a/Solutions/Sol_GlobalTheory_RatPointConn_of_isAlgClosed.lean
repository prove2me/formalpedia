-- Prove2me | solution 1 for GlobalTheory.RatPointConn.of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:44.649994+00:00
-- url     : https://prove2.me/submissions/b49665e9-7c11-46c1-b919-11af0e5eecf1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfRatPoint
import Theorems.Thm_GlobalTheory_RatPointConn_fibre_subsingleton

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
theorem _root_.solution {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [ConnectedSpace X] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z p q h => ?_⟩
  have := LocallyOfFiniteType.jacobsonSpace f
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hs : Surjective p := MorphismProperty.of_isPullback h.flip hy
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)
  have fib : ∀ x : X, IsClosed {x} → ∀ a b : Z, p a = x → p b = x → a = b := by
    intro x hx a b ha hb
    exact fibre_subsingleton h (pointOfClosedPoint f x hx) (pointOfClosedPoint_comp f x hx) a b
      (ha.trans (pointOfClosedPoint_apply f x hx _).symm)
      (hb.trans (pointOfClosedPoint_apply f x hx _).symm)
  have hne : Nonempty Z := (p.surjective (Classical.arbitrary X)).nonempty
  have : PreconnectedSpace Z := ⟨fun U V hU hV hUV hU' hV' => by
    rw [Set.univ_inter] at hU' hV' ⊢
    have o₁ : IsOpen (p '' U) := p.isOpenMap _ hU
    have o₂ : IsOpen (p '' V) := p.isOpenMap _ hV
    have hc : Set.univ ⊆ p '' U ∪ p '' V := by
      intro x _
      obtain ⟨z, rfl⟩ := p.surjective x
      exact (hUV (Set.mem_univ z)).imp (fun hz => ⟨z, hz, rfl⟩) (fun hz => ⟨z, hz, rfl⟩)
    have hi := isPreconnected_univ _ _ o₁ o₂ hc (by simpa using hU') (by simpa using hV')
    rw [Set.univ_inter] at hi
    obtain ⟨x, ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, hxc⟩ := nonempty_inter_closedPoints hi
      (o₁.inter o₂).isLocallyClosed
    exact ⟨a, ha, fib x hxc a b hax hbx ▸ hb⟩⟩
  exact ⟨hne⟩
end GlobalTheory.RatPointConn
