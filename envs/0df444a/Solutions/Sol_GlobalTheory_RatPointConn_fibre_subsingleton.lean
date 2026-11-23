-- Prove2me | solution 1 for GlobalTheory.RatPointConn.fibre_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:47.027025+00:00
-- url     : https://prove2.me/submissions/c9f55892-86a2-4675-9dff-93cf2b888f69

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
theorem _root_.solution {k K : Type u} [Field k] [Field K] {X Z : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {y : Spec (.of K) ⟶ Spec (.of k)} {p : Z ⟶ X} {q : Z ⟶ Spec (.of K)}
    (h : IsPullback p q f y) (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) (a b : Z)
    (ha : p a = s (IsLocalRing.closedPoint k)) (hb : p b = s (IsLocalRing.closedPoint k)) :
    a = b := by
  let t : Spec (.of K) ⟶ Z := h.lift (y ≫ s) (𝟙 _) (by simp [hs])
  have ht : IsPullback t y p s := by
    refine IsPullback.of_right (h₁₂ := q) (v₁₃ := y) (h₂₂ := f) ?_ (by simp [t]) h.flip
    rw [hs, show t ≫ q = 𝟙 _ by simp [t]]
    exact IsPullback.of_id_fst
  obtain ⟨a', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht a (IsLocalRing.closedPoint k) ha
  obtain ⟨b', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht b (IsLocalRing.closedPoint k) hb
  rw [Subsingleton.elim a' b']
end GlobalTheory.RatPointConn
