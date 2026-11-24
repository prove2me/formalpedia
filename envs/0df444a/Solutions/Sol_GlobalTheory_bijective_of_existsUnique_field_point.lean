-- Prove2me | solution 1 for GlobalTheory.bijective_of_existsUnique_field_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:19.974299+00:00
-- url     : https://prove2.me/submissions/1bb0a65f-283e-4c81-ad8d-05b5d58bf14f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) :
    Function.Bijective f := by
  constructor
  · intro x x' hx
    obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) x x' hx
    let p : Sp ((pullback f f).residueField z) ⟶ pullback f f :=
      (pullback f f).fromSpecResidueField z
    have e : p ≫ pullback.fst f f = p ≫ pullback.snd f f :=
      (h _ (p ≫ pullback.fst f f ≫ f)).unique (by simp) (by simp [pullback.condition])
    let a : Sp ((pullback f f).residueField z) := IsLocalRing.closedPoint _
    have ha : p a = z := Scheme.fromSpecResidueField_apply z a
    have e' : (p ≫ pullback.fst f f) a = (p ≫ pullback.snd f f) a := by rw [e]
    rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ha, hz, hz'] at e'
  · intro t
    obtain ⟨z, hz, -⟩ := h (T.residueField t) (T.fromSpecResidueField t)
    let a : Sp (T.residueField t) := IsLocalRing.closedPoint _
    refine ⟨z a, ?_⟩
    rw [← Scheme.Hom.comp_apply, hz]
    exact Scheme.fromSpecResidueField_apply t a
end GlobalTheory
