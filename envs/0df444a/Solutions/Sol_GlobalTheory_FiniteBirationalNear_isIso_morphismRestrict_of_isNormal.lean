-- Prove2me | solution 1 for GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:31:04.639662+00:00
-- url     : https://prove2.me/submissions/a6d6b63c-08bc-4be1-9bdc-2a5a0b1bbfcb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoNearNormalPointOfFiniteBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoMorphismRestrictFiniteOfIsNormalDense
import Theorems.Thm_GlobalTheory_FiniteBirationalNear_main
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FiniteBirationalNear
namespace GlobalTheory.FiniteBirationalNear
theorem _root_.solution : ∀ {S T : Scheme.{0}} [IsLocallyNoetherian T] (ν : S ⟶ T) [IsFinite ν] (U V : T.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (V : Scheme.{0}) → Dense (U : Set T) → Dense (ν ⁻¹' (U : Set T)) → IsIso (ν ∣_ U) → IsIso (ν ∣_ V) := by
  intro S T _ ν _ U V hS hV hU hνU hiso
  have : IsReduced S := by
    haveI : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
      have := (hS x).1
      infer_instance
    exact isReduced_of_isReduced_stalk S
  have hloc : ∀ x : V, ∃ W : T.Opens, (x : T) ∈ W ∧ IsIso (ν ∣_ W) := by
    intro x
    have e := (V.stalkIso x).symm.commRingCatIsoToRingEquiv
    have h1 : IsDomain (T.presheaf.stalk (x : T)) := by
      have := (hV x).1
      exact e.toMulEquiv.isDomain _
    have h2 : IsIntegrallyClosed (T.presheaf.stalk (x : T)) := by
      have := (hV x).2
      exact IsIntegrallyClosed.of_equiv e.symm
    exact main S T ν U ‹_› ‹_› hiso hU hνU (x : T) h1 h2
  choose W hxW hW using hloc
  let W' : V → V.toScheme.Opens := fun x => V.ι ⁻¹ᵁ W x
  have hcov : iSup W' = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxW y⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) W' hcov
    fun x => ?_
  have h1 : IsIso (ν ∣_ W x ∣_ ((W x).ι ⁻¹ᵁ V)) := inferInstance
  have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict ν (W x) ((W x).ι ⁻¹ᵁ V))).1 h1
  have e : (W x).ι ''ᵁ ((W x).ι ⁻¹ᵁ V) = V.ι ''ᵁ W' x := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, inf_comm]
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict ν V (W' x))).2
    (((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictEq ν e)).1 h2)
end GlobalTheory.FiniteBirationalNear
