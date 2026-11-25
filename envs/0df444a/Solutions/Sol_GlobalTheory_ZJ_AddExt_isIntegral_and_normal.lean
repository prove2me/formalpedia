-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.isIntegral_and_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:07:03.861479+00:00
-- url     : https://prove2.me/submissions/efe88135-06c1-4390-b81f-e266aa7f490f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension
import Theorems.Thm_GlobalTheory_ZJ_AddExt_isPullback_square
import Theorems.Thm_GlobalTheory_IsNormalScheme_isIntegral_of_connectedSpace
import Theorems.Thm_GlobalTheory_forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth


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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt
namespace GlobalTheory.ZJ.AddExt
theorem _root_.solution (C : Core) [Smooth C.GG.hom] (φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left)
    (h : IsSquare C.a φ₂) : IsIntegral (C.GG ⊗ C.GG).left ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (C.GG ⊗ C.GG).left ∧ Nonempty (C.A ⊗ C.A).left := by
  have hp := isPullback_square C φ₂ h
  have := C.lft
  have : Smooth (C.GG ⊗ C.GG).hom := inferInstanceAs (Smooth (pullback.fst C.GG.hom C.GG.hom ≫ C.GG.hom))
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (C.GG ⊗ C.GG).left :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (C.GG ⊗ C.GG).hom C.normal
  have := GlobalTheory.IsNormalScheme.of_pred hN
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.π
  have : IsLocallyNoetherian (C.GG ⊗ C.GG).left := LocallyOfFiniteType.isLocallyNoetherian (C.GG ⊗ C.GG).hom
  have := C.ab.smooth
  have := C.ab.geomConnected
  have : Nonempty C.U := ⟨⟨_, C.ne.some_mem⟩⟩
  have : ConnectedSpace C.A.left := GeometricallyConnected.connectedSpace C.A.hom C.A.hom.isOpenMap
  have hc : ConnectedSpace (C.A ⊗ C.A).left := inferInstanceAs (ConnectedSpace ↥(pullback C.A.hom C.A.hom))
  have hr : Set.range φ₂ = (C.GG ⊗ C.GG).hom ⁻¹' C.U := by
    rw [← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Function.Surjective.range_comp hp.isoPullback.hom.surjective, Scheme.Pullback.range_fst,
      Scheme.Opens.range_ι]
  have hd : Dense (Set.range φ₂) := by
    rw [hr]
    exact (C.U.isOpen.dense C.ne).preimage (C.GG ⊗ C.GG).hom.isOpenMap
  have : ConnectedSpace (C.GG ⊗ C.GG).left := by
    have h : _root_.IsConnected (closure (Set.range φ₂)) := (isConnected_range φ₂.continuous).closure
    rw [hd.closure_eq] at h
    exact connectedSpace_iff_univ.mpr h
  exact ⟨IsNormalScheme.isIntegral_of_connectedSpace _, hN, inferInstance⟩
end GlobalTheory.ZJ.AddExt
