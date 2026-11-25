-- Prove2me | solution 1 for GlobalTheory.EpsIso.isAffineHom_of_isHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:34:09.195554+00:00
-- url     : https://prove2.me/submissions/45a1d0ba-beef-4585-a1be-1ac311b30c92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickening
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_preimage_basicOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsIso
namespace GlobalTheory.EpsIso
theorem _root_.solution {X Y : Scheme.{0}} (e : X ⟶ Y) (he : IsHomeomorph e) :
    IsAffineHom e := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨x, rfl⟩ := he.surjective y
  have hmem : e x ∈ (⊤ : Y.Opens) := trivial
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hmem
  obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ e ⁻¹ᵁ V from hxV)
  let O : Y.Opens := ⟨(⇑e) '' (W : Set X), he.isOpenMap _ W.isOpen⟩
  obtain ⟨g, hgO, hgy⟩ := (show IsAffineOpen V from hV).exists_basicOpen_le (V := O)
    ⟨e x, ⟨x, hxW, rfl⟩⟩ hxV
  have hsub : e ⁻¹ᵁ Y.basicOpen g ≤ W := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hgO hz
    rwa [← he.injective hwz]
  refine ⟨Y.basicOpen g, hgy, (show IsAffineOpen V from hV).basicOpen g, ?_⟩
  have heq : e ⁻¹ᵁ Y.basicOpen g =
      X.basicOpen (X.presheaf.map (homOfLE hWV).op (e.app V g)) := by
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact (inf_eq_right.2 hsub).symm
  rw [heq]
  exact (show IsAffineOpen W from hW).basicOpen _
end GlobalTheory.EpsIso
