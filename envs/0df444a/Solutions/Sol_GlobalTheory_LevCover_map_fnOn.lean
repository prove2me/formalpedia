-- Prove2me | solution 1 for GlobalTheory.LevCover.map_fnOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:05.960895+00:00
-- url     : https://prove2.me/submissions/c957e691-6bdb-48f8-a2b0-bc176de18ae8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp
import Theorems.Thm_GlobalTheory_LevCover_RepTors_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
namespace GlobalTheory.LevCover
theorem _root_.solution {L k : Type} [CommRing L] [CommRing k] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp k ⟶ T)
    (β : L →+* k) (e : h ≫ g = spMap β) (c : Lˣ) :
    Units.map h.appTop.hom.toMonoidHom (Units.map (fnOn g).toMonoidHom c) = unitOn (Units.map β.toMonoidHom c) := by
  apply Units.ext
  show h.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) =
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (β c)
  have h1 : (h ≫ g).appTop = g.appTop ≫ h.appTop := Scheme.Hom.comp_appTop _ _
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  have h3 := congrArg (fun φ => φ.hom (c : L)) h2
  rw [e] at h1
  have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) h1
  exact h4.symm.trans h3.symm
end GlobalTheory.LevCover
