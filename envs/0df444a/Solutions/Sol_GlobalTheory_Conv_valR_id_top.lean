-- Prove2me | solution 1 for GlobalTheory.Conv.valR_id_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:00:01.536619+00:00
-- url     : https://prove2.me/submissions/fc33e444-1b15-4506-8bab-529c7f248a82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_evLoc_algebraMap
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent
attribute [local simp] GlobalTheory.Conv.evLoc_algebraMap
attribute [local simp] GlobalTheory.Conv.expandConv_u



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {A : Type} [CommRing A] {Z : Scheme.{0}}
namespace GlobalTheory.Conv
theorem _root_.solution (a : A) :
    valR (𝟙 (Sp A)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a := by
  rw [valR_eq _ _ le_top]
  have h : (𝟙 (Sp A) : Sp A ⟶ Sp A).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    (((𝟙 (Sp A) : Sp A ⟶ Sp A).appLE ⊤ ⊤ le_top).hom _) = a
  rw [h]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply a
end GlobalTheory.Conv
