-- Prove2me | solution 1 for GlobalTheory.Conv.valR_spMap_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:18:03.332826+00:00
-- url     : https://prove2.me/submissions/6f49203f-908c-490c-9130-481878cab492

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_GlobalTheory_Conv_valR_id_top
import Theorems.Thm_GlobalTheory_HolHom_valR_spMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {A : Type} [CommRing A] {Z : Scheme.{0}}
namespace GlobalTheory.Conv
theorem _root_.solution {O : Type} [CommRing O] (β : O →+* A) (a : O) :
    valR (spMap β) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) = β a := by
  have := valR_spMap β (𝟙 (Sp O)) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)
  rwa [Category.comp_id, valR_id_top] at this
end GlobalTheory.Conv
