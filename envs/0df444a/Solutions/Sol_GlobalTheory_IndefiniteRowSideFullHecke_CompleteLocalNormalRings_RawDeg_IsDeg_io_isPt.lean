-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg.IsDeg.io_isPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:50:15.156619+00:00
-- url     : https://prove2.me/submissions/f4914406-b20f-4a48-a945-7c524304601a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms
import Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_RawDeg___isGen_8ccbc68b0b48

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
variable (R : Type) [CommRing R] [IsDomain R]
attribute [instance] RawDeg.addCommGroup RawDeg.free RawDeg.finite
open GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
variable {R} (D : RawDeg R)
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
namespace IsDeg
theorem _root_.solution {D : RawDeg R} {I : Ideal R} (h : D.IsDeg I) (y : D.X) : (D.io y).IsPt :=
  ⟨fun χ => D.τ_isGen χ y, fun χ χ' => h.mul_left χ χ' y⟩
end IsDeg
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg
