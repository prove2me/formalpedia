-- Prove2me | solution 1 for GlobalTheory.TorusExt.isIota_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:56:33.829018+00:00
-- url     : https://prove2.me/submissions/48e59479-06cf-47b1-b2ab-9c44c234c45d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorusExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.TorusExt
theorem _root_.solution {x : D.X} {h h' : GtPtF D F} (e : GtPtF.IsIota x h) (e' : GtPtF.IsIota x h') : h = h' := by
  obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 e
  obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 e'
  exact gt_ext_val (b.trans b'.symm) fun χ y J hJ => (v χ y J hJ).trans (v' χ y J hJ).symm
end GlobalTheory.TorusExt
