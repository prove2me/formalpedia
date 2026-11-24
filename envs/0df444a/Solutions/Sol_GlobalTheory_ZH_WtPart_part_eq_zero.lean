-- Prove2me | solution 1 for GlobalTheory.ZH.WtPart.part_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:48.442654+00:00
-- url     : https://prove2.me/submissions/048ccf53-89a1-4645-a6f4-f6ea421fa61b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtPart
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
namespace GlobalTheory.ZH.WtPart
theorem _root_.solution {χ : X} {s : R} (h : cf hb χ s = 0) : part hb χ s = 0 := by
  rw [part, h, map_zero, zero_mul]
end GlobalTheory.ZH.WtPart
