-- Prove2me | solution 1 for GlobalTheory.ZH.WtPart.cf_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:30.165924+00:00
-- url     : https://prove2.me/submissions/26221f3d-2131-4158-90d9-fca75f6592db

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
theorem _root_.solution {K : Type} (χ : X) (T : Finset K) (s : K → R) :
    cf hb χ (∑ i ∈ T, s i) = ∑ i ∈ T, cf hb χ (s i) :=
  map_sum (AddMonoidHom.mk' (cf hb χ) (cf_add hb χ)) s T
end GlobalTheory.ZH.WtPart
