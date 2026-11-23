-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.wp_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:36.050911+00:00
-- url     : https://prove2.me/submissions/1871ff91-18ff-4182-a756-f7635149e83a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.NumD
variable (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution {k : ℕ} (p p' : N.QT k) (h : p.1.1.toAdd = 0) (h' : p'.1.1.toAdd = 0) :
    N.wp p p' = N.weil k p.1.2.b p'.1.2.b := by
  simp only [wp, tk, h, h', Gt.s_zero, one_mul, NumB.weil]
end GlobalTheory.Ex.NumD
