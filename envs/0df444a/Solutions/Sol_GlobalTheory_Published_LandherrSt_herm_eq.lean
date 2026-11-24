-- Prove2me | solution 1 for GlobalTheory.Published.LandherrSt.herm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:03.08887+00:00
-- url     : https://prove2.me/submissions/593ad45f-9ffe-4d12-8d6c-db0e89664d12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__LandherrStIffLandherr_9fec213082f17e18

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.LandherrSt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Published.LandherrSt
namespace _root_.GlobalTheory.Published.LandherrSt
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y = x ⬝ᵥ (G *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y b)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
end _root_.GlobalTheory.Published.LandherrSt
end GlobalTheory.Published.LandherrSt
