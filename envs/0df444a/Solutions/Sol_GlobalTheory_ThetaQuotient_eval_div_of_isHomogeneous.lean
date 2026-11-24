-- Prove2me | solution 1 for GlobalTheory.ThetaQuotient.eval_div_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:57.196069+00:00
-- url     : https://prove2.me/submissions/8862bd99-53ea-4419-95f5-c3ce5d92a68a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EvalDivOfIsHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaQuotient
namespace GlobalTheory.ThetaQuotient
theorem _root_.solution {σ : Type*} {F : MvPolynomial σ ℂ} {d : ℕ} (hF : F.IsHomogeneous d) (v : σ → ℂ)
    (t : ℂ) : MvPolynomial.eval (fun i => v i / t) F = MvPolynomial.eval v F / t ^ d := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hd, mul_div_assoc]
end GlobalTheory.ThetaQuotient
