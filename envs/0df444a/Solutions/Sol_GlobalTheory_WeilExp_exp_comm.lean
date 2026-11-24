-- Prove2me | solution 1 for GlobalTheory.WeilExp.exp_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:36.490024+00:00
-- url     : https://prove2.me/submissions/de2557aa-b844-479a-a801-8ce15425c398

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_WeilIsExpRiemannForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.WeilExp
namespace GlobalTheory.WeilExp
theorem _root_.solution {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (k : ℕ) (a b z : Fin g → ℂ) (E : ℤ)
    (hE : (E : ℝ) = (a ⬝ᵥ Hm.mulVec (star b)).im) :
    cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star a)))) *
        cexp (-(Real.pi * ((z + (k : ℂ)⁻¹ • a) ⬝ᵥ Hm.mulVec (star b)))) =
      cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star b)))) *
        cexp (-(Real.pi * ((z + (k : ℂ)⁻¹ • b) ⬝ᵥ Hm.mulVec (star a)))) *
        cexp (-(2 * Real.pi * Complex.I) * (E : ℂ) / k) := by
  have h1 : b ⬝ᵥ Hm.mulVec (star a) = star (a ⬝ᵥ Hm.mulVec (star b)) := by
    rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]
  have h2 : (E : ℂ) = ((a ⬝ᵥ Hm.mulVec (star b)).im : ℂ) := by
    rw [← hE]; simp
  have h3 := Complex.sub_conj (a ⬝ᵥ Hm.mulVec (star b))
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, add_dotProduct, add_dotProduct,
    smul_dotProduct, smul_dotProduct, h1, h2]
  congr 1
  rw [Complex.star_def]
  simp only [smul_eq_mul]
  push_cast at h3
  linear_combination (-(Real.pi : ℂ) * (k : ℂ)⁻¹) * h3
end GlobalTheory.WeilExp
