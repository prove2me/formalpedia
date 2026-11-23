-- Prove2me | solution 1 for GlobalTheory.RiemannRel.hermForm_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:51.264256+00:00
-- url     : https://prove2.me/submissions/11dd8eb8-adaa-47d0-8f3b-1c63a771a520

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse

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
open GlobalTheory GlobalTheory.RiemannRel
variable {g : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {g : ℕ}
namespace GlobalTheory.RiemannRel
namespace _root_.GlobalTheory.RiemannRel
theorem _root_.solution (G A B : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ v) (B *ᵥ w) = v ⬝ᵥ (Aᵀ * G * B.map (starRingEnd ℂ)) *ᵥ star w := by
  have hstar : star (B *ᵥ w) = B.map (starRingEnd ℂ) *ᵥ star w := by
    ext i; simp [mulVec, dotProduct, star_sum]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [hstar, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Aᵀ,
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
end _root_.GlobalTheory.RiemannRel
end GlobalTheory.RiemannRel
