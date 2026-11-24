-- Prove2me | solution 1 for GlobalTheory.HermSign.eq_of_re_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:29:19.45398+00:00
-- url     : https://prove2.me/submissions/96366b64-c353-4fbb-9208-c49700f8ef2e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
namespace GlobalTheory.HermSign
theorem _root_.solution {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) (z : ℂ) (hz : z ≠ 0)
    (h : ∀ u v : Fin r → ℂ, (z * (u ⬝ᵥ A *ᵥ star v)).re = (z * (u ⬝ᵥ B *ᵥ star v)).re) : A = B := by
  classical
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  have h2 := h (Pi.single a Complex.I) (Pi.single b 1)
  simp only [Pi.star_single, star_one, mulVec_single_one, single_dotProduct, one_mul, col_apply] at h1 h2
  refine mul_left_cancel₀ hz (Complex.ext h1 ?_)
  simp at h2 ⊢
  linarith
end GlobalTheory.HermSign
