-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.I_smul_ofBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:51.866263+00:00
-- url     : https://prove2.me/submissions/35a649b6-6538-48b1-9948-1a1d55a29e0c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Theorems.Thm_GlobalTheory_PeriodOnto_kap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ)
namespace GlobalTheory.PeriodOnto
theorem _root_.solution (t : ι) (w : Fin r → ℂ) :
    Complex.I • ofBlock idx q t w = ofBlock idx q t ((-Complex.I) • (sgnMat r q *ᵥ w)) := by
  ext k
  simp only [ofBlock, Pi.smul_apply, sgnMat, mulVec_diagonal, kap_apply, FD.sgn]
  split_ifs <;> simp
end GlobalTheory.PeriodOnto
