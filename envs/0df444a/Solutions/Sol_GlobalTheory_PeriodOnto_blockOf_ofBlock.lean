-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.blockOf_ofBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:32.813417+00:00
-- url     : https://prove2.me/submissions/657b09b3-1d1a-49a7-8246-c5ab96f30c9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Theorems.Thm_GlobalTheory_PeriodOnto_kap_kap
import Theorems.Thm_GlobalTheory_PeriodOnto_blockOf_apply

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
open Classical
namespace GlobalTheory.PeriodOnto
theorem _root_.solution (t t' : ι) (w : Fin r → ℂ) :
    blockOf idx q t' (ofBlock idx q t w) = if t' = t then w else 0 := by
  ext a
  by_cases h : t' = t <;> simp [blockOf_apply, ofBlock, h, kap_kap]
end GlobalTheory.PeriodOnto
