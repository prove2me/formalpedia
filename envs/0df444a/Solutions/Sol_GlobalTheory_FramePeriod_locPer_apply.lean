-- Prove2me | solution 1 for GlobalTheory.FramePeriod.locPer_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:53.208811+00:00
-- url     : https://prove2.me/submissions/89f9e937-67b6-412e-9445-507a09840145

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FramePeriod
theorem _root_.solution (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → ℂ) (a : Fin r) : locPer τ Gm q M u a =
      if (a : ℕ) < q then FD.hermC τ Gm (FD.col M a) u else (M⁻¹ *ᵥ u) a := rfl
end GlobalTheory.FramePeriod
