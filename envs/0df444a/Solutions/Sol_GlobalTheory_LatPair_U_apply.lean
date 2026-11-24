-- Prove2me | solution 1 for GlobalTheory.LatPair.U_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:35.366044+00:00
-- url     : https://prove2.me/submissions/d3526661-382f-40a0-8bbc-88fa8a0d2a62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_sumOp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)
open Classical
namespace GlobalTheory.LatPair
theorem _root_.solution (P : Pair k n) : U q φ P = ∑ P₁ ∈ withKer P.lat with cross q P₁ P = 1, φ P₁ := by
  simp [U, sumOp_apply]
end GlobalTheory.LatPair
