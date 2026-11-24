-- Prove2me | solution 1 for GlobalTheory.LatPair.Da_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:38.699909+00:00
-- url     : https://prove2.me/submissions/02043b02-4c01-4f23-85b3-172cc0b25c91

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
theorem _root_.solution (a : 𝓀[k]) (P₁ : Pair k n) :
    Da q a φ P₁ = ∑ P ∈ withLat P₁.ker with cross q P₁ P = a, φ P := by simp [Da, sumOp_apply]
end GlobalTheory.LatPair
