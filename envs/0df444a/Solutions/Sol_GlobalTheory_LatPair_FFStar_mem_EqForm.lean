-- Prove2me | solution 1 for GlobalTheory.LatPair.FFStar_mem_EqForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:48.633313+00:00
-- url     : https://prove2.me/submissions/58f12552-e416-4c00-8d0d-f05ea99584e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_FFStar_apply
import Theorems.Thm_GlobalTheory_LatPair_map_mem_EqForm
import Theorems.Thm_GlobalTheory_LatPair_FFStar_smul

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
variable [Fintype n] [DecidableEq n]
variable (π : Representation ℂ (GL n k) M)
variable (g : GL n k) (P : Pair k n)
variable {π φ}
namespace GlobalTheory.LatPair
theorem _root_.solution (h : φ ∈ EqForm π) : FFStar q χ φ ∈ EqForm π :=
  map_mem_EqForm π (fun g φ P => FFStar_smul q χ φ g P) (fun _ _ _ => by simp [FFStar_apply]) h
end GlobalTheory.LatPair
