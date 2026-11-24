-- Prove2me | solution 1 for GlobalTheory.LatPair.U_mem_EqForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:16.541166+00:00
-- url     : https://prove2.me/submissions/72b0b634-4f2a-41be-b1f4-f9d0c48ff527

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_U_apply
import Theorems.Thm_GlobalTheory_LatPair_map_mem_EqForm
import Theorems.Thm_GlobalTheory_LatPair_U_smul

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
theorem _root_.solution (h : φ ∈ EqForm π) : U q φ ∈ EqForm π :=
  map_mem_EqForm π (fun g φ P => U_smul q φ g P) (fun _ _ _ => by simp [U_apply]) h
end GlobalTheory.LatPair
