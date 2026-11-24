-- Prove2me | solution 1 for GlobalTheory.LatPair.FF_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:21.818805+00:00
-- url     : https://prove2.me/submissions/0e4827d0-0000-4eeb-a861-22fd119fe13c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_FF_apply
import Theorems.Thm_GlobalTheory_LatPair_sum_withLat_smul
import Theorems.Thm_GlobalTheory_LatPair_cross_smul


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
namespace GlobalTheory.LatPair
theorem _root_.solution : FF q χ φ (g • P) = FF q χ (fun Q => φ (g • Q)) P := by
  simp only [FF_apply, Pair.smul_ker, sum_withLat_smul]
  exact Finset.sum_congr rfl fun Q hQ => by rw [cross_smul q (mem_withLat.1 hQ)]
end GlobalTheory.LatPair
