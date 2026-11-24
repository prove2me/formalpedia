-- Prove2me | solution 1 for GlobalTheory.LatPair.FFStar_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:39.418249+00:00
-- url     : https://prove2.me/submissions/425b1766-95a3-4077-83a3-80aff0875cae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_FFStar_apply
import Theorems.Thm_GlobalTheory_LatPair_sum_withKer_smul
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
theorem _root_.solution : FFStar q χ φ (g • P) = FFStar q χ (fun Q => φ (g • Q)) P := by
  simp only [FFStar_apply, Pair.smul_lat, sum_withKer_smul]
  exact Finset.sum_congr rfl fun Q hQ => by rw [cross_smul q (mem_withKer.1 hQ).symm]
end GlobalTheory.LatPair
