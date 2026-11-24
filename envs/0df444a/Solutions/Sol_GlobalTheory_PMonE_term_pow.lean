-- Prove2me | solution 1 for GlobalTheory.PMonE.term_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:51:45.470143+00:00
-- url     : https://prove2.me/submissions/f8c830e8-c92c-412b-b7c8-deea209dcc60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuter
import Theorems.Thm_GlobalTheory_PMonE_pw_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
namespace GlobalTheory.PMonE
theorem _root_.solution {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam x' : Fin h → F) (r j : Fin h) (n : ℤ) :
    term p ϖ lam (fun i => x' i ^ p ^ h) r j n = ϖ * term p ϖ lam x' r j (n + 1) := by
  unfold term
  rw [pw_pow]
  have h1 : ((r : ℤ) + n * h + h) = (r : ℤ) + (n + 1) * h := by ring
  have h2 : ϖ ^ (-n) = ϖ * ϖ ^ (-(n + 1)) := by
    rw [show -n = -(n + 1) + 1 by ring, zpow_add_one₀ hϖ]; ring
  rw [h1, h2]; ring
end GlobalTheory.PMonE
