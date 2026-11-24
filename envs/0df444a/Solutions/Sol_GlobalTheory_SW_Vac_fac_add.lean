-- Prove2me | solution 1 for GlobalTheory.SW.Vac.fac_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:08:25.453832+00:00
-- url     : https://prove2.me/submissions/7c0fc06b-85e0-46ba-8c87-e0731b4cee7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Theorems.Thm_GlobalTheory_SW_Vac_pr_comm
import Theorems.Thm_GlobalTheory_SW_Vac_pr_add_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_sub_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_add_right
import Theorems.Thm_GlobalTheory_SW_Vac_ex_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ} {y y' : Matrix κ ι ℚ × Matrix κ ι ℚ}
    (h : ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2)) (x : Matrix κ ι ℚ) :
    fac ε (y + y') x = fac ε y x * fac ε y' (x - y.2) := by
  unfold fac
  rw [h, mul_assoc, ← ex_add, mul_mul_mul_comm, ← ex_add]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, pr_add_left, pr_add_right, pr_sub_left, pr_comm y.2 y'.1]
  ring
end GlobalTheory.SW.Vac
