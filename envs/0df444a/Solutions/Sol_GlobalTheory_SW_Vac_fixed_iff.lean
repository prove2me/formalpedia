-- Prove2me | solution 1 for GlobalTheory.SW.Vac.fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:00:13.40565+00:00
-- url     : https://prove2.me/submissions/4cf58850-fc74-401b-af86-eed17c32f045

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Theorems.Thm_GlobalTheory_SW_Vac_heisS_apply

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
theorem _root_.solution [DecidableEq ι] (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ)
    (y : Matrix κ ι ℚ × Matrix κ ι ℚ) (w : Matrix κ ι ℚ → ℂ) :
    ε y • heisS y.1 y.2 w = w ↔ ∀ x, fac ε y x * w (x - y.2) = w x := by
  rw [funext_iff]
  refine forall_congr' fun x => ?_
  rw [Pi.smul_apply, heisS_apply, fac, smul_eq_mul]
  constructor <;> intro h <;> rw [← h] <;> ring
end GlobalTheory.SW.Vac
