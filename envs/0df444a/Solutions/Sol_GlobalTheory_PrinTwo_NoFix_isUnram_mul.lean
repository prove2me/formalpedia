-- Prove2me | solution 1 for GlobalTheory.PrinTwo.NoFix.isUnram_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:31:01.217443+00:00
-- url     : https://prove2.me/submissions/049cf4cd-8c43-4955-b0fb-8c292c3fd30e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramifiedPrincipalSeriesNoInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PrinTwo
open GlobalTheory GlobalTheory.PrinTwo GlobalTheory.PrinTwo.NoFix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.PrinTwo.NoFix
theorem _root_.solution {χ ψ : kˣ →* ℂˣ} (h : IsUnram χ) (h' : IsUnram ψ) : IsUnram (χ * ψ) := fun x hx => by
  rw [MonoidHom.mul_apply, h x hx, h' x hx, one_mul]
end GlobalTheory.PrinTwo.NoFix
