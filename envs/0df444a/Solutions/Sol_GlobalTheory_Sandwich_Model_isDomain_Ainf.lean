-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.isDomain_Ainf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:51:46.48759+00:00
-- url     : https://prove2.me/submissions/d7d9b5de-fe9d-47cb-a610-7c3d2e0081a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.Model
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
omit hε [IsAlgClosed C]
namespace GlobalTheory.Sandwich.Model
theorem _root_.solution : IsDomain (Ainf p O) := by
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance
end GlobalTheory.Sandwich.Model
