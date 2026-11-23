-- Prove2me | solution 1 for GlobalTheory.AinfXi.coeff_pow_pow_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:01.67223+00:00
-- url     : https://prove2.me/submissions/c5857e2a-6aba-4cda-8724-b948f6dda447

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open GlobalTheory GlobalTheory.AinfXi
variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
namespace GlobalTheory.AinfXi
theorem _root_.solution (x : PreTilt O p) (n : ℕ) :
    PreTilt.coeff n x ^ p ^ n = PreTilt.coeff 0 x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, PreTilt.coeff_pow_p, ih]
end GlobalTheory.AinfXi
