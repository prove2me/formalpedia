-- Prove2me | solution 1 for GlobalTheory.AinfXi.coeff_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:32:48.009128+00:00
-- url     : https://prove2.me/submissions/9dce2891-9b12-470c-a08e-3a88dc1057e9

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrder
import Theorems.Thm_GlobalTheory_AinfXi_coeff_pow_pow_zero
import Theorems.Thm_ReciprocityTheory_PGsh_a0


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
open GlobalTheory.Sandwich
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
variable (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (root ε).untilt p)
include hv hε
namespace GlobalTheory.AinfXi
theorem _root_.solution (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : constantCoeff x = 0 := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -, -⟩ := ReciprocityTheory.PGsh.a0 p C v O hv
  obtain ⟨u, hu⟩ := ((hX ε hv hε).2.2.2 pf hpf).2
  have hu' : xi ε = u * ((p : Ainf p O) - teichmuller p pf) := hu
  have hxi : constantCoeff (xi ε) = constantCoeff (u : Ainf p O) * (-pf) := by
    rw [hu', map_mul, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub,
      constantCoeff_apply (x := teichmuller p pf), teichmuller_coeff_zero]
  refine Perfection.ext fun n => ?_
  obtain ⟨w, hw⟩ := hx (p ^ n)
  change PreTilt.coeff n (constantCoeff x) = PreTilt.coeff n 0
  have h0 : PreTilt.coeff n (-pf) ^ p ^ n = 0 := by
    rw [coeff_pow_pow_zero, map_neg, ← PreTilt.mk_untilt_eq_coeff_zero, hpf, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  simp only [hw, hxi, map_mul, map_pow, mul_pow]
  rw [h0, mul_zero, zero_mul, map_zero]
end GlobalTheory.AinfXi
