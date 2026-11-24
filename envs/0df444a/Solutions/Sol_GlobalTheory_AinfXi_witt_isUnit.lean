-- Prove2me | solution 1 for GlobalTheory.AinfXi.witt_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:58:34.385895+00:00
-- url     : https://prove2.me/submissions/39795ae3-8566-471a-97f2-8218f7e8af7d

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
variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
namespace GlobalTheory.AinfXi
theorem _root_.solution (c : WittVector p R) (h : IsUnit (constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have hmem : c * teichmuller p ((u⁻¹ : Rˣ) : R) - 1 ∈ span {(p : WittVector p R)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      constantCoeff_apply (x := teichmuller p _), teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have hj := IsAdicComplete.le_jacobson_bot (span {(p : WittVector p R)}) hmem
  have h1 := (mem_jacobson_bot.1 hj) 1
  rw [mul_one, sub_add_cancel] at h1
  exact isUnit_of_mul_isUnit_left h1
end GlobalTheory.AinfXi
