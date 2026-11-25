-- Prove2me | solution 1 for GlobalTheory.AinfXi.eq_zero_of_forall_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:46:30.550747+00:00
-- url     : https://prove2.me/submissions/71ebfcfc-a279-4671-ae3c-9cc551a26d7e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrder
import Theorems.Thm_GlobalTheory_AinfXi_dvd_of_dvd_mul_p
import Theorems.Thm_GlobalTheory_AinfXi_coeff_zero_eq_zero

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
theorem _root_.solution (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : x = 0 := by
  have key : ∀ k, ∀ x : Ainf p O, (∀ N, xi ε ^ N ∣ x) → (p : Ainf p O) ^ k ∣ x := by
    intro k
    induction k with
    | zero => intro x _; rw [pow_zero]; exact one_dvd _
    | succ k ih =>
      intro x hx
      have h0 := coeff_zero_eq_zero hv ε hε x hx
      rw [constantCoeff_apply] at h0
      obtain ⟨z, rfl⟩ := mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero x).2 h0)
      obtain ⟨w, hw⟩ := ih z fun N => dvd_of_dvd_mul_p hv ε hε N z (hx N)
      exact ⟨w, by rw [hw]; ring⟩
  ext n
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero x (n + 1)).1
    (mem_span_singleton.2 (key (n + 1) x hx)) n (Nat.lt_succ_self n)
  simpa using h
end GlobalTheory.AinfXi
