-- Prove2me | solution 1 for GlobalTheory.FinWeil.exists_addChar_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:51:04.671862+00:00
-- url     : https://prove2.me/submissions/b320e560-7e1a-4a58-9234-2f931e85f963

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PerfectPairingQuotients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution {G : Type} [AddCommGroup G] (H : AddSubgroup G) (f : G → ℂ)
    (h0 : f 0 = 1) (hadd : ∀ x y, f (x + y) = f x * f y) (hH : ∀ x ∈ H, f x = 1) :
    ∃ χ : AddChar (G ⧸ H) ℂ, ∀ g : G, χ (g : G ⧸ H) = f g := by
  have hout : ∀ g : G, f (Quotient.out (g : G ⧸ H)) = f g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H g
    rw [hh, hadd, hH _ h.2, mul_one]
  refine ⟨⟨fun q => f (Quotient.out q), ?_, ?_⟩, hout⟩
  · rw [← QuotientAddGroup.mk_zero, hout, h0]
  · intro a b
    induction a using QuotientAddGroup.induction_on
    induction b using QuotientAddGroup.induction_on
    rw [← QuotientAddGroup.mk_add, hout, hout, hout, hadd]
end GlobalTheory.FinWeil
