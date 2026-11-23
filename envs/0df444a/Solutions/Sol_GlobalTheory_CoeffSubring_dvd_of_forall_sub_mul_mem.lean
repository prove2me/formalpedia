-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.dvd_of_forall_sub_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:54.578592+00:00
-- url     : https://prove2.me/submissions/bf4b5540-bd8a-4190-b55b-03058f1f9217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}
namespace GlobalTheory.CoeffSubring
theorem _root_.solution [IsNoetherianRing S] {r a : S}
    (h : ∀ n, ∃ t, a - r * t ∈ maximalIdeal S ^ n) : r ∣ a := by
  have h1 := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := S ⧸ Ideal.span {r}) (maximalIdeal S)
    (maximalIdeal.isMaximal S).ne_top
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, ← Submodule.mem_bot S, ← h1,
    Submodule.mem_iInf]
  intro n
  obtain ⟨t, ht⟩ := h n
  have : Ideal.Quotient.mk (Ideal.span {r}) a = (a - r * t) • (1 : S ⧸ Ideal.span {r}) := by
    rw [← Algebra.algebraMap_eq_smul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]
    simp [Ideal.mem_span_singleton]
  rw [this]
  exact Submodule.smul_mem_smul ht trivial
end GlobalTheory.CoeffSubring
