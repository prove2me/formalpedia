-- Prove2me | solution 1 for GlobalTheory.Proof.clears_idempotent_of_exponent_bound.exists_coprime_mul_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:13:02.080974+00:00
-- url     : https://prove2.me/submissions/640855c7-d39a-45f4-afcf-031869ffa419

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfExponentBound
import Theorems.Thm_GlobalTheory_Proof_clears_idempotent_of_exponent_bound_colon_sup_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.clears_idempotent_of_exponent_bound
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound
theorem _root_.solution {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) {l : ℕ} (hl : l.Prime) {k : ℕ}
    (hk : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) :
    ∃ m : ℕ, m.Coprime l ∧ ((m : OF E) * (l : OF E) ^ k) ∈ 𝔣 := by
  set J := 𝔣.colon {((l : OF E) ^ k)} with hJ
  have hmemJ : ∀ r : OF E, r ∈ J ↔ r * (l : OF E) ^ k ∈ 𝔣 := fun r => by
    rw [hJ, Submodule.mem_colon_singleton, smul_eq_mul]
  have hfJ : 𝔣 ≤ J := fun r hr => (hmemJ r).2 (Ideal.mul_mem_right _ _ hr)
  have hJb : J ≠ ⊥ := fun h => h𝔣 (le_bot_iff.1 (h ▸ hfJ))
  have htop := colon_sup_eq_top h𝔣 hl.ne_zero hk
  rw [← hJ] at htop
  refine ⟨Ideal.absNorm J, ?_, (hmemJ _).1 (Ideal.absNorm_mem J)⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
  intro hdvd
  have hcard : Nat.card (OF E ⧸ J) = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : Nat.card (OF E ⧸ J) ≠ 0 := by
    rw [hcard]; exact fun h => hJb (Ideal.absNorm_eq_zero_iff.1 h)
  haveI : Finite (OF E ⧸ J) := Nat.finite_of_card_ne_zero hne
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := OF E ⧸ J) l (hcard ▸ hdvd)
  have h1 : (1 : OF E) ∈ J ⊔ Ideal.span {(l : OF E)} := htop ▸ Submodule.mem_top
  obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hu : (Ideal.Quotient.mk J a) * (l : OF E ⧸ J) = 1 := by
    have : Ideal.Quotient.mk J (j + a * l) = 1 := by rw [hjy, map_one]
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add, map_mul, map_natCast] at this
    exact this
  have hlx : (l : OF E ⧸ J) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]; exact addOrderOf_nsmul_eq_zero x
  have hx0 : x = 0 := by
    calc x = (Ideal.Quotient.mk J a * (l : OF E ⧸ J)) * x := by rw [hu, one_mul]
      _ = 0 := by rw [mul_assoc, hlx, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  exact hl.one_lt.ne hx
end GlobalTheory.Proof.clears_idempotent_of_exponent_bound
