-- Prove2me | solution 1 for GlobalTheory.exists_forall_eq_pow_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:10.181536+00:00
-- url     : https://prove2.me/submissions/b7a02e0c-4324-465a-8bf4-3264a5b1d2d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusPowerEmbeddings
import Theorems.Thm_GlobalTheory_exists_forall_eq_pow_of_finite_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (k : Type) [Field k] [CharP k p] (σ₀ σ : OE →+* k)
    (h : ∀ x, σ₀ x = 0 → σ x = 0) : ∃ n : ℕ, ∀ x, σ x = σ₀ x ^ p ^ n := by
  let I : Ideal OE := RingHom.ker σ₀
  have : I.IsPrime := RingHom.ker_isPrime σ₀
  have hp : (p : OE ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    simp [I, RingHom.mem_ker]
  have : Module.Finite ℤ (OE ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mk I).toIntAlgHom.toLinearMap
      Ideal.Quotient.mk_surjective
  have : Finite (OE ⧸ I) := by
    refine Module.finite_of_fg_torsion _ (fun x => ⟨⟨(p : ℤ), ?_⟩, ?_⟩)
    · exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    · change (p : ℤ) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, hp, zero_mul]
  let : Field (OE ⧸ I) := (Finite.isField_of_domain (OE ⧸ I)).toField
  obtain ⟨n, hn⟩ := exists_forall_eq_pow_of_finite_field p (OE ⧸ I) k
    (Ideal.Quotient.lift I σ₀ (fun _ hx => hx)) (Ideal.Quotient.lift I σ (fun x hx => h x hx))
  exact ⟨n, fun x => hn (Ideal.Quotient.mk I x)⟩
end GlobalTheory
