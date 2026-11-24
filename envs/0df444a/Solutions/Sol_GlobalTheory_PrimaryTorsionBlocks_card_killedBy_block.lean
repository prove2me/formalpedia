-- Prove2me | solution 1 for GlobalTheory.PrimaryTorsionBlocks.card_killedBy_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:44.662563+00:00
-- url     : https://prove2.me/submissions/3e5b0a39-e9e2-405d-bb4d-008def5f5345

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowers
import Theorems.Thm_GlobalTheory_PrimaryTorsionBlocks_mem_annOf
import Theorems.Thm_GlobalTheory_PrimaryTorsionBlocks_mem_killedBy_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PrimaryTorsionBlocks
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
namespace GlobalTheory.PrimaryTorsionBlocks
theorem _root_.solution (P J : Ideal R) (n : R) (e : ℕ)
    (hspan : Ideal.span {n} = P ^ e * J) (hcop : P ⊔ J = ⊤)
    (hlift : ∀ j : ℕ, ∀ y : M, n ^ j • y = 0 → ∃ z : M, n ^ (j + 1) • z = 0 ∧ n • z = y)
    (j : ℕ) :
    Nat.card (killedBy (M := M) (P ^ (e * (j + 1)))) =
      Nat.card (killedBy (M := M) (P ^ (e * j))) * Nat.card (killedBy (M := M) (P ^ e)) := by
  have hpow : ∀ k : ℕ, Ideal.span {n ^ k} = P ^ (e * k) * J ^ k := by
    intro k
    rw [← Ideal.span_singleton_pow, hspan, mul_pow, pow_mul]
  have hcop' : ∀ a b : ℕ, P ^ a ⊔ J ^ b = ⊤ := by
    intro a b
    exact Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_iff_sup_eq.2 hcop).pow)
  have hnmem : ∀ k : ℕ, n ^ k ∈ P ^ (e * k) := by
    intro k
    have : n ^ k ∈ Ideal.span {n ^ k} := Ideal.mem_span_singleton_self _
    rw [hpow k] at this
    exact (Ideal.mul_le_left : P ^ (e * k) * J ^ k ≤ P ^ (e * k)) this
  have hn : n ∈ P ^ e := by simpa using hnmem 1
  have hexp : e * (j + 1) = e * j + e := by ring
  have hle1 : P ^ (e * (j + 1)) ≤ P ^ (e * j) := Ideal.pow_le_pow_right (by rw [hexp]; omega)
  have hle2 : P ^ (e * (j + 1)) ≤ P ^ e := Ideal.pow_le_pow_right (by rw [hexp]; omega)

  let f : killedBy (M := M) (P ^ (e * (j + 1))) →+ killedBy (M := M) (P ^ (e * j)) :=
    AddMonoidHom.mk' (fun x => ⟨n • (x : M), fun a ha => by
      rw [smul_smul]
      apply x.2
      rw [hexp, pow_add]
      exact Ideal.mul_mem_mul ha hn⟩)
      (fun x y => by ext; simp [smul_add])
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy0 : n ^ j • y = 0 := hy _ (hnmem j)
    obtain ⟨z, hz, hzy⟩ := hlift j y hy0
    have h1 : (1 : R) ∈ P ^ (e * (j + 1)) ⊔ J ^ (j + 1) := by rw [hcop']; trivial
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1
    refine ⟨⟨t • z, fun a ha => ?_⟩, ?_⟩
    · rw [smul_smul]
      have hat : a * t ∈ Ideal.span {n ^ (j + 1)} := by
        rw [hpow]
        exact Ideal.mul_mem_mul ha ht
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hat
      rw [← hc, mul_smul, hz, smul_zero]
    · ext
      show n • t • z = y
      rw [smul_comm, hzy]
      have hsy : s • y = 0 := hy s (hle1 hs)
      calc t • y = s • y + t • y := by rw [hsy, zero_add]
        _ = (s + t) • y := (add_smul s t y).symm
        _ = y := by rw [hst, one_smul]
  have hsup : P ^ e ≤ P ^ (e * (j + 1)) ⊔ Ideal.span {n} := by
    have hc : P ^ (e * j) ⊔ J = ⊤ := by simpa using hcop' (e * j) 1
    have : P ^ e = P ^ e * (P ^ (e * j) ⊔ J) := by rw [hc, Ideal.mul_top]
    rw [this, Ideal.mul_sup, hspan, ← pow_add, hexp, add_comm (e * j) e]
  have hker : Nat.card f.ker = Nat.card (killedBy (M := M) (P ^ e)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : M), ?_⟩
        invFun := fun x => ⟨⟨(x : M), fun a ha => x.2 a (hle2 ha)⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    · have hx1 := mem_killedBy_iff.1 x.1.2
      have hx2 : n • (x.1 : M) = 0 := by
        have := x.2
        rw [AddMonoidHom.mem_ker] at this
        exact congrArg Subtype.val this
      refine mem_killedBy_iff.2 (le_trans hsup (sup_le hx1 ?_))
      rw [Ideal.span_singleton_le_iff_mem]
      exact mem_annOf.2 hx2
    · rw [AddMonoidHom.mem_ker]
      ext
      exact x.2 n hn
  have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, hker] at hmul
  exact hmul
end GlobalTheory.PrimaryTorsionBlocks
