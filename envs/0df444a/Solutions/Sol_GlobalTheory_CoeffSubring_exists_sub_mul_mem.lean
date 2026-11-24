-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.exists_sub_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:29:56.807338+00:00
-- url     : https://prove2.me/submissions/b2c0bd36-810a-44e0-88b3-20b3314658b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
import Theorems.Thm_GlobalTheory_CoeffSubring_exists_ringHom_pow
import Theorems.Thm_GlobalTheory_CoeffSubring_mem_level_of_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_pow_sub_pow_mem

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
theorem _root_.solution (hp : p.Prime) (h0 : (p : S) ∈ maximalIdeal S)
    (hL : Set.InjOn (residue S) L)
    (hB : ∀ (Q : Type) [CommRing Q] (f : ResidueField S →+* Q) (g : ResidueField S → Q),
      (∀ b ∈ residue S '' L, g b ^ p = f b) →
      ∃ σ : ResidueField S →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ residue S '' L, σ b = g b)
    (hs : ∀ n s, ∃ t ∈ level p L n, s - t ∈ maximalIdeal S) (n : ℕ) {a : S}
    (ha : a ∈ level p L n) (ha' : a ∈ maximalIdeal S) :
    ∃ t ∈ level p L n, a - p * t ∈ maximalIdeal S ^ (n + 1) := by
  classical
  let J : Ideal (level p L n) :=
    Ideal.span {(p : level p L n)} ⊔ (maximalIdeal S ^ (n + 1)).comap (level p L n).subtype
  let π := Ideal.Quotient.mk J
  let ρ : level p L n →+* ResidueField S := (residue S).comp (level p L n).subtype
  have hπ : ∀ x y : level p L n, (x : S) - y ∈ maximalIdeal S ^ (n + 1) → π x = π y :=
    fun x y h => Ideal.Quotient.eq.2 (Ideal.mem_sup_right h)
  have hp0 : (p : level p L n ⧸ J) = 0 := by
    rw [← map_natCast π]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  let φ : level p L n →+* level p L n ⧸ J :=
    { toFun := fun x => π x ^ p ^ n
      map_one' := by simp
      map_mul' := fun x y => by simp [mul_pow]
      map_zero' := by rw [map_zero, zero_pow hq]
      map_add' := fun x y => by
        obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (π x) (π y) n
        rw [map_add, hr, hp0]
        simp }
  have hρ : Function.Surjective ρ := fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    obtain ⟨t, ht, h⟩ := hs n x
    exact ⟨⟨t, ht⟩, (Ideal.Quotient.eq.2 h).symm⟩
  have hker : RingHom.ker ρ ≤ RingHom.ker φ := fun x hx => by
    have h1 : (x : S) - 0 ∈ maximalIdeal S := by simpa using (residue_eq_zero_iff _).1 hx
    have h2 := hπ (x ^ p ^ n) (0 ^ p ^ n) (pow_sub_pow_mem h0 h1 n)
    rw [zero_pow hq, map_zero, map_pow] at h2
    exact h2
  let f := ρ.liftOfSurjective hρ ⟨φ, hker⟩
  have hf : ∀ x, f (ρ x) = π x ^ p ^ n := fun x => ρ.liftOfSurjective_comp_apply hρ ⟨φ, hker⟩ x
  let g : ResidueField S → level p L n ⧸ J := fun b =>
    if h : b ∈ residue S '' L then π ⟨h.choose, mem_level_of_mem h.choose_spec.1⟩ else 0
  have hg : ∀ x (hx : x ∈ L), g (residue S x) = π ⟨x, mem_level_of_mem hx⟩ := fun x hx => by
    have h : residue S x ∈ residue S '' L := ⟨x, hx, rfl⟩
    simp only [g, dif_pos h, hL h.choose_spec.1 hx h.choose_spec.2]
  obtain ⟨σ, h1, h2⟩ := exists_ringHom_pow hB n _ f g (by
    rintro _ ⟨x, hx, rfl⟩
    rw [hg x hx, ← hf]
    rfl)
  have key : ∀ x (hx : x ∈ level p L n), σ (residue S x) = π ⟨x, hx⟩ := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with (⟨x, rfl⟩ | hx) | hx
      · obtain ⟨t, ht, h⟩ := hs n x
        have h3 : residue S x = ρ ⟨t, ht⟩ := Ideal.Quotient.eq.2 h
        rw [map_pow, h1, h3, hf, ← map_pow]
        exact (hπ _ _ (pow_sub_pow_mem h0 h n)).symm
      · rw [h2 _ ⟨x, hx, rfl⟩, hg x hx]
      · rw [(residue_eq_zero_iff _).2 (Ideal.pow_le_self n.succ_ne_zero hx), map_zero]
        exact ((hπ _ 0 (by simpa using hx)).trans (map_zero π)).symm
    | zero => rw [map_zero, map_zero]; exact (map_zero π).symm
    | one => rw [map_one, map_one]; exact (map_one π).symm
    | add x y hx hy ihx ihy => rw [map_add, map_add, ihx, ihy, ← map_add]; rfl
    | neg x hx ihx => rw [map_neg, map_neg, ihx, ← map_neg]; rfl
    | mul x y hx hy ihx ihy => rw [map_mul, map_mul, ihx, ihy, ← map_mul]; rfl
  have h3 := key a ha
  rw [(residue_eq_zero_iff _).2 ha', map_zero, eq_comm] at h3
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (Ideal.Quotient.eq_zero_iff_mem.1 h3)
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.1 hy
  refine ⟨t, t.2, ?_⟩
  have h4 : (p : S) * t + z = a := by simpa using congrArg Subtype.val hyz
  rw [← h4, add_sub_cancel_left]
  exact hz
end GlobalTheory.CoeffSubring
