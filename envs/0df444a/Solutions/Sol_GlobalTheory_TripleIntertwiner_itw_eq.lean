-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.itw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:51:45.395509+00:00
-- url     : https://prove2.me/submissions/8ee58c33-ac06-4632-bf66-56b178250390

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
import Theorems.Thm_GlobalTheory_TripleIntertwiner_sum_refine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]
variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}
namespace GlobalTheory.TripleIntertwiner
theorem _root_.solution (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A₀ A B : AddSubgroup V} (hA : A₀ ≤ A) (hB : A₀ ≤ B)
    [Fintype (B ⧸ A₀.addSubgroupOf B)] (cB : ∀ x ∈ B, ∀ y ∈ B, c x y = 1)
    (f : F) (hf : ∀ x ∈ A, W x f = f) :
    ∃ ρ : ℂ, ρ ^ 2 * ((A₀.relIndex B : ℂ) * (A₀.relIndex (A ⊓ B) : ℂ)) = 1 ∧
      itw W A B f = ρ • ∑ q : B ⧸ A₀.addSubgroupOf B, W (rep q) f := by
  have h0 : A₀.relIndex B ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have h1 : A.relIndex B ≠ 0 := fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hA h)
  haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h1
  letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
  obtain ⟨k, hk, hs⟩ := sum_refine (A := B) hA (fun x => W x f) (fun x hx l hl hl' => by
    have := H.1 x l f
    rw [hf l hl', cB x hx l hl, one_smul] at this
    exact this.symm)
  have hk' : k = A₀.relIndex (A ⊓ B) := by
    have := AddSubgroup.relIndex_mul_relIndex A₀ (A ⊓ B) B (le_inf hA hB) inf_le_right
    rw [AddSubgroup.inf_relIndex_right, ← hk] at this
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h1) this).symm
  have hk0 : (k : ℂ) ≠ 0 := by
    intro h
    have : k = 0 := by exact_mod_cast h
    rw [this, zero_mul] at hk; exact h0 hk.symm
  have hn : (A.relIndex B : ℂ) ≠ 0 := by exact_mod_cast h1
  have hsq : ((Real.sqrt ((A.addSubgroupOf B).index : ℝ) : ℝ) : ℂ) ^ 2 = (A.relIndex B : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; rfl
  refine ⟨((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) * (k : ℂ)⁻¹, ?_, ?_⟩
  · rw [← hk', ← hk, mul_pow, inv_pow, hsq]
    push_cast
    field_simp
  · rw [hs, itw, finsum_eq_sum_of_fintype, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_assoc,
      inv_mul_cancel₀ hk0, mul_one]
end GlobalTheory.TripleIntertwiner
