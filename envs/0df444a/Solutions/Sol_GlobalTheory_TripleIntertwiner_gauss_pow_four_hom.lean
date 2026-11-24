-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.gauss_pow_four_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:52:10.85162+00:00
-- url     : https://prove2.me/submissions/4c6b701b-6854-40fe-9059-c74112ca0a88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
import Theorems.Thm_GlobalTheory_TripleIntertwiner_quad_four

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
namespace GlobalTheory.TripleIntertwiner
theorem _root_.solution {M : Type*} [AddCommGroup M] [Fintype M] (β : M →+ M →+ Additive ℂˣ) :
    (∑ m, ((Additive.toMul (β m m) : ℂˣ) : ℂ)) ^ 4 = (∑ m, ((Additive.toMul (β m m) : ℂˣ) : ℂ)⁻¹) ^ 4 := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (Fintype.card M - 1)
  have hc : 1 ≤ Fintype.card M := Fintype.card_pos
  have hz : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 = (Fintype.card M : ℤ) - 1 := by
    have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast [Nat.cast_sub hc] at this
    exact this
  have hneg : ∀ m : M, ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) • m = -m := by
    intro m
    rw [hz, sub_smul, natCast_zsmul, card_nsmul_eq_zero]; simp
  let T : M × M × M × M → M × M × M × M := fun p =>
    ((a : ℤ) • p.1 - (b : ℤ) • p.2.1 - (c : ℤ) • p.2.2.1 - (d : ℤ) • p.2.2.2,
     (b : ℤ) • p.1 + (a : ℤ) • p.2.1 - (d : ℤ) • p.2.2.1 + (c : ℤ) • p.2.2.2,
     (c : ℤ) • p.1 + (d : ℤ) • p.2.1 + (a : ℤ) • p.2.2.1 - (b : ℤ) • p.2.2.2,
     (d : ℤ) • p.1 - (c : ℤ) • p.2.1 + (b : ℤ) • p.2.2.1 + (a : ℤ) • p.2.2.2)
  let T' : M × M × M × M → M × M × M × M := fun p =>
    (-((a : ℤ) • p.1 + (b : ℤ) • p.2.1 + (c : ℤ) • p.2.2.1 + (d : ℤ) • p.2.2.2),
     -(-((b : ℤ) • p.1) + (a : ℤ) • p.2.1 + (d : ℤ) • p.2.2.1 - (c : ℤ) • p.2.2.2),
     -(-((c : ℤ) • p.1) - (d : ℤ) • p.2.1 + (a : ℤ) • p.2.2.1 + (b : ℤ) • p.2.2.2),
     -(-((d : ℤ) • p.1) + (c : ℤ) • p.2.1 - (b : ℤ) • p.2.2.1 + (a : ℤ) • p.2.2.2))
  have hT : Function.LeftInverse T' T := by
    rintro ⟨x, y, z, w⟩
    simp only [T, T', Prod.mk.injEq, neg_eq_iff_eq_neg]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hneg x]; module
    · rw [← hneg y]; module
    · rw [← hneg z]; module
    · rw [← hneg w]; module
  have hbij : Function.Bijective T := Finite.injective_iff_bijective.mp hT.injective
  let Q : M × M × M × M → Additive ℂˣ := fun p =>
    β p.1 p.1 + β p.2.1 p.2.1 + β p.2.2.1 p.2.2.1 + β p.2.2.2 p.2.2.2
  have hQ : ∀ p, Q (T p) = -Q p := by
    rintro ⟨x, y, z, w⟩
    have e : ∀ m : M, -β m m = ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) • β m m := by
      intro m
      rw [← map_zsmul, hneg, map_neg]
    refine (quad_four β a b c d x y z w).trans ?_
    simp only [Q, neg_add, e, smul_add]
  have key : ∀ g : M → ℂ, (∑ m, g m) ^ 4 =
      ∑ p : M × M × M × M, g p.1 * g p.2.1 * g p.2.2.1 * g p.2.2.2 := by
    intro g
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [key, key, ← hbij.sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 := congrArg (fun t : Additive ℂˣ => ((Additive.toMul t : ℂˣ) : ℂ)) (hQ p)
  simp only [Q, toMul_add, toMul_neg, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv] at h1
  exact h1
end GlobalTheory.TripleIntertwiner
