-- Prove2me | solution 1 for GlobalTheory.NormOneInfinite.normOne_infinite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:39.962956+00:00
-- url     : https://prove2.me/submissions/cdaaf4d8-260b-472b-8b63-0e3e54d97141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormOneInfinite
namespace GlobalTheory.NormOneInfinite
theorem _root_.solution {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
    (c : Gal(E/F)) (hc : ∀ x : E, (c : E → E) ((c : E → E) x) = x) (h1 : c ≠ (1 : Gal(E/F))) :
    Set.Infinite {l : E | l * (c : E → E) l = (1 : E)} := by
  have hx : ∃ x : E, c x ≠ x := by
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    exact h1 (AlgEquiv.ext fun x => by rw [hall x, AlgEquiv.one_apply])
  obtain ⟨x, hx⟩ := hx
  have hcd : c (x - c x) = -(x - c x) := by
    rw [map_sub, hc x]
    ring
  have hd : x - c x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcn : ∀ n : ℕ, c (n : E) = n := fun n => map_natCast c n
  have h2d : ∀ y : E, y = -y → y = 0 := by
    intro y hy
    have h2 : (2 : E) * y = 0 := by linear_combination hy
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hsub : ∀ n : ℕ, (n : E) - (x - c x) ≠ 0 := by
    intro n h0
    have e : x - c x = n := (sub_eq_zero.mp h0).symm
    apply hd
    apply h2d
    calc x - c x = c (x - c x) := by rw [e, hcn]
      _ = -(x - c x) := hcd
  have hadd : ∀ n : ℕ, (n : E) + (x - c x) ≠ 0 := by
    intro n h0
    have e : x - c x = -(n : E) := by linear_combination h0
    apply hd
    apply h2d
    calc x - c x = c (x - c x) := by rw [e, map_neg, hcn]
      _ = -(x - c x) := hcd
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + (x - c x)) / ((n : E) - (x - c x))) ?_ ?_
  · intro n m hnm
    simp only at hnm
    rw [div_eq_div_iff (hsub n) (hsub m)] at hnm
    have h3 : (2 : E) * (x - c x) * ((m : E) - n) = 0 := by linear_combination hnm
    rcases mul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' two_ne_zero
      · exact absurd h' hd
    · exact (Nat.cast_injective (sub_eq_zero.mp h)).symm
  · intro n
    change ((n : E) + (x - c x)) / ((n : E) - (x - c x)) *
      c (((n : E) + (x - c x)) / ((n : E) - (x - c x))) = 1
    rw [map_div₀, map_add, map_sub c (n : E) (x - c x), hcn, hcd]
    have h4 : (n : E) + -(x - c x) = (n : E) - (x - c x) := by ring
    have h5 : (n : E) - -(x - c x) = (n : E) + (x - c x) := by ring
    rw [h4, h5, div_mul_div_comm, mul_comm ((n : E) - (x - c x))]
    exact div_self (mul_ne_zero (hadd n) (hsub n))
end GlobalTheory.NormOneInfinite
