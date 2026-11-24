-- Prove2me | solution 1 for GlobalTheory.NormFormGauss.sum_norm_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:37.754846+00:00
-- url     : https://prove2.me/submissions/34fe0414-2edf-41ff-bdc7-6ee7cdbcdd0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_ne_zero


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
open GlobalTheory GlobalTheory.NormFormGauss
namespace GlobalTheory.NormFormGauss
theorem _root_.solution {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    ∃ m : ℕ, Fintype.card kˣ = m * (Finset.univ.filter (fun x : kˣ => s x = x)).card ∧
      ∀ f : k → ℂ, ∑ x : kˣ, f (x * s x) =
        m * ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y := by
  let S : kˣ →* kˣ := Units.map s.toMonoidHom
  have hS : ∀ x : kˣ, ((S x : kˣ) : k) = s x := fun x => rfl
  let N : kˣ →* kˣ := MonoidHom.id _ * S
  let D : kˣ →* kˣ := MonoidHom.id _ / S
  have hN : ∀ x : kˣ, ((N x : kˣ) : k) = x * s x := fun x => rfl
  have hD : ∀ x : kˣ, ((D x : kˣ) : k) = x / s x := fun x => by
    simp [D, hS]
  have hθ : s (s r - r) = -(s r - r) := by rw [map_sub, hs]; ring
  have hne : ∀ x : kˣ, s x ≠ 0 := fun x => by simp
  have hDk : ∀ x : kˣ, x ∈ D.ker ↔ s x = x := fun x => by
    rw [MonoidHom.mem_ker, Units.ext_iff, hD, Units.val_one, div_eq_one_iff_eq (hne x), eq_comm]
  have hker : N.ker = D.range := by
    ext x
    rw [MonoidHom.mem_ker, Units.ext_iff, hN, Units.val_one]
    constructor
    · intro hx
      by_cases h : (1 + x : k) = 0
      · refine ⟨Units.mk0 _ hr, Units.ext ?_⟩
        rw [hD, Units.val_mk0, hθ, div_neg, div_self hr]
        linear_combination -h
      · refine ⟨Units.mk0 _ h, Units.ext ?_⟩
        have h' := hne (Units.mk0 _ h)
        rw [hD, div_eq_iff h', Units.val_mk0, map_add, map_one]
        linear_combination -hx
    · rintro ⟨y, rfl⟩
      rw [hD, map_div₀, hs]
      have := hne y
      have := y.ne_zero
      field_simp
  have c1 : Nat.card kˣ = Nat.card N.range * Nat.card N.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange N).toEquiv]
  have c2 : Nat.card kˣ = Nat.card D.range * Nat.card D.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange D).toEquiv]
  have c3 : Nat.card N.range = Nat.card D.ker := by
    rw [← hker, c1, mul_comm] at c2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos c2
  have hle : N.range ≤ D.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hDk, hN, map_mul, hs, mul_comm]
  have hr' : N.range = D.ker := Subgroup.eq_of_le_of_card_ge hle c3.ge
  have c4 : Nat.card D.ker = (Finset.univ.filter (fun x : kˣ => s x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, hDk]
  refine ⟨Nat.card N.ker, ?_, fun f => ?_⟩
  · rw [← Nat.card_eq_fintype_card, c1, c3, c4, mul_comm]
  · have himg : Finset.univ.image N = Finset.univ.filter (fun x : kˣ => s x = x) := by
      ext x
      simp only [Finset.mem_filter, ← hDk, ← hr', Finset.mem_image, Finset.mem_univ, true_and]
      rfl
    have := Finset.sum_comp (s := Finset.univ) (fun y : kˣ => f y) N
    simp only [hN] at this
    rw [this, ← himg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [nsmul_eq_mul]
    congr 2
    have hy' : y ∈ Set.range N := by simpa using hy
    rw [MonoidHom.card_fiber_eq_of_mem_range N hy' (⟨1, map_one N⟩ : (1 : kˣ) ∈ Set.range N),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [MonoidHom.mem_ker]
end GlobalTheory.NormFormGauss
