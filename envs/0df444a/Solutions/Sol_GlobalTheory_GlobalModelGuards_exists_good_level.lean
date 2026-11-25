-- Prove2me | solution 1 for GlobalTheory.GlobalModelGuards.exists_good_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:40.383339+00:00
-- url     : https://prove2.me/submissions/18427f92-1369-4b14-8625-24f1f1e574fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_ExistsGoodLevel
import Theorems.Thm_GlobalTheory_GlobalModelGuards_goodAt_of_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GlobalModelGuards
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.GlobalModelGuards
theorem _root_.solution (H : Host E) : ∃ l : Level H, l.A = 1 ∧ ∀ p : ℕ, p.Prime → l.GoodAt p := by
  have hd := H.d_mod
  obtain ⟨e, he⟩ : ∃ e, H.d = 16 * e + 7 := ⟨H.d / 16, by omega⟩
  have hrt : H.rt = 2 * H.w0 - 1 := by rw [H.two_weight_eq_one_add_root]; ring
  have hbar : H.bar H.rt = -H.rt := by
    have h2 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      have h3 : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, h]
      have φ : E →+* ℂ := Classical.choice inferInstance
      have h4 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
      rw [h3] at h4
      have h5 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      have h6 : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h4.symm
      have h7 := congrArg Complex.re h5
      simp [sq, h6] at h7
      have : (0 : ℝ) < H.d := by exact_mod_cast (by omega : 0 < H.d)
      nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
    · exact h
  set r := H.rt with hr
  have hr2 : r ^ 2 = -(H.d : 𝓞 E) := H.rt_sq
  set N₁ : ℕ := H.d + 4 with hN₁
  set N₂ : ℕ := 4 * N₁ ^ 2 + H.d with hN₂
  have hcop : N₁.Coprime N₂ := by
    have h1 : N₁.Coprime H.d := by
      rw [hN₁, Nat.coprime_self_add_left]
      exact (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2 H.d).2 ((Nat.coprime_two_left).2 ⟨8 * e + 3, by omega⟩)
    have : N₂ = H.d + N₁ * (4 * N₁) := by rw [hN₂]; ring
    rw [this, Nat.coprime_add_mul_left_right]; exact h1
  have o1 : Odd N₁ := ⟨8 * e + 5, by omega⟩
  have o2 : Odd N₂ := ⟨2 * N₁ ^ 2 + 8 * e + 3, by omega⟩
  let α : 𝓞 E := (2 + r) * (2 * N₁ + r)
  have hα : H.bar α = (2 - r) * (2 * N₁ - r) := by
    simp only [α, map_mul, map_add, map_natCast, map_ofNat, hbar]; ring
  have n1 : (2 + r) * (2 - r) = (N₁ : 𝓞 E) := by rw [hN₁]; push_cast; linear_combination -hr2
  have n2 : (2 * N₁ + r) * (2 * N₁ - r) = (N₂ : 𝓞 E) := by rw [hN₂]; push_cast; linear_combination -hr2
  have cZ : ∀ a b : ℕ, a.Coprime b → IsCoprime (a : 𝓞 E) (b : 𝓞 E) := fun a b h => Nat.Coprime.cast h
  have c4 : ∀ n : ℕ, Odd n → IsCoprime (n : 𝓞 E) (4 : 𝓞 E) := fun n hn => by
    have := cZ n 4 ((Nat.coprime_pow_right_iff (by norm_num : 0 < 2) n 2).2 (Nat.coprime_two_right.2 hn))
    simpa using this
  have c12 := cZ _ _ hcop
  have k1 : IsCoprime (2 + r) (2 - r) := by
    have := c4 _ o1
    rw [← n1] at this
    have h := this.of_mul_left_left
    have e4 : (4 : 𝓞 E) = (2 - r) + (2 + r) * 1 := by ring
    rw [e4] at h
    exact h.of_add_mul_left_right
  have k2 : IsCoprime (2 * (N₁ : 𝓞 E) + r) (2 * N₁ - r) := by
    have := (c4 _ o2).mul_right c12.symm
    rw [← n2] at this
    have h := this.of_mul_left_left
    have e4 : (4 : 𝓞 E) * N₁ = (2 * N₁ - r) + (2 * N₁ + r) * 1 := by ring
    rw [e4] at h
    exact h.of_add_mul_left_right
  have k3 : IsCoprime (2 + r) (2 * (N₁ : 𝓞 E) - r) := by
    have := c12
    rw [← n2] at this
    conv at this => lhs; rw [← n1]
    exact this.of_mul_left_left.of_mul_right_right
  have k4 : IsCoprime (2 * (N₁ : 𝓞 E) + r) (2 - r) := by
    have := c12.symm
    rw [← n2] at this
    conv at this => rhs; rw [← n1]
    exact this.of_mul_left_left.of_mul_right_right
  have hmap : (Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {H.bar α} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  have hmem : α ∈ Algebra.adjoin ℤ {H.w0} := by
    have hw : H.w0 ∈ Algebra.adjoin ℤ {H.w0} := Algebra.subset_adjoin rfl
    have hr' : r ∈ Algebra.adjoin ℤ {H.w0} := by
      rw [hrt]; exact sub_mem (mul_mem (ofNat_mem _ 2) hw) (one_mem _)
    exact mul_mem (add_mem (ofNat_mem _ 2) hr') (add_mem (mul_mem (ofNat_mem _ 2) (natCast_mem _ _)) hr')
  let l : Level H :=
    { M := N₁ * N₂
      three_le := by nlinarith [show 3 ≤ N₁ by omega, show 3 ≤ N₂ by omega]
      odd := o1.mul o2
      Mb := Ideal.span {α}
      fromK := le_antisymm (Ideal.span_mono (by
          rintro x rfl; exact ⟨Ideal.mem_span_singleton_self _, hmem⟩))
        (Ideal.span_le.2 fun x hx => hx.1)
      prod := by
        rw [hmap, Ideal.span_singleton_mul_span_singleton, hα]
        congr 2
        push_cast
        rw [← n2]
        conv_rhs => lhs; rw [← n1]
        simp only [α]; ring
      coprime := by
        rw [hmap, ← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff, hα]
        exact (k1.mul_right k3).mul_left (k4.mul_right k2)
      A := 1
      A_pos := one_pos }
  exact ⟨l, rfl, goodAt_of_coprime l N₁ N₂ (by omega) (by omega) hcop rfl⟩
end GlobalTheory.GlobalModelGuards
