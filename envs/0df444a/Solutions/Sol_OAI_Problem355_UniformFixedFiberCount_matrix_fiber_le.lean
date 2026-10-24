-- Prove2me | solution 1 for OAI.Problem355.UniformFixedFiberCount.matrix_fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:17:34.877614+00:00
-- url     : https://prove2.me/submissions/12c3b6b9-9fbd-4232-add5-dcda394e85b2

import Mathlib
import Definitions.Def_OAIQWHT000
import Theorems.Thm_OAI_Problem355_AuxiliaryZeroCount_weighted_count_le_log

section
-- module Solutions.OAIQW_Problem355.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AnisotropicDyadic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.Anisotropic

theorem card_dyadic_indices_le (S : Finset ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ i ∈ S, (2 : ℝ) ^ i ≤ R) :
    (S.card : ℝ) ≤ Real.log (2 * R) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hquot : 0 ≤ Real.log R / Real.log 2 := div_nonneg hlogR hlog2.le
  have hi (i : ℕ) (hi : i ∈ S) : i ≤ ⌊Real.log R / Real.log 2⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ hlog2).mpr
    calc
      (i : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ i) := (Real.log_pow 2 i).symm
      _ ≤ Real.log R := Real.log_le_log (by positivity) (hS i hi)
  have hs : S ⊆ Finset.range (⌊Real.log R / Real.log 2⌋₊ + 1) := by
    intro i hmem
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hi i hmem))
  have hc : (S.card : ℝ) ≤ (⌊Real.log R / Real.log 2⌋₊ : ℝ) + 1 := by
    exact_mod_cast (show S.card ≤ ⌊Real.log R / Real.log 2⌋₊ + 1 by
      simpa using Finset.card_le_card hs)
  calc
    (S.card : ℝ) ≤ (⌊Real.log R / Real.log 2⌋₊ : ℝ) + 1 := hc
    _ ≤ Real.log R / Real.log 2 + 1 := by
      linarith [Nat.floor_le hquot]
    _ = Real.log (2 * R) / Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by linarith : R ≠ 0)]
      field_simp
      ring

theorem card_dyadic_pairs_le (S : Finset (ℕ × ℕ)) {R T : ℝ}
    (hR : 1 ≤ R) (hT : 1 ≤ T)
    (hS : ∀ p ∈ S, (2 : ℝ) ^ p.1 ≤ R ∧ (2 : ℝ) ^ p.2 ≤ T) :
    (S.card : ℝ) ≤
      (Real.log (2 * R) / Real.log 2) * (Real.log (2 * T) / Real.log 2) := by
  have hfst : ∀ i ∈ S.image Prod.fst, (2 : ℝ) ^ i ≤ R := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact (hS p hp).1
  have hsnd : ∀ i ∈ S.image Prod.snd, (2 : ℝ) ^ i ≤ T := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact (hS p hp).2
  have hsub : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hc : (S.card : ℝ) ≤
      ((S.image Prod.fst).card : ℝ) * ((S.image Prod.snd).card : ℝ) := by
    exact_mod_cast (show S.card ≤ (S.image Prod.fst).card * (S.image Prod.snd).card by
      simpa using Finset.card_le_card hsub)
  exact hc.trans (mul_le_mul (card_dyadic_indices_le _ hR hfst)
    (card_dyadic_indices_le _ hT hsnd) (by positivity)
    ((Nat.cast_nonneg _).trans (card_dyadic_indices_le _ hR hfst)))

theorem sum_le_of_dyadic_fibers {α : Type*} [DecidableEq α]
    (S : Finset α) (index : α → ℕ × ℕ) (weight : α → ℝ)
    {R T A : ℝ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hA : 0 ≤ A)
    (hindex : ∀ x ∈ S, (2 : ℝ) ^ (index x).1 ≤ R ∧
      (2 : ℝ) ^ (index x).2 ≤ T)
    (hgroup : ∀ p ∈ S.image index,
      ∑ x ∈ S with index x = p, weight x ≤ A) :
    ∑ x ∈ S, weight x ≤
      A * (Real.log (2 * R) / Real.log 2) * (Real.log (2 * T) / Real.log 2) := by
  have hscales : ∀ p ∈ S.image index,
      (2 : ℝ) ^ p.1 ≤ R ∧ (2 : ℝ) ^ p.2 ≤ T := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact hindex x hx
  calc
    ∑ x ∈ S, weight x = ∑ p ∈ S.image index,
        ∑ x ∈ S with index x = p, weight x := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun x hx => Finset.mem_image_of_mem index hx) weight
    _ ≤ ∑ _p ∈ S.image index, A := Finset.sum_le_sum hgroup
    _ = A * ((S.image index).card : ℝ) := by simp [mul_comm]
    _ ≤ A * ((Real.log (2 * R) / Real.log 2) *
        (Real.log (2 * T) / Real.log 2)) :=
      mul_le_mul_of_nonneg_left (card_dyadic_pairs_le _ hR hT hscales) hA
    _ = _ := by ring

theorem thin_normal_group_numeric {U Y R₁ R₂ R₃ C : ℝ}
    (hU : 0 < U) (hY : 0 < Y) (hR : 0 ≤ R₃) (hUR : U ≤ R₃)
    (hC : 0 ≤ C) :
    C * U ^ 2 * Y ^ 2 * (R₁ ^ 2 / Y) *
        (R₂ ^ 2 / Y) * (R₃ / U) ≤ C * (R₁ * R₂ * R₃) ^ 2 := by
  have heq : C * U ^ 2 * Y ^ 2 * (R₁ ^ 2 / Y) *
      (R₂ ^ 2 / Y) * (R₃ / U) = C * R₁ ^ 2 * R₂ ^ 2 * R₃ * U := by
    field_simp
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_left hUR
    (show 0 ≤ C * R₁ ^ 2 * R₂ ^ 2 * R₃ by positivity)
  nlinarith

theorem dyadic_log_product_le {R₁ R₂ R₃ : ℝ}
    (h₂ : 1 ≤ R₂) (h₃ : 1 ≤ R₃) (h₂₁ : R₂ ≤ R₁) (h₃₁ : R₃ ≤ R₁) :
    (Real.log (2 * R₃) / Real.log 2) *
      (Real.log (2 * (R₂ * R₃)) / Real.log 2) ≤
        2 * (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
  have h₁ : 1 ≤ R₁ := h₂.trans h₂₁
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ Real.log (2 * R₁) / Real.log 2 := by
    apply div_nonneg _ hlog2.le
    exact Real.log_nonneg (by linarith)
  have hleft : Real.log (2 * R₃) / Real.log 2 ≤
      Real.log (2 * R₁) / Real.log 2 := by
    apply div_le_div_of_nonneg_right _ hlog2.le
    exact Real.log_le_log (by linarith) (by linarith)
  have hmul : R₂ * R₃ ≤ R₁ * R₁ :=
    mul_le_mul h₂₁ h₃₁ (by linarith) (by linarith)
  have hright : Real.log (2 * (R₂ * R₃)) / Real.log 2 ≤
      2 * (Real.log (2 * R₁) / Real.log 2) := by
    have hp : 0 < 2 * (R₂ * R₃) := by positivity
    have hr : Real.log (2 * (R₂ * R₃)) ≤ 2 * Real.log (2 * R₁) := by
      calc
        Real.log (2 * (R₂ * R₃)) ≤ Real.log ((2 * R₁) ^ 2) :=
          Real.log_le_log hp (by nlinarith [sq_nonneg R₁])
        _ = _ := by rw [Real.log_pow]; norm_num
    have := div_le_div_of_nonneg_right hr hlog2.le
    simpa [mul_div_assoc] using this
  have hright0 : 0 ≤ Real.log (2 * (R₂ * R₃)) / Real.log 2 := by
    apply div_nonneg _ hlog2.le
    apply Real.log_nonneg
    nlinarith
  have hprod := mul_le_mul hleft hright hright0 hL
  nlinarith

theorem sum_le_of_dyadic_shell_estimates {α : Type*} [DecidableEq α]
    (S : Finset α) (u v weight : α → ℝ) {R T A : ℝ}
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hA : 0 ≤ A)
    (hweight : ∀ x ∈ S, 0 ≤ weight x)
    (hvalue : ∀ x ∈ S, 1 ≤ u x ∧ u x ≤ R ∧ 1 ≤ v x ∧ v x ≤ T)
    (hshell : ∀ i j : ℕ,
      ∑ x ∈ S with ((2 : ℝ) ^ i ≤ u x ∧ u x < 2 ^ (i + 1) ∧
        (2 : ℝ) ^ j ≤ v x ∧ v x < 2 ^ (j + 1)), weight x ≤ A) :
    ∑ x ∈ S, weight x ≤
      A * (Real.log (2 * R) / Real.log 2) * (Real.log (2 * T) / Real.log 2) := by
  classical
  have hex : ∀ x : α, ∃ p : ℕ × ℕ, x ∈ S →
      (2 : ℝ) ^ p.1 ≤ u x ∧ u x < 2 ^ (p.1 + 1) ∧
      (2 : ℝ) ^ p.2 ≤ v x ∧ v x < 2 ^ (p.2 + 1) := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨i, hi, hi'⟩ := exists_nat_pow_near (hvalue x hx).1 (by norm_num : (1 : ℝ) < 2)
      obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near (hvalue x hx).2.2.1 (by norm_num : (1 : ℝ) < 2)
      exact ⟨(i,j), fun _ => ⟨hi, hi', hj, hj'⟩⟩
    · exact ⟨(0,0), fun h => (hx h).elim⟩
  choose index hindex using hex
  apply sum_le_of_dyadic_fibers S index weight hR hT hA
  · intro x hx
    exact ⟨(hindex x hx).1.trans (hvalue x hx).2.1,
      (hindex x hx).2.2.1.trans (hvalue x hx).2.2.2⟩
  · intro p hp
    have hsub : (S.filter fun x => index x = p) ⊆
        (S.filter fun x => (2 : ℝ) ^ p.1 ≤ u x ∧ u x < 2 ^ (p.1 + 1) ∧
          (2 : ℝ) ^ p.2 ≤ v x ∧ v x < 2 ^ (p.2 + 1)) := by
      intro x hx
      obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨hxS, ?_⟩
      simpa [hxp] using hindex x hxS
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x hx _ => hweight x (Finset.mem_filter.mp hx).1)).trans (hshell p.1 p.2)

end Problem355.Anisotropic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimitiveNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimitiveNormal

open Matrix
open scoped Matrix

lemma coordGcd_eq_zero_iff (v : Vector) : coordGcd v = 0 ↔ v = 0 := by
  rw [coordGcd, Int.gcd_eq_zero_iff]
  constructor
  · rintro ⟨h01, h2⟩
    have h01' : Int.gcd (v 0) (v 1) = 0 := by exact_mod_cast h01
    obtain ⟨h0, h1⟩ := Int.gcd_eq_zero_iff.mp h01'
    ext i
    fin_cases i <;> simp_all
  · intro h
    subst v
    simp

lemma coordGcd_dvd (v : Vector) (i : Fin 3) : (coordGcd v : ℤ) ∣ v i := by
  have h01 := Int.gcd_dvd_left (Int.gcd (v 0) (v 1) : ℤ) (v 2)
  have h2 := Int.gcd_dvd_right (Int.gcd (v 0) (v 1) : ℤ) (v 2)
  fin_cases i
  · exact dvd_trans h01 (Int.gcd_dvd_left _ _)
  · exact dvd_trans h01 (Int.gcd_dvd_right _ _)
  · exact h2

lemma exists_dot_eq_coordGcd (v : Vector) :
    ∃ z : Vector, v ⬝ᵥ z = (coordGcd v : ℤ) := by
  let d : ℤ := Int.gcd (v 0) (v 1)
  refine ⟨![Int.gcdA (v 0) (v 1) * Int.gcdA d (v 2),
    Int.gcdB (v 0) (v 1) * Int.gcdA d (v 2), Int.gcdB d (v 2)], ?_⟩
  have h01 := Int.gcd_eq_gcd_ab (v 0) (v 1)
  have h2 := Int.gcd_eq_gcd_ab d (v 2)
  simp only [vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  change _ = (Int.gcd d (v 2) : ℤ)
  rw [h2]
  change _ = (Int.gcd (v 0) (v 1) : ℤ) * _ + _
  rw [h01]
  ring

lemma isPrimitive_iff_exists_dot_eq_one (v : Vector) :
    IsPrimitive v ↔ ∃ z : Vector, v ⬝ᵥ z = 1 := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := exists_dot_eq_coordGcd v
    change coordGcd v = 1 at h
    exact ⟨z, by simpa [h] using hz⟩
  · rintro ⟨z, hz⟩
    have hd : (coordGcd v : ℤ) ∣ v ⬝ᵥ z := by
      rw [vec3_dotProduct]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left (coordGcd_dvd v 0) _)
        (dvd_mul_of_dvd_left (coordGcd_dvd v 1) _))
        (dvd_mul_of_dvd_left (coordGcd_dvd v 2) _)
    rw [hz] at hd
    have hd' : coordGcd v ∣ 1 := by exact_mod_cast hd
    exact Nat.dvd_one.mp hd'

lemma IsPrimitive.ne_zero {v : Vector} (h : IsPrimitive v) : v ≠ 0 := by
  intro hv
  have hg := (coordGcd_eq_zero_iff v).mpr hv
  unfold IsPrimitive at h
  omega

theorem exists_primitive_factor (v : Vector) (hv : v ≠ 0) :
    ∃ g : ℤ, 0 < g ∧ ∃ w : Vector, IsPrimitive w ∧ v = g • w := by
  let g : ℤ := coordGcd v
  have hg : 0 < g := by
    have : coordGcd v ≠ 0 := by simpa [coordGcd_eq_zero_iff] using hv
    change (0 : ℤ) < (coordGcd v : ℤ)
    exact_mod_cast Nat.pos_of_ne_zero this
  let w : Vector := fun i => v i / g
  have hscale : v = g • w := by
    ext i
    exact (Int.mul_ediv_cancel' (coordGcd_dvd v i)).symm
  obtain ⟨z, hz⟩ := exists_dot_eq_coordGcd v
  have hw : w ⬝ᵥ z = 1 := by
    apply mul_left_cancel₀ (ne_of_gt hg)
    calc
      g * (w ⬝ᵥ z) = (g • w) ⬝ᵥ z := by rw [smul_dotProduct, smul_eq_mul]
      _ = v ⬝ᵥ z := by rw [← hscale]
      _ = g := hz
      _ = g * 1 := by ring
  exact ⟨g, hg, w, (isPrimitive_iff_exists_dot_eq_one w).mpr ⟨z, hw⟩, hscale⟩

end Problem355.PrimitiveNormal

end OAI
end

section
-- module Solutions.OAIQW_Problem355.CrossNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.CrossNormal

open Matrix
open scoped Matrix
open PrimitiveNormal

lemma toEuclidean_zsmul (g : ℤ) (w : Vector) :
    toEuclidean (g • w) = (g : ℝ) • toEuclidean w := by
  ext i
  simp [PrimitiveNormal.toEuclidean, Pi.smul_apply, smul_eq_mul]

theorem norm_cross_le (u v : Vector) :
    ‖toEuclidean (u ⨯₃ v)‖ ≤ ‖toEuclidean u‖ * ‖toEuclidean v‖ := by
  let d : ℝ := ∑ i : Fin 3, (u i : ℝ) * (v i : ℝ)
  have hlagrange : ‖toEuclidean (u ⨯₃ v)‖ ^ 2 + d ^ 2 =
      ‖toEuclidean u‖ ^ 2 * ‖toEuclidean v‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    simp [PrimitiveNormal.toEuclidean, d, Fin.sum_univ_three, cross_apply]
    ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    ‖toEuclidean (u ⨯₃ v)‖ ^ 2 ≤
        ‖toEuclidean u‖ ^ 2 * ‖toEuclidean v‖ ^ 2 := by nlinarith [sq_nonneg d]
    _ = (‖toEuclidean u‖ * ‖toEuclidean v‖) ^ 2 := by ring

theorem norm_le_of_positive_factor {v w : Vector} {g : ℤ}
    (hg : 0 < g) (hscale : v = g • w) : ‖toEuclidean w‖ ≤ ‖toEuclidean v‖ := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  rw [hscale, toEuclidean_zsmul, norm_smul, Real.norm_eq_abs, abs_of_pos hgR]
  nlinarith [norm_nonneg (toEuclidean w)]

theorem determinant_eq_factor_dot {u v w : Vector} {g : ℤ}
    (hscale : u ⨯₃ v = g • w) (x : Vector) :
    Matrix.det ![x, u, v] = g * (x ⬝ᵥ w) := by
  rw [← triple_product_eq_det, hscale, dotProduct_smul, smul_eq_mul]

theorem determinant_eq_iff_difference_dot_zero {u v w : Vector} {g : ℤ}
    (hg : g ≠ 0) (hscale : u ⨯₃ v = g • w) (x z : Vector) :
    Matrix.det ![x, u, v] = Matrix.det ![z, u, v] ↔ (x - z) ⬝ᵥ w = 0 := by
  rw [determinant_eq_factor_dot hscale, determinant_eq_factor_dot hscale,
    sub_dotProduct, sub_eq_zero]
  constructor
  · exact mul_left_cancel₀ hg
  · intro h
    rw [h]

theorem exists_bounded_primitive_cross_factor (u v : Vector) (huv : u ⨯₃ v ≠ 0) :
    ∃ g : ℤ, 0 < g ∧ ∃ w : Vector, IsPrimitive w ∧ u ⨯₃ v = g • w ∧
      u ⬝ᵥ w = 0 ∧ v ⬝ᵥ w = 0 ∧
      ‖toEuclidean w‖ ≤ ‖toEuclidean u‖ * ‖toEuclidean v‖ ∧
      (∀ x z : Vector, Matrix.det ![x, u, v] = Matrix.det ![z, u, v] ↔
        (x - z) ⬝ᵥ w = 0) := by
  obtain ⟨g, hg, w, hw, hscale⟩ := exists_primitive_factor (u ⨯₃ v) huv
  have horth (x : Vector) (hx : x ⬝ᵥ u ⨯₃ v = 0) : x ⬝ᵥ w = 0 := by
    rw [hscale, dotProduct_smul, smul_eq_mul] at hx
    exact (mul_eq_zero.mp hx).resolve_left (ne_of_gt hg)
  refine ⟨g, hg, w, hw, hscale, horth u (dot_self_cross u v),
    horth v (dot_cross_self u v), ?_, ?_⟩
  · exact (norm_le_of_positive_factor hg hscale).trans (norm_cross_le u v)
  · exact determinant_eq_iff_difference_dot_zero (ne_of_gt hg) hscale

end Problem355.CrossNormal

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticeBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.LatticeBox

open Finset

theorem card_le_of_coord_bound {d N : ℕ} (S : Finset (Fin d → ℤ))
    (hS : ∀ v ∈ S, ∀ i, |v i| ≤ (N : ℤ)) :
    S.card ≤ (2 * N + 1) ^ d := by
  rw [← card_box]
  exact Finset.card_le_card (fun v hv => mem_box.mpr (hS v hv))

theorem int_abs_le_floor {a : ℤ} {R : ℝ} (h : |(a : ℝ)| ≤ R) :
    |a| ≤ (⌊R⌋₊ : ℤ) := by
  have hcast : (a.natAbs : ℝ) = |(a : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs a)
  have hn : a.natAbs ≤ ⌊R⌋₊ := Nat.le_floor (hcast ▸ h)
  rw [← Int.natCast_natAbs]
  exact_mod_cast hn

theorem card_le_of_real_coord_bound {d : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (S : Finset (Fin d → ℤ))
    (hS : ∀ v ∈ S, ∀ i, |(v i : ℝ)| ≤ R) :
    (S.card : ℝ) ≤ (2 * R + 1) ^ d := by
  have hcount := card_le_of_coord_bound S
    (fun v hv i => int_abs_le_floor (hS v hv i))
  calc
    (S.card : ℝ) ≤ ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) ^ d := by exact_mod_cast hcount
    _ = (2 * (⌊R⌋₊ : ℝ) + 1) ^ d := by norm_cast
    _ ≤ (2 * R + 1) ^ d := by
      gcongr
      exact Nat.floor_le hR

theorem card_le_onehundredtwentyfive_mul_cube {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, ∀ i, |(v i : ℝ)| ≤ 2 * R) :
    (S.card : ℝ) ≤ 125 * R ^ 3 := by
  calc
    (S.card : ℝ) ≤ (2 * (2 * R) + 1) ^ 3 :=
      card_le_of_real_coord_bound (by linarith) S hS
    _ ≤ (5 * R) ^ 3 := by gcongr; linarith
    _ = 125 * R ^ 3 := by ring

theorem abs_coord_le_norm {d : ℕ} (v : Fin d → ℤ) (i : Fin d) :
    |(v i : ℝ)| ≤ ‖realVector v‖ := by
  simpa [realVector, Real.norm_eq_abs] using PiLp.norm_apply_le (realVector v) i

theorem card_le_of_norm_bound_twice {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, ‖realVector v‖ ≤ 2 * R) :
    (S.card : ℝ) ≤ 125 * R ^ 3 :=
  card_le_onehundredtwentyfive_mul_cube hR S
    (fun v hv i => (abs_coord_le_norm v i).trans (hS v hv))

end Problem355.LatticeBox

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticeReciprocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.LatticeBox

open Finset

theorem one_le_norm_realVector {d : ℕ} {v : Fin d → ℤ} (hv : v ≠ 0) :
    1 ≤ ‖realVector v‖ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    ext i
    simpa using not_exists.mp h i
  have ha : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
  have har : (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast ha
  exact har.trans (abs_coord_le_norm v i)

theorem reciprocal_cube_shell_le {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, R ≤ ‖realVector v‖ ∧ ‖realVector v‖ ≤ 2 * R) :
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤ 125 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hcount := card_le_of_norm_bound_twice hR S (fun v hv => (hS v hv).2)
  calc
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤ ∑ _v ∈ S, 1 / R ^ 3 := by
      apply Finset.sum_le_sum
      intro v hv
      apply one_div_le_one_div_of_le (pow_pos hRpos 3)
      exact pow_le_pow_left₀ hRpos.le (hS v hv).1 3
    _ = (S.card : ℝ) / R ^ 3 := by simp [div_eq_mul_inv]
    _ ≤ 125 := (div_le_iff₀ (pow_pos hRpos 3)).mpr hcount

theorem reciprocal_cube_sum_lt_pow_le (m : ℕ) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, 1 ≤ ‖realVector v‖ ∧ ‖realVector v‖ < (2 : ℝ) ^ m) :
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤ 125 * (m : ℝ) := by
  induction m generalizing S with
  | zero =>
      have hempty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have h := hS v hv
        simpa using not_lt_of_ge h.1 h.2
      simp [hempty]
  | succ m ih =>
      let A := S.filter (fun v => ‖realVector v‖ < (2 : ℝ) ^ m)
      let B := S.filter (fun v => ¬ ‖realVector v‖ < (2 : ℝ) ^ m)
      have hA : ∑ v ∈ A, 1 / ‖realVector v‖ ^ 3 ≤ 125 * (m : ℝ) := by
        apply ih
        intro v hv
        exact ⟨(hS v (Finset.mem_filter.mp hv).1).1, (Finset.mem_filter.mp hv).2⟩
      have hB : ∑ v ∈ B, 1 / ‖realVector v‖ ^ 3 ≤ 125 := by
        apply reciprocal_cube_shell_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvS, hvB⟩
        refine ⟨le_of_not_gt hvB, ?_⟩
        have hh := (hS v hvS).2.le
        simpa [pow_succ, mul_comm] using hh
      have hsplit : (∑ v ∈ A, 1 / ‖realVector v‖ ^ 3) +
          (∑ v ∈ B, 1 / ‖realVector v‖ ^ 3) =
          ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 := by
        exact Finset.sum_filter_add_sum_filter_not S _ _
      rw [← hsplit]
      push_cast
      linarith

theorem reciprocal_cube_sum_le_logb {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, v ≠ 0 ∧ ‖realVector v‖ ≤ R) :
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤
      125 * (Real.logb 2 R + 1) := by
  let m := ⌊Real.logb 2 R⌋₊ + 1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlog : 0 ≤ Real.logb 2 R := Real.logb_nonneg (by norm_num) hR
  have hpow : R < (2 : ℝ) ^ m := by
    rw [← Real.rpow_natCast]
    apply (Real.logb_lt_iff_lt_rpow (by norm_num) hRpos).mp
    simpa [m] using Nat.lt_floor_add_one (Real.logb 2 R)
  calc
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤ 125 * (m : ℝ) := by
      apply reciprocal_cube_sum_lt_pow_le
      intro v hv
      exact ⟨one_le_norm_realVector (hS v hv).1, (hS v hv).2.trans_lt hpow⟩
    _ ≤ 125 * (Real.logb 2 R + 1) := by
      have hfloor := Nat.floor_le hlog
      dsimp [m]
      push_cast
      nlinarith

theorem reciprocal_cube_sum_le_log {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, v ≠ 0 ∧ ‖realVector v‖ ≤ R) :
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤
      (125 / Real.log 2) * Real.log (2 * R) := by
  calc
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤ 125 * (Real.logb 2 R + 1) :=
      reciprocal_cube_sum_le_logb hR S hS
    _ = (125 / Real.log 2) * Real.log (2 * R) := by
      rw [Real.log_mul (by norm_num) (by linarith : R ≠ 0), Real.logb]
      field_simp
      ring

end Problem355.LatticeBox

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormalGroupCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.LatticeBox

open Finset

theorem card_le_sum_card_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (r : α → β → Prop) [DecidableRel r]
    (hcover : ∀ a ∈ S, ∃ b ∈ T, r a b) :
    S.card ≤ ∑ b ∈ T, (S.filter (fun a => r a b)).card := by
  calc
    S.card ≤ (T.biUnion (fun b => S.filter (fun a => r a b))).card := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨b, hb, hab⟩ := hcover a ha
      exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hab⟩⟩
    _ ≤ ∑ b ∈ T, (S.filter (fun a => r a b)).card := Finset.card_biUnion_le

theorem normal_group_card_le {U Z C : ℝ} (hU : 1 ≤ U) (hC : 0 ≤ C)
    (P : (Fin 3 → ℤ) → Prop) (S : Finset (Fin 3 → ℤ))
    (hcover : ∀ y ∈ S, ∃ z : Fin 3 → ℤ,
      P z ∧ U ≤ ‖realVector z‖ ∧ ‖realVector z‖ ≤ 2 * U ∧ dotProduct z y = 0)
    (hplane : ∀ z, P z → U ≤ ‖realVector z‖ → ‖realVector z‖ ≤ 2 * U →
      ((S.filter (fun y => dotProduct z y = 0)).card : ℝ) ≤ C * U * Z ^ 2) :
    (S.card : ℝ) ≤ 125 * C * U ^ 4 * Z ^ 2 := by
  classical
  let T := (box 3 ⌊2 * U⌋₊).filter (fun z =>
    P z ∧ U ≤ ‖realVector z‖ ∧ ‖realVector z‖ ≤ 2 * U)
  have hT : ∀ z ∈ T, P z ∧ U ≤ ‖realVector z‖ ∧ ‖realVector z‖ ≤ 2 * U := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hTcard : (T.card : ℝ) ≤ 125 * U ^ 3 :=
    card_le_of_norm_bound_twice hU T (fun z hz => (hT z hz).2.2)
  have hcoverT : ∀ y ∈ S, ∃ z ∈ T, dotProduct z y = 0 := by
    intro y hy
    obtain ⟨z, hzP, hzU, hz2U, hzy⟩ := hcover y hy
    refine ⟨z, Finset.mem_filter.mpr ⟨?_, hzP, hzU, hz2U⟩, hzy⟩
    apply mem_box.mpr
    intro i
    exact int_abs_le_floor ((abs_coord_le_norm z i).trans hz2U)
  have hnat := card_le_sum_card_cover S T (fun y z => dotProduct z y = 0) hcoverT
  have hreal : (S.card : ℝ) ≤
      ∑ z ∈ T, ((S.filter (fun y => dotProduct z y = 0)).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (S.card : ℝ) ≤ ∑ z ∈ T, ((S.filter (fun y => dotProduct z y = 0)).card : ℝ) := hreal
    _ ≤ ∑ _z ∈ T, C * U * Z ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact hplane z (hT z hz).1 (hT z hz).2.1 (hT z hz).2.2
    _ = (T.card : ℝ) * (C * U * Z ^ 2) := by simp
    _ ≤ (125 * U ^ 3) * (C * U * Z ^ 2) := by
      apply mul_le_mul_of_nonneg_right hTcard
      positivity
    _ = 125 * C * U ^ 4 * Z ^ 2 := by ring

end Problem355.LatticeBox

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AnisotropicGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix
open scoped Matrix
open PrimitiveNormal

theorem affine_plane_card_le (y : IntVector) (d : PlaneData y)
    (S : Finset IntVector) (center : EuclideanSpace ℝ (Fin 3))
    (R : ℝ) (hR : d.second ≤ R)
    (hsize : ∀ v ∈ S, ‖LatticeBox.realVector v - center‖ ≤ R)
    (hplane : ∀ v ∈ S, ∀ w ∈ S, (v - w) ⬝ᵥ y = 0) :
    (S.card : ℝ) ≤ 36 * Real.pi * R ^ 2 / length y := by
  classical
  have hR0 : 0 ≤ R := (show (0 : ℝ) ≤ 1 by norm_num).trans
    (d.one_le_first.trans (d.first_le_second.trans hR))
  by_cases hS : S.Nonempty
  · obtain ⟨w, hw⟩ := hS
    let T := S.image (fun v => v - w)
    have hcard : T.card = S.card := Finset.card_image_of_injective _
      (fun _ _ h => sub_left_inj.mp h)
    have hT (v : IntVector) (hv : v ∈ T) :
        v ⬝ᵥ y = 0 ∧ length v ≤ 2 * R := by
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      refine ⟨hplane u hu w hw, ?_⟩
      have hcast : LatticeBox.realVector (u - w) =
          LatticeBox.realVector u - LatticeBox.realVector w := by
        ext i
        simp [LatticeBox.realVector]
      change ‖LatticeBox.realVector (u - w)‖ ≤ 2 * R
      rw [hcast]
      rw [show LatticeBox.realVector u - LatticeBox.realVector w =
        (LatticeBox.realVector u - center) - (LatticeBox.realVector w - center) by abel]
      exact (norm_sub_le _ _).trans (by linarith [hsize u hu, hsize w hw])
    have h := d.large_count T (2 * R) (by linarith) hT
    rw [hcard] at h
    convert h using 1; ring
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hzero]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end Problem355.Anisotropic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticeSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem355.LatticeSplit
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {A : Type*} [AddCommGroup A]

theorem exists_positive_image_generator (f : A →ₗ[ℤ] ℤ) (hf : f ≠ 0) :
    ∃ g : ℤ, 0 < g ∧ (∀ x, g ∣ f x) ∧ ∃ u : A, f u = g := by
  let g := Submodule.IsPrincipal.generator (LinearMap.range f)
  have hdiv : ∀ x, g ∣ f x := fun x =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd (LinearMap.range f)).mp ⟨x, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, f u = g := Submodule.IsPrincipal.generator_mem (LinearMap.range f)
  have hg : g ≠ 0 := by
    intro hg
    apply hf
    ext x
    have h := hdiv x
    simpa [hg] using h
  by_cases hpos : 0 < g
  · exact ⟨g, hpos, hdiv, u, hu⟩
  · refine ⟨-g, by omega, ?_, -u, ?_⟩
    · intro x
      simpa only [neg_dvd] using hdiv x
    · simp [hu]

theorem exists_plane_kernel_basis (f : (Fin 3 → ℤ) →ₗ[ℤ] ℤ) (hf : f ≠ 0) :
    Nonempty (Basis (Fin 2) ℤ (LinearMap.ker f)) := by
  obtain ⟨g, hg, hdiv, u, hu⟩ := exists_positive_image_generator f hf
  exact ⟨integerKernelBasisFin f g (ne_of_gt hg) hdiv u hu 2 (by simp)⟩

end Problem355.LatticeSplit

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PlaneCovolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Lattice

open Module MeasureTheory
open scoped BigOperators Matrix

theorem covolume_sq_eq_det_gram
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) (o : OrthonormalBasis ι ℝ E) :
    ZLattice.covolume L ^ 2 = (Matrix.gram ℝ (fun i => (b i : E))).det := by
  have hvol : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
    simp [Measure.real, o.volume_parallelepiped]
  have hcov := ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis
  rw [hvol, mul_one] at hcov
  rw [hcov, sq_abs, Matrix.gram_eq_conjTranspose_mul o,
    Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [Basis.det_apply, pow_two, star_trivial]
  rfl

theorem normal_smul_cross_eq_det_smul
    (u v w y : Fin 3 → ℝ)
    (hu : u ⬝ᵥ y = 0) (hv : v ⬝ᵥ y = 0) :
    (y ⬝ᵥ w) • (u ⨯₃ v) = (Matrix.det ![u, v, w]) • y := by
  have hz : (u ⨯₃ v) ⨯₃ y = 0 := by
    rw [cross_cross_eq_smul_sub_smul, hu, hv, zero_smul, zero_smul, sub_self]
  have h := cross_cross_eq_smul_sub_smul (u ⨯₃ v) y w
  rw [hz] at h
  have ht : (u ⨯₃ v) ⬝ᵥ w = Matrix.det ![u, v, w] := by
    rw [dotProduct_comm, triple_product_permutation, triple_product_eq_det]
  have hzero : (Matrix.det ![u, v, w]) • y - (y ⬝ᵥ w) • (u ⨯₃ v) = 0 := by
    simpa only [map_zero, LinearMap.zero_apply, ht] using h.symm
  exact (sub_eq_zero.mp hzero).symm

theorem cross_norm_eq_abs_det_mul_norm_div
    (u v w y : Fin 3 → ℝ)
    (hu : u ⬝ᵥ y = 0) (hv : v ⬝ᵥ y = 0) (hg : y ⬝ᵥ w ≠ 0) :
    ‖WithLp.toLp 2 (u ⨯₃ v)‖ =
      |Matrix.det ![u, v, w]| * ‖WithLp.toLp 2 y‖ / |y ⬝ᵥ w| := by
  have hn := congrArg (fun z : Fin 3 → ℝ => ‖WithLp.toLp 2 z‖)
    (normal_smul_cross_eq_det_smul u v w y hu hv)
  have hnorm : |y ⬝ᵥ w| * ‖WithLp.toLp 2 (u ⨯₃ v)‖ =
      |Matrix.det ![u, v, w]| * ‖WithLp.toLp 2 y‖ := by
    simpa only [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] using hn
  apply (eq_div_iff (abs_ne_zero.mpr hg)).2
  simpa only [mul_comm] using hnorm

theorem det_gram_pair_eq_cross_norm_sq
    (u v : EuclideanSpace ℝ (Fin 3)) :
    (Matrix.gram ℝ ![u, v]).det =
      ‖WithLp.toLp 2 (u.ofLp ⨯₃ v.ofLp)‖ ^ 2 := by
  rw [Matrix.det_fin_two, ← real_inner_self_eq_norm_sq]
  simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [cross_dot_cross]
  rw [dotProduct_comm v.ofLp u.ofLp]

theorem covolume_eq_cross_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 2) ℤ L) (o : OrthonormalBasis (Fin 2) ℝ E)
    (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ZLattice.covolume L =
      ‖WithLp.toLp 2 ((f (b 0)).ofLp ⨯₃ (f (b 1)).ofLp)‖ := by
  apply (sq_eq_sq₀ (ZLattice.covolume_pos L volume).le (norm_nonneg _)).mp
  rw [covolume_sq_eq_det_gram L b o, ← det_gram_pair_eq_cross_norm_sq]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.gram_apply, f.inner_map_map]

theorem covolume_eq_abs_det_mul_norm_div
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 2) ℤ L)
    (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (w y : Fin 3 → ℝ)
    (h0 : (f (b 0)).ofLp ⬝ᵥ y = 0)
    (h1 : (f (b 1)).ofLp ⬝ᵥ y = 0) (hg : y ⬝ᵥ w ≠ 0) :
    ZLattice.covolume L =
      |Matrix.det ![(f (b 0)).ofLp, (f (b 1)).ofLp, w]| *
        ‖WithLp.toLp 2 y‖ / |y ⬝ᵥ w| := by
  have hdim : finrank ℝ E = 2 := by
    simpa using finrank_eq_card_basis (b.ofZLatticeBasis ℝ)
  let o := (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  rw [covolume_eq_cross_norm L b o f]
  exact cross_norm_eq_abs_det_mul_norm_div _ _ w y h0 h1 hg

theorem covolume_eq_index_mul_norm_div
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 2) ℤ L)
    (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (w y : Fin 3 → ℝ) (I g : ℝ)
    (h0 : (f (b 0)).ofLp ⬝ᵥ y = 0)
    (h1 : (f (b 1)).ofLp ⬝ᵥ y = 0)
    (hI : |Matrix.det ![(f (b 0)).ofLp, (f (b 1)).ofLp, w]| = I)
    (hg : y ⬝ᵥ w = g) (hgpos : 0 < g) :
    ZLattice.covolume L = I * ‖WithLp.toLp 2 y‖ / g := by
  rw [covolume_eq_abs_det_mul_norm_div L b f w y h0 h1
    (by rw [hg]; exact ne_of_gt hgpos), hI, hg, abs_of_pos hgpos]

theorem abs_det_int_basis_eq_index
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (b : Basis ι ℤ L) :
    |(Matrix.of (fun i j => ((b i : ι → ℤ) j : ℝ))).det| =
      (L.toAddSubgroup.index : ℝ) := by
  have h : L.toAddSubgroup.index =
      (Matrix.of (fun i => (b i : ι → ℤ))).det.natAbs := by
    simpa only [Pi.basisFun_det_apply] using
      AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ ι) L.toAddSubgroup b
  rw [h, Nat.cast_natAbs, Int.cast_abs, Int.cast_det]
  rfl

theorem abs_det_sum_basis_eq_index
    (L : Submodule ℤ (Fin 3 → ℤ)) (b : Basis (Fin 2 ⊕ Unit) ℤ L) :
    |(Matrix.det ![(fun j => ((b (Sum.inl 0) : Fin 3 → ℤ) j : ℝ)),
      (fun j => ((b (Sum.inl 1) : Fin 3 → ℤ) j : ℝ)),
      (fun j => ((b (Sum.inr ()) : Fin 3 → ℤ) j : ℝ))])| =
        (L.toAddSubgroup.index : ℝ) := by
  let e : Fin 2 ⊕ Unit ≃ Fin 3 :=
    (Equiv.sumCongr (Equiv.refl (Fin 2)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv
  have h := abs_det_int_basis_eq_index L (b.reindex e)
  convert h using 1
  congr 2
  ext i j
  fin_cases i <;> simp [e, Basis.reindex_apply, finSumFinEquiv, Fin.addCases]

end Problem355.Lattice

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegralPlaneDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Lattice

open Module
open scoped Matrix

theorem abs_det_sum_basis_eq_one
    (b : Basis (Fin 2 ⊕ Unit) ℤ (Fin 3 → ℤ)) :
    |Matrix.det ![(fun j => (b (Sum.inl 0) j : ℝ)),
      (fun j => (b (Sum.inl 1) j : ℝ)),
      (fun j => (b (Sum.inr ()) j : ℝ))]| = 1 := by
  let bt : Basis (Fin 2 ⊕ Unit) ℤ (⊤ : Submodule ℤ (Fin 3 → ℤ)) :=
    b.map Submodule.topEquiv.symm
  simpa [bt] using abs_det_sum_basis_eq_index (⊤ : Submodule ℤ (Fin 3 → ℤ)) bt

theorem abs_det_primitive_kernel_basis_extension
    (f : (Fin 3 → ℤ) →ₗ[ℤ] ℤ) (u : Fin 3 → ℤ) (hu : f u = 1)
    (b : Basis (Fin 2) ℤ (LinearMap.ker f)) :
    |Matrix.det ![(fun j => ((b 0 : Fin 3 → ℤ) j : ℝ)),
      (fun j => ((b 1 : Fin 3 → ℤ) j : ℝ)), (fun j => (u j : ℝ))]| = 1 := by
  simpa only [LatticeSplit.extendKernelBasis_inl,
    LatticeSplit.extendKernelBasis_inr] using
    abs_det_sum_basis_eq_one (LatticeSplit.extendKernelBasis f u hu b)

end Problem355.Lattice

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ExactPlaneCovolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegralPlaneLattice

open Module
open scoped BigOperators Matrix

theorem lattice_covolume_of_equiv
    (y z : Fin 3 → ℤ) (hyz : ∑ i, y i * z i = 1)
    (e : integerPlane y ≃ₗ[ℤ] lattice y)
    (he : ∀ v, (((e v : lattice y) : plane y) :
      EuclideanSpace ℝ (Fin 3)) = castVec (v : Fin 3 → ℤ)) :
    ZLattice.covolume (lattice y) = ‖castVec y‖ := by
  let := isZLattice y z hyz
  let f : (Fin 3 → ℤ) →ₗ[ℤ] ℤ := integerDot y
  have hfz : f z = 1 := hyz
  have hf : f ≠ 0 := by
    intro h
    have hh := hfz
    rw [h] at hh
    norm_num at hh
  let bZ : Basis (Fin 2) ℤ f.ker :=
    Classical.choice (LatticeSplit.exists_plane_kernel_basis f hf)
  let b : Basis (Fin 2) ℤ (lattice y) := bZ.map e
  let emb := (plane y).subtypeₗᵢ
  have hb (i : Fin 2) : emb (b i) = castVec (bZ i : Fin 3 → ℤ) := by
    exact he (bZ i)
  have hdet : |Matrix.det ![(emb (b 0)).ofLp, (emb (b 1)).ofLp,
      (castVec z).ofLp]| = 1 := by
    rw [hb 0, hb 1]
    exact Lattice.abs_det_primitive_kernel_basis_extension f z hfz bZ
  have hzero (i : Fin 2) : (emb (b i)).ofLp ⬝ᵥ (castVec y).ofLp = 0 := by
    rw [dotProduct_comm]
    exact (b i : plane y).property
  have hheight : (castVec y).ofLp ⬝ᵥ (castVec z).ofLp = (1 : ℝ) := by
    change (∑ i, (y i : ℝ) * (z i : ℝ)) = 1
    exact_mod_cast hyz
  have h := Lattice.covolume_eq_index_mul_norm_div
    (lattice y) b emb (castVec z).ofLp (castVec y).ofLp
    1 1 (hzero 0) (hzero 1) hdet hheight (by norm_num)
  simpa only [one_mul, div_one, WithLp.toLp_ofLp] using h

theorem lattice_covolume (y z : Fin 3 → ℤ) (hyz : y ⬝ᵥ z = 1) :
    ZLattice.covolume (lattice y) = ‖castVec y‖ := by
  apply lattice_covolume_of_equiv y z hyz (kernelEquiv y)
  intro v
  rfl

end Problem355.IntegralPlaneLattice

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open MeasureTheory MeasureTheory.Measure Set
open scoped Pointwise ENNReal

namespace Problem355.LatticePacking

theorem card_mul_measure_le {G E : Type*} [AddGroup G]
    [MeasurableSpace G] [MeasurableSpace E] [AddAction G E]
    [MeasurableVAdd G E] (μ : Measure E) [VAddInvariantMeasure G E μ]
    {F T : Set E} (hF : IsAddFundamentalDomain G F μ)
    (A : Finset G) (hAT : ∀ a ∈ A, a +ᵥ F ⊆ T) :
    (A.card : ℝ≥0∞) * μ F ≤ μ T := by
  calc
    (A.card : ℝ≥0∞) * μ F = ∑ a ∈ A, μ (a +ᵥ F) := by
      simp [measure_vadd, nsmul_eq_mul]
    _ = μ (⋃ a ∈ A, a +ᵥ F) := by
      symm
      exact measure_biUnion_finset₀
        (fun a _ b _ hab => hF.aedisjoint hab)
        (fun a _ => hF.nullMeasurableSet.vadd a)
    _ ≤ μ T := measure_mono (iUnion_subset fun a => iUnion_subset (hAT a))

theorem card_mul_measure_le_closedBall {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    (L : AddSubgroup E) {F : Set E} (hF : IsAddFundamentalDomain L F μ)
    (A : Finset L) (c : E) (R D : ℝ)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
    (hFD : F ⊆ Metric.closedBall 0 D) :
    (A.card : ℝ≥0∞) * μ F ≤ μ (Metric.closedBall c (R + D)) := by
  apply card_mul_measure_le μ hF A
  intro a ha y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have ha' : ‖(a : E) - c‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hA a ha
  have hx' : ‖x‖ ≤ D := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hFD hx
  change dist ((a : E) + x) c ≤ R + D
  rw [dist_eq_norm, show (a : E) + x - c = ((a : E) - c) + x by abel]
  exact (norm_add_le _ _).trans (add_le_add ha' hx')

theorem fundamentalDomain_subset_closedBall {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (b : Module.Basis ι ℝ E) :
    ZSpan.fundamentalDomain b ⊆ Metric.closedBall 0 (∑ i, ‖b i‖) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  calc
    ‖x‖ = ‖∑ i, b.repr x i • b i‖ := congrArg norm (b.sum_repr x).symm
    _ ≤ ∑ i, ‖b.repr x i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖b i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hx i).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hx i).2.le

theorem plane_card_mul_area_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : Module.Basis (Fin 2) ℝ E)
    (A : Finset (Submodule.span ℤ (Set.range b)))
    (c : E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
    (hb : ∀ i, ‖b i‖ ≤ R) :
    (A.card : ℝ) * volume.real (ZSpan.fundamentalDomain b) ≤
      9 * Real.pi * R ^ 2 := by
  have hFD : ZSpan.fundamentalDomain b ⊆ Metric.closedBall 0 (2 * R) := by
    refine (fundamentalDomain_subset_closedBall b).trans (Metric.closedBall_subset_closedBall ?_)
    simpa [Fin.sum_univ_two, two_mul] using add_le_add (hb 0) (hb 1)
  have h := card_mul_measure_le_closedBall volume
    (Submodule.span ℤ (Set.range b)).toAddSubgroup
    (ZSpan.isAddFundamentalDomain' b volume) A c R (2 * R) hA hFD
  have hdim : Module.finrank ℝ E = 2 := by
    rw [Module.finrank_eq_card_basis b]
    simp
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hvol : volume (Metric.closedBall c (R + 2 * R)) =
      ENNReal.ofReal (R + 2 * R) ^ 2 * ENNReal.ofReal Real.pi := by
    simpa [hdim] using InnerProductSpace.volume_closedBall_of_dim_even
      (k := 1) (by simpa using hdim) c (R + 2 * R)
  rw [hvol] at h
  have h' := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ R + 2 * R),
    ENNReal.toReal_ofReal Real.pi_pos.le] at h'
  change (A.card : ℝ) * (volume (ZSpan.fundamentalDomain b)).toReal ≤ _
  nlinarith [h']

theorem card_le_relIndex_mul {E : Type*} [NormedAddCommGroup E]
    (H L : AddSubgroup E) [Finite (L ⧸ H.addSubgroupOf L)]
    (A : Finset L) (c : E) (R C : ℝ)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
    (hH : ∀ (B : Finset H) (d : E),
      (∀ b ∈ B, (b : E) ∈ Metric.closedBall d R) → (B.card : ℝ) ≤ C) :
    (A.card : ℝ) ≤ (H.relIndex L : ℝ) * C := by
  classical
  let Q := L ⧸ H.addSubgroupOf L
  let : Fintype Q := Fintype.ofFinite Q
  let f : L → Q := QuotientAddGroup.mk
  have hfiber (q : Q) : ((A.filter fun a => f a = q).card : ℝ) ≤ C := by
    let S := A.filter fun a => f a = q
    have hmem (a : L) (ha : a ∈ S) : (a - q.out : L) ∈ H.addSubgroupOf L := by
      apply QuotientAddGroup.eq_iff_sub_mem.mp
      exact (Finset.mem_filter.mp ha).2.trans (Quotient.out_eq q).symm
    let shift : {a // a ∈ S} → H := fun a =>
      ⟨(a.1 : E) - (q.out : E), hmem a.1 a.2⟩
    have hinj : Function.Injective shift := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      simpa only [shift, sub_left_inj] using (congrArg Subtype.val hab)
    let B := S.attach.image shift
    have hcard : B.card = S.card :=
      (Finset.card_image_of_injective _ hinj).trans Finset.card_attach
    rw [← hcard]
    apply hH B (c - (q.out : E))
    intro b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    change dist ((a.1 : E) - (q.out : E)) (c - (q.out : E)) ≤ R
    simpa only [dist_sub_right, Metric.mem_closedBall] using hA a.1 (Finset.mem_filter.mp a.2).1
  have hdecomp : A.card = ∑ q : Q, (A.filter fun a => f a = q).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  calc
    (A.card : ℝ) = ∑ q : Q, ((A.filter fun a => f a = q).card : ℝ) := by
      rw [hdecomp, Nat.cast_sum]
    _ ≤ ∑ _q : Q, C := Finset.sum_le_sum (fun q _ => hfiber q)
    _ = (H.relIndex L : ℝ) * C := by
      simp [AddSubgroup.relIndex, AddSubgroup.index, Q, Nat.card_eq_fintype_card,
        nsmul_eq_mul]

theorem plane_card_le_of_short_basis {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis (Fin 2) ℝ E)
    (hbL : ∀ i, b i ∈ L)
    (A : Finset L) (c : E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
    (hb : ∀ i, ‖b i‖ ≤ R) :
    (A.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
  let H := Submodule.span ℤ (Set.range b)
  have hHL : H ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hbL i
  have hHpos : 0 < ZLattice.covolume H := ZLattice.covolume_pos H volume
  have hLpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  have hratio := ZLattice.covolume_div_covolume_eq_relIndex' H L hHL
  have hindex : H.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero] at hratio
    exact (ne_of_gt (div_pos hHpos hLpos)) hratio
  let : Finite (L.toAddSubgroup ⧸ H.toAddSubgroup.addSubgroupOf L.toAddSubgroup) :=
    AddSubgroup.index_ne_zero_iff_finite.mp hindex
  have hbound : (A.card : ℝ) ≤
      (H.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) *
        (9 * Real.pi * R ^ 2 / ZLattice.covolume H) := by
    apply card_le_relIndex_mul H.toAddSubgroup L.toAddSubgroup A c R _ hA
    intro B d hB
    apply (le_div_iff₀ hHpos).mpr
    have h := plane_card_mul_area_le b B d R hR hB hb
    have hvol : ZLattice.covolume H = volume.real (ZSpan.fundamentalDomain b) :=
      ZLattice.covolume_eq_measure_fundamentalDomain H volume
        (ZSpan.isAddFundamentalDomain b volume)
    rwa [hvol]
  exact calc
    (A.card : ℝ) ≤ (H.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) *
        (9 * Real.pi * R ^ 2 / ZLattice.covolume H) := hbound
    _ = 9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
      rw [← hratio]
      field_simp

end Problem355.LatticePacking

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimitiveLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PrimitiveLine

theorem card_integral_multiples_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (hv : v ≠ 0) (R : ℝ) (hR : 0 ≤ R) (S : Finset E)
    (hline : ∀ p ∈ S, ∃ z : ℤ, p = (z : ℝ) • v)
    (hball : ∀ p ∈ S, ‖p‖ ≤ R) :
    (S.card : ℝ) ≤ 1 + 2 * R / ‖v‖ := by
  classical
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let T : ℝ := R / ‖v‖
  let Q : Finset ℤ := Finset.Icc (-⌊T⌋) ⌊T⌋
  have hT : 0 ≤ T := div_nonneg hR hvnorm.le
  have hf : (0 : ℤ) ≤ ⌊T⌋ := Int.le_floor.mpr (by simpa using hT)
  have hsubset : S ⊆ Q.image (fun z : ℤ => (z : ℝ) • v) := by
    intro p hp
    obtain ⟨z, hz⟩ := hline p hp
    have hzabs : |(z : ℝ)| ≤ T := by
      apply (le_div_iff₀ hvnorm).mpr
      simpa only [hz, norm_smul, Real.norm_eq_abs] using hball p hp
    have hzu : z ≤ ⌊T⌋ := Int.le_floor.mpr ((le_abs_self _).trans hzabs)
    have hzl : -z ≤ ⌊T⌋ := Int.le_floor.mpr (by
      simpa only [Int.cast_neg] using (neg_le_abs (z : ℝ)).trans hzabs)
    apply Finset.mem_image.mpr
    refine ⟨z, ?_, hz.symm⟩
    change z ∈ Finset.Icc (-⌊T⌋) ⌊T⌋
    simp only [Finset.mem_Icc]
    omega
  have hcard : S.card ≤ Q.card :=
    (Finset.card_le_card hsubset).trans Finset.card_image_le
  have hnat : 0 ≤ ⌊T⌋ + 1 - (-⌊T⌋) := by omega
  calc
    (S.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hcard
    _ = 2 * (⌊T⌋ : ℝ) + 1 := by
      dsimp [Q]
      rw [Int.card_Icc]
      have heq := Int.toNat_of_nonneg hnat
      have heqR : (((⌊T⌋ + 1 - (-⌊T⌋)).toNat : ℕ) : ℝ) =
          ((⌊T⌋ + 1 - (-⌊T⌋) : ℤ) : ℝ) := by exact_mod_cast heq
      rw [heqR]
      push_cast
      ring
    _ ≤ 1 + 2 * T := by linarith [Int.floor_le T]
    _ = 1 + 2 * R / ‖v‖ := by dsimp [T]; ring

theorem integer_multiple_of_shortest {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : AddSubgroup E) {v w : E} (hv : v ≠ 0) (hvL : v ∈ L)
    (hshort : ∀ u ∈ L, u ≠ 0 → ‖v‖ ≤ ‖u‖)
    (hwL : w ∈ L) (hline : ∃ r : ℝ, w = r • v) :
    ∃ z : ℤ, w = (z : ℝ) • v := by
  obtain ⟨r, hr⟩ := hline
  let u : E := (r - (⌊r⌋ : ℝ)) • v
  have humem : u ∈ L := by
    change (r - (⌊r⌋ : ℝ)) • v ∈ L
    rw [sub_smul, ← hr, Int.cast_smul_eq_zsmul]
    exact L.sub_mem hwL (L.zsmul_mem hvL _)
  have hnonneg : 0 ≤ r - (⌊r⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le r)
  have hlt : r - (⌊r⌋ : ℝ) < 1 := by linarith [Int.lt_floor_add_one r]
  have hunorm : ‖u‖ < ‖v‖ := by
    change ‖(r - (⌊r⌋ : ℝ)) • v‖ < ‖v‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    nlinarith [norm_pos_iff.mpr hv]
  have hu : u = 0 := by
    by_contra hne
    exact (not_lt_of_ge (hshort u humem hne)) hunorm
  refine ⟨⌊r⌋, sub_eq_zero.mp ?_⟩
  calc
    w - (⌊r⌋ : ℝ) • v = u := by rw [hr, ← sub_smul]
    _ = 0 := hu

end Problem355.PrimitiveLine

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticeLowerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open MeasureTheory Module Submodule
open scoped BigOperators

namespace Problem355.LatticeLowerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ}

theorem volumeReal_fundamentalDomain_orthonormal (o : OrthonormalBasis (Fin n) ℝ E) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [measureReal_def,
    measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
  change (volume (parallelepiped o)).toReal = 1
  rw [o.volume_parallelepiped]
  simp

theorem covolume_span_basis_le_prod_norm (b : Basis (Fin n) ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ≤ ∏ i, ‖b i‖ := by
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  have hvol : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 :=
    volumeReal_fundamentalDomain_orthonormal o
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis, hvol, mul_one]
  change |(InnerProductSpace.gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b).toBasis.det b| ≤ _
  rw [InnerProductSpace.gramSchmidtOrthonormalBasis_det, Finset.abs_prod]
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro i _
  calc
    |@inner ℝ E _ (o i) (b i)| ≤ ‖o i‖ * ‖b i‖ := abs_real_inner_le_norm _ _
    _ = ‖b i‖ := by rw [o.norm_eq_one]; ring

theorem covolume_mono_reverse (L₁ L₂ : Submodule ℤ E)
    [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (hL : L₁ ≤ L₂) :
    ZLattice.covolume L₂ ≤ ZLattice.covolume L₁ := by
  have hratio := ZLattice.covolume_div_covolume_eq_relIndex' L₁ L₂ hL
  have hpos : 0 < (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    rw [← hratio]
    exact div_pos (ZLattice.covolume_pos L₁) (ZLattice.covolume_pos L₂)
  have hnat : 1 ≤ L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
    have : 0 < L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by exact_mod_cast hpos
    omega
  have hone : (1 : ℝ) ≤ ZLattice.covolume L₁ / ZLattice.covolume L₂ := by
    rw [hratio]
    exact_mod_cast hnat
  have hh := (le_div_iff₀ (ZLattice.covolume_pos L₂)).mp hone
  simpa only [one_mul] using hh

theorem covolume_le_prod_norm (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin n) ℝ E) (hb : ∀ i, b i ∈ L) :
    ZLattice.covolume L ≤ ∏ i, ‖b i‖ := by
  have hspan : Submodule.span ℤ (Set.range b) ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i
  exact (covolume_mono_reverse _ _ hspan).trans (covolume_span_basis_le_prod_norm b)

theorem relIndex_span_basis_le (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin n) ℝ E) (hb : ∀ i, b i ∈ L) :
    ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≤
      (∏ i, ‖b i‖) / ZLattice.covolume L := by
  have hspan : Submodule.span ℤ (Set.range b) ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i
  rw [← ZLattice.covolume_div_covolume_eq_relIndex' _ _ hspan]
  exact div_le_div_of_nonneg_right (covolume_span_basis_le_prod_norm b)
    (ZLattice.covolume_pos L).le

end Problem355.LatticeLowerProduct

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SuccessiveBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.SuccessiveBox

open MeasureTheory Set
open scoped BigOperators

theorem box_volume_le {ι : Type*} [Fintype ι]
    (L : AddSubgroup (ι → ℝ)) [Countable L] (F : Set (ι → ℝ))
    (hF : IsAddFundamentalDomain L F volume) (w : ι → ℝ)
    (hempty : ∀ x : L, (∀ i, |(x : ι → ℝ) i| < w i) → x = 0) :
    (∏ i, ENNReal.ofReal (2 * w i)) ≤ volume F * 2 ^ Fintype.card ι := by
  let S : Set (ι → ℝ) := Set.pi Set.univ (fun i => Set.Ioo (-w i) (w i))
  have hsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx i hi
    have hxi := hx i hi
    change -w i < -x i ∧ -x i < w i
    constructor <;> linarith [hxi.1, hxi.2]
  have hconv : Convex ℝ S := convex_pi (by intro i hi; exact convex_Ioo _ _)
  have hvol : volume S ≤ volume F * 2 ^ Module.finrank ℝ (ι → ℝ) := by
    by_contra h
    obtain ⟨x, hx, hxS⟩ :=
      exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
        hF hsymm hconv (lt_of_not_ge h)
    apply hx
    apply hempty x
    intro i
    exact abs_lt.mpr (hxS i (Set.mem_univ i))
  simpa [S, Real.volume_pi_Ioo, sub_neg_eq_add, ← two_mul,
    Module.finrank_pi] using hvol

theorem width_product_le {ι : Type*} [Fintype ι]
    (L : AddSubgroup (ι → ℝ)) [Countable L] (F : Set (ι → ℝ))
    (hF : IsAddFundamentalDomain L F volume) (hfinite : volume F ≠ ⊤)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hempty : ∀ x : L, (∀ i, |(x : ι → ℝ) i| < w i) → x = 0) :
    (∏ i, w i) ≤ volume.real F := by
  have he := box_volume_le L F hF w hempty
  have ht : volume F * 2 ^ Fintype.card ι ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono ht he
  have hreal (i : ι) : (ENNReal.ofReal (2 * w i)).toReal = 2 * w i :=
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hw i))
  simp only [ENNReal.toReal_prod, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, hreal] at hr
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hr
  have hp : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  change (∏ i, w i) ≤ (volume F).toReal
  nlinarith

theorem successive_box_empty {n : ℕ} (hn : 0 < n)
    (L : AddSubgroup (Fin n → ℝ)) (ℓ : Fin n → ℝ)
    (hpositive : ∀ i, 0 < ℓ i) (hmono : Monotone ℓ)
    (hlength : ∀ (x : L) (j : Fin n), (x : Fin n → ℝ) j ≠ 0 →
      (∀ i, j < i → (x : Fin n → ℝ) i = 0) →
      ℓ j ^ 2 ≤ ∑ i, (x : Fin n → ℝ) i ^ 2) :
    ∀ x : L, (∀ i, |(x : Fin n → ℝ) i| < ℓ i / Real.sqrt n) → x = 0 := by
  classical
  intro x hx
  by_contra hx0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  let S : Finset (Fin n) := Finset.univ.filter (fun i => (x : Fin n → ℝ) i ≠ 0)
  have hS : S.Nonempty := by
    by_contra hs
    apply hx0
    apply Subtype.ext
    funext i
    have hi : i ∉ S := by simp [Finset.not_nonempty_iff_eq_empty.mp hs]
    simpa [S] using hi
  let j := S.max' hS
  have hj : (x : Fin n → ℝ) j ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have hlast : ∀ i, j < i → (x : Fin n → ℝ) i = 0 := by
    intro i hji
    by_contra hi
    have himem : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hij : i ≤ j := S.le_max' i himem
    exact (not_lt_of_ge hij) hji
  have hb (i : Fin n) : |(x : Fin n → ℝ) i| < ℓ j / Real.sqrt n := by
    by_cases hij : i ≤ j
    · exact lt_of_lt_of_le (hx i) ((div_le_div_iff_of_pos_right hc).mpr (hmono hij))
    · rw [hlast i (lt_of_not_ge hij), abs_zero]
      exact div_pos (hpositive j) hc
  have hsq (i : Fin n) : (x : Fin n → ℝ) i ^ 2 < (ℓ j / Real.sqrt n) ^ 2 := by
    apply sq_lt_sq.mpr
    rw [abs_of_pos (div_pos (hpositive j) hc)]
    exact hb i
  have hsum := Finset.sum_lt_sum_of_nonempty
    (s := Finset.univ) (⟨j, Finset.mem_univ j⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
    (fun i _ => hsq i)
  have heq : (n : ℝ) * (ℓ j / Real.sqrt n) ^ 2 = ℓ j ^ 2 := by
    rw [div_pow, Real.sq_sqrt hnR.le]
    field_simp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [heq] at hsum
  exact (not_lt_of_ge (hlength x j hj hlast)) hsum

theorem successive_product_le {n : ℕ} (hn : 0 < n)
    (L : AddSubgroup (Fin n → ℝ)) [Countable L] (F : Set (Fin n → ℝ))
    (hF : IsAddFundamentalDomain L F volume) (hfinite : volume F ≠ ⊤)
    (ℓ : Fin n → ℝ) (hpositive : ∀ i, 0 < ℓ i) (hmono : Monotone ℓ)
    (hlength : ∀ (x : L) (j : Fin n), (x : Fin n → ℝ) j ≠ 0 →
      (∀ i, j < i → (x : Fin n → ℝ) i = 0) →
      ℓ j ^ 2 ≤ ∑ i, (x : Fin n → ℝ) i ^ 2) :
    (∏ i, ℓ i) ≤ Real.sqrt n ^ n * volume.real F := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hw (i : Fin n) : 0 ≤ ℓ i / Real.sqrt n := (div_pos (hpositive i) hc).le
  have hprod := width_product_le L F hF hfinite
    (fun i => ℓ i / Real.sqrt n) hw (successive_box_empty hn L ℓ hpositive hmono hlength)
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hpow : 0 < Real.sqrt n ^ n := pow_pos hc n
  exact (div_le_iff₀ hpow).mp hprod |>.trans_eq (mul_comm _ _)

end Problem355.SuccessiveBox

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SuccessiveTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.SuccessiveBox

open MeasureTheory Set Module InnerProductSpace
open scoped BigOperators

theorem gramSchmidt_coordinate_zero_of_mem_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hdim : finrank ℝ E = Fintype.card (Fin n))
    (v : Fin n → E) (j : Fin n) {x : E}
    (hx : x ∈ Submodule.span ℝ (v '' Set.Iio j)) :
    (gramSchmidtOrthonormalBasis hdim v).repr x j = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact gramSchmidtOrthonormalBasis_inv_triangular' hdim v hi
  | zero => simp
  | add x y hx hy hx' hy' => simp [map_add, hx', hy']
  | smul a x hx hx' => simp [map_smul, hx']

theorem successive_norm_product_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (hn : 0 < n) (hdim : finrank ℝ E = Fintype.card (Fin n))
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : Fin n → E) (hpositive : ∀ i, 0 < ‖v i‖)
    (hmono : Monotone (fun i => ‖v i‖))
    (hmin : ∀ j (x : E), x ∈ L → x ∉ Submodule.span ℝ (v '' Set.Iio j) →
      ‖v j‖ ≤ ‖x‖) :
    (∏ i, ‖v i‖) ≤ Real.sqrt n ^ n * ZLattice.covolume L := by
  classical
  let b := gramSchmidtOrthonormalBasis hdim v
  let f : (Fin n → ℝ) ≃L[ℝ] E :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.trans b.repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f :=
    b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp (Fin n))
  let L' := ZLattice.comap ℝ L f.toLinearMap
  let b' := IsZLattice.basis L'
  let : Countable L'.toAddSubgroup := b'.equivFun.injective.countable
  let F := ZSpan.fundamentalDomain (b'.ofZLatticeBasis ℝ)
  have hF : IsAddFundamentalDomain L'.toAddSubgroup F volume :=
    ZLattice.isAddFundamentalDomain b' volume
  have hfinite : volume F ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (b'.ofZLatticeBasis ℝ)).measure_lt_top.ne
  have hlen : ∀ (x : L'.toAddSubgroup) (j : Fin n), (x : Fin n → ℝ) j ≠ 0 →
      (∀ i, j < i → (x : Fin n → ℝ) i = 0) →
      ‖v j‖ ^ 2 ≤ ∑ i, (x : Fin n → ℝ) i ^ 2 := by
    intro x j hxj _
    have hxmem : f (x : Fin n → ℝ) ∈ L := x.property
    have hcoord : b.repr (f (x : Fin n → ℝ)) j = (x : Fin n → ℝ) j := by
      simp [f]
    have hout : f (x : Fin n → ℝ) ∉ Submodule.span ℝ (v '' Set.Iio j) := by
      intro h
      have hz := gramSchmidt_coordinate_zero_of_mem_span hdim v j h
      change b.repr (f (x : Fin n → ℝ)) j = 0 at hz
      exact hxj (hcoord.symm.trans hz)
    have hle := hmin j _ hxmem hout
    have hnorm : ‖f (x : Fin n → ℝ)‖ ^ 2 = ∑ i, (x : Fin n → ℝ) i ^ 2 := by
      calc
        ‖f (x : Fin n → ℝ)‖ ^ 2 = ‖b.repr (f (x : Fin n → ℝ))‖ ^ 2 := by simp
        _ = ∑ i, ‖b.repr (f (x : Fin n → ℝ)) i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
        _ = ∑ i, (x : Fin n → ℝ) i ^ 2 := by simp [f, Real.norm_eq_abs, sq_abs]
    rw [← hnorm]
    exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hle
  have hresult := successive_product_le hn L'.toAddSubgroup F hF hfinite
    (fun i => ‖v i‖) hpositive hmono hlen
  have hcov : volume.real F = ZLattice.covolume L := by
    rw [← ZLattice.covolume_eq_measure_fundamentalDomain L' volume
      (ZLattice.isAddFundamentalDomain b' volume)]
    exact ZLattice.covolume_comap L volume volume hf
  rwa [hcov] at hresult

end Problem355.SuccessiveBox

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SuccessiveVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.SuccessiveVectors

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

variable [NormedSpace ℝ E]

omit [ProperSpace E] in

theorem IsSuccessive.monotone_norm {L : Submodule ℤ E} {n : ℕ} {v : Fin n → E}
    (hv : IsSuccessive L v) : Monotone (fun i => ‖v i‖) := by
  intro i j hij
  apply hv.minimal i (v j) (hv.mem_lattice j)
  exact hv.independent.notMem_span_image (not_lt_of_ge hij)

end Problem355.SuccessiveVectors

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SuccessiveEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open Module Submodule
open scoped BigOperators

namespace Problem355.SuccessiveEstimates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem monotone_norm_of_minimizing_basis (L : Submodule ℤ E)
    (b : Basis (Fin n) ℝ E) (hb : ∀ i, b i ∈ L)
    (hmin : ∀ j (x : E), x ∈ L → x ∉ Submodule.span ℝ (b '' Set.Iio j) →
      ‖b j‖ ≤ ‖x‖) : Monotone (fun i => ‖b i‖) := by
  intro i j hij
  apply hmin i (b j) (hb j)
  rw [b.self_mem_span_image]
  exact not_lt_of_ge hij

theorem successive_basis_estimates (hn : 0 < n) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin n) ℝ E) (hb : ∀ i, b i ∈ L)
    (hmin : ∀ j (x : E), x ∈ L → x ∉ Submodule.span ℝ (b '' Set.Iio j) →
      ‖b j‖ ≤ ‖x‖) :
    ZLattice.covolume L ≤ ∏ i, ‖b i‖ ∧
      (∏ i, ‖b i‖) ≤ Real.sqrt n ^ n * ZLattice.covolume L ∧
      ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≤
        Real.sqrt n ^ n := by
  have hpositive : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.mpr (b.ne_zero i)
  have hupper := SuccessiveBox.successive_norm_product_le hn
    (Module.finrank_eq_card_basis b) L b hpositive
    (monotone_norm_of_minimizing_basis L b hb hmin) hmin
  refine ⟨LatticeLowerProduct.covolume_le_prod_norm L b hb, hupper, ?_⟩
  calc
    ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≤
        (∏ i, ‖b i‖) / ZLattice.covolume L :=
      LatticeLowerProduct.relIndex_span_basis_le L b hb
    _ ≤ Real.sqrt n ^ n := (div_le_iff₀ (ZLattice.covolume_pos L)).mpr hupper

theorem relIndex_le_five (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 3) ℝ E) (hb : ∀ i, b i ∈ L)
    (hmin : ∀ j (x : E), x ∈ L → x ∉ Submodule.span ℝ (b '' Set.Iio j) →
      ‖b j‖ ≤ ‖x‖) :
    (Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≤ 5 := by
  have hbound := (successive_basis_estimates (by norm_num : 0 < 3) L b hb hmin).2.2
  have hsqrt : Real.sqrt (3 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hcub : Real.sqrt (3 : ℝ) ^ 3 < 6 := by
    calc
      Real.sqrt (3 : ℝ) ^ 3 = 3 * Real.sqrt (3 : ℝ) := by
        rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      _ < 6 := by linarith
  have hlt : ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) < 6 :=
    hbound.trans_lt hcub
  have hint : (Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup < 6 := by
    exact_mod_cast hlt
  omega

end Problem355.SuccessiveEstimates

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PlaneCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PlaneCount

open MeasureTheory

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem plane_lattice_count
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis (Fin 2) ℝ E) (hbL : ∀ i, b i ∈ L)
    (hfirst : ∀ u ∈ L, u ≠ 0 → ‖b 0‖ ≤ ‖u‖)
    (hsecond : ∀ u ∈ L, u ∉ Submodule.span ℝ {b 0} → ‖b 1‖ ≤ ‖u‖)
    (A : Finset L) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, ‖(a : E)‖ ≤ R) :
    (‖b 1‖ ≤ R →
      (A.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume L) ∧
    (R < ‖b 1‖ →
      (∀ a ∈ A, ∃ z : ℤ, (a : E) = (z : ℝ) • b 0) ∧
      (A.card : ℝ) ≤ 1 + 2 * R / ‖b 0‖) := by
  classical
  have hv : b 0 ≠ 0 := b.ne_zero 0
  have horder : ‖b 0‖ ≤ ‖b 1‖ := hfirst (b 1) (hbL 1) (b.ne_zero 1)
  have hshort : ∀ u ∈ L.toAddSubgroup, u ≠ 0 → ‖b 0‖ ≤ ‖u‖ := hfirst
  constructor
  · intro hlarge
    apply LatticePacking.plane_card_le_of_short_basis L b hbL A 0 R hR
    · intro a ha
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hA a ha
    · intro i
      fin_cases i
      · exact horder.trans hlarge
      · exact hlarge
  · intro hsmall
    have hline (u : E) (hu : u ∈ L) (hnorm : ‖u‖ ≤ R) :
        ∃ r : ℝ, u = r • b 0 := by
      have hspan : u ∈ Submodule.span ℝ {b 0} := by
        by_contra hout
        exact (not_lt_of_ge (hsecond u hu hout)) (hnorm.trans_lt hsmall)
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hspan
      exact ⟨r, hr.symm⟩
    have hinteger (a : L) (ha : a ∈ A) :
        ∃ z : ℤ, (a : E) = (z : ℝ) • b 0 :=
      PrimitiveLine.integer_multiple_of_shortest L.toAddSubgroup hv (hbL 0)
        hshort a.property (hline a a.property (hA a ha))
    refine ⟨hinteger, ?_⟩
    let e : L ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
    let S : Finset E := A.map e
    have hSmult : ∀ p ∈ S, ∃ z : ℤ, p = (z : ℝ) • b 0 := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hp
      exact hinteger a ha
    have hSnorm : ∀ p ∈ S, ‖p‖ ≤ R := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hp
      exact hA a ha
    have hcount := PrimitiveLine.card_integral_multiples_le
      (b 0) hv R hR S hSmult hSnorm
    simpa only [S, Finset.card_map] using hcount

end Problem355.PlaneCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimitiveVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimitiveVector

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem exists_factorization (x : ι → ℤ) (hx : x ≠ 0) :
    ∃ (g : ℤ) (y z : ι → ℤ),
      0 < g ∧ (∀ i, x i = g * y i) ∧ (∑ i, y i * z i = 1) ∧
      (∀ i, |y i| ≤ |x i|) ∧ (∀ i, y i = 0 ↔ x i = 0) := by
  classical
  have hxi : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hxi
  let g : ℤ := Finset.univ.gcd x
  have hg_nonneg : 0 ≤ g :=
    Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)
  have hg_ne : g ≠ 0 := by
    intro hg
    exact hi ((Finset.gcd_eq_zero_iff.mp hg) i (Finset.mem_univ i))
  have hg_pos : 0 < g := lt_of_le_of_ne hg_nonneg (Ne.symm hg_ne)
  obtain ⟨y, hxy, hy⟩ := Finset.extract_gcd x
    (show (Finset.univ : Finset ι).Nonempty from ⟨i, Finset.mem_univ i⟩)
  have hfactor : ∀ i, x i = g * y i := fun i => hxy i (Finset.mem_univ i)
  obtain ⟨z, hz⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset ι) y
  have hbezout : ∑ i, y i * z i = 1 := by
    simpa only [hy] using hz.symm
  refine ⟨g, y, z, hg_pos, hfactor, hbezout, ?_, ?_⟩
  · intro j
    rw [hfactor j, abs_mul, abs_of_pos hg_pos]
    have hg_one : 1 ≤ g := hg_pos
    nlinarith [abs_nonneg (y j)]
  · intro j
    rw [hfactor j]
    simp [hg_ne]

theorem dot_eq_zero_of_factor {g : ℤ} (hg : g ≠ 0)
    {x y : ι → ℤ} (hxy : ∀ i, x i = g * y i)
    (a : ι → ℤ) (ha : ∑ i, a i * x i = 0) :
    ∑ i, a i * y i = 0 := by
  have hmul : g * (∑ i, a i * y i) = 0 := by
    calc
      _ = ∑ i, a i * x i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hxy i]
        ring
      _ = 0 := ha
  exact (mul_eq_zero.mp hmul).resolve_left hg

theorem exists_factorization_mem_ker {κ : Type*}
    (A : Matrix κ ι ℤ) (x : ι → ℤ) (hx : x ≠ 0)
    (hAx : A.mulVec x = 0) :
    ∃ (g : ℤ) (y z : ι → ℤ),
      0 < g ∧ (∀ i, x i = g * y i) ∧ (∑ i, y i * z i = 1) ∧
      (∀ i, |y i| ≤ |x i|) ∧ (∀ i, y i = 0 ↔ x i = 0) ∧
      A.mulVec y = 0 := by
  obtain ⟨g, y, z, hg, hxy, hyz, hbound, hzero⟩ := exists_factorization x hx
  refine ⟨g, y, z, hg, hxy, hyz, hbound, hzero, ?_⟩
  funext k
  apply dot_eq_zero_of_factor hg.ne' hxy (A k)
  exact congrFun hAx k

end Problem355.PrimitiveVector

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ShortestIntegralVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.IntegralMinima

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma norm_sq_eq (x : ι → ℤ) :
    ‖toEuclidean x‖ ^ 2 = (normSq x : ℝ) := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [toEuclidean, PiLp.toLp_apply, normSq, Nat.cast_sum, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro i _
  have habs : ((x i).natAbs : ℝ) = |(x i : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (x i))
  rw [habs, sq_abs]

theorem one_le_norm {x : ι → ℤ} (hx : x ≠ 0) :
    1 ≤ ‖toEuclidean x‖ := by
  classical
  have hxi : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hxi
  have hi_pos : 0 < (x i).natAbs := Int.natAbs_pos.mpr hi
  have hsq : 1 ≤ (x i).natAbs ^ 2 := Nat.pow_pos hi_pos
  have hsum : (x i).natAbs ^ 2 ≤ normSq x := by
    exact Finset.single_le_sum (f := fun j => (x j).natAbs ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hnormSq : (1 : ℝ) ≤ normSq x := by exact_mod_cast hsq.trans hsum
  have hnorm := norm_sq_eq x
  nlinarith [norm_nonneg (toEuclidean x)]

theorem shortest_kernel_has_bezout {κ : Type*}
    (A : Matrix κ ι ℤ) (x : ι → ℤ) (hx : x ≠ 0)
    (hAx : A.mulVec x = 0)
    (hmin : ∀ y : ι → ℤ, y ≠ 0 → A.mulVec y = 0 →
      ‖toEuclidean x‖ ≤ ‖toEuclidean y‖) :
    ∃ z : ι → ℤ, ∑ i, x i * z i = 1 := by
  obtain ⟨g, y, z, hg, hxy, hyz, _, hzero, hAy⟩ :=
    PrimitiveVector.exists_factorization_mem_ker A x hx hAx
  have hyne : y ≠ 0 := by
    intro hy
    apply hx
    funext i
    rw [hxy i]
    simp [hy]
  have heq : toEuclidean x = (g : ℝ) • toEuclidean y := by
    ext i
    simp only [toEuclidean, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hxy i, Int.cast_mul]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hnorm := hmin y hyne hAy
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hgR] at hnorm
  have hypos : 0 < ‖toEuclidean y‖ := lt_of_lt_of_le zero_lt_one (one_le_norm hyne)
  have hgleR : (g : ℝ) ≤ 1 := by nlinarith
  have hgle : g ≤ 1 := by exact_mod_cast hgleR
  have hgone : g = 1 := by omega
  refine ⟨z, ?_⟩
  simpa only [hxy, hgone, one_mul] using hyz

end Problem355.IntegralMinima

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerPlaneEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerPlaneEstimates

open Module Matrix IntegralPlaneLattice

lemma norm_liftFinset_le (y : Vec) (S : Finset Vec)
    (hS : ∀ v ∈ S, y ⬝ᵥ v = 0) (R : ℝ)
    (hR : ∀ v ∈ S, ‖LatticeBox.realVector v‖ ≤ R) :
    ∀ a ∈ liftFinset y S hS, ‖(a : plane y)‖ ≤ R := by
  intro a ha
  obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp ha
  exact hR v v.property

lemma one_le_norm_of_int_ne_zero (v : Vec) (hv : v ≠ 0) :
    1 ≤ ‖LatticeBox.realVector v‖ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have habs : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
  have hreal : (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast habs
  exact hreal.trans (LatticeBox.abs_coord_le_norm v i)

lemma one_le_norm_of_lattice_ne_zero (y : Vec) (v : plane y)
    (hv : v ∈ lattice y) (hne : v ≠ 0) : 1 ≤ ‖v‖ := by
  obtain ⟨w, hw⟩ := kernelMap_surjective y ⟨v, hv⟩
  have hcast : castVec (w : Vec) = (v : Ambient) :=
    congrArg (fun a : lattice y => ((a : plane y) : Ambient)) hw
  have hwne : (w : Vec) ≠ 0 := by
    intro hzero
    apply hne
    apply Subtype.ext
    rw [← hcast, hzero]
    ext i
    simp [castVec]
  have hn := one_le_norm_of_int_ne_zero w hwne
  change 1 ≤ ‖(v : Ambient)‖
  rw [← hcast]
  exact hn

lemma successiveBasis_spec (y z : Vec) (hz : y ⬝ᵥ z = 1) :
    (∀ i, successiveBasis y z hz i ∈ lattice y) ∧
    (∀ v ∈ lattice y, v ≠ 0 → ‖successiveBasis y z hz 0‖ ≤ ‖v‖) ∧
    (∀ v ∈ lattice y, v ∉ Submodule.span ℝ {successiveBasis y z hz 0} →
      ‖successiveBasis y z hz 1‖ ≤ ‖v‖) := by
  let := isZLattice y z hz
  exact Classical.choose_spec (PlaneCount.exists_successive_plane_basis (lattice y)
    (plane_finrank y z hz))

lemma one_le_first (y z : Vec) (hz : y ⬝ᵥ z = 1) : 1 ≤ first y z hz :=
  one_le_norm_of_lattice_ne_zero y _ ((successiveBasis_spec y z hz).1 0)
    (by exact (successiveBasis y z hz).ne_zero 0)

lemma first_le_second (y z : Vec) (hz : y ⬝ᵥ z = 1) :
    first y z hz ≤ second y z hz :=
  (successiveBasis_spec y z hz).2.1 _ ((successiveBasis_spec y z hz).1 1)
    ((successiveBasis y z hz).ne_zero 1)

lemma fromLattice_dot (y : Vec) (v : lattice y) : y ⬝ᵥ fromLattice y v = 0 :=
  ((kernelEquiv y).symm v).property

lemma cast_fromLattice (y : Vec) (v : lattice y) :
    castVec (fromLattice y v) = ((v : plane y) : Ambient) := by
  exact congrArg (fun a : lattice y => ((a : plane y) : Ambient))
    ((kernelEquiv y).apply_symm_apply v)

lemma toLattice_ne_zero (y v : Vec) (hv : y ⬝ᵥ v = 0) (hne : v ≠ 0) :
    (toLattice y v hv : plane y) ≠ 0 := by
  intro h
  apply hne
  have he : toLattice y v hv = toLattice y 0 (by simp) := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [toLattice_coe, castVec_zero, Submodule.coe_zero] using congrArg Subtype.val h
  exact toLattice_injective y v 0 hv (by simp) he

lemma first_le_norm (y z : Vec) (hz : y ⬝ᵥ z = 1)
    (v : Vec) (hv : y ⬝ᵥ v = 0) (hne : v ≠ 0) :
    first y z hz ≤ ‖LatticeBox.realVector v‖ := by
  have h := (successiveBasis_spec y z hz).2.1
    (toLattice y v hv : plane y) (toLattice y v hv).property
    (toLattice_ne_zero y v hv hne)
  rw [norm_toLattice] at h
  exact h

theorem exists_shortest_integer (y z : Vec) (hz : y ⬝ᵥ z = 1) :
    ∃ v : Vec, v ≠ 0 ∧ y ⬝ᵥ v = 0 ∧
      ‖LatticeBox.realVector v‖ = first y z hz := by
  let a : lattice y := ⟨successiveBasis y z hz 0, (successiveBasis_spec y z hz).1 0⟩
  refine ⟨fromLattice y a, ?_, fromLattice_dot y a, ?_⟩
  · intro hzero
    have hcast := cast_fromLattice y a
    rw [hzero] at hcast
    have hb : successiveBasis y z hz 0 = 0 := by
      apply Subtype.ext
      simpa only [a, castVec_zero, Submodule.coe_zero] using hcast.symm
    exact (successiveBasis y z hz).ne_zero 0 hb
  · change ‖castVec (fromLattice y a)‖ = ‖successiveBasis y z hz 0‖
    rw [cast_fromLattice]
    rfl

theorem plane_counts (y z : Vec) (hz : y ⬝ᵥ z = 1)
    (S : Finset Vec) (hS : ∀ v ∈ S, y ⬝ᵥ v = 0)
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ v ∈ S, ‖LatticeBox.realVector v‖ ≤ R) :
    (second y z hz ≤ R →
      (S.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume (lattice y)) ∧
    (R < second y z hz → (S.card : ℝ) ≤ 1 + 2 * R / first y z hz) := by
  let := isZLattice y z hz
  obtain ⟨hb, hf, hs⟩ := successiveBasis_spec y z hz
  have h := PlaneCount.plane_lattice_count (lattice y) (successiveBasis y z hz)
    hb hf hs (liftFinset y S hS) R hR (norm_liftFinset_le y S hS R hbound)
  constructor
  · intro hlarge
    simpa only [card_liftFinset] using h.1 hlarge
  · intro hsmall
    simpa only [card_liftFinset, first] using (h.2 hsmall).2

theorem exists_primitive_shortest_integer (y z : Vec) (hz : y ⬝ᵥ z = 1) :
    ∃ v : Vec, v ≠ 0 ∧ y ⬝ᵥ v = 0 ∧
      ‖LatticeBox.realVector v‖ = first y z hz ∧ ∃ w : Vec, v ⬝ᵥ w = 1 := by
  obtain ⟨v, hv, hyv, hnorm⟩ := exists_shortest_integer y z hz
  have hker : Matrix.mulVec (fun _ : Unit => y) v = 0 := by
    funext i
    exact hyv
  obtain ⟨w, hw⟩ := IntegralMinima.shortest_kernel_has_bezout
    (fun _ : Unit => y) v hv hker (by
      intro u hu hku
      change ‖LatticeBox.realVector v‖ ≤ ‖LatticeBox.realVector u‖
      rw [hnorm]
      exact first_le_norm y z hz u (congrFun hku ()) hu)
  exact ⟨v, hv, hyv, hnorm, w, hw⟩

theorem second_le_of_independent (y z : Vec) (hz : y ⬝ᵥ z = 1)
    (w : Fin 2 → Vec) (hw : ∀ i, y ⬝ᵥ w i = 0)
    (hind : LinearIndependent ℝ (fun i => LatticeBox.realVector (w i)))
    (R : ℝ) (hR : ∀ i, ‖LatticeBox.realVector (w i)‖ ≤ R) :
    second y z hz ≤ R := by
  let f : Fin 2 → plane y := fun i => toLattice y (w i) (hw i)
  have hfind : LinearIndependent ℝ f := by
    apply LinearIndependent.of_comp (plane y).subtype
    exact hind
  have hex : ∃ i, f i ∉ Submodule.span ℝ {successiveBasis y z hz 0} := by
    by_contra! hall
    have hle : Submodule.span ℝ (Set.range f) ≤
        Submodule.span ℝ {successiveBasis y z hz 0} := by
      apply Submodule.span_le.mpr
      rintro u ⟨i, rfl⟩
      exact hall i
    have hd := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hfind,
      finrank_span_singleton ((successiveBasis y z hz).ne_zero 0)] at hd
    norm_num at hd
  obtain ⟨i, hi⟩ := hex
  have hmin := (successiveBasis_spec y z hz).2.2 (f i)
    (toLattice y (w i) (hw i)).property hi
  exact hmin.trans (hR i)

theorem thin_count (y z : Vec) (hz : y ⬝ᵥ z = 1)
    (S : Finset Vec) (hS : ∀ v ∈ S, y ⬝ᵥ v = 0)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ v ∈ S, ‖LatticeBox.realVector v‖ ≤ R)
    (hsmall : R < second y z hz) (hone : first y z hz ≤ R) :
    (S.card : ℝ) ≤ 3 * R / first y z hz := by
  have h := (plane_counts y z hz S hS R hR hbound).2 hsmall
  have hp : 0 < first y z hz := lt_of_lt_of_le zero_lt_one (one_le_first y z hz)
  have hr : 1 ≤ R / first y z hz := (le_div_iff₀ hp).mpr (by simpa using hone)
  calc
    (S.card : ℝ) ≤ 1 + 2 * R / first y z hz := h
    _ ≤ 3 * R / first y z hz := by
      simp only [mul_div_assoc]
      linarith

end Problem355.IntegerPlaneEstimates

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ShortKernelVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ShortKernelVectors

theorem pair_independent_of_coordinates {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℝ ι) (i j : ι)
    (hu : u i ≠ 0) (hv : v i = 0) (hvj : v j ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  apply linearIndependent_fin2.mpr
  change v ≠ 0 ∧ ∀ a : ℝ, a • v ≠ u
  constructor
  · intro h
    apply hvj
    simp only [h, PiLp.zero_apply]
  · intro a h
    have hi := congrArg (fun x : EuclideanSpace ℝ ι => x i) h
    simp only [PiLp.smul_apply, smul_eq_mul, hv, mul_zero] at hi
    exact hu hi.symm

theorem short_kernel_pair_zero (x : Fin 3 → ℤ) (hx : x 0 ≠ 0) :
    ∃ u v : Fin 3 → ℤ,
      dotProduct x u = 0 ∧ dotProduct x v = 0 ∧
      LinearIndependent ℝ ![IntegralMinima.toEuclidean u, IntegralMinima.toEuclidean v] ∧
      ‖IntegralMinima.toEuclidean u‖ ≤ ‖IntegralMinima.toEuclidean x‖ ∧
      ‖IntegralMinima.toEuclidean v‖ ≤ ‖IntegralMinima.toEuclidean x‖ := by
  let u : Fin 3 → ℤ := ![-x 1, x 0, 0]
  let v : Fin 3 → ℤ := ![-x 2, 0, x 0]
  have hxR : (x 0 : ℝ) ≠ 0 := by exact_mod_cast hx
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_⟩
  · simp [u, dotProduct, Fin.sum_univ_three]
    ring
  · simp [v, dotProduct, Fin.sum_univ_three]
    ring
  · apply pair_independent_of_coordinates (IntegralMinima.toEuclidean u) (IntegralMinima.toEuclidean v) 1 2
    · simpa [IntegralMinima.toEuclidean, u] using hxR
    · simp [IntegralMinima.toEuclidean, v]
    · simpa [IntegralMinima.toEuclidean, v] using hxR
  · have hsq : ‖IntegralMinima.toEuclidean u‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, u]; nlinarith [sq_nonneg (x 2 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean u), norm_nonneg (IntegralMinima.toEuclidean x)]
  · have hsq : ‖IntegralMinima.toEuclidean v‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, v]; nlinarith [sq_nonneg (x 1 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean v), norm_nonneg (IntegralMinima.toEuclidean x)]

theorem short_kernel_pair_one (x : Fin 3 → ℤ) (hx : x 1 ≠ 0) :
    ∃ u v : Fin 3 → ℤ,
      dotProduct x u = 0 ∧ dotProduct x v = 0 ∧
      LinearIndependent ℝ ![IntegralMinima.toEuclidean u, IntegralMinima.toEuclidean v] ∧
      ‖IntegralMinima.toEuclidean u‖ ≤ ‖IntegralMinima.toEuclidean x‖ ∧
      ‖IntegralMinima.toEuclidean v‖ ≤ ‖IntegralMinima.toEuclidean x‖ := by
  let u : Fin 3 → ℤ := ![x 1, -x 0, 0]
  let v : Fin 3 → ℤ := ![0, -x 2, x 1]
  have hxR : (x 1 : ℝ) ≠ 0 := by exact_mod_cast hx
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_⟩
  · simp [u, dotProduct, Fin.sum_univ_three]
    ring
  · simp [v, dotProduct, Fin.sum_univ_three]
    ring
  · apply pair_independent_of_coordinates (IntegralMinima.toEuclidean u) (IntegralMinima.toEuclidean v) 0 2
    · simpa [IntegralMinima.toEuclidean, u] using hxR
    · simp [IntegralMinima.toEuclidean, v]
    · simpa [IntegralMinima.toEuclidean, v] using hxR
  · have hsq : ‖IntegralMinima.toEuclidean u‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, u]; nlinarith [sq_nonneg (x 2 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean u), norm_nonneg (IntegralMinima.toEuclidean x)]
  · have hsq : ‖IntegralMinima.toEuclidean v‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, v]; nlinarith [sq_nonneg (x 0 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean v), norm_nonneg (IntegralMinima.toEuclidean x)]

theorem short_kernel_pair_two (x : Fin 3 → ℤ) (hx : x 2 ≠ 0) :
    ∃ u v : Fin 3 → ℤ,
      dotProduct x u = 0 ∧ dotProduct x v = 0 ∧
      LinearIndependent ℝ ![IntegralMinima.toEuclidean u, IntegralMinima.toEuclidean v] ∧
      ‖IntegralMinima.toEuclidean u‖ ≤ ‖IntegralMinima.toEuclidean x‖ ∧
      ‖IntegralMinima.toEuclidean v‖ ≤ ‖IntegralMinima.toEuclidean x‖ := by
  let u : Fin 3 → ℤ := ![x 2, 0, -x 0]
  let v : Fin 3 → ℤ := ![0, x 2, -x 1]
  have hxR : (x 2 : ℝ) ≠ 0 := by exact_mod_cast hx
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_⟩
  · simp [u, dotProduct, Fin.sum_univ_three]
    ring
  · simp [v, dotProduct, Fin.sum_univ_three]
    ring
  · apply pair_independent_of_coordinates (IntegralMinima.toEuclidean u) (IntegralMinima.toEuclidean v) 0 1
    · simpa [IntegralMinima.toEuclidean, u] using hxR
    · simp [IntegralMinima.toEuclidean, v]
    · simpa [IntegralMinima.toEuclidean, v] using hxR
  · have hsq : ‖IntegralMinima.toEuclidean u‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, u]; nlinarith [sq_nonneg (x 1 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean u), norm_nonneg (IntegralMinima.toEuclidean x)]
  · have hsq : ‖IntegralMinima.toEuclidean v‖ ^ 2 ≤ ‖IntegralMinima.toEuclidean x‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, IntegralMinima.toEuclidean,
        Fin.sum_univ_three, v]; nlinarith [sq_nonneg (x 0 : ℝ)]
    nlinarith [norm_nonneg (IntegralMinima.toEuclidean v), norm_nonneg (IntegralMinima.toEuclidean x)]

theorem exists_short_kernel_pair (x : Fin 3 → ℤ) (hx : x ≠ 0) :
    ∃ u v : Fin 3 → ℤ,
      dotProduct x u = 0 ∧ dotProduct x v = 0 ∧
      LinearIndependent ℝ ![IntegralMinima.toEuclidean u, IntegralMinima.toEuclidean v] ∧
      ‖IntegralMinima.toEuclidean u‖ ≤ ‖IntegralMinima.toEuclidean x‖ ∧
      ‖IntegralMinima.toEuclidean v‖ ≤ ‖IntegralMinima.toEuclidean x‖ := by
  by_cases h0 : x 0 ≠ 0
  · exact short_kernel_pair_zero x h0
  by_cases h1 : x 1 ≠ 0
  · exact short_kernel_pair_one x h1
  have h2 : x 2 ≠ 0 := by
    intro h2
    apply hx
    funext i
    fin_cases i <;> simp_all
  exact short_kernel_pair_two x h2

end Problem355.ShortKernelVectors

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AnisotropicPlaneData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix
open scoped Matrix
open PrimitiveNormal IntegerPlaneEstimates

lemma independent_realVector_of_cross_ne_zero (u v : IntVector)
    (huv : u ⨯₃ v ≠ 0) :
    LinearIndependent ℝ (fun i : Fin 2 => LatticeBox.realVector (![u, v] i)) := by
  let uR : Fin 3 → ℝ := fun i => (u i : ℝ)
  let vR : Fin 3 → ℝ := fun i => (v i : ℝ)
  have hcross : uR ⨯₃ vR ≠ 0 := by
    intro h
    apply huv
    ext i
    have hi := congrFun h i
    fin_cases i <;>
      simp [cross_apply, uR, vR] at hi ⊢ <;> exact_mod_cast hi
  have hind := crossProduct_ne_zero_iff_linearIndependent.mp hcross
  apply LinearIndependent.of_comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
  convert hind using 1 <;> try rfl
  funext i
  fin_cases i <;> rfl

lemma second_le_normal_length (y z : IntVector) (hz : y ⬝ᵥ z = 1)
    (hy : y ≠ 0) : second y z hz ≤ length y := by
  obtain ⟨u, v, hu, hv, hind, hnu, hnv⟩ :=
    ShortKernelVectors.exists_short_kernel_pair y hy
  apply second_le_of_independent y z hz ![u, v]
  · intro i
    fin_cases i
    · exact hu
    · exact hv
  · convert hind using 1
    funext i
    fin_cases i <;> rfl
  · intro i
    fin_cases i
    · exact hnu
    · exact hnv

theorem exists_planeData (y : IntVector) (hy : IsPrimitive y) :
    Nonempty (PlaneData y) := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one y).mp hy
  refine ⟨{
    first := first y z hz
    second := second y z hz
    one_le_first := one_le_first y z hz
    first_le_second := first_le_second y z hz
    second_le_length := second_le_normal_length y z hz hy.ne_zero
    first_le := ?_
    second_le := ?_
    shortest := ?_
    large_count := ?_
    small_count := ?_
  }⟩
  · intro v hv hne
    exact first_le_norm y z hz v (by simpa only [dotProduct_comm] using hv) hne
  · intro u v hu hv huv
    apply second_le_of_independent y z hz ![u, v]
    · intro i
      fin_cases i
      · change y ⬝ᵥ u = 0
        simpa only [dotProduct_comm] using hu
      · change y ⬝ᵥ v = 0
        simpa only [dotProduct_comm] using hv
    · exact independent_realVector_of_cross_ne_zero u v huv
    · intro i
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
  · obtain ⟨v, _, hv, he, hw⟩ := exists_primitive_shortest_integer y z hz
    exact ⟨v, (isPrimitive_iff_exists_dot_eq_one v).mpr hw,
      by simpa only [dotProduct_comm] using hv, he⟩
  · intro S R hR hS
    have hR0 : 0 ≤ R := by
      have h1 := one_le_first y z hz
      have h2 := first_le_second y z hz
      linarith
    have hc := (plane_counts y z hz S
      (fun v hv => by simpa only [dotProduct_comm] using (hS v hv).1)
      R hR0 (fun v hv => (hS v hv).2)).1 hR
    rw [IntegralPlaneLattice.lattice_covolume y z hz] at hc
    exact hc
  · intro S R hfirst hsecond hS
    have hR0 : 0 ≤ R := by linarith [one_le_first y z hz]
    exact thin_count y z hz S
      (fun v hv => by simpa only [dotProduct_comm] using (hS v hv).1)
      R hR0 (fun v hv => (hS v hv).2) hsecond hfirst

end Problem355.Anisotropic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerNormalGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix PrimitiveNormal

theorem normal_group_card_le_of_data
    (hplanes : ∀ y : IntVector, IsPrimitive y → Nonempty (PlaneData y))
    {U Y : ℝ} (hU : 1 ≤ U) (hY : 0 ≤ Y) (S : Finset IntVector)
    (hS : ∀ y ∈ S, IsPrimitive y ∧ length y ≤ 2 * Y ∧
      (∀ w : IntVector, w ⬝ᵥ y = 0 → w ≠ 0 → U ≤ length w) ∧
      ∃ w : IntVector, w ⬝ᵥ y = 0 ∧ w ≠ 0 ∧ length w ≤ 2 * U) :
    (S.card : ℝ) ≤ 18000 * Real.pi * U ^ 2 * Y ^ 2 := by
  classical
  let P : IntVector → Prop := fun z => IsPrimitive z ∧ length z ≤ 2 * Y
  have hcover : ∀ y ∈ S, ∃ z : IntVector,
      P z ∧ U ≤ length z ∧ length z ≤ 2 * U ∧ z ⬝ᵥ y = 0 := by
    intro y hy
    obtain ⟨hyp, hyl, hlow, w, hwy, hw0, hwU⟩ := hS y hy
    let d := Classical.choice (hplanes y hyp)
    obtain ⟨z, hzp, hzy, hzlen⟩ := d.shortest
    have hzY : length z ≤ 2 * Y := by
      rw [hzlen]
      exact d.first_le_second.trans (d.second_le_length.trans hyl)
    have hzU : length z ≤ 2 * U := by
      rw [hzlen]
      exact (d.first_le w hwy hw0).trans hwU
    exact ⟨z, ⟨hzp, hzY⟩, hlow z hzy hzp.ne_zero, hzU, hzy⟩
  have hplane : ∀ z, P z → U ≤ length z → length z ≤ 2 * U →
      ((S.filter (fun y => z ⬝ᵥ y = 0)).card : ℝ) ≤
        (9 * Real.pi) * (4 * Y) ^ 2 / length z := by
    intro z hz _ _
    let d := Classical.choice (hplanes z hz.1)
    apply d.large_count _ (4 * Y)
    · exact d.second_le_length.trans (hz.2.trans (by linarith))
    · intro y hy
      obtain ⟨hyS, hzy⟩ := Finset.mem_filter.mp hy
      exact ⟨by simpa only [dotProduct_comm] using hzy,
        (hS y hyS).2.1.trans (by linarith)⟩
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have h := LatticeBox.normal_group_card_le (Z := Y / U) hU
    (show 0 ≤ 144 * Real.pi by positivity) P S hcover (by
      intro z hz hzU hz2U
      calc
        ((S.filter (fun y => z ⬝ᵥ y = 0)).card : ℝ) ≤
            (9 * Real.pi) * (4 * Y) ^ 2 / length z := hplane z hz hzU hz2U
        _ ≤ (9 * Real.pi) * (4 * Y) ^ 2 / U :=
          div_le_div_of_nonneg_left (by positivity) hU0 hzU
        _ = (144 * Real.pi) * U * (Y / U) ^ 2 := by field_simp; ring)
  have heq : 125 * (144 * Real.pi) * U ^ 4 * (Y / U) ^ 2 =
      18000 * Real.pi * U ^ 2 * Y ^ 2 := by field_simp; ring
  simpa only [heq] using h

theorem normal_shell_card_le
    (hplanes : ∀ y : IntVector, IsPrimitive y → Nonempty (PlaneData y))
    {U Y : ℝ} (hU : 1 ≤ U) (hY : 0 ≤ Y) (S : Finset IntVector)
    (hS : ∀ y ∈ S, IsPrimitive y ∧ length y ≤ 2 * Y ∧
      ∃ d : PlaneData y, U ≤ d.first ∧ d.first ≤ 2 * U) :
    (S.card : ℝ) ≤ 18000 * Real.pi * U ^ 2 * Y ^ 2 := by
  apply normal_group_card_le_of_data hplanes hU hY S
  intro y hy
  obtain ⟨hyp, hyl, d, hUd, hdU⟩ := hS y hy
  refine ⟨hyp, hyl, fun w hw hw0 => hUd.trans (d.first_le w hw hw0), ?_⟩
  obtain ⟨z, hzp, hzy, hzlen⟩ := d.shortest
  exact ⟨z, hzy, hzp.ne_zero, hzlen.le.trans hdU⟩

end Problem355.Anisotropic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DeterminantFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DeterminantFibers

open scoped Matrix
open LatticeBox

theorem exists_translate_into_plane {d : ℕ} (S : Finset (Fin d → ℤ))
    (y : Fin d → ℤ) (c : ℤ) (R : ℝ)
    (hS : S.Nonempty)
    (hdot : ∀ u ∈ S, u ⬝ᵥ y = c)
    (hnorm : ∀ u ∈ S, ‖realVector u‖ ≤ R) :
    ∃ T : Finset (Fin d → ℤ), ∃ center : EuclideanSpace ℝ (Fin d),
      T.card = S.card ∧
      ∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z - center‖ ≤ R := by
  classical
  obtain ⟨u₀, hu₀⟩ := hS
  refine ⟨S.image (fun u => u - u₀), -realVector u₀, ?_, ?_⟩
  · exact Finset.card_image_of_injective _ (fun u v h => sub_left_injective h)
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    constructor
    · rw [sub_dotProduct, hdot u hu, hdot u₀ hu₀, sub_self]
    · simpa using hnorm u hu

theorem card_dot_fiber_le {d : ℕ} (S : Finset (Fin d → ℤ))
    (y : Fin d → ℤ) (c : ℤ) (R B : ℝ) (hB : 0 ≤ B)
    (hdot : ∀ u ∈ S, u ⬝ᵥ y = c)
    (hnorm : ∀ u ∈ S, ‖realVector u‖ ≤ R)
    (hplane : ∀ T : Finset (Fin d → ℤ), ∀ center : EuclideanSpace ℝ (Fin d),
      (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z - center‖ ≤ R) →
      (T.card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ B := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simpa [hS] using hB
  · obtain ⟨T, center, hcard, hT⟩ := exists_translate_into_plane S y c R hS hdot hnorm
    simpa only [hcard] using hplane T center hT

theorem dot_eq_of_fixed_triple_product
    (u u₀ v w y : Fin 3 → ℤ) (a : ℤ) (ha : a ≠ 0)
    (hcross : v ⨯₃ w = a • y)
    (hdet : u ⬝ᵥ (v ⨯₃ w) = u₀ ⬝ᵥ (v ⨯₃ w)) :
    u ⬝ᵥ y = u₀ ⬝ᵥ y := by
  rw [hcross, dotProduct_smul, dotProduct_smul] at hdet
  exact mul_left_cancel₀ ha hdet

theorem card_determinant_fiber_le
    (S : Finset (Fin 3 → ℤ)) (v w y : Fin 3 → ℤ) (a t : ℤ)
    (ha : a ≠ 0) (hcross : v ⨯₃ w = a • y)
    (R B : ℝ) (hB : 0 ≤ B)
    (hdet : ∀ u ∈ S, u ⬝ᵥ (v ⨯₃ w) = t)
    (hnorm : ∀ u ∈ S, ‖realVector u‖ ≤ R)
    (hplane : ∀ T : Finset (Fin 3 → ℤ), ∀ center : EuclideanSpace ℝ (Fin 3),
      (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z - center‖ ≤ R) →
      (T.card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ B := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simpa [hS] using hB
  · obtain ⟨u₀, hu₀⟩ := hS
    apply card_dot_fiber_le S y (u₀ ⬝ᵥ y) R B hB _ hnorm hplane
    intro u hu
    exact dot_eq_of_fixed_triple_product u u₀ v w y a ha hcross
      ((hdet u hu).trans (hdet u₀ hu₀).symm)

end Problem355.DeterminantFibers

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormalFiberCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.NormalFiberCount

theorem card_le_sum_fiber_bounds {α β : Type*} [DecidableEq β]
    (S : Finset α) (Y : Finset β) (f : α → β) (bound : β → ℝ)
    (hf : ∀ x ∈ S, f x ∈ Y)
    (hbound : ∀ y ∈ Y, ((S.filter (fun x => f x = y)).card : ℝ) ≤ bound y) :
    (S.card : ℝ) ≤ ∑ y ∈ Y, bound y := by
  classical
  have hcard := Finset.card_eq_sum_card_fiberwise hf
  calc
    (S.card : ℝ) = ∑ y ∈ Y, ((S.filter (fun x => f x = y)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ _ := Finset.sum_le_sum hbound

theorem card_le_card_mul_fiber_bound {α β : Type*} [DecidableEq β]
    (S : Finset α) (Y : Finset β) (f : α → β) (bound : ℝ)
    (hf : ∀ x ∈ S, f x ∈ Y)
    (hbound : ∀ y ∈ Y, ((S.filter (fun x => f x = y)).card : ℝ) ≤ bound) :
    (S.card : ℝ) ≤ (Y.card : ℝ) * bound := by
  simpa using card_le_sum_fiber_bounds S Y f (fun _ => bound) hf hbound

theorem card_triples_le_mul {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (S : Finset (α × β × γ)) (Y : Finset β) (Z : Finset γ)
    (B₁ B₂ B₃ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hY : (Y.card : ℝ) ≤ B₂) (hZ : (Z.card : ℝ) ≤ B₃)
    (hproj : ∀ x ∈ S, x.2.1 ∈ Y ∧ x.2.2 ∈ Z)
    (hfirst : ∀ y ∈ Y, ∀ z ∈ Z,
      ((S.filter (fun x => x.2 = (y, z))).card : ℝ) ≤ B₁) :
    (S.card : ℝ) ≤ B₁ * B₂ * B₃ := by
  have hcount := card_le_card_mul_fiber_bound S (Y.product Z)
    (fun x => x.2) B₁ (fun x hx => Finset.mem_product.mpr (hproj x hx))
    (fun yz hyz => hfirst yz.1 (Finset.mem_product.mp hyz).1
      yz.2 (Finset.mem_product.mp hyz).2)
  have hprod : ((Y.product Z).card : ℝ) = (Y.card : ℝ) * (Z.card : ℝ) := by
    exact_mod_cast Finset.card_product Y Z
  have hcount' : (S.card : ℝ) ≤ (Y.card : ℝ) * (Z.card : ℝ) * B₁ := by
    rwa [hprod] at hcount
  calc
    (S.card : ℝ) ≤ (Y.card : ℝ) * (Z.card : ℝ) * B₁ := hcount'
    _ ≤ B₂ * B₃ * B₁ := by
      apply mul_le_mul_of_nonneg_right _ hB₁
      exact mul_le_mul hY hZ (Nat.cast_nonneg _) hB₂
    _ = B₁ * B₂ * B₃ := by ring

end Problem355.NormalFiberCount

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PlaneFiberAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PlaneFiberAssembly

open scoped Matrix
open LatticeBox

theorem triple_count_of_plane_counts
    (S : Finset Triple) (y : Vec) (t : ℤ) (R₁ R₂ R₃ B₁ B₂ B₃ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hcross : ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y)
    (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0)
    (hnorm : ∀ x ∈ S, ‖realVector x.1‖ ≤ R₁ ∧
      ‖realVector x.2.1‖ ≤ R₂ ∧ ‖realVector x.2.2‖ ≤ R₃)
    (hcount₁ : ∀ T : Finset Vec, ∀ center : EuclideanSpace ℝ (Fin 3),
      (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z - center‖ ≤ R₁) →
      (T.card : ℝ) ≤ B₁)
    (hcount₂ : ∀ T : Finset Vec,
      (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z‖ ≤ R₂) → (T.card : ℝ) ≤ B₂)
    (hcount₃ : ∀ T : Finset Vec,
      (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z‖ ≤ R₃) → (T.card : ℝ) ≤ B₃) :
    (S.card : ℝ) ≤ B₁ * B₂ * B₃ := by
  classical
  let Y := S.image (fun x => x.2.1)
  let Z := S.image (fun x => x.2.2)
  have hY : (Y.card : ℝ) ≤ B₂ := by
    apply hcount₂
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨(hplane x hx).1, (hnorm x hx).2.1⟩
  have hZ : (Z.card : ℝ) ≤ B₃ := by
    apply hcount₃
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨(hplane x hx).2, (hnorm x hx).2.2⟩
  apply NormalFiberCount.card_triples_le_mul S Y Z B₁ B₂ B₃ hB₁ hB₂ hY hZ
  · intro x hx
    exact ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
  · intro v hv w hw
    let F := S.filter (fun x => x.2 = (v, w))
    change (F.card : ℝ) ≤ B₁
    rcases F.eq_empty_or_nonempty with hF | hF
    · simpa [hF] using hB₁
    · obtain ⟨x₀, hx₀⟩ := hF
      have hx₀S := (Finset.mem_filter.mp hx₀).1
      have htail₀ := (Finset.mem_filter.mp hx₀).2
      obtain ⟨a, ha, haxy⟩ := hcross x₀ hx₀S
      have haxy' : v ⨯₃ w = a • y := by
        simpa only [htail₀] using haxy
      let U := F.image Prod.fst
      have hcard : U.card = F.card := by
        apply Finset.card_image_of_injOn
        intro x hx x' hx' hfirst
        apply Prod.ext hfirst
        exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hx').2.symm
      have hU : (U.card : ℝ) ≤ B₁ := by
        apply DeterminantFibers.card_determinant_fiber_le U v w y a t ha haxy'
          R₁ B₁ hB₁ _ _ hcount₁
        · intro u hu
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
          have hd := hdet x (Finset.mem_filter.mp hx).1
          simpa only [(Finset.mem_filter.mp hx).2] using hd
        · intro u hu
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
          exact (hnorm x (Finset.mem_filter.mp hx).1).1
      simpa only [hcard] using hU

end Problem355.PlaneFiberAssembly

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AnisotropicCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix
open scoped Matrix
open PrimitiveNormal

theorem thick_fiber_card_le
    (S : Finset Triple) (y : IntVector) (d : PlaneData y) (t : ℤ)
    (R₁ R₂ R₃ : ℝ) (h₂₁ : R₂ ≤ R₁) (h₃₂ : R₃ ≤ R₂)
    (hlarge : d.second ≤ R₃)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hcross : ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y)
    (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0)
    (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    (S.card : ℝ) ≤ 2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2 / length y ^ 3 := by
  have h := PlaneFiberAssembly.triple_count_of_plane_counts S y t R₁ R₂ R₃
    (36 * Real.pi * R₁ ^ 2 / length y)
    (9 * Real.pi * R₂ ^ 2 / length y)
    (9 * Real.pi * R₃ ^ 2 / length y)
    (by positivity) (by positivity) hdet hcross hplane hnorm
    (fun T center hT => affine_plane_card_le y d T center R₁
      (hlarge.trans (h₃₂.trans h₂₁)) (fun v hv => (hT v hv).2)
      (fun v hv w hw => by rw [sub_dotProduct, (hT v hv).1, (hT w hw).1, sub_self]))
    (fun T hT => d.large_count T R₂ (hlarge.trans h₃₂) hT)
    (fun T hT => d.large_count T R₃ hlarge hT)
  convert h using 1; ring

theorem thin_fiber_card_le
    (S : Finset Triple) (y : IntVector) (d : PlaneData y) (t : ℤ)
    (R₁ R₂ R₃ : ℝ) (h₂₁ : R₂ ≤ R₁)
    (hlarge : d.second ≤ R₂) (hfirst : d.first ≤ R₃) (hthin : R₃ < d.second)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hcross : ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y)
    (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0)
    (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    (S.card : ℝ) ≤ 972 * Real.pi ^ 2 * R₁ ^ 2 * R₂ ^ 2 * R₃ /
      (length y ^ 2 * d.first) := by
  have h := PlaneFiberAssembly.triple_count_of_plane_counts S y t R₁ R₂ R₃
    (36 * Real.pi * R₁ ^ 2 / length y)
    (9 * Real.pi * R₂ ^ 2 / length y) (3 * R₃ / d.first)
    (by positivity) (by positivity) hdet hcross hplane hnorm
    (fun T center hT => affine_plane_card_le y d T center R₁
      (hlarge.trans h₂₁) (fun v hv => (hT v hv).2)
      (fun v hv w hw => by rw [sub_dotProduct, (hT v hv).1, (hT w hw).1, sub_self]))
    (fun T hT => d.large_count T R₂ hlarge hT)
    (fun T hT => d.small_count T R₃ hfirst hthin hT)
  convert h using 1; ring

theorem scales_le_of_nonempty
    (S : Finset Triple) (y : IntVector) (d : PlaneData y) (t : ℤ) (ht : t ≠ 0)
    (R₂ R₃ : ℝ) (h₃₂ : R₃ ≤ R₂) (hS : S.Nonempty)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0)
    (hnorm : ∀ x ∈ S, length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    d.first ≤ R₃ ∧ d.second ≤ R₂ := by
  obtain ⟨x, hx⟩ := hS
  have hc : x.2.1 ⨯₃ x.2.2 ≠ 0 := by
    intro hc
    apply ht
    have h := hdet x hx
    simpa [hc] using h.symm
  have hv : x.2.2 ≠ 0 := by
    intro hv
    apply hc
    simp [hv]
  refine ⟨(d.first_le _ (hplane x hx).2 hv).trans (hnorm x hx).2, ?_⟩
  exact (d.second_le _ _ (hplane x hx).1 (hplane x hx).2 hc).trans
    (max_le (hnorm x hx).1 ((hnorm x hx).2.trans h₃₂))

theorem thin_shell_sum_le
    (S : Finset IntVector) (first weight : IntVector → ℝ)
    (R₁ R₂ R₃ U Y C₀ C₁ : ℝ)
    (hU : 0 < U) (hY : 0 < Y) (hR₃ : 0 ≤ R₃) (hUR : U ≤ R₃)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hcard : (S.card : ℝ) ≤ C₀ * U ^ 2 * Y ^ 2)
    (hrange : ∀ y ∈ S, U ≤ first y ∧ Y ≤ length y)
    (hweight : ∀ y ∈ S, weight y ≤
      C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (length y ^ 2 * first y)) :
    ∑ y ∈ S, weight y ≤ C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 := by
  have hB : 0 ≤ C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U) := by positivity
  calc
    ∑ y ∈ S, weight y ≤
        ∑ _y ∈ S, C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U) := by
      apply Finset.sum_le_sum
      intro y hy
      apply (hweight y hy).trans
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul (pow_le_pow_left₀ hY.le (hrange y hy).2 2)
        (hrange y hy).1 hU.le (sq_nonneg _)
    _ = (S.card : ℝ) * (C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U)) := by simp
    _ ≤ (C₀ * U ^ 2 * Y ^ 2) *
        (C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (Y ^ 2 * U)) :=
      mul_le_mul_of_nonneg_right hcard hB
    _ = (C₀ * C₁) * U ^ 2 * Y ^ 2 * (R₁ ^ 2 / Y) *
        (R₂ ^ 2 / Y) * (R₃ / U) := by field_simp
    _ ≤ (C₀ * C₁) * (R₁ * R₂ * R₃) ^ 2 :=
      thin_normal_group_numeric hU hY hR₃ hUR (mul_nonneg hC₀ hC₁)

theorem thin_normal_sum_le
    (S : Finset IntVector) (first weight : IntVector → ℝ)
    (R₁ R₂ R₃ C₀ C₁ : ℝ)
    (h₂ : 1 ≤ R₂) (h₃ : 1 ≤ R₃)
    (h₂₁ : R₂ ≤ R₁) (h₃₁ : R₃ ≤ R₁)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hweight0 : ∀ y ∈ S, 0 ≤ weight y)
    (hrange : ∀ y ∈ S, 1 ≤ first y ∧ first y ≤ R₃ ∧
      1 ≤ length y ∧ length y ≤ R₂ * R₃)
    (hweight : ∀ y ∈ S, weight y ≤
      C₁ * R₁ ^ 2 * R₂ ^ 2 * R₃ / (length y ^ 2 * first y))
    (hgroup : ∀ (T : Finset IntVector), T ⊆ S → ∀ U Y : ℝ,
      1 ≤ U → 1 ≤ Y →
      (∀ y ∈ T, U ≤ first y ∧ first y ≤ 2 * U ∧
        Y ≤ length y ∧ length y ≤ 2 * Y) →
      (T.card : ℝ) ≤ C₀ * U ^ 2 * Y ^ 2) :
    ∑ y ∈ S, weight y ≤
      2 * C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 *
        (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
  classical
  have hprod : 1 ≤ R₂ * R₃ := by nlinarith
  have hA : 0 ≤ C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2 := by positivity
  have h := sum_le_of_dyadic_shell_estimates S first length weight h₃ hprod hA
    hweight0 hrange (by
      intro i j
      let T := S.filter fun y => (2 : ℝ) ^ i ≤ first y ∧ first y < 2 ^ (i + 1) ∧
        (2 : ℝ) ^ j ≤ length y ∧ length y < 2 ^ (j + 1)
      have hU : 1 ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      have hY : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hTS : T ⊆ S := Finset.filter_subset _ _
      have hT (y : IntVector) (hy : y ∈ T) :
          (2 : ℝ) ^ i ≤ first y ∧ first y ≤ 2 * 2 ^ i ∧
          (2 : ℝ) ^ j ≤ length y ∧ length y ≤ 2 * 2 ^ j := by
        obtain ⟨_, h₁, h₂, h₃, h₄⟩ := Finset.mem_filter.mp hy
        exact ⟨h₁, by simpa [pow_succ, mul_comm] using h₂.le,
          h₃, by simpa [pow_succ, mul_comm] using h₄.le⟩
      change ∑ y ∈ T, weight y ≤ _
      by_cases hne : T.Nonempty
      · obtain ⟨y, hy⟩ := hne
        exact thin_shell_sum_le T first weight R₁ R₂ R₃ _ _ C₀ C₁
          (by positivity) (by positivity) (by linarith)
          ((hT y hy).1.trans (hrange y (hTS hy)).2.1) hC₀ hC₁
          (hgroup T hTS _ _ hU hY hT)
          (fun z hz => ⟨(hT z hz).1, (hT z hz).2.2.1⟩)
          (fun z hz => hweight z (hTS hz))
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simpa using hA)
  calc
    ∑ y ∈ S, weight y ≤
        (C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2) *
          ((Real.log (2 * R₃) / Real.log 2) *
          (Real.log (2 * (R₂ * R₃)) / Real.log 2)) := by
      simpa only [mul_assoc] using h
    _ ≤ (C₀ * C₁ * (R₁ * R₂ * R₃) ^ 2) *
        (2 * (Real.log (2 * R₁) / Real.log 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (dyadic_log_product_le h₂ h₃ h₂₁ h₃₁) hA
    _ = _ := by ring

theorem triple_card_le_of_normal_assignment
    (hplanes : ∀ y : IntVector, IsPrimitive y → Nonempty (PlaneData y))
    (S : Finset Triple) (normal : Triple → IntVector) (t : ℤ) (ht : t ≠ 0)
    (R₁ R₂ R₃ : ℝ) (h₃ : 1 ≤ R₃) (h₃₂ : R₃ ≤ R₂) (h₂₁ : R₂ ≤ R₁)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hprim : ∀ x ∈ S, IsPrimitive (normal x))
    (hcross : ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • normal x)
    (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ normal x = 0 ∧ x.2.2 ⬝ᵥ normal x = 0)
    (hnormal : ∀ x ∈ S, length (normal x) ≤ R₂ * R₃)
    (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    (S.card : ℝ) ≤ 35721000 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2 *
      (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
  classical
  let Y := S.image normal
  let F (y : IntVector) := S.filter (fun x => normal x = y)
  let weight (y : IntVector) : ℝ := (F y).card
  let data (y : IntVector) (hy : IsPrimitive y) : PlaneData y :=
    Classical.choice (hplanes y hy)
  let first (y : IntVector) := if hy : IsPrimitive y then (data y hy).first else 1
  let second (y : IntVector) := if hy : IsPrimitive y then (data y hy).second else 1
  have hY (y : IntVector) (hy : y ∈ Y) : IsPrimitive y ∧
      1 ≤ length y ∧ length y ≤ R₂ * R₃ ∧ (F y).Nonempty := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨hprim x hx, LatticeBox.one_le_norm_realVector (hprim x hx).ne_zero,
      hnormal x hx, ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩⟩
  have hFdet (y : IntVector) : ∀ x ∈ F y,
      x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t :=
    fun x hx => hdet x (Finset.mem_filter.mp hx).1
  have hFcross (y : IntVector) : ∀ x ∈ F y,
      ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y := by
    intro x hx
    obtain ⟨hxS, hxy⟩ := Finset.mem_filter.mp hx
    simpa only [hxy] using hcross x hxS
  have hFplane (y : IntVector) : ∀ x ∈ F y,
      x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0 := by
    intro x hx
    obtain ⟨hxS, hxy⟩ := Finset.mem_filter.mp hx
    simpa only [hxy] using hplane x hxS
  have hFnorm (y : IntVector) : ∀ x ∈ F y, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃ :=
    fun x hx => hnorm x (Finset.mem_filter.mp hx).1
  have hscale (y : IntVector) (hy : y ∈ Y) :
      1 ≤ first y ∧ first y ≤ R₃ ∧ second y ≤ R₂ := by
    have hp := (hY y hy).1
    have hs := scales_le_of_nonempty (F y) y (data y hp) t ht R₂ R₃ h₃₂
      (hY y hy).2.2.2 (hFdet y) (hFplane y) (fun x hx => (hFnorm y x hx).2)
    simpa only [first, second, dite_eq_left hp] using
      And.intro (data y hp).one_le_first hs
  let E := Y.filter (fun y => second y ≤ R₃)
  let T := Y.filter (fun y => ¬ second y ≤ R₃)
  have h₂ : 1 ≤ R₂ := h₃.trans h₃₂
  have h₁ : 1 ≤ R₁ := h₂.trans h₂₁
  have hRprod : 1 ≤ R₂ * R₃ := by nlinarith
  have hthin : ∑ y ∈ T, weight y ≤
      2 * (18000 * Real.pi) * (972 * Real.pi ^ 2) * (R₁ * R₂ * R₃) ^ 2 *
        (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
    apply thin_normal_sum_le T first weight R₁ R₂ R₃ _ _ h₂ h₃ h₂₁ (h₃₂.trans h₂₁)
      (by positivity) (by positivity)
    · intro y hy
      exact Nat.cast_nonneg _
    · intro y hy
      have hyY := (Finset.mem_filter.mp hy).1
      exact ⟨(hscale y hyY).1, (hscale y hyY).2.1,
        (hY y hyY).2.1, (hY y hyY).2.2.1⟩
    · intro y hy
      obtain ⟨hyY, hyt⟩ := Finset.mem_filter.mp hy
      have hp := (hY y hyY).1
      have hlarge : (data y hp).second ≤ R₂ := by
        simpa only [second, dite_eq_left hp] using (hscale y hyY).2.2
      have hfirst : (data y hp).first ≤ R₃ := by
        simpa only [first, dite_eq_left hp] using (hscale y hyY).2.1
      have hlow : R₃ < (data y hp).second := by
        simpa only [second, dite_eq_left hp] using lt_of_not_ge hyt
      simpa only [first, dite_eq_left hp, weight] using
        thin_fiber_card_le (F y) y (data y hp) t R₁ R₂ R₃ h₂₁
          hlarge hfirst hlow (hFdet y) (hFcross y) (hFplane y) (hFnorm y)
    · intro A hAT U Z hU hZ hA
      apply normal_shell_card_le hplanes hU (by linarith) A
      intro y hy
      have hyY := (Finset.mem_filter.mp (hAT hy)).1
      have hp := (hY y hyY).1
      refine ⟨hp, (hA y hy).2.2.2, data y hp, ?_, ?_⟩
      · simpa only [first, dite_eq_left hp] using (hA y hy).1
      · simpa only [first, dite_eq_left hp] using (hA y hy).2.1
  have heasy : ∑ y ∈ E, weight y ≤
      (2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2) *
        ((125 / Real.log 2) * Real.log (2 * (R₂ * R₃))) := by
    calc
      ∑ y ∈ E, weight y ≤ ∑ y ∈ E,
          (2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2) / length y ^ 3 := by
        apply Finset.sum_le_sum
        intro y hy
        obtain ⟨hyY, hye⟩ := Finset.mem_filter.mp hy
        have hp := (hY y hyY).1
        have hlarge : (data y hp).second ≤ R₃ := by
          simpa only [second, dite_eq_left hp] using hye
        exact thick_fiber_card_le (F y) y (data y hp) t R₁ R₂ R₃ h₂₁ h₃₂
          hlarge (hFdet y) (hFcross y) (hFplane y) (hFnorm y)
      _ = (2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2) *
          ∑ y ∈ E, 1 / length y ^ 3 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (LatticeBox.reciprocal_cube_sum_le_log hRprod E (by
          intro y hy
          have h := hY y (Finset.mem_filter.mp hy).1
          exact ⟨h.1.ne_zero, h.2.2.1⟩)) (by positivity)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogprod : 0 ≤ Real.log (2 * (R₂ * R₃)) / Real.log 2 := by
    apply div_nonneg _ hlog2.le
    exact Real.log_nonneg (by nlinarith)
  have hlog3 : 1 ≤ Real.log (2 * R₃) / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * R₃)
  have hlogbound : Real.log (2 * (R₂ * R₃)) / Real.log 2 ≤
      2 * (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
    exact (le_mul_of_one_le_left hlogprod hlog3).trans
      (dyadic_log_product_le h₂ h₃ h₂₁ (h₃₂.trans h₂₁))
  have heasy' : ∑ y ∈ E, weight y ≤
      250 * 2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2 *
        (Real.log (2 * R₁) / Real.log 2) ^ 2 := by
    calc
      ∑ y ∈ E, weight y ≤ _ := heasy
      _ = (125 * 2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2) *
          (Real.log (2 * (R₂ * R₃)) / Real.log 2) := by ring
      _ ≤ (125 * 2916 * Real.pi ^ 3 * (R₁ * R₂ * R₃) ^ 2) *
          (2 * (Real.log (2 * R₁) / Real.log 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hlogbound (by positivity)
      _ = _ := by ring
  have hcard : (S.card : ℝ) = ∑ y ∈ Y, weight y := by
    dsimp only [weight, F]
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (s := S) (t := Y) (f := normal) (fun x hx => Finset.mem_image_of_mem normal hx))
  have hsplit : (∑ y ∈ E, weight y) + (∑ y ∈ T, weight y) =
      ∑ y ∈ Y, weight y := Finset.sum_filter_add_sum_filter_not Y _ _
  rw [hcard, ← hsplit]
  calc
    _ ≤ _ := add_le_add heasy' hthin
    _ = _ := by ring

theorem anisotropic_count_of_planeData
    (hplanes : ∀ y : IntVector, IsPrimitive y → Nonempty (PlaneData y))
    (S : Finset Triple) (t : ℤ) (ht : t ≠ 0)
    (R₁ R₂ R₃ : ℝ) (h₃ : 1 ≤ R₃) (h₃₂ : R₃ ≤ R₂) (h₂₁ : R₂ ≤ R₁)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    (S.card : ℝ) ≤ (35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2) *
      (R₁ * R₂ * R₃) ^ 2 * Real.log (2 * R₁) ^ 2 := by
  classical
  have hex : ∀ x : Triple, ∃ y : IntVector, x ∈ S →
      IsPrimitive y ∧ (∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y) ∧
      (x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0) ∧ length y ≤ R₂ * R₃ := by
    intro x
    by_cases hx : x ∈ S
    · have hnz : x.2.1 ⨯₃ x.2.2 ≠ 0 := by
        intro hc
        apply ht
        have hd := hdet x hx
        simpa [hc] using hd.symm
      obtain ⟨a, ha, y, hyp, hfactor, horth₁, horth₂, hyl, _⟩ :=
        CrossNormal.exists_bounded_primitive_cross_factor x.2.1 x.2.2 hnz
      refine ⟨y, fun _ => ⟨hyp, ⟨a, ne_of_gt ha, hfactor⟩, ⟨horth₁, horth₂⟩, ?_⟩⟩
      exact hyl.trans (mul_le_mul (hnorm x hx).2.1 (hnorm x hx).2.2
        (norm_nonneg _) ((norm_nonneg _).trans (hnorm x hx).2.1))
    · exact ⟨0, fun h => (hx h).elim⟩
  choose normal hnormal using hex
  have h := triple_card_le_of_normal_assignment hplanes S normal t ht
    R₁ R₂ R₃ h₃ h₃₂ h₂₁ hdet (fun x hx => (hnormal x hx).1)
    (fun x hx => (hnormal x hx).2.1) (fun x hx => (hnormal x hx).2.2.1)
    (fun x hx => (hnormal x hx).2.2.2) hnorm
  convert h using 1; simp only [div_pow]; ring

theorem anisotropic_count
    (S : Finset Triple) (t : ℤ) (ht : t ≠ 0)
    (R₁ R₂ R₃ : ℝ) (h₃ : 1 ≤ R₃) (h₃₂ : R₃ ≤ R₂) (h₂₁ : R₂ ≤ R₁)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hnorm : ∀ x ∈ S, length x.1 ≤ R₁ ∧
      length x.2.1 ≤ R₂ ∧ length x.2.2 ≤ R₃) :
    (S.card : ℝ) ≤ (35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2) *
      (R₁ * R₂ * R₃) ^ 2 * Real.log (2 * R₁) ^ 2 :=
  anisotropic_count_of_planeData exists_planeData S t ht R₁ R₂ R₃
    h₃ h₃₂ h₂₁ hdet hnorm

theorem anisotropic_constant_pos :
    0 < 35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2 := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

end Problem355.Anisotropic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroGlobalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.ZeroGlobalCount

open Matrix PrimitiveNormal ZeroDeterminantCount
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma countConstant_nonneg {Ca Cg Cd : ℝ}
    (ha : 0 ≤ Ca) (hg : 0 ≤ Cg) (hd : 0 ≤ Cd) :
    0 ≤ countConstant Ca Cg Cd := by
  unfold countConstant planeConstant
  positivity

end Problem355.ZeroGlobalCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliaryZeroCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.AuxiliaryZeroCount

open Matrix PrimitiveNormal ZeroDeterminantCount LiftingProbability
open scoped BigOperators

lemma countConstant_nonneg : 0 ≤ countConstant :=
  ZeroGlobalCount.countConstant_nonneg (by norm_num) (by positivity) (by positivity)

end Problem355.AuxiliaryZeroCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticeCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.LatticeCoordinates

open scoped BigOperators
open Matrix

variable {n : Type*} [finiteIndex : Fintype n] [decidableIndex : DecidableEq n]

theorem exists_integer_coordinates_of_mem_span {n : Type*} [Fintype n] [DecidableEq n] (V A : Matrix n n ℝ) (m : ℕ)
    (hA : ∀ i, m • A i ∈ Submodule.span ℤ (Set.range V)) :
    ∃ Q : Matrix n n ℤ, Q.map (Int.castRingHom ℝ) * V = (m : ℝ) • A := by
  classical
  choose Q hQ using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hA i)
  refine ⟨Matrix.of Q, ?_⟩
  ext i j
  have h := congrFun (hQ i) j
  simpa [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, nsmul_eq_mul,
    zsmul_eq_mul] using h

theorem coordinates_det (V A : Matrix n n ℝ) (m : ℝ)
    (hV : V.det ≠ 0) (Q : Matrix n n ℤ)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A) :
    (Q.det : ℝ) = m ^ Fintype.card n * A.det / V.det := by
  apply (eq_div_iff hV).mpr
  have h := congrArg Matrix.det hQ
  have hcast : (Q.map (Int.castRingHom ℝ)).det = (Q.det : ℝ) := by
    exact ((Int.castRingHom ℝ).map_det Q).symm
  rw [Matrix.det_mul, hcast, Matrix.det_smul] at h
  exact h

theorem coordinates_injective {n : Type*} [Fintype n] [DecidableEq n] (V A A' : Matrix n n ℝ) (m : ℝ)
    (hm : m ≠ 0) (Q : Matrix n n ℤ)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A)
    (hQ' : Q.map (Int.castRingHom ℝ) * V = m • A') : A = A' := by
  have h : m • A = m • A' := hQ.symm.trans hQ'
  exact (smul_right_injective _ hm) h

theorem abs_det_le_factorial_prod (V : Matrix n n ℝ) (R : n → ℝ)
    (hV : ∀ i j, |V i j| ≤ R i) :
    |V.det| ≤ (Nat.factorial (Fintype.card n) : ℝ) * ∏ i, R i := by
  calc
    |V.det| = ‖∑ σ : Equiv.Perm n, σ.sign • ∏ i, V (σ i) i‖ := by
      rw [← Matrix.det_apply, Real.norm_eq_abs]
    _ ≤ ∑ σ : Equiv.Perm n, ‖σ.sign • ∏ i, V (σ i) i‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ∏ i, |V (σ i) i| := by
      simp only [norm_units_zsmul, norm_prod, Real.norm_eq_abs]
    _ ≤ ∑ σ : Equiv.Perm n, ∏ i, R i := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [← Equiv.prod_comp σ R]
      exact Finset.prod_le_prod (fun i hi => abs_nonneg _) (fun i hi => hV (σ i) i)
    _ = (Nat.factorial (Fintype.card n) : ℝ) * ∏ i, R i := by
      simp [Fintype.card_perm]

theorem coordinate_abs_bound (V : Matrix n n ℝ) (α u : n → ℝ)
    (R : n → ℝ) (X : ℝ) (hV : V.det ≠ 0)
    (hR : ∀ i j, |V i j| ≤ R i) (hu : ∀ j, |u j| ≤ X)
    (hα : ∑ i, α i • V i = u) (j : n) :
    |α j| ≤ ((Nat.factorial (Fintype.card n) : ℝ) * X *
      ∏ i ∈ Finset.univ.erase j, R i) / |V.det| := by
  have hdet : (V.updateRow j u).det = α j * V.det := by
    rw [← hα, Matrix.det_updateRow_sum, smul_eq_mul]
  have hbound := abs_det_le_factorial_prod (V.updateRow j u) (Function.update R j X) ?_
  · rw [hdet, abs_mul, Finset.prod_update_of_mem (Finset.mem_univ j)] at hbound
    apply (le_div_iff₀ (abs_pos.mpr hV)).mpr
    simpa [Finset.sdiff_singleton_eq_erase, mul_assoc] using hbound
  · intro i k
    by_cases hi : i = j
    · subst i
      simpa using hu k
    · simpa [Matrix.updateRow_ne hi, Function.update_of_ne hi] using hR i k

theorem coordinate_abs_bound_of_product_bound
    (V : Matrix n n ℝ) (α u R : n → ℝ) (X C : ℝ)
    (hV : V.det ≠ 0) (hR : ∀ i j, |V i j| ≤ R i)
    (hu : ∀ j, |u j| ≤ X) (hX : 0 ≤ X)
    (hα : ∑ i, α i • V i = u) (j : n) (hRj : 0 < R j)
    (hprod : (∏ i, R i) ≤ C * |V.det|) :
    |α j| ≤ (Nat.factorial (Fintype.card n) : ℝ) * C * X / R j := by
  have hd : 0 < |V.det| := abs_pos.mpr hV
  have hp : (∏ i ∈ Finset.univ.erase j, R i) / |V.det| ≤ C / R j := by
    apply (div_le_div_iff₀ hd hRj).mpr
    calc
      (∏ i ∈ Finset.univ.erase j, R i) * R j = ∏ i, R i := by
        rw [mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      _ ≤ C * |V.det| := hprod
  calc
    |α j| ≤ ((Nat.factorial (Fintype.card n) : ℝ) * X *
        ∏ i ∈ Finset.univ.erase j, R i) / |V.det| :=
      coordinate_abs_bound V α u R X hV hR hu hα j
    _ = ((Nat.factorial (Fintype.card n) : ℝ) * X) *
        ((∏ i ∈ Finset.univ.erase j, R i) / |V.det|) := by ring
    _ ≤ ((Nat.factorial (Fintype.card n) : ℝ) * X) * (C / R j) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (Nat.cast_nonneg _) hX)
    _ = (Nat.factorial (Fintype.card n) : ℝ) * C * X / R j := by ring

theorem integer_coordinates_entry_bound
    (V A : Matrix n n ℝ) (Q : Matrix n n ℤ) (m X C : ℝ) (R : n → ℝ)
    (hV : V.det ≠ 0) (hR : ∀ i j, |V i j| ≤ R i)
    (hA : ∀ i j, |A i j| ≤ X) (hX : 0 ≤ X)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A)
    (hprod : (∏ i, R i) ≤ C * |V.det|) (i j : n) (hRj : 0 < R j) :
    |(Q i j : ℝ)| ≤
      (Nat.factorial (Fintype.card n) : ℝ) * C * (|m| * X) / R j := by
  apply coordinate_abs_bound_of_product_bound V (fun k => (Q i k : ℝ))
    ((m • A) i) R (|m| * X) C hV hR _ (mul_nonneg (abs_nonneg _) hX)
    _ j hRj hprod
  · intro k
    change |m * A i k| ≤ |m| * X
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hA i k) (abs_nonneg _)
  · ext k
    have h := congrFun (congrFun hQ i) k
    simpa [Matrix.mul_apply, Matrix.map_apply] using h

theorem exists_coordinate_family (V : Matrix n n ℝ) (m : ℝ) (hm : m ≠ 0)
    (S : Finset (Matrix n n ℝ))
    (hS : ∀ A ∈ S, ∃ Q : Matrix n n ℤ,
      Q.map (Int.castRingHom ℝ) * V = m • A) :
    ∃ T : Finset (Matrix n n ℤ), T.card = S.card ∧
      (∀ Q ∈ T, ∃ A ∈ S, Q.map (Int.castRingHom ℝ) * V = m • A) ∧
      (∀ A ∈ S, ∃ Q ∈ T, Q.map (Int.castRingHom ℝ) * V = m • A) := by
  classical
  choose f hf using fun A : S => hS A A.property
  have hinj : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    apply coordinates_injective V A B m hm (f A) (hf A)
    rw [h]
    exact hf B
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro Q hQ
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨A, A.property, hf A⟩
  · intro A hA
    exact ⟨f ⟨A, hA⟩, Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_univ _, rfl⟩,
      hf ⟨A, hA⟩⟩

theorem coordinates_det_ne_zero (V A : Matrix n n ℝ) (m : ℝ)
    (hm : m ≠ 0) (hA : A.det ≠ 0) (Q : Matrix n n ℤ)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A) : Q.det ≠ 0 := by
  intro hzero
  have h := congrArg Matrix.det hQ
  have hcast : (Q.map (Int.castRingHom ℝ)).det = (Q.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det Q).symm
  rw [Matrix.det_mul, hcast, hzero, Int.cast_zero, zero_mul, Matrix.det_smul] at h
  exact (mul_ne_zero (pow_ne_zero _ hm) hA) h.symm

theorem euclidean_norm_le_of_coord_bound {n : Type*} [Fintype n] [DecidableEq n] (v : EuclideanSpace ℝ n) (B : ℝ)
    (hB : 0 ≤ B) (hv : ∀ i, |v i| ≤ B) :
    ‖v‖ ≤ Real.sqrt (Fintype.card n) * B := by
  have hsum : (∑ i, ‖v i‖ ^ 2) ≤ (Fintype.card n : ℝ) * B ^ 2 := by
    calc
      (∑ i, ‖v i‖ ^ 2) ≤ ∑ _i : n, B ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
      _ = (Fintype.card n : ℝ) * B ^ 2 := by simp
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤
        Real.sqrt ((Fintype.card n : ℝ) * B ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card n) * B := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB]

theorem integer_coordinates_column_bound
    (V A : Matrix n n ℝ) (Q : Matrix n n ℤ) (m X C : ℝ) (R : n → ℝ)
    (hV : V.det ≠ 0) (hR : ∀ i j, |V i j| ≤ R i)
    (hA : ∀ i j, |A i j| ≤ X) (hX : 0 ≤ X) (hC : 0 ≤ C)
    (hQ : Q.map (Int.castRingHom ℝ) * V = m • A)
    (hprod : (∏ i, R i) ≤ C * |V.det|) (j : n) (hRj : 0 < R j) :
    ‖(WithLp.toLp 2 (fun i => (Q i j : ℝ)) : EuclideanSpace ℝ n)‖ ≤
      Real.sqrt (Fintype.card n) *
        ((Nat.factorial (Fintype.card n) : ℝ) * C * (|m| * X) / R j) := by
  apply euclidean_norm_le_of_coord_bound
  · positivity
  · intro i
    exact integer_coordinates_entry_bound V A Q m X C R hV hR hA hX hQ hprod i j hRj

theorem exists_fixed_det_coordinate_family
    (V : Matrix n n ℝ) (m : ℕ) (hm : 0 < m) (R : n → ℝ) (X C : ℝ)
    (hV : V.det ≠ 0) (hR : ∀ i j, |V i j| ≤ R i)
    (hRpos : ∀ j, 0 < R j) (hX : 0 ≤ X) (hC : 0 ≤ C)
    (hprod : (∏ i, R i) ≤ C * |V.det|)
    (S : Finset (Matrix n n ℝ)) (hne : S.Nonempty)
    (hspan : ∀ A ∈ S, ∀ i, m • A i ∈ Submodule.span ℤ (Set.range V))
    (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X)
    (t : ℝ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    ∃ u : ℤ, u ≠ 0 ∧ (u : ℝ) = (m : ℝ) ^ Fintype.card n * t / V.det ∧
      ∃ T : Finset (Matrix n n ℤ), T.card = S.card ∧
        ∀ Q ∈ T, Q.det = u ∧ ∀ j,
          ‖(WithLp.toLp 2 (fun i => (Q i j : ℝ)) : EuclideanSpace ℝ n)‖ ≤
            Real.sqrt (Fintype.card n) *
              ((Nat.factorial (Fintype.card n) : ℝ) * C * ((m : ℝ) * X) / R j) := by
  classical
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  obtain ⟨T, hcard, hforward, hback⟩ := exists_coordinate_family V (m : ℝ) hmR S
    (fun A hA => exists_integer_coordinates_of_mem_span V A m (hspan A hA))
  obtain ⟨A₀, hA₀⟩ := hne
  obtain ⟨Q₀, hQ₀, hcoord₀⟩ := hback A₀ hA₀
  have ht₀ : A₀.det ≠ 0 := by rw [hdet A₀ hA₀]; exact ht
  have hdet₀ : (Q₀.det : ℝ) = (m : ℝ) ^ Fintype.card n * t / V.det := by
    simpa [hdet A₀ hA₀] using coordinates_det V A₀ (m : ℝ) hV Q₀ hcoord₀
  refine ⟨Q₀.det, coordinates_det_ne_zero V A₀ (m : ℝ) hmR ht₀ Q₀ hcoord₀,
    hdet₀, T, hcard, ?_⟩
  intro Q hQ
  obtain ⟨A, hA, hcoord⟩ := hforward Q hQ
  constructor
  · have hdetQ : (Q.det : ℝ) = (m : ℝ) ^ Fintype.card n * t / V.det := by
      simpa [hdet A hA] using coordinates_det V A (m : ℝ) hV Q hcoord
    exact_mod_cast hdetQ.trans hdet₀.symm
  · intro j
    simpa only [abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m)] using
      integer_coordinates_column_bound V A Q (m : ℝ) X C R hV hR
        (hbound A hA) hX hC hcoord hprod j (hRpos j)

end Problem355.LatticeCoordinates

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FixedDetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.FixedDetReduction

open scoped BigOperators

lemma log_radius_bound (X r : ℝ) (hX : 1 ≤ X) (hr : 1 ≤ r)
    (hrX : r ≤ 1000 * X) :
    Real.log (2 * r) ≤ 12 * Real.log (2 * X) := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog2 : Real.log 2 ≤ Real.log (2 * X) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hlogX : Real.log X ≤ Real.log (2 * X) :=
    Real.log_le_log hXp (by nlinarith)
  have hlog2000 : Real.log 2000 ≤ 11 * Real.log 2 := by
    have h := Real.log_le_log (show (0 : ℝ) < 2000 by norm_num)
      (show (2000 : ℝ) ≤ 2 ^ 11 by norm_num)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  calc
    Real.log (2 * r) ≤ Real.log (2000 * X) :=
      Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log 2000 + Real.log X := Real.log_mul (by norm_num) hXp.ne'
    _ ≤ 11 * Real.log (2 * X) + Real.log (2 * X) :=
      add_le_add (hlog2000.trans (mul_le_mul_of_nonneg_left hlog2 (by norm_num))) hlogX
    _ = 12 * Real.log (2 * X) := by ring

lemma radius_antitone (X : ℝ) (ℓ : Fin 3 → ℝ) (hX : 0 ≤ X)
    (hℓ : ∀ j, 0 < ℓ j) (hmono : Monotone ℓ) : Antitone (radius X ℓ) := by
  intro i j hij
  exact div_le_div_of_nonneg_left (by positivity) (hℓ i) (hmono hij)

lemma one_le_radius (X : ℝ) (ℓ : Fin 3 → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (hℓX : ∀ j, ℓ j ≤ X) (j : Fin 3) : 1 ≤ radius X ℓ j := by
  apply (le_div_iff₀ (hℓ j)).mpr
  have hXp : 0 < X := lt_of_lt_of_le (hℓ j) (hℓX j)
  nlinarith [hℓX j]

lemma radius_product_bound (X I : ℝ) (ℓ : Fin 3 → ℝ)
    (hX : 0 ≤ X) (hI : 0 < I) (hℓ : ∀ j, 0 < ℓ j)
    (hIℓ : I ≤ ∏ j, ℓ j) :
    (∏ j, radius X ℓ j) ≤ (1000 * X) ^ 3 / I := by
  have hprod : 0 < ∏ j, ℓ j := Finset.prod_pos fun j hj => hℓ j
  calc
    (∏ j, radius X ℓ j) = (1000 * X) ^ 3 / (∏ j, ℓ j) := by
      simp [radius, Finset.prod_div_distrib]
    _ ≤ (1000 * X) ^ 3 / I :=
      div_le_div_of_nonneg_left (by positivity) hI hIℓ

theorem radius_count_factor_bound (X I : ℝ) (ℓ : Fin 3 → ℝ)
    (hX : 1 ≤ X) (hI : 0 < I) (hℓ1 : ∀ j, 1 ≤ ℓ j)
    (hℓX : ∀ j, ℓ j ≤ X) (hIℓ : I ≤ ∏ j, ℓ j) :
    (∏ j, radius X ℓ j) ^ 2 * Real.log (2 * radius X ℓ 0) ^ 2 ≤
      (1000 : ℝ) ^ 6 * 144 * (X ^ 6 / I ^ 2) * Real.log (2 * X) ^ 2 := by
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hℓ : ∀ j, 0 < ℓ j := fun j => lt_of_lt_of_le zero_lt_one (hℓ1 j)
  have hr : ∀ j, 1 ≤ radius X ℓ j := one_le_radius X ℓ hℓ hℓX
  have hrX : radius X ℓ 0 ≤ 1000 * X := by
    apply (div_le_iff₀ (hℓ 0)).mpr
    nlinarith [hℓ1 0]
  have hlog := log_radius_bound X (radius X ℓ 0) hX (hr 0) hrX
  have hlognonneg : 0 ≤ Real.log (2 * radius X ℓ 0) :=
    Real.log_nonneg (by nlinarith [hr 0])
  have hprodnonneg : 0 ≤ ∏ j, radius X ℓ j :=
    Finset.prod_nonneg fun j hj => le_trans zero_le_one (hr j)
  have hprod := radius_product_bound X I ℓ hXp.le hI hℓ hIℓ
  calc
    (∏ j, radius X ℓ j) ^ 2 * Real.log (2 * radius X ℓ 0) ^ 2 ≤
        ((1000 * X) ^ 3 / I) ^ 2 * (12 * Real.log (2 * X)) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ hprodnonneg hprod 2)
        (pow_le_pow_left₀ hlognonneg hlog 2) (sq_nonneg _) (sq_nonneg _)
    _ = (1000 : ℝ) ^ 6 * 144 * (X ^ 6 / I ^ 2) * Real.log (2 * X) ^ 2 := by
      ring

lemma coordinate_radius_le (X l : ℝ) (m : ℕ)
    (hX : 0 ≤ X) (hl : 0 < l) (hm : m ≤ 6) :
    Real.sqrt (Fintype.card (Fin 3)) *
      ((Nat.factorial (Fintype.card (Fin 3)) : ℝ) * 6 * ((m : ℝ) * X) / l) ≤
        1000 * X / l := by
  have hsqrt : Real.sqrt (3 : ℝ) ≤ 2 := by norm_num [Real.sqrt_le_iff]
  have hmR : (m : ℝ) ≤ 6 := by exact_mod_cast hm
  norm_num only [Fintype.card_fin, Nat.factorial, Nat.cast_ofNat]
  have hnum : Real.sqrt (3 : ℝ) * (36 * ((m : ℝ) * X)) ≤ 1000 * X := by
    calc
      Real.sqrt (3 : ℝ) * (36 * ((m : ℝ) * X)) ≤
          2 * (36 * (6 * X)) := by gcongr
      _ ≤ 1000 * X := by nlinarith
  calc
    Real.sqrt (3 : ℝ) * (36 * ((m : ℝ) * X) / l) =
        (Real.sqrt (3 : ℝ) * (36 * ((m : ℝ) * X))) / l := by ring
    _ ≤ 1000 * X / l := div_le_div_of_nonneg_right hnum hl.le

theorem fixed_det_count_of_short_basis
    (a : ℝ) (ha : 0 ≤ a) (hanis : AnisotropicEstimate a)
    (V : Matrix (Fin 3) (Fin 3) ℝ) (m : ℕ) (hm : 0 < m) (hm6 : m ≤ 6)
    (ℓ : Fin 3 → ℝ) (X I : ℝ)
    (hV : V.det ≠ 0) (hℓ : ∀ i j, |V i j| ≤ ℓ i)
    (hℓ1 : ∀ j, 1 ≤ ℓ j) (hℓX : ∀ j, ℓ j ≤ X) (hmono : Monotone ℓ)
    (hX : 1 ≤ X) (hI : 0 < I) (hIℓ : I ≤ ∏ j, ℓ j)
    (hprod : (∏ j, ℓ j) ≤ 6 * |V.det|)
    (S : Finset (Matrix (Fin 3) (Fin 3) ℝ))
    (hspan : ∀ A ∈ S, ∀ i, m • A i ∈ Submodule.span ℤ (Set.range V))
    (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X)
    (t : ℝ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 / I ^ 2 := by
  classical
  by_cases hne : S.Nonempty
  · have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
    have hℓpos : ∀ j, 0 < ℓ j := fun j => lt_of_lt_of_le zero_lt_one (hℓ1 j)
    obtain ⟨u, hu, huvalue, T, hcard, hT⟩ :=
      LatticeCoordinates.exists_fixed_det_coordinate_family V m hm ℓ X 6 hV hℓ
        hℓpos hXp.le (by norm_num) hprod S hne hspan hbound t ht hdet
    have hcols : ∀ Q ∈ T, Q.det = u ∧ ∀ j,
        ‖(WithLp.toLp 2 (fun i => (Q i j : ℝ)) : EuclideanSpace ℝ (Fin 3))‖ ≤
          radius X ℓ j := by
      intro Q hQ
      refine ⟨(hT Q hQ).1, ?_⟩
      intro j
      exact ((hT Q hQ).2 j).trans (coordinate_radius_le X (ℓ j) m hXp.le (hℓpos j) hm6)
    have hcount := hanis (radius X ℓ) u T (radius_antitone X ℓ hXp.le hℓpos hmono)
      (one_le_radius X ℓ hℓpos hℓX 2) hu hcols
    have hfactor := radius_count_factor_bound X I ℓ hX hI hℓ1 hℓX hIℓ
    calc
      (S.card : ℝ) ≤ a * ((∏ j, radius X ℓ j) ^ 2 *
          Real.log (2 * radius X ℓ 0) ^ 2) := by
        simpa only [hcard, mul_assoc] using hcount
      _ ≤ a * (1000 ^ 6 * 144 * (X ^ 6 / I ^ 2) * Real.log (2 * X) ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor ha
      _ = (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 / I ^ 2 := by ring
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hS, Finset.card_empty, Nat.cast_zero]
    positivity

end Problem355.FixedDetReduction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FixedDetLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.FixedDetLattice

open Module Submodule MeasureTheory
open scoped BigOperators

lemma orthonormal_det_eq (b : Basis (Fin 3) ℝ E) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det b = (basisMatrix b).det := by
  rw [Basis.det_apply]
  have hmat : (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.toMatrix b =
      (basisMatrix b).transpose := by
    ext i j
    rfl
  rw [hmat, Matrix.det_transpose]

lemma covolume_span_basis_eq_det (b : Basis (Fin 3) ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |(basisMatrix b).det| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis,
    LatticeLowerProduct.volumeReal_fundamentalDomain_orthonormal,
    mul_one, orthonormal_det_eq]

lemma basisMatrix_det_ne_zero (b : Basis (Fin 3) ℝ E) : (basisMatrix b).det ≠ 0 := by
  apply abs_pos.mp
  rw [← covolume_span_basis_eq_det]
  exact ZLattice.covolume_pos (Submodule.span ℤ (Set.range b)) volume

lemma basisMatrix_coord_bound (b : Basis (Fin 3) ℝ E) (i j : Fin 3) :
    |basisMatrix b i j| ≤ ‖b i‖ := by
  simpa only [basisMatrix, Real.norm_eq_abs] using PiLp.norm_apply_le (b i) j

lemma relIndex_clears_rows (L : Submodule ℤ E) (b : Basis (Fin 3) ℝ E)
    (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L) :
    ∀ i, (Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup • A i ∈
      Submodule.span ℤ (Set.range (basisMatrix b)) := by
  intro i
  have h := (Submodule.span ℤ (Set.range b)).toAddSubgroup.nsmul_relIndex_mem
    (K := L.toAddSubgroup) (g := (WithLp.toLp 2 (A i) : E)) (hA i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
  apply (Submodule.mem_span_range_iff_exists_fun ℤ).mpr
  refine ⟨c, ?_⟩
  ext j
  have hh := congrArg (fun x : E => x j) hc
  simpa [basisMatrix] using hh

theorem fixed_det_count_of_successive_basis
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hunit : ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖x‖)
    (b : Basis (Fin 3) ℝ E) (hb : SuccessiveVectors.IsSuccessive L b)
    (X : ℝ) (hX : 1 ≤ X) (hlast : ‖b 2‖ ≤ X)
    (S : Finset (Matrix (Fin 3) (Fin 3) ℝ))
    (hrows : ∀ A ∈ S, ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖(WithLp.toLp 2 (A i) : E)‖ ≤ X)
    (t : ℝ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      ZLattice.covolume L ^ 2 := by
  let L₀ := Submodule.span ℤ (Set.range b)
  let m := L₀.toAddSubgroup.relIndex L.toAddSubgroup
  have hsub : L₀ ≤ L := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hb.mem_lattice i
  have hratio : ZLattice.covolume L₀ / ZLattice.covolume L = (m : ℝ) :=
    ZLattice.covolume_div_covolume_eq_relIndex' L₀ L hsub
  have hm : 0 < m := by
    have hmR : (0 : ℝ) < m := by
      rw [← hratio]
      exact div_pos (ZLattice.covolume_pos L₀) (ZLattice.covolume_pos L)
    exact_mod_cast hmR
  have hm6 : m ≤ 6 := (SuccessiveEstimates.relIndex_le_five L b
    hb.mem_lattice hb.minimal).trans (by norm_num)
  have hest := SuccessiveEstimates.successive_basis_estimates
    (by norm_num : 0 < 3) L b hb.mem_lattice hb.minimal
  have hsqrt : Real.sqrt (3 : ℝ) ^ 3 ≤ 6 := by
    have hs : Real.sqrt (3 : ℝ) ≤ 2 := by norm_num [Real.sqrt_le_iff]
    have heq : Real.sqrt (3 : ℝ) ^ 3 = 3 * Real.sqrt (3 : ℝ) := by
      rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    rw [heq]
    linarith
  have hprod : (∏ i, ‖b i‖) ≤ 6 * |(basisMatrix b).det| := by
    calc
      (∏ i, ‖b i‖) ≤ Real.sqrt (3 : ℝ) ^ 3 * ZLattice.covolume L := hest.2.1
      _ ≤ 6 * ZLattice.covolume L :=
        mul_le_mul_of_nonneg_right hsqrt (ZLattice.covolume_pos L).le
      _ ≤ 6 * ZLattice.covolume L₀ :=
        mul_le_mul_of_nonneg_left (LatticeLowerProduct.covolume_mono_reverse L₀ L hsub)
          (by norm_num)
      _ = 6 * |(basisMatrix b).det| := by rw [covolume_span_basis_eq_det]
  apply FixedDetReduction.fixed_det_count_of_short_basis a ha hanis (basisMatrix b) m hm hm6
    (fun i => ‖b i‖) X (ZLattice.covolume L volume) (basisMatrix_det_ne_zero b)
    (basisMatrix_coord_bound b) _ _ hb.monotone_norm hX (ZLattice.covolume_pos L volume)
    hest.1 hprod S _ _ t ht hdet
  · intro i
    exact hunit (b i) (hb.mem_lattice i) (b.ne_zero i)
  · intro i
    exact (hb.monotone_norm (Fin.le_last i)).trans hlast
  · intro A hA
    exact relIndex_clears_rows L b A (hrows A hA)
  · intro A hA i j
    have hcoord : |A i j| ≤ ‖(WithLp.toLp 2 (A i) : E)‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp 2 (A i) : E) j
    exact hcoord.trans (hnorm A hA i)

lemma last_norm_le_of_matrix (L : Submodule ℤ E)
    (b : Basis (Fin 3) ℝ E) (hb : SuccessiveVectors.IsSuccessive L b)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det ≠ 0)
    (hrows : ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L)
    (X : ℝ) (hnorm : ∀ i, ‖(WithLp.toLp 2 (A i) : E)‖ ≤ X) :
    ‖b 2‖ ≤ X := by
  classical
  let v : Fin 3 → E := fun i => WithLp.toLp 2 (A i)
  have hv : LinearIndependent ℝ v := by
    convert! (Matrix.linearIndependent_rows_of_det_ne_zero hA).map'
        (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
        (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.injective) using 1
  let c : Basis (Fin 3) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank' v hv (by simp [E])
  let W := Submodule.span ℝ (SuccessiveVectors.earlier b 2)
  have hbW : b 2 ∉ W :=
    hb.independent.notMem_span_image (by simp)
  have hex : ∃ i, v i ∉ W := by
    by_contra h
    have hall : ∀ i, v i ∈ W := by simpa using h
    have hle : Submodule.span ℝ (Set.range c) ≤ W := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      convert! hall i using 1
      exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' v hv (by simp [E])) i
    rw [c.span_eq] at hle
    exact hbW (hle (by trivial))
  obtain ⟨i, hi⟩ := hex
  exact (hb.minimal 2 (v i) (hrows i) hi).trans (hnorm i)

theorem fixed_det_count
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hunit : ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖x‖)
    (X : ℝ) (hX : 1 ≤ X)
    (S : Finset (Matrix (Fin 3) (Fin 3) ℝ))
    (hrows : ∀ A ∈ S, ∀ i, (WithLp.toLp 2 (A i) : E) ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖(WithLp.toLp 2 (A i) : E)‖ ≤ X)
    (t : ℝ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      ZLattice.covolume L ^ 2 := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨A, hA⟩ := hS
    have hex : ∃ b : Basis (Fin 3) ℝ E, SuccessiveVectors.IsSuccessive L b := by
      obtain ⟨v, hv⟩ := SuccessiveVectors.exists_successive L 3 (by simp [E])
      refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hv.independent (by simp [E]), ?_⟩
      simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hv
    obtain ⟨b, hb⟩ := hex
    have hlast : ‖b 2‖ ≤ X :=
      last_norm_le_of_matrix L b hb A (by simpa only [hdet A hA] using ht)
        (hrows A hA) X (hnorm A hA)
    exact fixed_det_count_of_successive_basis a ha hanis L hunit b hb X hX hlast
      S hrows hnorm t ht hdet
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem integer_fixed_det_count
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hunit : ∀ x ∈ L, x ≠ 0 → 1 ≤ ‖x‖)
    (X : ℝ) (hX : 1 ≤ X)
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hrows : ∀ A ∈ S, ∀ i, (WithLp.toLp 2 (fun j => (A i j : ℝ)) : E) ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖(WithLp.toLp 2 (fun j => (A i j : ℝ)) : E)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      ZLattice.covolume L ^ 2 := by
  classical
  let f : Matrix (Fin 3) (Fin 3) ℤ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun A => A.map (Int.castRingHom ℝ)
  have hf : Function.Injective f := by
    intro A B h
    ext i j
    have hh := congrArg (fun C => C i j) h
    change (A i j : ℝ) = (B i j : ℝ) at hh
    exact_mod_cast hh
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injective S hf
  rw [← hcard]
  refine fixed_det_count a ha hanis L hunit X hX (S.image f) ?_ ?_ (t : ℝ)
    (by exact_mod_cast ht) ?_
  · intro A hA i
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact hrows B hB i
  · intro A hA i
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact hnorm B hB i
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    change (B.map (Int.castRingHom ℝ)).det = (t : ℝ)
    have hd := (Int.castRingHom ℝ).map_det B
    change (B.det : ℝ) = (B.map (Int.castRingHom ℝ)).det at hd
    rw [← hd, hdet B hB]

end Problem355.FixedDetLattice

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegralAmbientLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.IntegralPlaneLattice
open Module MeasureTheory

lemma castLinear_injective : Function.Injective castLinear := by
  intro v w h
  funext i
  have hi := congrArg (fun u : Ambient => u i) h
  change (v i : ℝ) = (w i : ℝ) at hi
  exact_mod_cast hi

lemma realLattice_top : realLattice ⊤ = standardLattice := by
  apply le_antisymm (realLattice_le_standard _)
  intro v hv
  choose z hz using (mem_standardLattice v).mp hv
  refine ⟨z, trivial, ?_⟩
  ext i
  exact hz i

lemma realLattice_spans (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    Submodule.span ℝ (realLattice L : Set Ambient) = ⊤ := by
  apply top_unique
  rw [← stdBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  have hi : castVec (Pi.single i 1) = stdBasis i := by
    ext j
    simp [castVec, stdBasis, EuclideanSpace.basisFun_apply, Pi.single_apply]
  have hm : E • stdBasis i ∈ realLattice L := by
    refine ⟨E • Pi.single i 1, hL _, ?_⟩
    rw [map_smul]
    exact congrArg (fun u : Ambient => E • u) hi
  have hs : (E : ℝ) • stdBasis i ∈ Submodule.span ℝ (realLattice L : Set Ambient) := by
    rw [Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.subset_span hm
  exact (Submodule.smul_mem_iff _ (by exact_mod_cast hE : (E : ℝ) ≠ 0)).mp hs

lemma realLattice_isZLattice (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) : IsZLattice ℝ (realLattice L) :=
  ⟨realLattice_spans L E hE hL⟩

lemma standardLattice_covolume : ZLattice.covolume standardLattice = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain standardLattice volume
    (ZSpan.isAddFundamentalDomain stdBasis volume)]
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped stdBasis volume)]
  change (volume (parallelepiped (EuclideanSpace.basisFun (Fin 3) ℝ))).toReal = 1
  rw [OrthonormalBasis.volume_parallelepiped]
  simp

lemma realLattice_relIndex (L : Submodule ℤ (Fin 3 → ℤ)) :
    (realLattice L).toAddSubgroup.relIndex standardLattice.toAddSubgroup =
      L.toAddSubgroup.index := by
  rw [← realLattice_top]
  change (L.toAddSubgroup.map castLinear.toAddMonoidHom).relIndex
      ((⊤ : AddSubgroup (Fin 3 → ℤ)).map castLinear.toAddMonoidHom) = _
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ castLinear_injective]
  simp

lemma one_le_norm_of_mem_standardLattice (v : Ambient) (hv : v ∈ standardLattice)
    (hv0 : v ≠ 0) : 1 ≤ ‖v‖ := by
  have hi : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv0
    ext i
    exact not_not.mp (fun hn => h ⟨i, hn⟩)
  obtain ⟨i, hi⟩ := hi
  obtain ⟨z, hz⟩ := (mem_standardLattice v).mp hv i
  have hz0 : z ≠ 0 := by
    intro h
    apply hi
    simpa [h] using hz.symm
  have ha : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz0
  calc
    (1 : ℝ) ≤ |v i| := by simpa [hz] using ha
    _ ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i

lemma one_le_norm_of_mem_realLattice (L : Submodule ℤ (Fin 3 → ℤ))
    (v : Ambient) (hv : v ∈ realLattice L) (hv0 : v ≠ 0) : 1 ≤ ‖v‖ :=
  one_le_norm_of_mem_standardLattice v (realLattice_le_standard L hv) hv0

lemma realLattice_covolume (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    ZLattice.covolume (realLattice L) = (L.toAddSubgroup.index : ℝ) := by
  let := realLattice_isZLattice L E hE hL
  have h := ZLattice.covolume_div_covolume_eq_relIndex'
    (realLattice L) standardLattice (realLattice_le_standard L)
  simpa [standardLattice_covolume, realLattice_relIndex] using h

end Problem355.IntegralPlaneLattice

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FullIntegralLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.FullIntegralLattice
open IntegralPlaneLattice

theorem fixed_det_count
    (a : ℝ) (ha : 0 ≤ a) (hanis : FixedDetReduction.AnisotropicEstimate a)
    (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
    (hL : ∀ v, m • v ∈ L)
    (X : ℝ) (hX : 1 ≤ X) (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ (a * 1000 ^ 6 * 144) * Real.log (2 * X) ^ 2 * X ^ 6 /
      (L.toAddSubgroup.index : ℝ) ^ 2 := by
  let := realLattice_isZLattice L m hm hL
  have h := FixedDetLattice.integer_fixed_det_count a ha hanis (realLattice L)
    (one_le_norm_of_mem_realLattice L) X hX S
    (fun A hA i => ⟨A i, hrows A hA i, rfl⟩) hnorm t ht hdet
  rw [realLattice_covolume L m hm hL] at h
  exact h

end Problem355.FullIntegralLattice

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.OrbitRowLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.OrbitRowLattice

open Matrix

variable {R : Type*} [CommRing R]

theorem rowImage_mul_left_unit
    (P : Matrix.GeneralLinearGroup (Fin 3) R) (C : Matrix (Fin 3) (Fin 3) R) :
    RowLattice.rowImage ((P : Matrix _ _ _) * C) = RowLattice.rowImage C := by
  ext y
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v ᵥ* (P : Matrix _ _ _), ?_⟩
    change v ᵥ* (P.val * C) = y at hv
    change (v ᵥ* P.val) ᵥ* C = y
    rw [Matrix.vecMul_vecMul]
    exact hv
  · rintro ⟨v, hv⟩
    refine ⟨v ᵥ* ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix _ _ _), ?_⟩
    change (v ᵥ* (P⁻¹).val) ᵥ* (P.val * C) = y
    calc
      (v ᵥ* (P⁻¹).val) ᵥ* (P.val * C) = v ᵥ* C := by
        rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      _ = y := hv

theorem rowImage_eq_of_mem_slOrbit
    {C A : Matrix (Fin 3) (Fin 3) R} (hA : A ∈ Section04Orbit.slOrbit C) :
    RowLattice.rowImage A = RowLattice.rowImage C := by
  obtain ⟨g, rfl⟩ := hA
  exact rowImage_mul_left_unit (Matrix.SpecialLinearGroup.toGL g) C

theorem row_mem_rowImage (C : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) :
    C i ∈ RowLattice.rowImage C := by
  refine ⟨Pi.single i 1, ?_⟩
  ext j
  simp [Matrix.single_vecMul]

theorem row_mem_integerRowLattice_of_reduction_mem_slOrbit
    (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit C) (i : Fin 3) :
    A i ∈ RowLattice.integerRowLattice h C := by
  change (fun j => (A i j : ZMod h)) ∈ RowLattice.rowImage C
  rw [← rowImage_eq_of_mem_slOrbit hA]
  exact row_mem_rowImage (A.map (Int.castRingHom (ZMod h))) i

end Problem355.OrbitRowLattice

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NonzeroWeightedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.NonzeroWeightedCount

open Matrix
open scoped BigOperators Matrix

lemma columnTriple_injective : Function.Injective columnTriple := by
  intro A B h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg (fun x : Anisotropic.Triple => x.2.1) h
  have h2 := congrArg (fun x : Anisotropic.Triple => x.2.2) h
  ext i j
  fin_cases j
  · exact congrFun h0 i
  · exact congrFun h1 i
  · exact congrFun h2 i

lemma columnTriple_det (A : IntMatrix) :
    (columnTriple A).1 ⬝ᵥ ((columnTriple A).2.1 ⨯₃ (columnTriple A).2.2) = A.det := by
  simp [columnTriple, Matrix.det_fin_three, dotProduct, Fin.sum_univ_succ,
    crossProduct, Matrix.col]
  ring

lemma anisotropicConstant_pos : 0 < anisotropicConstant :=
  Anisotropic.anisotropic_constant_pos

theorem anisotropic_estimate :
    FixedDetReduction.AnisotropicEstimate anisotropicConstant := by
  classical
  intro r u T hr hr2 hu hT
  have hcount := Anisotropic.anisotropic_count (T.image columnTriple) u hu
    (r 0) (r 1) (r 2) hr2 (hr (by decide : (1 : Fin 3) ≤ 2))
    (hr (by decide : (0 : Fin 3) ≤ 1))
    (by
      intro x hx
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
      rw [columnTriple_det]
      exact (hT A hA).1)
    (by
      intro x hx
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨(hT A hA).2 0, (hT A hA).2 1, (hT A hA).2 2⟩)
  simpa [anisotropicConstant, Finset.card_image_of_injective _ columnTriple_injective,
    Fin.prod_univ_succ, mul_assoc] using hcount

lemma latticeConstant_pos : 0 < latticeConstant := by
  unfold latticeConstant
  exact mul_pos (mul_pos anisotropicConstant_pos (by positivity)) (by norm_num)

theorem lattice_count
    (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
    (hL : ∀ v, m • v ∈ L)
    (X : ℝ) (hX : 1 ≤ X) (S : Finset IntMatrix)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖IntegralPlaneLattice.castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t) :
    (S.card : ℝ) ≤ latticeConstant * Real.log (2 * X) ^ 2 * X ^ 6 /
      (L.toAddSubgroup.index : ℝ) ^ 2 :=
  FullIntegralLattice.fixed_det_count anisotropicConstant anisotropicConstant_pos.le
    anisotropic_estimate L m hm hL X hX S hrows hnorm t ht hdet

theorem weighted_lattice_count
    (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
    (hL : ∀ v, m • v ∈ L)
    (X : ℝ) (hX : 1 ≤ X) (S : Finset IntMatrix)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖IntegralPlaneLattice.castVec (A i)‖ ≤ X)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t)
    (W : IntMatrix → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hW : ∀ A ∈ S, W A ≤ w) :
    (∑ A ∈ S, W A) ≤ (w * latticeConstant) * Real.log (2 * X) ^ 2 * X ^ 6 /
      (L.toAddSubgroup.index : ℝ) ^ 2 := by
  calc
    (∑ A ∈ S, W A) ≤ ∑ _A ∈ S, w := Finset.sum_le_sum hW
    _ = w * (S.card : ℝ) := by simp [mul_comm]
    _ ≤ w * (latticeConstant * Real.log (2 * X) ^ 2 * X ^ 6 /
        (L.toAddSubgroup.index : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (lattice_count L m hm hL X hX S hrows hnorm t ht hdet) hw
    _ = _ := by ring

lemma boxConstant_pos : 0 < boxConstant := by
  unfold boxConstant
  exact mul_pos (mul_pos latticeConstant_pos (by norm_num)) (by positivity)

theorem weighted_box_count
    (L : Submodule ℤ (Fin 3 → ℤ)) (m : ℤ) (hm : m ≠ 0)
    (hL : ∀ v, m • v ∈ L)
    (N : ℝ) (hN : 1 ≤ N) (S : Finset IntMatrix)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ L)
    (hnorm : ∀ A ∈ S, ∀ i, ‖IntegralPlaneLattice.castVec (A i)‖ ≤ 4 * N)
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t)
    (W : IntMatrix → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hW : ∀ A ∈ S, W A ≤ w) :
    (∑ A ∈ S, W A) ≤ (w * boxConstant) * Real.log (2 * N) ^ 2 * N ^ 6 /
      (L.toAddSubgroup.index : ℝ) ^ 2 := by
  have hcount := weighted_lattice_count L m hm hL (4 * N) (by linarith)
    S hrows hnorm t ht hdet W w hw hW
  have hlog := FixedDetReduction.log_radius_bound N (4 * N) hN
    (by linarith) (by nlinarith)
  have hlog0 : 0 ≤ Real.log (2 * (4 * N)) := Real.log_nonneg (by linarith)
  have hlog2 := pow_le_pow_left₀ hlog0 hlog 2
  have hfactor : 0 ≤ w * latticeConstant := mul_nonneg hw latticeConstant_pos.le
  calc
    (∑ A ∈ S, W A) ≤ _ := hcount
    _ ≤ (w * latticeConstant) * (12 * Real.log (2 * N)) ^ 2 * (4 * N) ^ 6 /
        (L.toAddSubgroup.index : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog2 hfactor) (by positivity)) (sq_nonneg _)
    _ = _ := by unfold boxConstant; ring

lemma row_norm_le_four_mul (A : IntMatrix) (N : ℝ) (hN : 0 ≤ N)
    (hbox : ∀ j, Homogeneous.InBox N (fun i => (A i j : ℝ))) (i : Fin 3) :
    ‖IntegralPlaneLattice.castVec (A i)‖ ≤ 4 * N := by
  have hcoord : ∀ j, |(IntegralPlaneLattice.castVec (A i)) j| ≤ 2 * N := by
    intro j
    have hj := hbox j
    fin_cases i
    · change |(A 0 j : ℝ)| ≤ 2 * N
      rw [abs_of_nonneg hj.1]
      linarith [hj.2.1]
    · change |(A 1 j : ℝ)| ≤ 2 * N
      rw [abs_of_nonneg hj.2.2.1]
      linarith [hj.2.2.2.1]
    · change |(A 2 j : ℝ)| ≤ 2 * N
      rw [abs_of_nonneg (hN.trans hj.2.2.2.2.1)]
      exact hj.2.2.2.2.2.le
  have h := LatticeCoordinates.euclidean_norm_le_of_coord_bound
    (IntegralPlaneLattice.castVec (A i)) (2 * N) (by positivity) hcoord
  have hs : Real.sqrt (3 : ℝ) ≤ 2 := by norm_num [Real.sqrt_le_iff]
  simp only [Fintype.card_fin] at h
  apply h.trans
  calc
    Real.sqrt (3 : ℝ) * (2 * N) ≤ 2 * (2 * N) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 4 * N := by ring

theorem weighted_orbit_count
    (B k b e : ℕ) (hB : 0 < B) (hb : b ≤ k) (he : e ≤ k) (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix _ _ _) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
        (Q : Matrix _ _ _))
    (N : ℝ) (hN : 1 ≤ N) (S : Finset IntMatrix)
    (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
      Section04Orbit.slOrbit C)
    (hbox : ∀ A ∈ S, ∀ j, Homogeneous.InBox N (fun i => (A i j : ℝ)))
    (t : ℤ) (ht : t ≠ 0) (hdet : ∀ A ∈ S, A.det = t)
    (W : IntMatrix → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hW : ∀ A ∈ S, W A ≤ w) :
    (∑ A ∈ S, W A) ≤ (w * boxConstant) * Real.log (2 * N) ^ 2 * N ^ 6 /
      ((B : ℝ) ^ b * (B : ℝ) ^ e) ^ 2 := by
  let : NeZero B := ⟨ne_of_gt hB⟩
  let L := (RowLattice.integerRowLattice (B ^ k) C).toIntSubmodule
  have hL : ∀ v, (B ^ e : ℤ) • v ∈ L := by
    intro v
    change (B ^ e : ℤ) • v ∈ RowLattice.integerRowLattice (B ^ k) C
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact RowLattice.nsmul_mem_integerRowLattice_prime_power B k b e hbe C P Q hC v
  have hm : (B ^ e : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero e (ne_of_gt hB)
  have hc := weighted_box_count L (B ^ e : ℤ) hm hL N hN S
    (fun A hA i => OrbitRowLattice.row_mem_integerRowLattice_of_reduction_mem_slOrbit
      (B ^ k) C A (horbit A hA) i)
    (fun A hA i => row_norm_le_four_mul A N (by linarith) (hbox A hA) i)
    t ht hdet W w hw hW
  have hi : L.toAddSubgroup.index = B ^ b * B ^ e :=
    RowLattice.integerRowLattice_index_prime_power B k b e hb he C P Q hC
  simpa only [hi, Nat.cast_mul, Nat.cast_pow] using hc

end Problem355.NonzeroWeightedCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimePowerRowData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PrimePowerRowData

open Matrix PrimitiveNormal PairingDivisor

variable {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}

theorem larger_divisor_isUnit (d : PrimePowerData B k C) {q : ℕ}
    (hcop : (B ^ k).Coprime q) :
    IsUnit (((B ^ d.e : ℕ) : ℤ) : ZMod q) := by
  have he : (B ^ d.e).Coprime q :=
    hcop.of_dvd_left (Nat.pow_dvd_pow B d.e_le_k)
  simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime (B ^ d.e) q).mpr he

theorem orbit_rows_mem (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : A.map (Int.castRingHom (ZMod (B ^ k))) ∈ Section04Orbit.slOrbit C)
    (i : Fin 3) : A i ∈ rowModule C :=
  OrbitRowLattice.row_mem_integerRowLattice_of_reduction_mem_slOrbit (B ^ k) C A hA i

end Problem355.PrimePowerRowData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SmallDeterminantWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.SmallDeterminantWeight

theorem intCast_ne_zero_of_abs_lt {q : ℕ} {t : ℤ}
    (ht : t ≠ 0) (hsmall : |t| < (q : ℤ)) : (t : ZMod q) ≠ 0 := by
  intro hzero
  have hdvd : (q : ℤ) ∣ t := (ZMod.intCast_zmod_eq_zero_iff_dvd t q).mp hzero
  have hle := Int.le_abs_of_dvd ht hdvd
  omega

theorem det_map_ne_zero {q : ℕ} (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det ≠ 0) (hsmall : |A.det| < (q : ℤ)) :
    (A.map (Int.castRingHom (ZMod q))).det ≠ 0 := by
  have hd := (Int.castRingHom (ZMod q)).map_det A
  change (A.det : ZMod q) = (A.map (Int.castRingHom (ZMod q))).det at hd
  rw [← hd]
  exact intCast_ne_zero_of_abs_lt hdet hsmall

theorem affineIndependent_columns {q : ℕ} [Fact q.Prime]
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det ≠ 0) (hsmall : |A.det| < (q : ℤ)) :
    AffineIndependent (ZMod q) (fun j i => (A i j : ZMod q)) := by
  exact (Matrix.linearIndependent_cols_of_det_ne_zero
    (det_map_ne_zero A hdet hsmall)).affineIndependent

end Problem355.SmallDeterminantWeight

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroCountNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.ZeroCountNormalization

open Matrix
open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

theorem log_four_mul_le_two_log_two_mul {N : ℝ} (hN : 1 ≤ N) :
    Real.log (4 * N) ≤ 2 * Real.log (2 * N) := by
  have hpos : 0 < 4 * N := by positivity
  have hscale : 4 * N ≤ (2 * N) ^ 2 := by nlinarith
  have h := Real.log_le_log hpos hscale
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem normal_log_le_squared_log {N : ℝ} (hN : 1 ≤ N) :
    Real.log (4 * N) / Real.log 2 ≤
      (2 / (Real.log 2) ^ 2) * (Real.log (2 * N)) ^ 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlower : Real.log (2 : ℝ) ≤ Real.log (2 * N) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hratio : 1 ≤ Real.log (2 * N) / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by simpa using hlower)
  calc
    Real.log (4 * N) / Real.log 2 ≤
        (2 * Real.log (2 * N)) / Real.log 2 :=
      div_le_div_of_nonneg_right (log_four_mul_le_two_log_two_mul hN) hlog2.le
    _ = 2 * (Real.log (2 * N) / Real.log 2) := by ring
    _ ≤ 2 * (Real.log (2 * N) / Real.log 2) ^ 2 := by nlinarith
    _ = (2 / (Real.log 2) ^ 2) * (Real.log (2 * N)) ^ 2 := by ring

end Problem355.ZeroCountNormalization

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroRowData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PrimePowerData

open ZeroDeterminantCount

variable {B k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))}

theorem toZeroRowData_index_real (d : PrimePowerData B k C) (hB : B.Prime) :
    ((d.toZeroRowData hB).I : ℝ) = (B : ℝ) ^ d.b * (B : ℝ) ^ d.e := by
  simp only [toZeroRowData_I, pow_add, Nat.cast_mul, Nat.cast_pow]

theorem orbit_rows_mem_toZeroRowData (d : PrimePowerData B k C) (hB : B.Prime)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : A.map (Int.castRingHom (ZMod (B ^ k))) ∈ Section04Orbit.slOrbit C)
    (i : Fin 3) : A i ∈ (d.toZeroRowData hB).L :=
  PrimePowerRowData.orbit_rows_mem A hA i

theorem toZeroRowData_E_isUnit (d : PrimePowerData B k C) (hB : B.Prime)
    {q : ℕ} (hcop : (B ^ k).Coprime q) :
    IsUnit ((d.toZeroRowData hB).E : ZMod q) := by
  simpa only [toZeroRowData_E, Int.cast_natCast] using
    PrimePowerRowData.larger_divisor_isUnit d hcop

end Problem355.PrimePowerData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.UniformFixedFiberCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.UniformFixedFiberCount

open Finset

lemma normal_log_le_log_square {N : ℝ} (hN : 1 ≤ N) :
    Real.log (4 * N) / Real.log 2 ≤
      (2 / (Real.log 2) ^ 2) * (Real.log (2 * N)) ^ 2 :=
  ZeroCountNormalization.normal_log_le_squared_log hN

theorem sum_fiber_le {α : Type*} (S : Finset α) (d : α → ℤ) (W : α → ℝ)
    {N U Czero Cnonzero : ℝ} (hN : 1 ≤ N) (hU : 0 ≤ U)
    (hCzero : 0 ≤ Czero) (hCnonzero : 0 ≤ Cnonzero)
    (hzero : (∑ x ∈ S.filter (fun x => d x = 0), W x) ≤
      Czero * (Real.log (4 * N) / Real.log 2) * U)
    (t : ℤ) (hnonzero : t ≠ 0 →
      (∑ x ∈ S.filter (fun x => d x = t), W x) ≤
        Cnonzero * (Real.log (2 * N)) ^ 2 * U) :
    (∑ x ∈ S.filter (fun x => d x = t), W x) ≤
      commonConstant Czero Cnonzero * (Real.log (2 * N)) ^ 2 * U := by
  classical
  by_cases ht : t = 0
  · subst t
    apply hzero.trans
    have habs := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (normal_log_le_log_square hN) hCzero) hU
    have hextra : 0 ≤ Cnonzero * (Real.log (2 * N)) ^ 2 * U := by positivity
    unfold commonConstant
    simp only [div_eq_mul_inv] at habs ⊢
    nlinarith only [habs, hextra]
  · apply (hnonzero ht).trans
    have hextra : 0 ≤ (2 * Czero / (Real.log 2) ^ 2) *
        (Real.log (2 * N)) ^ 2 * U := by positivity
    unfold commonConstant
    simp only [div_eq_mul_inv] at hextra ⊢
    nlinarith only [hextra]

theorem matrix_fiber_le_of_zero_count
    {B k q : ℕ} (hB : 0 < B) [Fact q.Prime]
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) (d : PrimePowerData B k C)
    (N : ℝ) (hN : 1 ≤ N) (S : Finset NonzeroWeightedCount.IntMatrix)
    (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
      Section04Orbit.slOrbit C)
    (hbox : ∀ A ∈ S, ∀ j, Homogeneous.InBox N (fun i => (A i j : ℝ)))
    (W : NonzeroWeightedCount.IntMatrix → ℝ) (w Czero : ℝ)
    (hw : 0 ≤ w) (hCzero : 0 ≤ Czero)
    (hW : ∀ A ∈ S,
      AffineIndependent (ZMod q) (fun j i => (A i j : ZMod q)) → W A ≤ w)
    (hzero : (∑ A ∈ S.filter (fun A => A.det = 0), W A) ≤
      Czero * (Real.log (4 * N) / Real.log 2) * N ^ 6 /
        ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2)
    (t : ℤ) (htq : |t| < (q : ℤ)) :
    (∑ A ∈ S.filter (fun A => A.det = t), W A) ≤
      commonConstant Czero (w * NonzeroWeightedCount.boxConstant) *
        Real.log (2 * N) ^ 2 * N ^ 6 /
          ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
  classical
  have hz : (∑ A ∈ S.filter (fun A => A.det = 0), W A) ≤
      Czero * (Real.log (4 * N) / Real.log 2) *
        (N ^ 6 / ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2) := by
    simpa only [mul_div_assoc] using hzero
  have hdiag : C = (d.left : Matrix _ _ _) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ d.b) (B ^ d.e) *
        (d.right : Matrix _ _ _) := by
    simpa only [DiagonalStabilizer.diagonal3, Nat.cast_pow] using d.diagonalization
  have hb := sum_fiber_le S Matrix.det W hN
    (show 0 ≤ N ^ 6 / ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 by positivity)
    hCzero (mul_nonneg hw NonzeroWeightedCount.boxConstant_pos.le) hz t (by
      intro ht
      have hc := NonzeroWeightedCount.weighted_orbit_count B k d.b d.e hB
        d.b_le_k d.e_le_k d.b_le_e C d.left d.right hdiag N hN
        (S.filter (fun A => A.det = t))
        (fun A hA => horbit A (Finset.mem_filter.mp hA).1)
        (fun A hA => hbox A (Finset.mem_filter.mp hA).1)
        t ht (fun A hA => (Finset.mem_filter.mp hA).2) W w hw (by
          intro A hA
          obtain ⟨hAS, hAt⟩ := Finset.mem_filter.mp hA
          exact hW A hAS (SmallDeterminantWeight.affineIndependent_columns A
            (by simpa only [hAt] using ht) (by simpa only [hAt] using htq)))
      simpa only [mul_div_assoc] using hc)
  simpa only [mul_div_assoc] using hb

lemma box_height_ne_zero {N : ℕ} (hN : 1 ≤ N)
    (A : NonzeroWeightedCount.IntMatrix)
    (hbox : ∀ j, Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ)))
    (j : Fin 3) : A 2 j ≠ 0 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hp : (0 : ℝ) < A 2 j := hNp.trans_le (hbox j).2.2.2.2.1
  intro hz
  simp only [hz, Int.cast_zero, lt_self_iff_false] at hp

lemma box_abs_le_two_mul {N : ℕ} (A : NonzeroWeightedCount.IntMatrix)
    (hbox : ∀ j, Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ)))
    (i j : Fin 3) : |A i j| ≤ (2 * N : ℕ) := by
  have hr : |(A i j : ℝ)| ≤ 2 * (N : ℝ) := by
    have hj := hbox j
    fin_cases i
    · change |(A 0 j : ℝ)| ≤ 2 * (N : ℝ)
      rw [abs_of_nonneg hj.1]
      linarith [hj.2.1, Nat.cast_nonneg (α := ℝ) N]
    · change |(A 1 j : ℝ)| ≤ 2 * (N : ℝ)
      rw [abs_of_nonneg hj.2.2.1]
      linarith [hj.2.2.2.1, Nat.cast_nonneg (α := ℝ) N]
    · change |(A 2 j : ℝ)| ≤ 2 * (N : ℝ)
      rw [abs_of_nonneg ((Nat.cast_nonneg N).trans hj.2.2.2.2.1)]
      exact hj.2.2.2.2.2.le
  exact_mod_cast hr

theorem matrix_fiber_le_oai
    {B k q : ℕ} (hB : B.Prime) [Fact q.Prime]
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) (d : PrimePowerData B k C)
    (L : AuxiliarySampling.Law q ((B ^ k) ^ 2))
    (hcop : (B ^ k).Coprime q) (hparam : ((B : ℝ) ^ k) ^ 26 ≤ (q : ℝ))
    (N : ℕ) (hN : 1 ≤ N) (S : Finset NonzeroWeightedCount.IntMatrix)
    (horbit : ∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
      Section04Orbit.slOrbit C)
    (hbox : ∀ A ∈ S, ∀ j, Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ)))
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      PlaneRowTransport.projectedColumn A i ≠ PlaneRowTransport.projectedColumn A j)
    (t : ℤ) (htq : |t| < (q : ℤ)) :
    (∑ A ∈ S.filter (fun A => A.det = t),
      LiftingProbability.auxiliaryWeight q L.size L.weight L.sets
        (A.map (Int.castRingHom (ZMod q))).col) ≤
      countConstant * Real.log (2 * (N : ℝ)) ^ 2 * (N : ℝ) ^ 6 /
        ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
  classical
  have hz := AuxiliaryZeroCount.weighted_count_le_log (d.toZeroRowData hB) q N hN
    (d.toZeroRowData_E_isUnit hB hcop)
    (by simpa only [PrimePowerData.toZeroRowData_h] using hparam) L
    (S.filter (fun A => A.det = 0))
    (fun A hA => (Finset.mem_filter.mp hA).2)
    (fun A hA i => d.orbit_rows_mem_toZeroRowData hB A
      (horbit A (Finset.mem_filter.mp hA).1) i)
    (fun A hA => box_height_ne_zero hN A (hbox A (Finset.mem_filter.mp hA).1))
    (fun A hA => hproj A (Finset.mem_filter.mp hA).1)
    (fun A hA => box_abs_le_two_mul A (hbox A (Finset.mem_filter.mp hA).1))
  have hzero : (∑ A ∈ S.filter (fun A => A.det = 0),
      LiftingProbability.auxiliaryWeight q L.size L.weight L.sets
        (A.map (Int.castRingHom (ZMod q))).col) ≤
      AuxiliaryZeroCount.countConstant * (Real.log (4 * (N : ℝ)) / Real.log 2) *
        (N : ℝ) ^ 6 / ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2 := by
    rw [d.toZeroRowData_index_real hB] at hz
    convert hz using 1
    ring
  exact matrix_fiber_le_of_zero_count hB.pos C d (N : ℝ)
    (by exact_mod_cast hN) S horbit hbox
    (fun A => LiftingProbability.auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col)
    8 AuxiliaryZeroCount.countConstant (by norm_num)
    AuxiliaryZeroCount.countConstant_nonneg
    (fun A _ hAI => L.weight_le_eight _ hAI) hzero t htq

end Problem355.UniformFixedFiberCount

end

end OAI
end

theorem solution : type_of% @OAI.Problem355.UniformFixedFiberCount.matrix_fiber_le_oai := @OAI.Problem355.UniformFixedFiberCount.matrix_fiber_le_oai
