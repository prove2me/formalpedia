-- Prove2me | solution 1 for OAI.Problem355.AuxiliaryZeroCount.weighted_count_le_log
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:17:33.518403+00:00
-- url     : https://prove2.me/submissions/1b15d0ae-8ad9-40e3-870e-82e6eae1acce

import Mathlib
import Definitions.Def_OAIQWHT000

section
-- module Solutions.OAIQW_Problem355.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AffineShellCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ZeroShell

open scoped BigOperators

theorem affine_shell_sum_le {α : Type*} (S : Finset α)
    (f g len J : α → ℝ) (R I A C : ℝ)
    (hR : 0 < R) (hI : 0 < I) (hA : 0 ≤ A)
    (hg : ∀ x ∈ S, 0 < g x) (hlen : ∀ x ∈ S, R ≤ len x)
    (hJ : ∀ x ∈ S, J x = I * len x / g x)
    (hf : ∀ x ∈ S, f x ≤ A / (J x) ^ 3)
    (hmoment : ∑ x ∈ S, (g x) ^ 3 ≤ C * R ^ 3 * I) :
    ∑ x ∈ S, f x ≤ A * C / I ^ 2 := by
  have hpoint : ∀ x ∈ S, f x ≤ (A / (I ^ 3 * R ^ 3)) * (g x) ^ 3 := by
    intro x hx
    have hgx := hg x hx
    have hlx : 0 < len x := lt_of_lt_of_le hR (hlen x hx)
    have hlen3 : R ^ 3 ≤ (len x) ^ 3 := pow_le_pow_left₀ hR.le (hlen x hx) 3
    have hden : I ^ 3 * R ^ 3 ≤ I ^ 3 * (len x) ^ 3 :=
      mul_le_mul_of_nonneg_left hlen3 (pow_nonneg hI.le 3)
    calc
      f x ≤ A / (J x) ^ 3 := hf x hx
      _ = (A * (g x) ^ 3) / (I ^ 3 * (len x) ^ 3) := by
        rw [hJ x hx]
        field_simp
      _ ≤ (A * (g x) ^ 3) / (I ^ 3 * R ^ 3) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = (A / (I ^ 3 * R ^ 3)) * (g x) ^ 3 := by ring
  calc
    (∑ x ∈ S, f x) ≤ ∑ x ∈ S, (A / (I ^ 3 * R ^ 3)) * (g x) ^ 3 :=
      Finset.sum_le_sum hpoint
    _ = (A / (I ^ 3 * R ^ 3)) * ∑ x ∈ S, (g x) ^ 3 := by rw [Finset.mul_sum]
    _ ≤ (A / (I ^ 3 * R ^ 3)) * (C * R ^ 3 * I) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = A * C / I ^ 2 := by
      field_simp

end Problem355.ZeroShell

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

theorem sum_le_of_single_dyadic_shell_estimates {α : Type*} [DecidableEq α]
    (S : Finset α) (u weight : α → ℝ) {R A : ℝ}
    (hR : 1 ≤ R) (hA : 0 ≤ A)
    (hweight : ∀ x ∈ S, 0 ≤ weight x)
    (hvalue : ∀ x ∈ S, 1 ≤ u x ∧ u x ≤ R)
    (hshell : ∀ i : ℕ,
      ∑ x ∈ S with ((2 : ℝ) ^ i ≤ u x ∧ u x < 2 ^ (i + 1)), weight x ≤ A) :
    ∑ x ∈ S, weight x ≤ A * (Real.log (2 * R) / Real.log 2) := by
  have h := sum_le_of_dyadic_shell_estimates S u (fun _ => 1) weight
    hR (by norm_num : (1 : ℝ) ≤ 1) hA hweight
    (fun x hx => ⟨(hvalue x hx).1, (hvalue x hx).2, le_rfl, le_rfl⟩)
  have hs : ∀ i j : ℕ,
      ∑ x ∈ S with ((2 : ℝ) ^ i ≤ u x ∧ u x < 2 ^ (i + 1) ∧
        (2 : ℝ) ^ j ≤ 1 ∧ (1 : ℝ) < 2 ^ (j + 1)), weight x ≤ A := by
    intro i j
    apply le_trans _ (hshell i)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      obtain ⟨hxS, hx⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxS, hx.1, hx.2.1⟩
    · intro x hx _
      exact hweight x (Finset.mem_filter.mp hx).1
  simpa [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))] using h hs

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

lemma coordinate_abs_le_of_factor {v w : Vector} {g : ℤ}
    (hg : 0 < g) (hscale : v = g • w) (i : Fin 3) : |w i| ≤ |v i| := by
  have hg1 : 1 ≤ g := hg
  rw [hscale, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hg]
  nlinarith [abs_nonneg (w i)]

lemma mulVec_rowNormals (A : Matrix (Fin 3) (Fin 3) ℤ) (i j : Fin 3) :
    (A *ᵥ rowNormals A i) j = if j = i then A.det else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [rowNormals, mulVec, vecHead, vecTail, cross_apply, det_fin_three] <;> ring

lemma exists_rowNormal_ne_zero (A : Matrix (Fin 3) (Fin 3) ℤ)
    (h : (fun j => A j 0) ⨯₃ (fun j => A j 1) ≠ 0) :
    ∃ i : Fin 3, rowNormals A i ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  ext i
  fin_cases i
  · simpa [rowNormals, cross_apply, mul_comm] using congrFun (hn 0) 2
  · simpa [rowNormals, cross_apply, mul_comm] using congrFun (hn 1) 2
  · simpa [rowNormals, cross_apply, mul_comm] using congrFun (hn 2) 2

lemma coefficients_zero_of_cross_ne_zero (u v : Vector) (h : u ⨯₃ v ≠ 0)
    (a b : ℤ) (hab : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  have ha : a • (u ⨯₃ v) = 0 := by
    calc
      a • (u ⨯₃ v) = (a • u + b • v) ⨯₃ v := by
        ext i
        fin_cases i <;> simp [cross_apply, Pi.smul_apply] <;> ring
      _ = 0 := by rw [hab]; simp
  have hb : b • (u ⨯₃ v) = 0 := by
    calc
      b • (u ⨯₃ v) = u ⨯₃ (a • u + b • v) := by
        ext i
        fin_cases i <;> simp [cross_apply, Pi.smul_apply] <;> ring
      _ = 0 := by rw [hab]; simp
  exact ⟨(smul_eq_zero.mp ha).resolve_right h, (smul_eq_zero.mp hb).resolve_right h⟩

lemma kernel_coordinates_ne_zero (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hpair : ∀ i j : Fin 3, i ≠ j → Aᵀ i ⨯₃ Aᵀ j ≠ 0)
    (w : Vector) (hw : w ≠ 0) (hk : A *ᵥ w = 0) :
    ∀ i : Fin 3, w i ≠ 0 := by
  have hrow (j : Fin 3) : A j 0 * w 0 + A j 1 * w 1 + A j 2 * w 2 = 0 := by
    simpa only [mulVec, vec3_dotProduct, Pi.zero_apply] using congrFun hk j
  intro i hi
  fin_cases i
  · change w 0 = 0 at hi
    have hrel : w 1 • Aᵀ 1 + w 2 • Aᵀ 2 = 0 := by
      ext j
      simpa [hi, mul_comm] using hrow j
    obtain ⟨h1, h2⟩ := coefficients_zero_of_cross_ne_zero _ _ (hpair 1 2 (by decide)) _ _ hrel
    apply hw
    ext j
    fin_cases j <;> simp [hi, h1, h2]
  · change w 1 = 0 at hi
    have hrel : w 0 • Aᵀ 0 + w 2 • Aᵀ 2 = 0 := by
      ext j
      simpa [hi, mul_comm] using hrow j
    obtain ⟨h0, h2⟩ := coefficients_zero_of_cross_ne_zero _ _ (hpair 0 2 (by decide)) _ _ hrel
    apply hw
    ext j
    fin_cases j <;> simp [hi, h0, h2]
  · change w 2 = 0 at hi
    have hrel : w 0 • Aᵀ 0 + w 1 • Aᵀ 1 = 0 := by
      ext j
      simpa [hi, mul_comm] using hrow j
    obtain ⟨h0, h1⟩ := coefficients_zero_of_cross_ne_zero _ _ (hpair 0 1 (by decide)) _ _ hrel
    apply hw
    ext j
    fin_cases j <;> simp [hi, h0, h1]

lemma abs_minor_le (a b c d X : ℤ) (hX : 0 ≤ X)
    (ha : |a| ≤ X) (hb : |b| ≤ X) (hc : |c| ≤ X) (hd : |d| ≤ X) :
    |a * b - c * d| ≤ 2 * X ^ 2 := by
  calc
    |a * b - c * d| ≤ |a * b| + |c * d| := by simpa using abs_sub_le (a * b) 0 (c * d)
    _ = |a| * |b| + |c| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ X * X + X * X := add_le_add
      (mul_le_mul ha hb (abs_nonneg _) hX)
      (mul_le_mul hc hd (abs_nonneg _) hX)
    _ = 2 * X ^ 2 := by ring

lemma cross_coordinate_bound (u v : Vector) (X : ℤ) (hX : 0 ≤ X)
    (hu : ∀ i, |u i| ≤ X) (hv : ∀ i, |v i| ≤ X) (i : Fin 3) :
    |(u ⨯₃ v) i| ≤ 2 * X ^ 2 := by
  fin_cases i <;> simp only [cross_apply] <;>
    apply abs_minor_le _ _ _ _ X hX <;> first | apply hu | apply hv

theorem exists_primitive_right_null (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det = 0)
    (hpair : ∀ i j : Fin 3, i ≠ j → Aᵀ i ⨯₃ Aᵀ j ≠ 0)
    (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ i j, |A i j| ≤ X) :
    ∃ w : Vector, IsPrimitive w ∧ A *ᵥ w = 0 ∧
      (∀ i, w i ≠ 0) ∧ (∀ i, |w i| ≤ 2 * X ^ 2) := by
  obtain ⟨i, hi⟩ := exists_rowNormal_ne_zero A (hpair 0 1 (by decide))
  obtain ⟨g, hg, w, hw, hscale⟩ := exists_primitive_factor (rowNormals A i) hi
  have hk : A *ᵥ w = 0 := by
    ext j
    have hj : A j ⬝ᵥ rowNormals A i = 0 := by
      simpa [hdet, mulVec] using mulVec_rowNormals A i j
    rw [hscale, dotProduct_smul, smul_eq_mul] at hj
    exact (mul_eq_zero.mp hj).resolve_left (ne_of_gt hg)
  refine ⟨w, hw, hk, kernel_coordinates_ne_zero A hpair w hw.ne_zero hk, ?_⟩
  intro j
  apply le_trans (coordinate_abs_le_of_factor hg hscale j)
  fin_cases i <;> simp only [rowNormals] <;>
    apply cross_coordinate_bound _ _ X hX <;> apply hbound

lemma cross_ne_zero_of_projective_ne (u v : Vector)
    (hu : u 2 ≠ 0) (hv : v 2 ≠ 0)
    (hproj : ((u 0 : ℝ) / u 2, (u 1 : ℝ) / u 2) ≠
      ((v 0 : ℝ) / v 2, (v 1 : ℝ) / v 2)) : u ⨯₃ v ≠ 0 := by
  intro hc
  have h0 : u 1 * v 2 - u 2 * v 1 = 0 := by
    simpa [cross_apply] using congrFun hc 0
  have h1 : u 2 * v 0 - u 0 * v 2 = 0 := by
    simpa [cross_apply] using congrFun hc 1
  have huR : (u 2 : ℝ) ≠ 0 := by exact_mod_cast hu
  have hvR : (v 2 : ℝ) ≠ 0 := by exact_mod_cast hv
  apply hproj
  apply Prod.ext
  · apply (div_eq_div_iff huR hvR).mpr
    have h1R : (u 2 : ℝ) * v 0 - (u 0 : ℝ) * v 2 = 0 := by exact_mod_cast h1
    nlinarith
  · apply (div_eq_div_iff huR hvR).mpr
    have h0R : (u 1 : ℝ) * v 2 - (u 2 : ℝ) * v 1 = 0 := by exact_mod_cast h0
    nlinarith

theorem exists_primitive_right_null_of_projections (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det = 0) (hheight : ∀ i, A 2 i ≠ 0)
    (hproj : ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ i j, |A i j| ≤ X) :
    ∃ w : Vector, IsPrimitive w ∧ A *ᵥ w = 0 ∧
      (∀ i, w i ≠ 0) ∧ (∀ i, |w i| ≤ 2 * X ^ 2) := by
  apply exists_primitive_right_null A hdet _ X hX hbound
  intro i j hij
  exact cross_ne_zero_of_projective_ne _ _ (hheight i) (hheight j) (hproj i j hij)

lemma norm_le_three_mul_of_coordinate_bound (v : Vector) (R : ℝ)
    (hR : 0 ≤ R) (h : ∀ i, |(v i : ℝ)| ≤ R) : ‖toEuclidean v‖ ≤ 3 * R := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h0 := sq_le_sq₀ (abs_nonneg (v 0 : ℝ)) hR |>.mpr (h 0)
  have h1 := sq_le_sq₀ (abs_nonneg (v 1 : ℝ)) hR |>.mpr (h 1)
  have h2 := sq_le_sq₀ (abs_nonneg (v 2 : ℝ)) hR |>.mpr (h 2)
  simp only [sq_abs] at h0 h1 h2
  simp [toEuclidean, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg R]

lemma one_le_norm_of_ne_zero (v : Vector) (hv : v ≠ 0) : 1 ≤ ‖toEuclidean v‖ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  have hi1 : (1 : ℤ) ≤ |v i| := abs_pos.mpr hi
  calc
    (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast hi1
    _ = ‖(toEuclidean v).ofLp i‖ := by simp [toEuclidean]
    _ ≤ ‖toEuclidean v‖ := PiLp.norm_apply_le _ _

end Problem355.PrimitiveNormal

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliaryIntegralSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.AuxiliarySet

open scoped BigOperators

theorem coordinate_abs_le_of_euclidean_norm_le
    {x : PrimitiveNormal.Vector} {H : ℕ}
    (hx : ‖PrimitiveNormal.toEuclidean x‖ ≤ (H : ℝ)) :
    ∀ i, |x i| ≤ (H : ℤ) := by
  intro i
  have hi := (PiLp.norm_apply_le (PrimitiveNormal.toEuclidean x) i).trans hx
  have hi' : |(x i : ℝ)| ≤ (H : ℝ) := by
    simpa [PrimitiveNormal.toEuclidean, Real.norm_eq_abs] using hi
  exact_mod_cast hi'

theorem cast_mulVec_eq_zero {q : ℕ}
    {A : Matrix (Fin 3) (Fin 3) ℤ} {x : Fin 3 → ℤ}
    (hx : A.mulVec x = 0) :
    (A.map (Int.castRingHom (ZMod q))).mulVec (fun i => (x i : ZMod q)) = 0 := by
  funext i
  have hi := congrArg (fun z : ℤ => (z : ZMod q)) (congrFun hx i)
  simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using hi

end Problem355.AuxiliarySet

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LiftingProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.LiftingProbability

 theorem inclusionMass_nonneg {Ω B : Type*} [Fintype Ω]
    (w : Ω → ℝ) (V : Ω → Finset B) (hw : ∀ ω, 0 ≤ w ω) (b : Fin 3 → B) :
    0 ≤ inclusionMass w V b := by
  classical
  unfold inclusionMass
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp_all

end Problem355.LiftingProbability

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliarySamplingSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.AuxiliarySampling

open scoped BigOperators
open LiftingProbability

namespace Law

variable {q H : ℕ} [Fact q.Prime]

theorem exists_outcome_of_weight_pos (L : Law q H) (p : Fin 3 → Fin 3 → ZMod q)
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets p) :
    ∃ ω : L.Outcome, ∀ i, p i ∈ L.sets ω := by
  classical
  have hinc : 0 < inclusionMass L.weight L.sets p := by
    by_contra hn
    have hn' : inclusionMass L.weight L.sets p ≤ 0 := le_of_not_gt hn
    have hbad : auxiliaryWeight q L.size L.weight L.sets p ≤ 0 := by
      unfold auxiliaryWeight
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hn'
    exact (not_le_of_gt hpositive) hbad
  by_contra hn
  have hnone : ∀ ω : L.Outcome, ¬ (∀ i, p i ∈ L.sets ω) := by
    intro ω hω
    exact hn ⟨ω, hω⟩
  have hz : inclusionMass L.weight L.sets p = 0 := by
    unfold inclusionMass
    apply Finset.sum_eq_zero
    intro ω hω
    exact ite_eq_right (hnone ω)
  exact (ne_of_gt hinc) hz

theorem support_of_weight_pos (L : Law q H) (p : Fin 3 → Fin 3 → ZMod q)
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets p) :
    (∀ i, p i ≠ 0) ∧
      (AffineIndependent (ZMod q) p ∨ ∃ i j, i ≠ j ∧ p i = p j) ∧
      (AffineIndependent (ZMod q) p → ∀ x : Fin 3 → ℤ,
        (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
          (∑ i, (x i : ZMod q) • p i) ≠ 0) := by
  classical
  obtain ⟨ω, hω⟩ := L.exists_outcome_of_weight_pos p hpositive
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact L.zero_not_mem ω (hi ▸ hω i)
  · by_cases hinj : Function.Injective p
    · exact Or.inl (AuxiliarySet.affineIndependent_of_mem_cap (L.isCap ω) hω hinj)
    · right
      simp only [Function.Injective] at hinj
      push Not at hinj
      obtain ⟨i, j, heq, hne⟩ := hinj
      exact ⟨i, j, hne, heq⟩
  · intro hAI x hx hne
    exact L.short_relation ω p hω hAI.injective x hx hne

theorem matrix_short_kernel_excluded (L : Law q H)
    (A : Matrix (Fin 3) (Fin 3) (ZMod q))
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets A.col)
    (hAI : AffineIndependent (ZMod q) A.col)
    (x : Fin 3 → ℤ) (hx : ∀ i, |x i| ≤ (H : ℤ)) (hne : x ≠ 0) :
    A.mulVec (fun i => (x i : ZMod q)) ≠ 0 := by
  intro hrel
  have hno := (L.support_of_weight_pos A.col hpositive).2.2 hAI x hx hne
  apply hno
  funext i
  have hi := congrFun hrel i
  simpa [Matrix.mulVec, Matrix.col, dotProduct, Finset.sum_apply, mul_comm] using hi

theorem kernel_norm_gt_of_weight_pos (L : Law q H)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col)
    (hAI : AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col)
    {x : PrimitiveNormal.Vector} (hne : x ≠ 0) (hkernel : A.mulVec x = 0) :
    (H : ℝ) < ‖PrimitiveNormal.toEuclidean x‖ := by
  by_contra hn
  have hx := AuxiliarySet.coordinate_abs_le_of_euclidean_norm_le (le_of_not_gt hn)
  have hno := L.matrix_short_kernel_excluded (A.map (Int.castRingHom (ZMod q)))
    hpositive hAI x hx hne
  exact hno (AuxiliarySet.cast_mulVec_eq_zero hkernel)

theorem kernel_norm_gt_main_square {h : ℕ} (L : Law q (h ^ 2))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col)
    (hAI : AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col)
    {x : PrimitiveNormal.Vector} (hne : x ≠ 0) (hkernel : A.mulVec x = 0) :
    (h : ℝ) ^ 2 < ‖PrimitiveNormal.toEuclidean x‖ := by
  simpa only [Nat.cast_pow] using L.kernel_norm_gt_of_weight_pos A hpositive hAI hne hkernel

end Law
end Problem355.AuxiliarySampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PlaneReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PlaneReduction

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem lift_orthogonal (q : ℕ) (x z : ι → ℤ)
    (hz : ∑ i, x i * z i = 1) (v : ι → ZMod q)
    (hv : ∑ i, (x i : ZMod q) * v i = 0) :
    ∃ w : ι → ℤ, (∑ i, x i * w i = 0) ∧
      ∀ i, (w i : ZMod q) = v i := by
  classical
  choose a ha using fun i => ZMod.intCast_surjective (v i)
  let t : ℤ := ∑ i, x i * a i
  have ht : (t : ZMod q) = 0 := by
    simpa [t, ha] using hv
  refine ⟨fun i => a i - t * z i, ?_, ?_⟩
  · calc
      (∑ i, x i * (a i - t * z i)) =
          (∑ i, x i * a i) - t * (∑ i, x i * z i) := by
            simp only [mul_sub, Finset.sum_sub_distrib,
              Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := by rw [hz]; simp [t]
  · intro i
    simp [ht, ha]

theorem lift_orthogonal_scaled (q : ℕ) (x z : ι → ℤ)
    (hz : ∑ i, x i * z i = 1) (E : ℤ)
    (hE : IsUnit (E : ZMod q)) (v : ι → ZMod q)
    (hv : ∑ i, (x i : ZMod q) * v i = 0) :
    ∃ w : ι → ℤ, (∑ i, x i * w i = 0) ∧
      ∀ i, ((E * w i : ℤ) : ZMod q) = v i := by
  obtain ⟨u, hu⟩ := hE
  let v' : ι → ZMod q := fun i => (↑(u⁻¹) : ZMod q) * v i
  have hv' : ∑ i, (x i : ZMod q) * v' i = 0 := by
    calc
      (∑ i, (x i : ZMod q) * v' i) =
          (↑(u⁻¹) : ZMod q) * ∑ i, (x i : ZMod q) * v i := by
            simp only [v', Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := by rw [hv, mul_zero]
  obtain ⟨w, hw, hred⟩ := lift_orthogonal q x z hz v' hv'
  refine ⟨w, hw, ?_⟩
  intro i
  rw [Int.cast_mul, hred, ← hu]
  simp [v', ← mul_assoc]

theorem lift_orthogonal_mem (q : ℕ) (x z : ι → ℤ)
    (hz : ∑ i, x i * z i = 1) (E : ℤ)
    (hE : IsUnit (E : ZMod q)) (Λ : Submodule ℤ (ι → ℤ))
    (hΛ : ∀ w : ι → ℤ, E • w ∈ Λ) (v : ι → ZMod q)
    (hv : ∑ i, (x i : ZMod q) * v i = 0) :
    ∃ w : ι → ℤ, w ∈ Λ ∧ (∑ i, x i * w i = 0) ∧
      ∀ i, (w i : ZMod q) = v i := by
  obtain ⟨w, hw, hred⟩ := lift_orthogonal_scaled q x z hz E hE v hv
  refine ⟨E • w, hΛ w, ?_, ?_⟩
  · change (∑ i, x i * (E * w i)) = 0
    calc
      (∑ i, x i * (E * w i)) = E * ∑ i, x i * w i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hw, mul_zero]
  · exact hred

theorem normal_reduction_ne_zero (q : ℕ) [Nontrivial (ZMod q)]
    (x z : ι → ℤ) (hz : ∑ i, x i * z i = 1) :
    (fun i => (x i : ZMod q)) ≠ 0 := by
  intro hx
  have hcast : (∑ i, (x i : ZMod q) * (z i : ZMod q)) = 1 := by
    simpa using congrArg (fun a : ℤ => (a : ZMod q)) hz
  have hxi : ∀ i, (x i : ZMod q) = 0 := fun i => congrFun hx i
  simp [hxi] at hcast

end Problem355.PlaneReduction

end OAI
end

section
-- module Solutions.OAIQW_Problem355.WeightedZeroPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.WeightedZeroPartition

open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem affine_or_equalPair_of_cap {F : Type*} [Field F]
    (v : Fin 3 → (Fin 3 → F)) (T : Set (Fin 3 → F))
    (hT : AuxiliaryCap.IsCap T) (hv : ∀ i, v i ∈ T) :
    AffineIndependent F v ∨ ∃ p : Fin 3, EqualPair v p := by
  by_cases h01 : v 0 = v 1
  · exact Or.inr ⟨0, h01⟩
  by_cases h02 : v 0 = v 2
  · exact Or.inr ⟨1, h02⟩
  by_cases h12 : v 1 = v 2
  · exact Or.inr ⟨2, h12⟩
  left
  have h := (affineIndependent_iff_not_collinear_set).mpr
    (hT (v 0) (hv 0) (v 1) (hv 1) (v 2) (hv 2) h01 h02 h12)
  convert h using 1
  funext i
  fin_cases i <;> rfl

theorem sum_le_four_case_sums {α : Type*}
    (S : Finset α) (W : α → ℝ)
    (affine : α → Prop) (equalPair : Fin 3 → α → Prop)
    (exceptional : Fin 3 → Prop) (lowRank : α → Prop)
    (hW : ∀ a ∈ S, 0 ≤ W a)
    (hsupport : ∀ a ∈ S, 0 < W a → affine a ∨ ∃ p, equalPair p a) :
    (∑ a ∈ S, W a) ≤
      (∑ a ∈ S.filter affine, W a) +
      ∑ p : Fin 3,
        ((∑ a ∈ S.filter (fun a => equalPair p a ∧ ¬ exceptional p), W a) +
         (∑ a ∈ S.filter (fun a => equalPair p a ∧ exceptional p ∧ ¬ lowRank a), W a) +
         (∑ a ∈ S.filter (fun a => equalPair p a ∧ exceptional p ∧ lowRank a), W a)) := by
  classical
  have hpoint (a : α) (ha : a ∈ S) :
      W a ≤ (if affine a then W a else 0) +
        ∑ p : Fin 3, if equalPair p a then W a else 0 := by
    have hnonneg (p : Fin 3) : 0 ≤ if equalPair p a then W a else 0 := by
      split_ifs <;> first | exact hW a ha | rfl
    by_cases hw : 0 < W a
    · rcases hsupport a ha hw with haf | ⟨p, hp⟩
      · simp only [ite_eq_left haf]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun p _ => hnonneg p)
      · have hs := Finset.single_le_sum
          (s := Finset.univ) (f := fun p => if equalPair p a then W a else 0)
          (fun p _ => hnonneg p) (Finset.mem_univ p)
        have hs' : W a ≤ ∑ p : Fin 3, if equalPair p a then W a else 0 := by
          simpa only [ite_eq_left hp] using hs
        exact hs'.trans (le_add_of_nonneg_left (by split_ifs <;> positivity))
    · have hz : W a = 0 := le_antisymm (not_lt.mp hw) (hW a ha)
      simp [hz]
  have hsplit (p : Fin 3) (a : α) :
      (if equalPair p a then W a else 0) =
        (if equalPair p a ∧ ¬ exceptional p then W a else 0) +
        (if equalPair p a ∧ exceptional p ∧ ¬ lowRank a then W a else 0) +
        (if equalPair p a ∧ exceptional p ∧ lowRank a then W a else 0) := by
    by_cases he : equalPair p a <;> by_cases hx : exceptional p <;>
      by_cases hl : lowRank a <;> simp [he, hx, hl]
  calc
    (∑ a ∈ S, W a) ≤ ∑ a ∈ S,
        ((if affine a then W a else 0) +
          ∑ p : Fin 3, if equalPair p a then W a else 0) :=
      Finset.sum_le_sum hpoint
    _ = _ := by
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_add_distrib, ← Finset.sum_filter]

end Problem355.WeightedZeroPartition

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliaryThreeCase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.AuxiliaryThreeCase

open WeightedZeroPartition
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem not_exceptional_zero_one {F : Type*} [Field F]
    (x : Fin 3 → F) (hx : x ≠ 0) :
    ¬ (ExceptionalVector x 0 ∧ ExceptionalVector x 1) := by
  rintro ⟨h0, h1⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h0
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h1
  have ha2 := congrFun ha 2
  have hb2 := congrFun hb 2
  simp [columnPair] at ha2 hb2
  have hb0 : b = 0 := by simpa [← ha2] using hb2
  apply hx
  rw [← hb, hb0, zero_smul]

theorem exists_nonexceptional {F : Type*} [Field F]
    (x : Fin 3 → F) (hx : x ≠ 0) :
    ∃ p : Fin 3, ¬ ExceptionalVector x p := by
  by_cases h0 : ExceptionalVector x 0
  · exact ⟨1, fun h1 => not_exceptional_zero_one x hx ⟨h0, h1⟩⟩
  · exact ⟨0, h0⟩

theorem three_case_cover {F : Type*} [Field F]
    (x : Fin 3 → F) (hx : x ≠ 0) (v : Fin 3 → (Fin 3 → F))
    (hsupport : AffineIndependent F v ∨ ∃ p : Fin 3, EqualPair v p) :
    AffineIndependent F v ∨
      (∃ p : Fin 3, EqualPair v p ∧ ¬ ExceptionalVector x p) ∨
      (∃ p : Fin 3, EqualPair v p ∧ ExceptionalVector x p ∧
        ∃ i j : Fin 3, v i ≠ v j) := by
  rcases hsupport with ha | ⟨p, hp⟩
  · exact Or.inl ha
  right
  by_cases he : ExceptionalVector x p
  · by_cases hn : ∃ i j : Fin 3, v i ≠ v j
    · exact Or.inr ⟨p, hp, he, hn⟩
    · obtain ⟨p', hp'⟩ := exists_nonexceptional x hx
      left
      refine ⟨p', ?_, hp'⟩
      exact not_not.mp (fun h => hn ⟨(columnPair p').1, (columnPair p').2, h⟩)
  · exact Or.inl ⟨p, hp, he⟩

theorem sum_le_three_case_sums {F α : Type*} [Field F]
    (x : Fin 3 → F) (hx : x ≠ 0) (S : Finset α) (W : α → ℝ)
    (v : α → Fin 3 → (Fin 3 → F))
    (hW : ∀ a ∈ S, 0 ≤ W a)
    (hsupport : ∀ a ∈ S, 0 < W a →
      AffineIndependent F (v a) ∨ ∃ p : Fin 3, EqualPair (v a) p) :
    (∑ a ∈ S, W a) ≤
      (∑ a ∈ S.filter (fun a => AffineIndependent F (v a)), W a) +
      ∑ p : Fin 3,
        ((∑ a ∈ S.filter (fun a => EqualPair (v a) p ∧
          ¬ ExceptionalVector x p), W a) +
         (∑ a ∈ S.filter (fun a => EqualPair (v a) p ∧
          ExceptionalVector x p ∧ ∃ i j : Fin 3, v a i ≠ v a j), W a)) := by
  classical
  let eq' := fun p a => EqualPair (v a) p ∧
    (¬ ExceptionalVector x p ∨ ∃ i j : Fin 3, v a i ≠ v a j)
  have hcover : ∀ a ∈ S, 0 < W a →
      AffineIndependent F (v a) ∨ ∃ p : Fin 3, eq' p a := by
    intro a ha hw
    rcases three_case_cover x hx (v a) (hsupport a ha hw) with
      h | ⟨p, he, hp⟩ | ⟨p, he, hp, hn⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, he, Or.inl hp⟩
    · exact Or.inr ⟨p, he, Or.inr hn⟩
  have H := sum_le_four_case_sums S W
    (fun a => AffineIndependent F (v a)) eq' (ExceptionalVector x)
    (fun _ => False) hW hcover
  have heq (p : Fin 3) (a : α) :
      (eq' p a ∧ ¬ ExceptionalVector x p) ↔
        (EqualPair (v a) p ∧ ¬ ExceptionalVector x p) := by
    simp only [eq']
    tauto
  have hne (p : Fin 3) (a : α) :
      (eq' p a ∧ ExceptionalVector x p ∧ ¬ False) ↔
        (EqualPair (v a) p ∧ ExceptionalVector x p ∧
          ∃ i j : Fin 3, v a i ≠ v a j) := by
    simp only [eq']
    tauto
  simp_rw [heq, hne] at H
  simpa only [and_false, Finset.filter_false, Finset.sum_empty, add_zero] using H

theorem matrix_sum_le_three_case_sums
    (q : ℕ) [Fact q.Prime] (x : Fin 3 → ℤ) (hx : PrimitiveNormal.IsPrimitive x)
    (S : Finset IntMatrix) (W : IntMatrix → ℝ)
    (hW : ∀ A ∈ S, 0 ≤ W A)
    (hcap : ∀ A ∈ S, 0 < W A → ∃ T : Set (Fin 3 → ZMod q),
      AuxiliaryCap.IsCap T ∧ ∀ i, residueColumns q A i ∈ T) :
    (∑ A ∈ S, W A) ≤
      (∑ A ∈ S.filter (fun A => AffineIndependent (ZMod q) (residueColumns q A)), W A) +
      ∑ p : Fin 3,
        ((∑ A ∈ S.filter (fun A => EqualPair (residueColumns q A) p ∧
          ¬ Exceptional q x p), W A) +
         (∑ A ∈ S.filter (fun A => EqualPair (residueColumns q A) p ∧
          Exceptional q x p ∧ ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j), W A)) := by
  obtain ⟨z, hz⟩ := (PrimitiveNormal.isPrimitive_iff_exists_dot_eq_one x).mp hx
  have hnormal := PlaneReduction.normal_reduction_ne_zero q x z hz
  have hs : ∀ A ∈ S, 0 < W A → AffineIndependent (ZMod q) (residueColumns q A) ∨
      ∃ p : Fin 3, EqualPair (residueColumns q A) p := by
    intro A hA hp
    obtain ⟨T, hT, hcols⟩ := hcap A hA hp
    exact affine_or_equalPair_of_cap (residueColumns q A) T hT hcols
  have H := sum_le_three_case_sums (fun i => (x i : ZMod q)) hnormal S W
    (residueColumns q) hW hs
  simpa only [exceptionalVector_reduction] using H

end Problem355.AuxiliaryThreeCase

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LiftedBadEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.LiftingProbability

open Finset

noncomputable section

 theorem auxiliaryWeight_nonneg {Ω B : Type*} [Fintype Ω]
    (q s : ℕ) (w : Ω → ℝ) (V : Ω → Finset B)
    (hw : ∀ ω, 0 ≤ w ω) (b : Fin 3 → B) :
    0 ≤ auxiliaryWeight q s w V b := by
  unfold auxiliaryWeight
  exact mul_nonneg (by positivity) (inclusionMass_nonneg w V hw b)

end
end Problem355.LiftingProbability

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliaryZeroWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.AuxiliarySampling.Law

open scoped BigOperators
open LiftingProbability

variable {q h : ℕ} [Fact q.Prime]

theorem density_ratio_le_main_square (L : Law q (h ^ 2)) :
    (q : ℝ) ^ 3 / L.size ≤ 2000 ^ 3 * (q : ℝ) * (h : ℝ) ^ 12 := by
  have hs : (q : ℝ) ^ 2 ≤ 2000 ^ 3 * ((h : ℝ) ^ 2) ^ 6 * L.size := by
    exact_mod_cast L.size_lower
  have hsize : (0 : ℝ) < L.size := by exact_mod_cast L.size_pos
  apply (div_le_iff₀ hsize).mpr
  calc
    (q : ℝ) ^ 3 = (q : ℝ) * (q : ℝ) ^ 2 := by ring
    _ ≤ (q : ℝ) * (2000 ^ 3 * ((h : ℝ) ^ 2) ^ 6 * L.size) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg q)
    _ = _ := by ring

theorem weight_le_two_main_square (L : Law q (h ^ 2))
    (p : Fin 3 → Fin 3 → ZMod q) :
    auxiliaryWeight q L.size L.weight L.sets p ≤
      (2 * 2000 ^ 6) * (q : ℝ) ^ 2 * (h : ℝ) ^ 24 := by
  calc
    _ ≤ 2 * ((q : ℝ) ^ 3 / L.size) ^ 2 := L.weight_le_two p
    _ ≤ 2 * (2000 ^ 3 * (q : ℝ) * (h : ℝ) ^ 12) ^ 2 := by
      gcongr
      exact L.density_ratio_le_main_square
    _ = _ := by ring

theorem weight_le_four_main_square (L : Law q (h ^ 2))
    (p : Fin 3 → Fin 3 → ZMod q) (hne : ∃ i j, p i ≠ p j) :
    auxiliaryWeight q L.size L.weight L.sets p ≤
      (4 * 2000 ^ 3) * (q : ℝ) * (h : ℝ) ^ 12 := by
  obtain ⟨i, j, hij⟩ := hne
  calc
    _ ≤ 4 * ((q : ℝ) ^ 3 / L.size) := L.weight_le_four p i j hij
    _ ≤ 4 * (2000 ^ 3 * (q : ℝ) * (h : ℝ) ^ 12) :=
      mul_le_mul_of_nonneg_left L.density_ratio_le_main_square (by norm_num)
    _ = _ := by ring

end Problem355.AuxiliarySampling.Law

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PlaneRowTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PlaneRowTransport

open Matrix IntegralPlaneLattice

theorem linearIndependent_of_minor_ne_zero (u v : Ambient) (s t : Fin 3)
    (hminor : u s * v t - u t * v s ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hv
    have hv' : v = 0 := hv
    apply hminor
    simp [hv']
  · intro a ha
    have ha' : a • v = u := ha
    have hs := congrArg (fun w : Ambient => w s) ha'
    have ht := congrArg (fun w : Ambient => w t) ha'
    change a * v s = u s at hs
    change a * v t = u t at ht
    apply hminor
    rw [← hs, ← ht]
    ring

theorem rows_pair_linearIndependent_of_minor
    (x : Fin 3 → ℤ) (A : PlaneMatrices x) (i j s t : Fin 3)
    (hminor : A.val i s * A.val j t - A.val i t * A.val j s ≠ 0) :
    LinearIndependent ℝ ![(rows x A i : plane x), (rows x A j : plane x)] := by
  have hm : castVec (A.val i) s * castVec (A.val j) t -
      castVec (A.val i) t * castVec (A.val j) s ≠ 0 := by
    simp only [castVec_apply]
    exact_mod_cast hminor
  apply LinearIndependent.of_comp (plane x).subtype
  convert linearIndependent_of_minor_ne_zero (castVec (A.val i))
    (castVec (A.val j)) s t hm using 1
  ext a
  fin_cases a <;> rfl

theorem norm_rows_le_of_coordinate_bounds
    (x : Fin 3 → ℤ) (A : PlaneMatrices x) (i : Fin 3)
    {R : ℝ} (hR : 0 ≤ R) (hA : ∀ j, |(A.val i j : ℝ)| ≤ R) :
    ‖rows x A i‖ ≤ Real.sqrt 3 * R := by
  rw [norm_rows]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hR)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [EuclideanSpace.norm_sq_eq]
  calc
    ∑ j, ‖(castVec (A.val i)).ofLp j‖ ^ 2 ≤ ∑ _j : Fin 3, R ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply (sq_le_sq₀ (norm_nonneg _) hR).mpr
      simpa only [Real.norm_eq_abs, castVec, WithLp.ofLp_toLp] using hA j
    _ = 3 * R ^ 2 := by simp

theorem exists_minor_of_projected_columns_ne
    (A : IntMatrix) (s t : Fin 3)
    (hs : A 2 s ≠ 0) (ht : A 2 t ≠ 0)
    (hne : projectedColumn A s ≠ projectedColumn A t) :
    ∃ i : Fin 3, i ≠ 2 ∧ A i s * A 2 t - A i t * A 2 s ≠ 0 := by
  by_contra h
  push Not at h
  have h₀ := sub_eq_zero.mp (h 0 (by decide))
  have h₁ := sub_eq_zero.mp (h 1 (by decide))
  have hsR : (A 2 s : ℝ) ≠ 0 := by exact_mod_cast hs
  have htR : (A 2 t : ℝ) ≠ 0 := by exact_mod_cast ht
  apply hne
  apply Prod.ext
  · apply (div_eq_div_iff hsR htR).mpr
    exact_mod_cast h₀
  · apply (div_eq_div_iff hsR htR).mpr
    exact_mod_cast h₁

theorem norm_rows_le_four_mul
    (x : Fin 3 → ℤ) (A : PlaneMatrices x) (i : Fin 3)
    {N : ℝ} (hN : 0 ≤ N) (hA : ∀ j, |(A.val i j : ℝ)| ≤ 2 * N) :
    ‖rows x A i‖ ≤ 4 * N := by
  have hrow := norm_rows_le_of_coordinate_bounds x A i (by positivity) hA
  have hsqrt : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hm := mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ 2 * N by positivity)
  exact hrow.trans (by nlinarith)

end Problem355.PlaneRowTransport

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.RowLatticeMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.RowLatticeMatrices

open Matrix IntegralPlaneLattice

theorem rowsEquiv_independent_of_minor (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (A : RowMatrices x L) (i j s t : Fin 3)
    (hm : A.val i s * A.val j t - A.val i t * A.val j s ≠ 0) :
    LinearIndependent ℝ ![(rowsEquiv x L A i : plane x),
      (rowsEquiv x L A j : plane x)] := by
  exact PlaneRowTransport.rows_pair_linearIndependent_of_minor x
    ⟨A.val, A.property.1⟩ i j s t hm

theorem rowsEquiv_independent_of_projections (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (A : RowMatrices x L) (s t : Fin 3)
    (hs : A.val 2 s ≠ 0) (ht : A.val 2 t ≠ 0)
    (hne : PlaneRowTransport.projectedColumn A.val s ≠
      PlaneRowTransport.projectedColumn A.val t) :
    ∃ i j : Fin 3, LinearIndependent ℝ ![(rowsEquiv x L A i : plane x),
      (rowsEquiv x L A j : plane x)] := by
  obtain ⟨i, _, hi⟩ := PlaneRowTransport.exists_minor_of_projected_columns_ne
    A.val s t hs ht hne
  exact ⟨i, 2, rowsEquiv_independent_of_minor x L A i 2 s t hi⟩

theorem rowsEquiv_norm_le_four_mul (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (A : RowMatrices x L) (i : Fin 3)
    {N : ℝ} (hN : 0 ≤ N) (hA : ∀ j, |(A.val i j : ℝ)| ≤ 2 * N) :
    ‖rowsEquiv x L A i‖ ≤ 4 * N := by
  exact PlaneRowTransport.norm_rows_le_four_mul x ⟨A.val, A.property.1⟩ i hN hA

theorem sum_rowFamily (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ))
    (S : Finset IntMatrix) (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    (W : IntMatrix → ℝ) :
    ∑ u ∈ rowFamily x L S hS, W ((rowsEquiv x L).symm u).val =
      ∑ A ∈ S, W A := by
  classical
  rw [rowFamily, Finset.sum_image]
  · simp only [Equiv.symm_apply_apply]
    exact Finset.sum_attach S W
  · intro A hA B hB h
    apply Subtype.ext
    exact congrArg (fun M : RowMatrices x L => M.val) ((rowsEquiv x L).injective h)

theorem rowFamily_norm_le_four_mul (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (S : Finset IntMatrix)
    (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    {N : ℝ} (hN : 0 ≤ N)
    (hbound : ∀ A ∈ S, ∀ i j, |(A i j : ℝ)| ≤ 2 * N) :
    ∀ u ∈ rowFamily x L S hS, ∀ i, ‖(u i : plane x)‖ ≤ 4 * N := by
  intro u hu i
  have hm := (mem_rowFamily x L S hS u).mp hu
  have h := rowsEquiv_norm_le_four_mul x L ((rowsEquiv x L).symm u) i hN
    (hbound _ hm i)
  change ‖u i‖ ≤ 4 * N
  simpa only [Equiv.apply_symm_apply] using h

theorem rowFamily_independent_of_projections (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (S : Finset IntMatrix)
    (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    (hproj : ∀ A ∈ S, ∃ s t : Fin 3, A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t) :
    ∀ u ∈ rowFamily x L S hS, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(u i : plane x), (u j : plane x)] := by
  intro u hu
  have hm := (mem_rowFamily x L S hS u).mp hu
  obtain ⟨s, t, hs, ht, hne⟩ := hproj _ hm
  have h := rowsEquiv_independent_of_projections x L ((rowsEquiv x L).symm u)
    s t hs ht hne
  simpa only [Equiv.apply_symm_apply] using h

end Problem355.RowLatticeMatrices

end

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

theorem abs_det_kernel_basis_extension
    (L : Submodule ℤ (Fin 3 → ℤ)) (f : L →ₗ[ℤ] ℤ)
    (g : ℤ) (hg : g ≠ 0) (hdiv : ∀ x, g ∣ f x)
    (u : L) (hu : f u = g) (b : Basis (Fin 2) ℤ (LinearMap.ker f)) :
    |Matrix.det ![(fun j => (((b 0 : L) : Fin 3 → ℤ) j : ℝ)),
      (fun j => (((b 1 : L) : Fin 3 → ℤ) j : ℝ)),
      (fun j => ((u : Fin 3 → ℤ) j : ℝ))]| = (L.toAddSubgroup.index : ℝ) := by
  simpa only [LatticeSplit.extendIntegerKernelBasis_inl,
    LatticeSplit.extendIntegerKernelBasis_inr] using
    abs_det_sum_basis_eq_index L
      (LatticeSplit.extendIntegerKernelBasis f g hg hdiv u hu b)

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

theorem latticeIn_covolume
    (y z : Fin 3 → ℤ) (hyz : y ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (g : ℤ) (hg : 0 < g)
    (hdiv : ∀ v : L, g ∣ y ⬝ᵥ (v : Fin 3 → ℤ))
    (u : L) (hu : y ⬝ᵥ (u : Fin 3 → ℤ) = g) :
    ZLattice.covolume (latticeIn y L) =
      (L.toAddSubgroup.index : ℝ) * ‖castVec y‖ / (g : ℝ) := by
  let := latticeIn_isZLattice y z hyz L E hE hL
  let f := (integerDot y).comp L.subtype
  let e : f.ker ≃ₗ[ℤ] latticeIn y L :=
    (LatticeSplit.restrictedKernelEquiv L (integerDot y)).trans (kernelEquivIn y L)
  let bZ : Basis (Fin 2) ℤ f.ker :=
    (integerBasisIn y z hyz L E hE hL).map
      (LatticeSplit.restrictedKernelEquiv L (integerDot y)).symm
  let b : Basis (Fin 2) ℤ (latticeIn y L) := bZ.map e
  let emb := (plane y).subtypeₗᵢ
  have hb (i : Fin 2) : emb (b i) = castVec ((bZ i : L) : Fin 3 → ℤ) := by
    rfl
  have hdet : |Matrix.det ![(emb (b 0)).ofLp, (emb (b 1)).ofLp,
      (castVec (u : Fin 3 → ℤ)).ofLp]| = (L.toAddSubgroup.index : ℝ) := by
    rw [hb 0, hb 1]
    exact Lattice.abs_det_kernel_basis_extension L f g (ne_of_gt hg) hdiv u hu bZ
  have hzero (i : Fin 2) : (emb (b i)).ofLp ⬝ᵥ (castVec y).ofLp = 0 := by
    rw [dotProduct_comm]
    exact (b i : plane y).property
  have hheight : (castVec y).ofLp ⬝ᵥ (castVec (u : Fin 3 → ℤ)).ofLp = (g : ℝ) := by
    change (∑ i, (y i : ℝ) * ((u : Fin 3 → ℤ) i : ℝ)) = (g : ℝ)
    exact_mod_cast hu
  have h := Lattice.covolume_eq_index_mul_norm_div
    (latticeIn y L) b emb (castVec (u : Fin 3 → ℤ)).ofLp (castVec y).ofLp
    (L.toAddSubgroup.index : ℝ) (g : ℝ) (hzero 0) (hzero 1) hdet hheight
    (by exact_mod_cast hg)
  simpa only [WithLp.toLp_ofLp] using h

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

theorem plane_card_le_of_short_independent {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (hdim : Module.finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : Fin 2 → E) (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ L)
    (A : Finset L) (c : E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
    (hvn : ∀ i, ‖v i‖ ≤ R) :
    (A.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
  let b := basisOfLinearIndependentOfCardEqFinrank hv (by simpa using hdim.symm)
  apply plane_card_le_of_short_basis L b (by simpa [b] using hvL) A c R hR hA
  simpa [b] using hvn

theorem card_tuples_le_pow {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Finset (Fin m → α)) (C : ℝ)
    (hA : ∀ i, ((A.image (fun a => a i)).card : ℝ) ≤ C) :
    (A.card : ℝ) ≤ C ^ m := by
  classical
  let B : Fin m → Finset α := fun i => A.image (fun a => a i)
  have hsub : A ⊆ Fintype.piFinset B := by
    intro a ha
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hcard : A.card ≤ ∏ i, (B i).card := by
    simpa only [Fintype.card_piFinset] using Finset.card_le_card hsub
  exact calc
    (A.card : ℝ) ≤ ∏ i, ((B i).card : ℝ) := by
      simpa only [Nat.cast_prod] using (Nat.cast_le (α := ℝ)).mpr hcard
    _ ≤ ∏ _i : Fin m, C :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hA i)
    _ = C ^ m := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem plane_spanning_triples_card_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (hdim : Module.finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Finset (Fin 3 → L)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, ∀ i, ‖(a i : E)‖ ≤ R)
    (hpair : ∀ a ∈ A, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : E), (a j : E)]) :
    (A.card : ℝ) ≤ (9 * Real.pi * R ^ 2 / ZLattice.covolume L) ^ 3 := by
  classical
  by_cases hne : A.Nonempty
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨i, j, hij⟩ := hpair a ha
    let v : Fin 2 → E := ![(a i : E), (a j : E)]
    have hvL : ∀ k, v k ∈ L := by
      intro k
      fin_cases k <;> exact Subtype.coe_prop _
    have hvn : ∀ k, ‖v k‖ ≤ R := by
      intro k
      fin_cases k
      · exact hA a ha i
      · exact hA a ha j
    let B : Fin 3 → Finset L := fun k => A.image (fun t => t k)
    have hB (k : Fin 3) : ((B k).card : ℝ) ≤
        9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
      apply plane_card_le_of_short_independent hdim L v hij hvL (B k) 0 R hR _ hvn
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hA t ht k
    exact card_tuples_le_pow A _ hB
  · have hzero : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst A
    simp only [Finset.card_empty, Nat.cast_zero]
    exact pow_nonneg (div_nonneg (by positivity) (ZLattice.covolume_pos L volume).le) 3

end Problem355.LatticePacking

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DiagonalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DiagonalKernel

open scoped BigOperators Matrix

variable {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]

theorem natCard_kernel_change (A : Matrix ι ι R) (P Q : (Matrix ι ι R)ˣ) :
    Nat.card (Kernel ((P : Matrix ι ι R) * A * (Q : Matrix ι ι R))) =
      Nat.card (Kernel A) :=
  Nat.card_congr (changeKernelEquiv A P Q)

section Cardinality

variable [Fintype R] [DecidableEq R]

theorem card_kernel_diagonal (d : ι → R) :
    Fintype.card (Kernel (Matrix.diagonal d)) =
      ∏ i, Fintype.card {x : R // d i * x = 0} := by
  classical
  rw [Fintype.card_congr (diagonalKernelEquiv d), Fintype.card_pi]

theorem card_kernel_diagonal_three (D E : R) :
    Fintype.card (Kernel (Matrix.diagonal ![1, D, E])) =
      Fintype.card {x : R // D * x = 0} *
        Fintype.card {x : R // E * x = 0} := by
  rw [card_kernel_diagonal]
  simp [Fin.prod_univ_succ]
  exact Or.inl rfl

end Cardinality

theorem card_pow_annihilator (B j b : ℕ) [NeZero B] :
    Nat.card {x : ZMod (B ^ j) // (B : ZMod (B ^ j)) ^ b * x = 0} =
      B ^ min b j := by
  rcases le_total b j with h | h
  · simpa only [Nat.min_eq_left h] using zmod_card_pow_mul_eq_zero B j b h
  · simpa only [Nat.cast_pow, Nat.gcd_eq_left (pow_dvd_pow B h),
      Nat.min_eq_right h] using zmod_card_mul_eq_zero (B ^ j) (B ^ b)

theorem card_kernel_diagonal_prime_power (B j b e : ℕ) [NeZero B]
    (hje : j ≤ e) :
    Nat.card (Kernel (Matrix.diagonal
      ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e])) =
        B ^ (j + min b j) := by
  classical
  rw [Nat.card_eq_fintype_card, card_kernel_diagonal_three,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_pow_annihilator, card_pow_annihilator,
    Nat.min_eq_right hje, pow_add]
  exact Nat.mul_comm _ _

theorem card_kernel_diagonal_prime_power_density (B j b e : ℕ) [NeZero B]
    (hje : j ≤ e) :
    Nat.card (Kernel (Matrix.diagonal
      ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e])) *
          B ^ (j + (j - b)) = (B ^ j) ^ 3 := by
  rw [card_kernel_diagonal_prime_power B j b e hje, ← pow_add, ← pow_mul]
  congr 1
  omega

theorem card_kernel_prime_power_density (B j b e : ℕ) [NeZero B]
    (hje : j ≤ e) (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)))
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)))ˣ)
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e] *
        (Q : Matrix _ _ _)) :
    Nat.card (Kernel C) * B ^ (j + (j - b)) = (B ^ j) ^ 3 := by
  rw [hC, natCard_kernel_change]
  exact card_kernel_diagonal_prime_power_density B j b e hje

theorem card_kernel_reduction_density (B k j b e : ℕ) [NeZero B]
    (hjk : j ≤ k) (hje : j ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
        (Q : Matrix _ _ _)) :
    Nat.card (Kernel (C.map
      (ZMod.castHom (pow_dvd_pow B hjk) (ZMod (B ^ j))))) *
        B ^ (j + (j - b)) = (B ^ j) ^ 3 := by
  let f : ZMod (B ^ k) →+* ZMod (B ^ j) :=
    ZMod.castHom (pow_dvd_pow B hjk) (ZMod (B ^ j))
  have hd : (Matrix.diagonal
      ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e]).map f =
      Matrix.diagonal ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e] := by
    ext i l
    by_cases h : i = l
    · subst l
      fin_cases i <;> simp
    · simp [h]
  apply card_kernel_prime_power_density B j b e hje (C.map f)
    (Units.map f.mapMatrix.toMonoidHom P) (Units.map f.mapMatrix.toMonoidHom Q)
  change C.map f = (P : Matrix _ _ _).map f *
    Matrix.diagonal ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e] *
      (Q : Matrix _ _ _).map f
  simpa only [Matrix.map_mul, hd] using congrArg (fun A => A.map f) hC

end Problem355.DiagonalKernel

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticeShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.LatticeShell

open Finset

theorem card_box_residue_le {d : ℕ} (s : Finset (Fin d → ℤ))
    (lo hi q : ℤ) (hq : 0 < q) (r : Fin d → ℤ)
    (hbox : ∀ x ∈ s, ∀ i, lo ≤ x i ∧ x i ≤ hi)
    (hres : ∀ x ∈ s, ∀ i, x i % q = r i) :
    s.card ≤ (hi / q + 1 - lo / q).toNat ^ d := by
  classical
  let F : ↥s → (Fin d → ↥(Icc (lo / q) (hi / q))) := fun x i =>
    ⟨x.val i / q, mem_Icc.mpr
      ⟨Int.ediv_le_ediv hq (hbox x.val x.property i).1,
       Int.ediv_le_ediv hq (hbox x.val x.property i).2⟩⟩
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hdiv : x.val i / q = y.val i / q :=
      congrArg Subtype.val (congrFun hxy i)
    calc
      x.val i = x.val i % q + q * (x.val i / q) :=
        (Int.emod_add_mul_ediv _ _).symm
      _ = y.val i % q + q * (y.val i / q) := by
        rw [hdiv, hres x.val x.property i, hres y.val y.property i]
      _ = y.val i := Int.emod_add_mul_ediv _ _
  have hc := Fintype.card_le_of_injective F hF
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin,
    Int.card_Icc] using hc

theorem symmetric_quotient_length_le (R q : ℕ) (hq : 0 < q) :
    ((R : ℤ) / q + 1 - (-(R : ℤ)) / q).toNat ≤ 2 * (R / q) + 2 := by
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  apply Int.toNat_le.mpr
  rw [Int.neg_ediv]
  have hs : (q : ℤ).sign = 1 := Int.sign_eq_one_of_pos hqz
  rw [hs]
  push_cast
  rw [← Int.natCast_ediv]
  split_ifs <;> omega

theorem card_symmetric_box_residue_le {d : ℕ} (s : Finset (Fin d → ℤ))
    (R q : ℕ) (hq : 0 < q) (r : Fin d → ℤ)
    (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ s, ∀ i, x i % (q : ℤ) = r i) :
    s.card ≤ (2 * (R / q) + 2) ^ d := by
  calc
    s.card ≤ ((R : ℤ) / q + 1 - (-(R : ℤ)) / q).toNat ^ d :=
      card_box_residue_le s (-(R : ℤ)) R q (by exact_mod_cast hq) r hbox hres
    _ ≤ (2 * (R / q) + 2) ^ d :=
      Nat.pow_le_pow_left (symmetric_quotient_length_le R q hq) d

theorem card_symmetric_box_zmod_residue_le {d : ℕ}
    (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q)
    (r : Fin d → ZMod q)
    (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ s, ∀ i, (x i : ZMod q) = r i) :
    s.card ≤ (2 * (R / q) + 2) ^ d := by
  let : NeZero q := ⟨by omega⟩
  apply card_symmetric_box_residue_le s R q hq (fun i => ((r i).val : ℤ)) hbox
  intro x hx i
  rw [← ZMod.val_intCast, hres x hx i]

theorem card_symmetric_box_residues_le {d : ℕ}
    (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q)
    (T : Finset (Fin d → ZMod q))
    (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ s, (fun i => (x i : ZMod q)) ∈ T) :
    s.card ≤ (2 * (R / q) + 2) ^ d * T.card := by
  classical
  apply card_le_mul_card_image_of_maps_to hres
  intro r hr
  apply card_symmetric_box_zmod_residue_le _ R q hq r
  · intro x hx i
    exact hbox x (mem_filter.mp hx).1 i
  · intro x hx i
    exact congrFun (mem_filter.mp hx).2 i

theorem card_symmetric_box_residues_le_real {d : ℕ}
    (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
    (T : Finset (Fin d → ZMod q))
    (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ s, (fun i => (x i : ZMod q)) ∈ T) :
    (s.card : ℝ) ≤ (4 * (R : ℝ) / (q : ℝ)) ^ d * (T.card : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hratio : 1 ≤ (R : ℝ) / (q : ℝ) := by
    apply (le_div_iff₀ hq0).mpr
    simpa using (show (q : ℝ) ≤ R by exact_mod_cast hqR)
  have hdiv : ((R / q : ℕ) : ℝ) ≤ (R : ℝ) / (q : ℝ) := Nat.cast_div_le
  have hfactor : ((2 * (R / q) + 2 : ℕ) : ℝ) ≤ 4 * (R : ℝ) / (q : ℝ) := by
    push_cast
    rw [mul_div_assoc]
    linarith
  have hcount : (s.card : ℝ) ≤
      ((2 * (R / q) + 2 : ℕ) : ℝ) ^ d * (T.card : ℝ) := by
    exact_mod_cast card_symmetric_box_residues_le s R q hq T hbox hres
  exact hcount.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hfactor d) (by positivity))

theorem card_symmetric_box_of_residue_density_le {d : ℕ}
    (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
    (T : Finset (Fin d → ZMod q)) (D : ℝ) (hD : 0 < D)
    (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ s, (fun i => (x i : ZMod q)) ∈ T)
    (hT : (T.card : ℝ) ≤ (q : ℝ) ^ d / D) :
    (s.card : ℝ) ≤ 4 ^ d * (R : ℝ) ^ d / D := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    (s.card : ℝ) ≤ (4 * (R : ℝ) / (q : ℝ)) ^ d * (T.card : ℝ) :=
      card_symmetric_box_residues_le_real s R q hq hqR T hbox hres
    _ ≤ (4 * (R : ℝ) / (q : ℝ)) ^ d * ((q : ℝ) ^ d / D) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ = 4 ^ d * (R : ℝ) ^ d / D := by
      rw [div_pow, mul_pow]
      field_simp

end Problem355.LatticeShell

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroMomentSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.ZeroMoment

theorem geometric_sum_le {B : ℝ} (hB : 2 ≤ B) (e : ℕ) :
    ∑ j ∈ Finset.range (e + 1), B ^ j ≤ 2 * B ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hp : 0 ≤ B ^ e := pow_nonneg (by linarith) _
      nlinarith

theorem diagonal_sum_le {B : ℝ} (hB : 2 ≤ B) (b e : ℕ) :
    ∑ j ∈ Finset.range (e + 1), B ^ (2 * j - (j - b)) ≤
      2 * B ^ (b + e) := by
  have hB1 : 1 ≤ B := by linarith
  calc
    ∑ j ∈ Finset.range (e + 1), B ^ (2 * j - (j - b)) ≤
        ∑ j ∈ Finset.range (e + 1), B ^ (b + j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_right₀ hB1 (by omega)
    _ = B ^ b * ∑ j ∈ Finset.range (e + 1), B ^ j := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
    _ ≤ B ^ b * (2 * B ^ e) :=
      mul_le_mul_of_nonneg_left (geometric_sum_le hB e) (by positivity)
    _ = 2 * B ^ (b + e) := by rw [pow_add]; ring

theorem cubic_moment_of_tail {α : Type*} [DecidableEq α]
    (S : Finset α) (v : α → ℕ) {B A : ℝ} (b e : ℕ)
    (hB : 2 ≤ B) (hA : 0 ≤ A)
    (hv : ∀ x ∈ S, v x ≤ e)
    (htail : ∀ j ≤ e,
      ((S.filter fun x => j ≤ v x).card : ℝ) ≤ A / B ^ (j + (j - b))) :
    ∑ x ∈ S, B ^ (3 * v x) ≤ 2 * A * B ^ (b + e) := by
  have hB0 : 0 < B := by linarith
  have hterm (x : α) (hx : x ∈ S) :
      B ^ (3 * v x) ≤ ∑ j ∈ Finset.range (e + 1),
        if j ≤ v x then B ^ (3 * j) else 0 := by
    have hmem : v x ∈ Finset.range (e + 1) := by
      simpa using Nat.lt_succ_of_le (hv x hx)
    simpa using Finset.single_le_sum
      (f := fun j => if j ≤ v x then B ^ (3 * j) else 0)
      (fun j hj => by split_ifs <;> positivity) hmem
  calc
    ∑ x ∈ S, B ^ (3 * v x) ≤
        ∑ x ∈ S, ∑ j ∈ Finset.range (e + 1),
          if j ≤ v x then B ^ (3 * j) else 0 :=
      Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.range (e + 1),
        B ^ (3 * j) * ((S.filter fun x => j ≤ v x).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ ≤ ∑ j ∈ Finset.range (e + 1),
        B ^ (3 * j) * (A / B ^ (j + (j - b))) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left (htail j (by simpa using hj))
      positivity
    _ = A * ∑ j ∈ Finset.range (e + 1), B ^ (2 * j - (j - b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have he : 3 * j - (j + (j - b)) = 2 * j - (j - b) := by omega
      rw [← he, pow_sub₀ B hB0.ne' (by omega)]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ A * (2 * B ^ (b + e)) :=
      mul_le_mul_of_nonneg_left (diagonal_sum_le hB b e) hA
    _ = 2 * A * B ^ (b + e) := by ring

end Problem355.ZeroMoment

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticeMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.LatticeMoment

open Finset

theorem cubic_moment_of_residue_counts
    (S : Finset (Fin 3 → ℤ)) (v : (Fin 3 → ℤ) → ℕ)
    (B R b e : ℕ) (hB : 2 ≤ B) (hR : B ^ e ≤ R)
    (T : ∀ j : ℕ, Finset (Fin 3 → ZMod (B ^ j)))
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hv : ∀ x ∈ S, v x ≤ e)
    (hres : ∀ j ≤ e, ∀ x ∈ S, j ≤ v x →
      (fun i => (x i : ZMod (B ^ j))) ∈ T j)
    (hT : ∀ j ≤ e, ((T j).card : ℝ) ≤
      (B : ℝ) ^ (3 * j) / (B : ℝ) ^ (j + (j - b))) :
    ∑ x ∈ S, (B : ℝ) ^ (3 * v x) ≤
      128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  classical
  have hB0 : 0 < B := by omega
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have htail : ∀ j ≤ e,
      ((S.filter fun x => j ≤ v x).card : ℝ) ≤
        (64 * (R : ℝ) ^ 3) / (B : ℝ) ^ (j + (j - b)) := by
    intro j hj
    have hq : 0 < B ^ j := pow_pos hB0 _
    have hqR : B ^ j ≤ R :=
      (Nat.pow_le_pow_right (by omega : 1 ≤ B) hj).trans hR
    have hdensity : ((T j).card : ℝ) ≤
        ((B ^ j : ℕ) : ℝ) ^ 3 / (B : ℝ) ^ (j + (j - b)) := by
      simpa only [Nat.cast_pow, ← pow_mul, Nat.mul_comm j 3] using hT j hj
    have hc := LatticeShell.card_symmetric_box_of_residue_density_le
      (S.filter fun x => j ≤ v x) R (B ^ j) hq hqR (T j)
      ((B : ℝ) ^ (j + (j - b))) (by positivity)
      (fun x hx i => hbox x (mem_filter.mp hx).1 i)
      (fun x hx => hres j hj x (mem_filter.mp hx).1 (mem_filter.mp hx).2)
      hdensity
    norm_num only [show (4 : ℝ) ^ 3 = 64 by norm_num] at hc
    exact hc
  calc
    ∑ x ∈ S, (B : ℝ) ^ (3 * v x) ≤
        2 * (64 * (R : ℝ) ^ 3) * (B : ℝ) ^ (b + e) :=
      ZeroMoment.cubic_moment_of_tail S v b e hBR (by positivity) hv htail
    _ = 128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by ring

theorem cubic_divisor_moment_of_residue_counts
    (S : Finset (Fin 3 → ℤ)) (g : (Fin 3 → ℤ) → ℕ)
    (B R b e : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R)
    (T : ∀ j : ℕ, Finset (Fin 3 → ZMod (B ^ j)))
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hg : ∀ x ∈ S, g x ∣ B ^ e)
    (hres : ∀ j ≤ e, ∀ x ∈ S, B ^ j ∣ g x →
      (fun i => (x i : ZMod (B ^ j))) ∈ T j)
    (hT : ∀ j ≤ e, ((T j).card : ℝ) ≤
      (B : ℝ) ^ (3 * j) / (B : ℝ) ^ (j + (j - b))) :
    ∑ x ∈ S, (g x : ℝ) ^ 3 ≤
      128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  classical
  have hex : ∀ x : Fin 3 → ℤ, ∃ a ≤ e, x ∈ S → g x = B ^ a := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨a, ha, hga⟩ := (Nat.dvd_prime_pow hB).mp (hg x hx)
      exact ⟨a, ha, fun _ => hga⟩
    · exact ⟨0, Nat.zero_le _, fun h => (hx h).elim⟩
  choose v hv hgv using hex
  have hm := cubic_moment_of_residue_counts S v B R b e hB.two_le hR T hbox
    (fun x _ => hv x) (fun j hj x hx hjv => hres j hj x hx (by
      rw [hgv x hx]
      exact Nat.pow_dvd_pow B hjv)) hT
  calc
    ∑ x ∈ S, (g x : ℝ) ^ 3 = ∑ x ∈ S, (B : ℝ) ^ (3 * v x) := by
      apply sum_congr rfl
      intro x hx
      rw [hgv x hx, Nat.cast_pow, ← pow_mul, Nat.mul_comm (v x) 3]
    _ ≤ 128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := hm

end Problem355.LatticeMoment

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegralKernelMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.LatticeMoment

theorem cast_mulVec_eq_zero_of_dvd_rows {m d : ℕ}
    (C : Matrix (Fin m) (Fin d) ℤ) (x : Fin d → ℤ) (g q : ℕ)
    (hqg : q ∣ g) (hrows : ∀ i, (g : ℤ) ∣ (C.mulVec x) i) :
    (C.map (Int.castRingHom (ZMod q))).mulVec (fun i => (x i : ZMod q)) = 0 := by
  ext i
  have hqgz : (q : ℤ) ∣ (g : ℤ) := by exact_mod_cast hqg
  have hz : ((C.mulVec x) i : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hqgz.trans (hrows i))
  simpa [Matrix.mulVec, dotProduct] using hz

theorem cubic_divisor_moment_of_diagonal_form
    (S : Finset (Fin 3 → ℤ)) (g : (Fin 3 → ℤ) → ℕ)
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R) (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hg : ∀ x ∈ S, g x ∣ B ^ e)
    (hrows : ∀ x ∈ S, ∀ i, (g x : ℤ) ∣ (C.mulVec x) i) :
    ∑ x ∈ S, (g x : ℝ) ^ 3 ≤
      128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  classical
  let : NeZero B := ⟨hB.ne_zero⟩
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB.pos
  let T : ∀ j : ℕ, Finset (Fin 3 → ZMod (B ^ j)) := fun j =>
    Finset.univ.filter fun x => (C.map (Int.castRingHom (ZMod (B ^ j)))).mulVec x = 0
  apply cubic_divisor_moment_of_residue_counts S g B R b e hB hR T hbox hg
  · intro j hj x hx hjg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      cast_mulVec_eq_zero_of_dvd_rows C x (g x) (B ^ j) hjg (hrows x hx)⟩
  · intro j hj
    have hc := DiagonalKernel.card_kernel_reduction_density B k j b e
      (hj.trans hek) hj (C.map (Int.castRingHom (ZMod (B ^ k)))) P Q hC
    have hmap : (C.map (Int.castRingHom (ZMod (B ^ k)))).map
        (ZMod.castHom (pow_dvd_pow B (hj.trans hek)) (ZMod (B ^ j))) =
        C.map (Int.castRingHom (ZMod (B ^ j))) := by
      ext i l
      simp
    rw [hmap] at hc
    have htc : (T j).card = Nat.card
        (DiagonalKernel.Kernel (C.map (Int.castRingHom (ZMod (B ^ j))))) := by
      simp [T, DiagonalKernel.Kernel, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hc' : (T j).card * B ^ (j + (j - b)) = B ^ (3 * j) := by
      rw [htc]
      simpa only [← pow_mul, Nat.mul_comm j 3] using hc
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) ^ (j + (j - b)))).mpr
    exact_mod_cast hc'.le

end Problem355.LatticeMoment

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PairingDivisor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PairingDivisor

variable {ι : Type*} [Fintype ι]

theorem exists_pairing_divisor
    (L : AddSubgroup (ι → ℤ)) (x z : ι → ℤ) (hprimitive : dotProduct x z = 1)
    (E : ℕ) (hE : 0 < E) (hcontain : ∀ v : ι → ℤ, E • v ∈ L) :
    ∃ g : ℕ, 0 < g ∧ g ∣ E ∧
      L.map (dotHom x) = AddSubgroup.zmultiples (g : ℤ) ∧
      (∀ v ∈ L, (g : ℤ) ∣ dotProduct x v) ∧
      ∃ u ∈ L, dotProduct x u = (g : ℤ) := by
  have hEimage : (E : ℤ) ∈ L.map (dotHom x) := by
    apply AddSubgroup.mem_map.mpr
    refine ⟨E • z, hcontain z, ?_⟩
    change dotProduct x (E • z) = (E : ℤ)
    rw [dotProduct_smul, hprimitive]
    simp
  obtain ⟨a, ha⟩ :=
    (L.map (dotHom x)).isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance
  have ha0 : a ≠ 0 := by
    intro hz
    have hbad := hEimage
    rw [← ha, hz] at hbad
    have heq : (E : ℤ) = 0 := by simpa using hbad
    exact (Nat.ne_of_gt hE) (by exact_mod_cast heq)
  have hmap : L.map (dotHom x) = AddSubgroup.zmultiples (a.natAbs : ℤ) :=
    ((Int.zmultiples_natAbs a).trans ha).symm
  have hdivE : (a.natAbs : ℤ) ∣ (E : ℤ) := by
    apply Int.mem_zmultiples_iff.mp
    rw [← hmap]
    exact hEimage
  refine ⟨a.natAbs, Int.natAbs_pos.mpr ha0, by exact_mod_cast hdivE, hmap, ?_, ?_⟩
  · intro v hv
    apply Int.mem_zmultiples_iff.mp
    rw [← hmap]
    exact AddSubgroup.mem_map.mpr ⟨v, hv, rfl⟩
  · have hgmem : (a.natAbs : ℤ) ∈ L.map (dotHom x) := by
      rw [hmap]
      exact AddSubgroup.mem_zmultiples _
    obtain ⟨u, hu, heq⟩ := AddSubgroup.mem_map.mp hgmem
    exact ⟨u, hu, heq⟩

theorem integer_subgroup_eq_zmultiples_index (H : AddSubgroup ℤ) :
    H = AddSubgroup.zmultiples (H.index : ℤ) := by
  obtain ⟨a, ha⟩ := H.isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance
  have hindex : H.index = a.natAbs := by rw [← ha, Int.index_zmultiples]
  rw [hindex, Int.zmultiples_natAbs]
  exact ha.symm

theorem pairing_image (L : AddSubgroup (ι → ℤ)) (x : ι → ℤ) :
    L.map (dotHom x) = AddSubgroup.zmultiples (pairingDivisor L x : ℤ) :=
  integer_subgroup_eq_zmultiples_index _

theorem pairingDivisor_dvd_pairing (L : AddSubgroup (ι → ℤ)) (x v : ι → ℤ)
    (hv : v ∈ L) : (pairingDivisor L x : ℤ) ∣ dotProduct x v := by
  apply Int.mem_zmultiples_iff.mp
  rw [← pairing_image]
  exact AddSubgroup.mem_map.mpr ⟨v, hv, rfl⟩

theorem exists_pairing_eq_divisor (L : AddSubgroup (ι → ℤ)) (x : ι → ℤ) :
    ∃ u ∈ L, dotProduct x u = (pairingDivisor L x : ℤ) := by
  have hgmem : (pairingDivisor L x : ℤ) ∈ L.map (dotHom x) := by
    rw [pairing_image]
    exact AddSubgroup.mem_zmultiples _
  exact AddSubgroup.mem_map.mp hgmem

theorem pairingDivisor_pos_and_dvd
    (L : AddSubgroup (ι → ℤ)) (x z : ι → ℤ) (hprimitive : dotProduct x z = 1)
    (E : ℕ) (hE : 0 < E) (hcontain : ∀ v : ι → ℤ, E • v ∈ L) :
    0 < pairingDivisor L x ∧ pairingDivisor L x ∣ E := by
  obtain ⟨g, hg, hdiv, himage, _, _⟩ :=
    exists_pairing_divisor L x z hprimitive E hE hcontain
  have heq : pairingDivisor L x = g := by
    unfold pairingDivisor
    rw [himage, Int.index_zmultiples, Int.natAbs_natCast]
  exact heq.symm ▸ ⟨hg, hdiv⟩

end Problem355.PairingDivisor

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PairingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.LatticeMoment

open PairingDivisor

theorem pairing_divisor_moment_of_diagonal_form
    (S : Finset (Fin 3 → ℤ)) (L : AddSubgroup (Fin 3 → ℤ))
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R) (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hprimitive : ∀ x ∈ S, ∃ z : Fin 3 → ℤ, dotProduct x z = 1)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L) :
    ∑ x ∈ S, (pairingDivisor L x : ℝ) ^ 3 ≤
      128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  apply cubic_divisor_moment_of_diagonal_form S (pairingDivisor L) C
    B R b e k hB hR hek P Q hC hbox
  · intro x hx
    obtain ⟨z, hz⟩ := hprimitive x hx
    exact (pairingDivisor_pos_and_dvd L x z hz (B ^ e)
      (pow_pos hB.pos _) hcontain).2
  · intro x hx i
    simpa only [Matrix.mulVec, dotProduct_comm] using
      pairingDivisor_dvd_pairing L x (C i) (hrows i)

end Problem355.LatticeMoment

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroAffineShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ZeroAffineShell

open scoped BigOperators Matrix
open PairingDivisor PrimitiveNormal

theorem pairing_moment_euclidean_shell
    (S : Finset (Fin 3 → ℤ)) (L : AddSubgroup (Fin 3 → ℤ))
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ 2 * R) (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hnorm : ∀ x ∈ S, ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L) :
    ∑ x ∈ S, (pairingDivisor L x : ℝ) ^ 3 ≤
      1024 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  have hbox : ∀ x ∈ S, ∀ i, -((2 * R : ℕ) : ℤ) ≤ x i ∧
      x i ≤ ((2 * R : ℕ) : ℤ) := by
    intro x hx i
    have hcoord : |(x i : ℝ)| ≤ ‖toEuclidean x‖ := by
      change ‖(toEuclidean x).ofLp i‖ ≤ ‖toEuclidean x‖
      exact PiLp.norm_apply_le _ _
    have hbound : |(x i : ℝ)| ≤ (2 * R : ℕ) := by
      push_cast
      exact hcoord.trans (hnorm x hx).le
    have hz : |x i| ≤ ((2 * R : ℕ) : ℤ) := by exact_mod_cast hbound
    exact abs_le.mp hz
  have hm := LatticeMoment.pairing_divisor_moment_of_diagonal_form
    S L C B (2 * R) b e k hB hR hek P Q hC hbox
    (fun x hx => (isPrimitive_iff_exists_dot_eq_one x).mp (hprimitive x hx))
    hcontain hrows
  convert hm using 1
  push_cast
  ring

private lemma row_cubic_constant (W N J : ℝ) :
    W * (9 * Real.pi * (4 * N) ^ 2 / J) ^ 3 =
      (W * (144 * Real.pi) ^ 3 * N ^ 6) / J ^ 3 := by
  ring

theorem weighted_spanning_triples_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (hdim : Module.finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (T : Finset (Fin 3 → L)) (W : (Fin 3 → L) → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ a ∈ T, W a ≤ W₀)
    (hshort : ∀ a ∈ T, ∀ i, ‖(a i : E)‖ ≤ 4 * N)
    (hpair : ∀ a ∈ T, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : E), (a j : E)]) :
    (∑ a ∈ T, W a) ≤ (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) /
      ZLattice.covolume L ^ 3 := by
  have hc := LatticePacking.plane_spanning_triples_card_le hdim L T (4 * N)
    (by positivity) hshort hpair
  generalize hJ : ZLattice.covolume L MeasureTheory.volume = J at hc ⊢
  calc
    (∑ a ∈ T, W a) ≤ ∑ _a ∈ T, W₀ := Finset.sum_le_sum hW
    _ = W₀ * (T.card : ℝ) := by simp [mul_comm]
    _ ≤ W₀ * (9 * Real.pi * (4 * N) ^ 2 / J) ^ 3 :=
      mul_le_mul_of_nonneg_left hc hW₀
    _ = _ := row_cubic_constant W₀ N (J)

theorem weighted_lattice_fibre_le
    (x z : Fin 3 → ℤ) (hz : dotProduct x z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℕ) (hE : 0 < E)
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (T : Finset (Fin 3 → IntegralPlaneLattice.latticeIn x L))
    (W : (Fin 3 → IntegralPlaneLattice.latticeIn x L) → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ a ∈ T, W a ≤ W₀)
    (hshort : ∀ a ∈ T, ∀ i,
      ‖(a i : IntegralPlaneLattice.plane x)‖ ≤ 4 * N)
    (hpair : ∀ a ∈ T, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : IntegralPlaneLattice.plane x),
        (a j : IntegralPlaneLattice.plane x)]) :
    (∑ a ∈ T, W a) ≤ (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) /
      ZLattice.covolume (IntegralPlaneLattice.latticeIn x L) ^ 3 := by
  let := IntegralPlaneLattice.latticeIn_isZLattice x z hz L
    (E : ℤ) (by exact_mod_cast Nat.ne_of_gt hE)
    (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
  exact weighted_spanning_triples_le (IntegralPlaneLattice.plane_finrank x z hz)
    (IntegralPlaneLattice.latticeIn x L) T W N W₀ hN hW₀ hW hshort hpair

theorem canonical_pairing_covolume
    (x : Fin 3 → ℤ) (hx : IsPrimitive x)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℕ) (hE : 0 < E)
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    ZLattice.covolume (IntegralPlaneLattice.latticeIn x L) =
      (L.toAddSubgroup.index : ℝ) * ‖toEuclidean x‖ /
        (pairingDivisor L.toAddSubgroup x : ℝ) := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp hx
  have hg := (pairingDivisor_pos_and_dvd L.toAddSubgroup x z hz E hE hcontain).1
  obtain ⟨u, hu, hval⟩ := exists_pairing_eq_divisor L.toAddSubgroup x
  have hc := IntegralPlaneLattice.latticeIn_covolume x z hz L (E : ℤ)
    (by exact_mod_cast Nat.ne_of_gt hE)
    (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
    (pairingDivisor L.toAddSubgroup x : ℤ) (by exact_mod_cast hg)
    (fun v => pairingDivisor_dvd_pairing L.toAddSubgroup x v v.property)
    ⟨u, hu⟩ hval
  simpa only [Int.cast_natCast, IntegralPlaneLattice.castVec,
    PrimitiveNormal.toEuclidean] using hc

theorem weighted_lattice_shell_le
    (S : Finset (Fin 3 → ℤ)) (L : Submodule ℤ (Fin 3 → ℤ))
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hRpos : 0 < R)
    (hR : B ^ e ≤ 2 * R) (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hnorm : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L)
    (T : ∀ x : Fin 3 → ℤ, Finset (Fin 3 → IntegralPlaneLattice.latticeIn x L))
    (W : ∀ x : Fin 3 → ℤ, (Fin 3 → IntegralPlaneLattice.latticeIn x L) → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ x ∈ S, ∀ a ∈ T x, W x a ≤ W₀)
    (hshort : ∀ x ∈ S, ∀ a ∈ T x, ∀ i,
      ‖(a i : IntegralPlaneLattice.plane x)‖ ≤ 4 * N)
    (hpair : ∀ x ∈ S, ∀ a ∈ T x, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : IntegralPlaneLattice.plane x),
        (a j : IntegralPlaneLattice.plane x)])
    (hindex : L.toAddSubgroup.index = B ^ (b + e)) :
    (∑ x ∈ S, ∑ a ∈ T x, W x a) ≤
      (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) * 1024 /
        ((B : ℝ) ^ (b + e)) ^ 2 := by
  classical
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB.pos
  have hE : (B ^ e : ℕ) > 0 := pow_pos hB.pos _
  apply ZeroShell.affine_shell_sum_le S
    (fun x => ∑ a ∈ T x, W x a)
    (fun x => (pairingDivisor L.toAddSubgroup x : ℝ))
    (fun x => ‖toEuclidean x‖)
    (fun x => ZLattice.covolume (IntegralPlaneLattice.latticeIn x L))
    (R : ℝ) ((B : ℝ) ^ (b + e))
    (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) 1024
    (by exact_mod_cast hRpos) (by positivity) (by positivity)
  · intro x hx
    obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp (hprimitive x hx)
    exact_mod_cast (pairingDivisor_pos_and_dvd L.toAddSubgroup x z hz
      (B ^ e) hE hcontain).1
  · exact fun x hx => (hnorm x hx).1
  · intro x hx
    rw [canonical_pairing_covolume x (hprimitive x hx) L (B ^ e) hE hcontain,
      hindex, Nat.cast_pow]
  · intro x hx
    obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp (hprimitive x hx)
    exact weighted_lattice_fibre_le x z hz L (B ^ e) hE hcontain
      (T x) (W x) N W₀ hN hW₀ (hW x hx) (hshort x hx) (hpair x hx)
  · exact pairing_moment_euclidean_shell S L.toAddSubgroup C B R b e k
      hB hR hek P Q hC (fun x hx => (hnorm x hx).2) hprimitive hcontain hrows

theorem weighted_lattice_shell_le_of_short_exclusion
    (S : Finset (Fin 3 → ℤ)) (L : Submodule ℤ (Fin 3 → ℤ))
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hRpos : 0 < R)
    (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hnorm : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L)
    (T : ∀ x : Fin 3 → ℤ, Finset (Fin 3 → IntegralPlaneLattice.latticeIn x L))
    (W : ∀ x : Fin 3 → ℤ, (Fin 3 → IntegralPlaneLattice.latticeIn x L) → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ x ∈ S, ∀ a ∈ T x, W x a ≤ W₀)
    (hshort : ∀ x ∈ S, ∀ a ∈ T x, ∀ i,
      ‖(a i : IntegralPlaneLattice.plane x)‖ ≤ 4 * N)
    (hpair : ∀ x ∈ S, ∀ a ∈ T x, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : IntegralPlaneLattice.plane x),
        (a j : IntegralPlaneLattice.plane x)])
    (hexclude : ∀ x ∈ S, ∀ a ∈ T x, 0 < W x a →
      ((B : ℝ) ^ k) ^ 2 < ‖toEuclidean x‖)
    (hindex : L.toAddSubgroup.index = B ^ (b + e)) :
    (∑ x ∈ S, ∑ a ∈ T x, W x a) ≤
      (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) * 1024 /
        ((B : ℝ) ^ (b + e)) ^ 2 := by
  by_cases hR : B ^ e ≤ 2 * R
  · exact weighted_lattice_shell_le S L C B R b e k hB hRpos hR hek
      P Q hC hnorm hprimitive hcontain hrows T W N W₀ hN hW₀
      hW hshort hpair hindex
  · have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB.one_le
    have hpow1 : (1 : ℝ) ≤ (B : ℝ) ^ k := one_le_pow₀ hB1
    have hEH : (B : ℝ) ^ e ≤ (B : ℝ) ^ k := pow_le_pow_right₀ hB1 hek
    have hsmall : (2 : ℝ) * (R : ℝ) < (B : ℝ) ^ e := by
      exact_mod_cast (Nat.lt_of_not_ge hR)
    have hwzero : ∀ x ∈ S, ∀ a ∈ T x, W x a ≤ 0 := by
      intro x hx a ha
      apply le_of_not_gt
      intro hw
      have hs := (hnorm x hx).2
      have hl := hexclude x hx a ha hw
      nlinarith
    calc
      (∑ x ∈ S, ∑ a ∈ T x, W x a) ≤ 0 :=
        Finset.sum_nonpos (fun x hx => Finset.sum_nonpos (hwzero x hx))
      _ ≤ _ := by positivity

end Problem355.ZeroAffineShell

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MatrixAffineShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.MatrixAffineShell

open scoped BigOperators Matrix
open Matrix RowLatticeMatrices PrimitiveNormal

theorem weighted_matrix_shell_le_of_short_exclusion
    (S : Finset (Fin 3 → ℤ)) (L : Submodule ℤ (Fin 3 → ℤ))
    (C : IntMatrix) (B R b e k : ℕ) (hB : B.Prime) (hRpos : 0 < R)
    (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hnorm : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L)
    (F : (Fin 3 → ℤ) → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    (W : (Fin 3 → ℤ) → IntMatrix → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ x ∈ S, ∀ A ∈ F x, W x A ≤ W₀)
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hexclude : ∀ x ∈ S, ∀ A ∈ F x, 0 < W x A →
      ((B : ℝ) ^ k) ^ 2 < ‖toEuclidean x‖)
    (hindex : L.toAddSubgroup.index = B ^ (b + e)) :
    (∑ x ∈ S, ∑ A ∈ F x, W x A) ≤
      (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) * 1024 /
        ((B : ℝ) ^ (b + e)) ^ 2 := by
  let T := fun x => rowFamily x L (F x) (hF x)
  let V := fun x u => W x ((rowsEquiv x L).symm u).val
  have h := ZeroAffineShell.weighted_lattice_shell_le_of_short_exclusion S L C B R b e k
    hB hRpos hek P Q hC hnorm hprimitive hcontain hrows T V N W₀
    hN hW₀
    (fun x hx u hu => hW x hx _ ((mem_rowFamily x L (F x) (hF x) u).mp hu))
    (fun x hx => rowFamily_norm_le_four_mul x L (F x) (hF x) hN (hcoord x hx))
    (fun x hx => rowFamily_independent_of_projections x L (F x) (hF x) (hproj x hx))
    (fun x hx u hu hpos => hexclude x hx _
      ((mem_rowFamily x L (F x) (hF x) u).mp hu) hpos)
    hindex
  have heq : (∑ x ∈ S, ∑ u ∈ T x, V x u) = ∑ x ∈ S, ∑ A ∈ F x, W x A := by
    apply Finset.sum_congr rfl
    intro x hx
    exact sum_rowFamily x L (F x) (hF x) (W x)
  rw [heq] at h
  exact h

end Problem355.MatrixAffineShell

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LatticeResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.LatticeResidues

open Finset

theorem eq_of_ediv_eq_of_emod_eq {a b q : ℤ}
    (hdiv : a / q = b / q) (hmod : a % q = b % q) : a = b := by
  calc
    a = a / q * q + a % q := (Int.ediv_mul_add_emod a q).symm
    _ = b / q * q + b % q := by rw [hdiv, hmod]
    _ = b := Int.ediv_mul_add_emod b q

theorem card_residue_interval_le (S : Finset ℤ) (lo hi q r : ℤ)
    (hq : 0 < q)
    (hS : ∀ x ∈ S, lo ≤ x ∧ x ≤ hi ∧ x % q = r) :
    S.card ≤ (hi / q - lo / q + 1).toNat := by
  have hinj : Set.InjOn (fun x : ℤ => x / q) S := by
    intro a ha b hb hab
    exact eq_of_ediv_eq_of_emod_eq hab ((hS a ha).2.2.trans (hS b hb).2.2.symm)
  have hsub : S.image (fun x : ℤ => x / q) ⊆ Icc (lo / q) (hi / q) := by
    intro x hx
    rcases mem_image.mp hx with ⟨a, ha, rfl⟩
    exact mem_Icc.mpr ⟨Int.ediv_le_ediv hq (hS a ha).1,
      Int.ediv_le_ediv hq (hS a ha).2.1⟩
  calc
    S.card = (S.image (fun x : ℤ => x / q)).card := (card_image_of_injOn hinj).symm
    _ ≤ (Icc (lo / q) (hi / q)).card := card_le_card hsub
    _ = (hi / q - lo / q + 1).toNat := by
      rw [Int.card_Icc]
      congr 1
      omega

theorem card_residue_box_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (ι → ℤ)) (lo hi r : ι → ℤ) (q : ℤ)
    (hq : 0 < q)
    (hS : ∀ x ∈ S, ∀ i, lo i ≤ x i ∧ x i ≤ hi i ∧ x i % q = r i) :
    S.card ≤ ∏ i, (hi i / q - lo i / q + 1).toNat := by
  classical
  let T : ι → Finset ℤ := fun i => (Icc (lo i) (hi i)).filter (fun x => x % q = r i)
  have hsub : S ⊆ Fintype.piFinset T := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(hS x hx i).1, (hS x hx i).2.1⟩,
      (hS x hx i).2.2⟩
  calc
    S.card ≤ (Fintype.piFinset T).card := card_le_card hsub
    _ = ∏ i, (T i).card := Fintype.card_piFinset T
    _ ≤ ∏ i, (hi i / q - lo i / q + 1).toNat := by
      apply prod_le_prod'
      intro i _
      apply card_residue_interval_le (T i) (lo i) (hi i) q (r i) hq
      intro x hx
      rcases mem_filter.mp hx with ⟨hbox, hmod⟩
      exact ⟨(mem_Icc.mp hbox).1, (mem_Icc.mp hbox).2, hmod⟩

theorem card_residue_cube_le (d : ℕ) (S : Finset (Fin d → ℤ))
    (lo hi q : ℤ) (r : Fin d → ℤ) (hq : 0 < q)
    (hS : ∀ x ∈ S, ∀ i, lo ≤ x i ∧ x i ≤ hi ∧ x i % q = r i) :
    S.card ≤ (hi / q - lo / q + 1).toNat ^ d := by
  simpa using card_residue_box_le S (fun _ => lo) (fun _ => hi) r q hq hS

theorem card_residue_classes_cube_le (d : ℕ) (S A : Finset (Fin d → ℤ))
    (lo hi q : ℤ) (hq : 0 < q)
    (hbox : ∀ x ∈ S, ∀ i, lo ≤ x i ∧ x i ≤ hi)
    (hres : ∀ x ∈ S, (fun i => x i % q) ∈ A) :
    S.card ≤ A.card * (hi / q - lo / q + 1).toNat ^ d := by
  classical
  calc
    S.card = ∑ r ∈ A, (S.filter (fun x => (fun i => x i % q) = r)).card :=
      card_eq_sum_card_fiberwise hres
    _ ≤ ∑ _r ∈ A, (hi / q - lo / q + 1).toNat ^ d := by
      apply sum_le_sum
      intro r _hr
      apply card_residue_cube_le d _ lo hi q r hq
      intro x hx i
      rcases mem_filter.mp hx with ⟨hxS, hxres⟩
      exact ⟨(hbox x hxS i).1, (hbox x hxS i).2, congrFun hxres i⟩
    _ = A.card * (hi / q - lo / q + 1).toNat ^ d := by simp

theorem symmetric_quotient_bound (R q : ℤ) (_hR : 0 ≤ R) (hq : 0 < q) :
    (R / q - (-R) / q + 1).toNat ≤ (2 * (R / q) + 2).toNat := by
  apply Int.toNat_le_toNat
  rw [Int.neg_ediv]
  have hsign : q.sign = 1 := Int.sign_eq_one_of_pos hq
  rw [hsign]
  split_ifs <;> omega

theorem card_symmetric_residue_classes_le (d : ℕ) (S A : Finset (Fin d → ℤ))
    (R q : ℤ) (hR : 0 ≤ R) (hq : 0 < q)
    (hbox : ∀ x ∈ S, ∀ i, -R ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ S, (fun i => x i % q) ∈ A) :
    S.card ≤ A.card * (2 * (R / q) + 2).toNat ^ d := by
  exact (card_residue_classes_cube_le d S A (-R) R q hq hbox hres).trans
    (Nat.mul_le_mul_left A.card (Nat.pow_le_pow_left (symmetric_quotient_bound R q hR hq) d))

theorem card_symmetric_residue_classes_mul_pow_le (d : ℕ)
    (S A : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ (R : ℤ))
    (hres : ∀ x ∈ S, (fun i => x i % (q : ℤ)) ∈ A) :
    S.card * q ^ d ≤ A.card * (4 * R) ^ d := by
  have hs : S.card ≤ A.card * (2 * (R / q) + 2) ^ d := by
    have h := card_symmetric_residue_classes_le d S A (R : ℤ) (q : ℤ)
      (by positivity) (by exact_mod_cast hq) hbox hres
    rw [← Int.natCast_ediv, ← Nat.cast_ofNat, ← Nat.cast_mul,
      ← Nat.cast_ofNat, ← Nat.cast_add, Int.toNat_natCast] at h
    exact h
  have hscale : (2 * (R / q) + 2) * q ≤ 4 * R := by
    have hfloor : R / q * q ≤ R := Nat.div_mul_le_self R q
    nlinarith
  calc
    S.card * q ^ d ≤ (A.card * (2 * (R / q) + 2) ^ d) * q ^ d :=
      Nat.mul_le_mul_right (q ^ d) hs
    _ = A.card * ((2 * (R / q) + 2) * q) ^ d := by rw [mul_pow]; ring
    _ ≤ A.card * (4 * R) ^ d :=
      Nat.mul_le_mul_left A.card (Nat.pow_le_pow_left hscale d)

theorem card_thin_residue_classes_mul_sq_le
    (S A : Finset (Fin 3 → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
    (hA : A.card ≤ q)
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ (R : ℤ))
    (hres : ∀ x ∈ S, (fun i => x i % (q : ℤ)) ∈ A) :
    S.card * q ^ 2 ≤ (4 * R) ^ 3 := by
  have h := card_symmetric_residue_classes_mul_pow_le 3 S A R q hq hqR hbox hres
  have h' : (S.card * q ^ 2) * q ≤ ((4 * R) ^ 3) * q := by
    calc
      (S.card * q ^ 2) * q = S.card * q ^ 3 := by ring
      _ ≤ A.card * (4 * R) ^ 3 := h
      _ ≤ q * (4 * R) ^ 3 := Nat.mul_le_mul_right _ hA
      _ = ((4 * R) ^ 3) * q := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right h' hq

theorem card_modular_line_mul_sq_le
    (S : Finset (Fin 3 → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
    (delta : Fin 3 → ZMod q)
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ (R : ℤ))
    (hline : ∀ x ∈ S, ∃ a : ZMod q, ∀ i, (x i : ZMod q) = a * delta i) :
    S.card * q ^ 2 ≤ (4 * R) ^ 3 := by
  classical
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let A : Finset (Fin 3 → ℤ) :=
    univ.image (fun a : ZMod q => fun i => ((a * delta i).val : ℤ))
  apply card_thin_residue_classes_mul_sq_le S A R q hq hqR
  · calc
      A.card ≤ (univ : Finset (ZMod q)).card := card_image_le
      _ = q := by simp
  · exact hbox
  · intro x hx
    obtain ⟨a, ha⟩ := hline x hx
    apply mem_image.mpr
    refine ⟨a, mem_univ _, ?_⟩
    funext i
    rw [← ha i, ZMod.val_intCast]

end Problem355.LatticeResidues

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SpecialNormals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.SpecialNormals

variable {ι : Type*} [DecidableEq ι]

theorem outside_coordinate_zero {R : Type*} [CommRing R]
    (v : ι → R) (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j)
    (hv : v ∈ Submodule.span R {Pi.single i (1 : R) - Pi.single j 1}) :
    v k = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
  have hk := congrFun ha k
  simpa [hki, hkj, Ne.symm hki, Ne.symm hkj] using hk.symm

theorem outside_coordinate_dvd (q : ℕ) (x : ι → ℤ)
    (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j)
    (hx : (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
    (q : ℤ) ∣ x k := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x k) q).mp
    (outside_coordinate_zero _ i j k hki hkj hx)

theorem modulus_le_outside_natAbs (q : ℕ) (x : ι → ℤ)
    (i j k : ι) (hki : k ≠ i) (hkj : k ≠ j) (hxk : x k ≠ 0)
    (hx : (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
    q ≤ (x k).natAbs := by
  simpa using Int.natAbs_le_of_dvd_ne_zero
    (outside_coordinate_dvd q x i j k hki hkj hx) hxk

theorem card_exceptional_normals_mul_sq_le
    (S : Finset (Fin 3 → ℤ)) (R q : ℕ) (hq : 0 < q)
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hbox : ∀ x ∈ S, ∀ t, -(R : ℤ) ≤ x t ∧ x t ≤ (R : ℤ))
    (hnonzero : ∀ x ∈ S, x k ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
    S.card * q ^ 2 ≤ (4 * R) ^ 3 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨x, hx⟩
  · simp [hS]
  have hheight : (x k).natAbs ≤ R := by
    have h := abs_le.mpr (hbox x hx k)
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hqR : q ≤ R :=
    (modulus_le_outside_natAbs q x i j k hki hkj (hnonzero x hx) (hline x hx)).trans hheight
  apply LatticeResidues.card_modular_line_mul_sq_le S R q hq hqR
    (Pi.single i 1 - Pi.single j 1) hbox
  intro y hy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hline y hy)
  refine ⟨a, fun t => ?_⟩
  simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun ha t).symm

theorem card_exceptional_normals_le
    (S : Finset (Fin 3 → ℤ)) (R q : ℕ) (hq : 0 < q)
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hbox : ∀ x ∈ S, ∀ t, -(R : ℤ) ≤ x t ∧ x t ≤ (R : ℤ))
    (hnonzero : ∀ x ∈ S, x k ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}) :
    (S.card : ℝ) ≤ 64 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  apply (le_div_iff₀ (sq_pos_of_pos hqpos)).mpr
  have h := card_exceptional_normals_mul_sq_le S R q hq i j k hki hkj hbox hnonzero hline
  have hreal : (S.card : ℝ) * (q : ℝ) ^ 2 ≤ (4 * (R : ℝ)) ^ 3 := by
    exact_mod_cast h
  nlinarith

end Problem355.SpecialNormals

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SpecialRankTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.SpecialRankTwo

open scoped BigOperators

theorem sum_weights_le {α : Type*} (A : Finset α) (W : α → ℝ)
    (M C : ℝ) (hM : 0 ≤ M) (hW : ∀ a ∈ A, W a ≤ M)
    (hc : (A.card : ℝ) ≤ C) : ∑ a ∈ A, W a ≤ M * C := by
  calc
    ∑ a ∈ A, W a ≤ ∑ _a ∈ A, M := Finset.sum_le_sum hW
    _ = M * (A.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_comm _ _
    _ ≤ M * C := mul_le_mul_of_nonneg_left hc hM

theorem weighted_bound_of_covol_cube {T N R I h M J : ℝ}
    (_hN : 0 ≤ N) (hR : 0 < R) (hI : 0 < I) (hM : 0 ≤ M)
    (hJ : 0 < J) (hcov : I ^ 2 * R ^ 3 ≤ h ^ 2 * J ^ 3)
    (hcount : T ≤ M * (9 * Real.pi * (4 * N) ^ 2 / J) ^ 3) :
    T ≤ (144 * Real.pi) ^ 3 * M * N ^ 6 * h ^ 2 / (I ^ 2 * R ^ 3) := by
  have hden : 0 < I ^ 2 * R ^ 3 := by positivity
  have hinv : 1 / J ^ 3 ≤ h ^ 2 / (I ^ 2 * R ^ 3) := by
    apply (div_le_div_iff₀ (by positivity) hden).mpr
    simpa using hcov
  calc
    T ≤ M * (9 * Real.pi * (4 * N) ^ 2 / J) ^ 3 := hcount
    _ = ((144 * Real.pi) ^ 3 * M * N ^ 6) * (1 / J ^ 3) := by ring
    _ ≤ ((144 * Real.pi) ^ 3 * M * N ^ 6) *
        (h ^ 2 / (I ^ 2 * R ^ 3)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

section OnePlane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weighted_spanning_triples_le
    (hdim : Module.finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Finset (Fin 3 → L)) (W : (Fin 3 → L) → ℝ)
    (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hA : ∀ a ∈ A, ∀ i, ‖(a i : E)‖ ≤ R)
    (hpair : ∀ a ∈ A, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : E), (a j : E)])
    (hW : ∀ a ∈ A, W a ≤ M) :
    ∑ a ∈ A, W a ≤ M * (9 * Real.pi * R ^ 2 / ZLattice.covolume L) ^ 3 := by
  have hc : (A.card : ℝ) ≤ (9 * Real.pi * R ^ 2 / ZLattice.covolume L) ^ 3 :=
    LatticePacking.plane_spanning_triples_card_le (E := E) hdim L A R hR hA hpair
  exact sum_weights_le A W M _ hM hW hc

theorem weighted_spanning_triples_le_shell
    (hdim : Module.finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Finset (Fin 3 → L)) (W : (Fin 3 → L) → ℝ)
    (N R I h M : ℝ) (hN : 0 ≤ N) (hR : 0 < R) (hI : 0 < I)
    (hM : 0 ≤ M)
    (hA : ∀ a ∈ A, ∀ i, ‖(a i : E)‖ ≤ 4 * N)
    (hpair : ∀ a ∈ A, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : E), (a j : E)])
    (hW : ∀ a ∈ A, W a ≤ M)
    (hcov : I ^ 2 * R ^ 3 ≤ h ^ 2 * ZLattice.covolume L ^ 3) :
    ∑ a ∈ A, W a ≤ (144 * Real.pi) ^ 3 * M * N ^ 6 * h ^ 2 /
      (I ^ 2 * R ^ 3) := by
  exact weighted_bound_of_covol_cube hN hR hI hM
    (ZLattice.covolume_pos L MeasureTheory.volume) hcov
    (weighted_spanning_triples_le hdim L A W (4 * N) M
      (by positivity) hM hA hpair hW)

end OnePlane

theorem covolume_cube_lower {I R r g h J : ℝ}
    (hI : 0 < I) (hR : 0 ≤ R) (hr : R ≤ r) (hg : 0 < g)
    (hJ : J = I * r / g) (hg3 : g ^ 3 ≤ I * h ^ 2) :
    I ^ 2 * R ^ 3 ≤ h ^ 2 * J ^ 3 := by
  have hr0 : 0 ≤ r := hR.trans hr
  have hpow : R ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hR hr 3
  have hmul : I ^ 2 * R ^ 3 * g ^ 3 ≤ I ^ 3 * r ^ 3 * h ^ 2 := by
    calc
      I ^ 2 * R ^ 3 * g ^ 3 ≤ I ^ 2 * r ^ 3 * g ^ 3 := by gcongr
      _ ≤ I ^ 2 * r ^ 3 * (I * h ^ 2) :=
        mul_le_mul_of_nonneg_left hg3 (by positivity)
      _ = _ := by ring
  rw [hJ, div_pow, ← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < g ^ 3)).mpr
  nlinarith only [hmul]

theorem special_rank_two_shell_subtype
    (S : Finset (Fin 3 → ℤ)) (E : S → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
    [∀ x, FiniteDimensional ℝ (E x)]
    [∀ x, MeasurableSpace (E x)] [∀ x, BorelSpace (E x)]
    (L : ∀ x, Submodule ℤ (E x))
    [∀ x, DiscreteTopology (L x)] [∀ x, IsZLattice ℝ (L x)]
    (A : ∀ x, Finset (Fin 3 → L x))
    (W : ∀ x, (Fin 3 → L x) → ℝ)
    (R q : ℕ) (hR : 0 < R) (hq : 0 < q)
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hbox : ∀ x ∈ S, ∀ t,
      -((2 * R : ℕ) : ℤ) ≤ x t ∧ x t ≤ ((2 * R : ℕ) : ℤ))
    (hnonzero : ∀ x ∈ S, x k ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (N I h Cw : ℝ) (hN : 0 ≤ N) (hI : 0 < I) (hCw : 0 ≤ Cw)
    (hparam : h ^ 14 ≤ (q : ℝ))
    (hdim : ∀ x, Module.finrank ℝ (E x) = 2)
    (hA : ∀ x, ∀ a ∈ A x, ∀ t, ‖(a t : E x)‖ ≤ 4 * N)
    (hpair : ∀ x, ∀ a ∈ A x, ∃ s t : Fin 3,
      LinearIndependent ℝ ![(a s : E x), (a t : E x)])
    (hW : ∀ x, ∀ a ∈ A x, W x a ≤ Cw * (q : ℝ) * h ^ 12)
    (hcov : ∀ x,
      I ^ 2 * (R : ℝ) ^ 3 ≤ h ^ 2 * ZLattice.covolume (L x) ^ 3) :
    ∑ x : S, ∑ a ∈ A x, W x a ≤
      512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / I ^ 2 := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  let F : ℝ := (144 * Real.pi) ^ 3 * (Cw * (q : ℝ) * h ^ 12) *
    N ^ 6 * h ^ 2 / (I ^ 2 * (R : ℝ) ^ 3)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hfiber : ∀ x : S, ∑ a ∈ A x, W x a ≤ F := by
    intro x
    exact weighted_spanning_triples_le_shell (hdim x) (L x) (A x) (W x)
      N R I h (Cw * (q : ℝ) * h ^ 12) hN hRreal hI (by positivity)
      (hA x) (hpair x) (hW x) (hcov x)
  have hcard : (S.card : ℝ) ≤ 512 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
    calc
      (S.card : ℝ) ≤ 64 * ((2 * R : ℕ) : ℝ) ^ 3 / (q : ℝ) ^ 2 :=
        SpecialNormals.card_exceptional_normals_le S (2 * R) q hq
          i j k hki hkj hbox hnonzero hline
      _ = _ := by push_cast; ring
  have hratio : h ^ 14 / (q : ℝ) ≤ 1 :=
    (div_le_one hqreal).mpr hparam
  calc
    ∑ x : S, ∑ a ∈ A x, W x a ≤ ∑ _x : S, F :=
      Finset.sum_le_sum (fun x _ => hfiber x)
    _ = (S.card : ℝ) * F := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ (512 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2) * F :=
      mul_le_mul_of_nonneg_right hcard hF
    _ = (512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / I ^ 2) *
        (h ^ 14 / (q : ℝ)) := by
      dsimp [F]
      field_simp
    _ ≤ (512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / I ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := mul_one _

end Problem355.SpecialRankTwo

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MatrixSpecialRankTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.MatrixSpecialRankTwo

open scoped BigOperators Matrix
open Matrix RowLatticeMatrices PrimitiveNormal IntegralPlaneLattice PairingDivisor

theorem canonical_covolume_cube_lower
    (x : Fin 3 → ℤ) (hx : IsPrimitive x)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E I : ℕ)
    (hE : 0 < E) (hI : 0 < I)
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (hindex : L.toAddSubgroup.index = I)
    (R h : ℝ) (hR : 0 ≤ R) (hnorm : R ≤ ‖toEuclidean x‖)
    (hcube : (E : ℝ) ^ 3 ≤ (I : ℝ) * h ^ 2) :
    (I : ℝ) ^ 2 * R ^ 3 ≤ h ^ 2 * ZLattice.covolume (latticeIn x L) ^ 3 := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp hx
  obtain ⟨hgpos, hgdvd⟩ := pairingDivisor_pos_and_dvd L.toAddSubgroup x z hz
    E hE hcontain
  have hgE : (pairingDivisor L.toAddSubgroup x : ℝ) ≤ E := by
    exact_mod_cast Nat.le_of_dvd hE hgdvd
  have hg3 : (pairingDivisor L.toAddSubgroup x : ℝ) ^ 3 ≤ (I : ℝ) * h ^ 2 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hgE 3).trans hcube
  apply SpecialRankTwo.covolume_cube_lower (by exact_mod_cast hI) hR hnorm
    (by exact_mod_cast hgpos) _ hg3
  rw [ZeroAffineShell.canonical_pairing_covolume x hx L E hE hcontain, hindex]

theorem prime_power_cube_bound (B b e k : ℕ) (hB : 1 ≤ B) (hek : e ≤ k) :
    ((B ^ e : ℕ) : ℝ) ^ 3 ≤ ((B ^ (b + e) : ℕ) : ℝ) *
      (((B ^ k : ℕ) : ℝ)) ^ 2 := by
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hexp : e * 3 ≤ b + e + k * 2 := by omega
  have hp := pow_le_pow_right₀ hBR hexp
  push_cast
  simpa only [← pow_mul, ← pow_add] using hp

theorem weighted_matrix_shell_le
    (S : Finset (Fin 3 → ℤ)) (L : Submodule ℤ (Fin 3 → ℤ))
    (E I R q : ℕ) (hE : 0 < E) (hI : 0 < I) (hR : 0 < R) (hq : 0 < q)
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (hindex : L.toAddSubgroup.index = I)
    (hnorm : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hnonzero : ∀ x ∈ S, x k ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (F : (Fin 3 → ℤ) → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ a, A a ∈ L)
    (W : (Fin 3 → ℤ) → IntMatrix → ℝ)
    (N h Cw : ℝ) (hN : 0 ≤ N) (hCw : 0 ≤ Cw)
    (hparam : h ^ 14 ≤ (q : ℝ))
    (hcube : (E : ℝ) ^ 3 ≤ (I : ℝ) * h ^ 2)
    (hW : ∀ x ∈ S, ∀ A ∈ F x, W x A ≤ Cw * (q : ℝ) * h ^ 12)
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ a b, |(A a b : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t) :
    (∑ x ∈ S, ∑ A ∈ F x, W x A) ≤
      512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / (I : ℝ) ^ 2 := by
  classical
  have hz : ∀ x : S, ∃ z : Fin 3 → ℤ, dotProduct (x : Fin 3 → ℤ) z = 1 :=
    fun x => (isPrimitive_iff_exists_dot_eq_one x.val).mp (hprimitive x.val x.property)
  choose z hz using hz
  let : ∀ x : S, IsZLattice ℝ (latticeIn x.val L) := fun x =>
    latticeIn_isZLattice x.val (z x) (hz x) L (E : ℤ)
      (by exact_mod_cast Nat.ne_of_gt hE)
      (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
  let T := fun x : S => rowFamily x.val L (F x.val) (hF x.val)
  let V := fun (x : S) u => W x.val ((rowsEquiv x.val L).symm u).val
  have hbox : ∀ x ∈ S, ∀ t,
      -((2 * R : ℕ) : ℤ) ≤ x t ∧ x t ≤ ((2 * R : ℕ) : ℤ) := by
    intro x hx t
    have hc : |(x t : ℝ)| ≤ ‖toEuclidean x‖ := by
      change ‖(toEuclidean x).ofLp t‖ ≤ ‖toEuclidean x‖
      exact PiLp.norm_apply_le _ _
    have hb : |(x t : ℝ)| ≤ (2 * R : ℕ) := by
      push_cast
      exact hc.trans (hnorm x hx).2.le
    exact abs_le.mp (show |x t| ≤ ((2 * R : ℕ) : ℤ) by exact_mod_cast hb)
  have hbound := SpecialRankTwo.special_rank_two_shell_subtype S
    (fun x => plane x.val) (fun x => latticeIn x.val L) T V
    R q hR hq i j k hki hkj hbox hnonzero hline N I h Cw hN
    (by exact_mod_cast hI) hCw hparam
    (fun x => plane_finrank x.val (z x) (hz x))
    (fun x => rowFamily_norm_le_four_mul x.val L (F x.val) (hF x.val)
      hN (hcoord x.val x.property))
    (fun x => rowFamily_independent_of_projections x.val L (F x.val) (hF x.val)
      (hproj x.val x.property))
    (fun x u hu => hW x.val x.property _
      ((mem_rowFamily x.val L (F x.val) (hF x.val) u).mp hu))
    (fun x => canonical_covolume_cube_lower x.val (hprimitive x.val x.property)
      L E I hE hI hcontain hindex R h (Nat.cast_nonneg R)
      (hnorm x.val x.property).1 hcube)
  have heq : (∑ x : S, ∑ u ∈ T x, V x u) = ∑ x ∈ S, ∑ A ∈ F x, W x A := by
    calc
      (∑ x : S, ∑ u ∈ T x, V x u) = ∑ x : S, ∑ A ∈ F x.val, W x.val A := by
        apply Finset.sum_congr rfl
        intro x hx
        exact sum_rowFamily x.val L (F x.val) (hF x.val) (W x.val)
      _ = _ := Finset.sum_attach S (fun x => ∑ A ∈ F x, W x A)
  rw [heq] at hbound
  exact hbound

end Problem355.MatrixSpecialRankTwo

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FiniteIndexPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.FiniteIndexPlane

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]

theorem discrete_of_le (Γ L : Submodule ℤ E) [DiscreteTopology L]
    (hΓL : Γ ≤ L) : DiscreteTopology Γ := by
  apply DiscreteTopology.of_continuous_injective
    (f := Submodule.inclusion hΓL) _ (Submodule.inclusion_injective hΓL)
  change Continuous (fun x : Γ => (⟨x.1, hΓL x.2⟩ : L))
  fun_prop

theorem relIndex_nsmul_mem (Γ L : Submodule ℤ E) (x : E) (hx : x ∈ L) :
    Γ.toAddSubgroup.relIndex L.toAddSubgroup • x ∈ Γ := by
  exact (Γ.toAddSubgroup.addSubgroupOf L.toAddSubgroup).nsmul_index_mem
    (⟨x, hx⟩ : L.toAddSubgroup)

theorem isZLattice_of_relIndex_ne_zero [NormedSpace ℝ E] (Γ L : Submodule ℤ E)
    [DiscreteTopology Γ] [DiscreteTopology L] [IsZLattice ℝ L]
    (hindex : Γ.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    IsZLattice ℝ Γ := by
  constructor
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := L)]
  apply Submodule.span_le.mpr
  intro x hx
  change x ∈ Submodule.span ℝ (Γ : Set E)
  have hmem := Submodule.subset_span (R := ℝ) (relIndex_nsmul_mem Γ L x hx)
  have hreal : (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast hindex
  have hscaled := (Submodule.span ℝ (Γ : Set E)).smul_mem
    (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ)⁻¹ hmem
  simpa only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hreal, one_smul] using hscaled

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem covolume_eq_index_mul (Γ L : Submodule ℤ E)
    [DiscreteTopology Γ] [DiscreteTopology L] [IsZLattice ℝ Γ] [IsZLattice ℝ L]
    (hΓL : Γ ≤ L) :
    ZLattice.covolume Γ =
      (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L := by
  have hvol := ZLattice.covolume_pos L volume
  exact (div_eq_iff hvol.ne').mp
    (ZLattice.covolume_div_covolume_eq_relIndex' Γ L hΓL)

theorem spanning_triples_card_le (hdim : Module.finrank ℝ E = 2)
    (Γ L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hΓL : Γ ≤ L) (m : ℕ) (hm : 0 < m)
    (hindex : Γ.toAddSubgroup.relIndex L.toAddSubgroup = m)
    (A : Finset (Fin 3 → Γ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, ∀ i, ‖(a i : E)‖ ≤ R)
    (hpair : ∀ a ∈ A, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : E), (a j : E)]) :
    (A.card : ℝ) ≤
      (9 * Real.pi * R ^ 2 / ((m : ℝ) * ZLattice.covolume L)) ^ 3 := by
  let : DiscreteTopology Γ := discrete_of_le Γ L hΓL
  let : IsZLattice ℝ Γ := isZLattice_of_relIndex_ne_zero Γ L (by omega)
  have h := LatticePacking.plane_spanning_triples_card_le hdim Γ A R hR hA hpair
  rwa [covolume_eq_index_mul Γ L hΓL, hindex] at h

end Problem355.FiniteIndexPlane

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PlaneFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PlaneFunctional

variable {ι K : Type*} [Fintype ι] [Field K]

theorem exists_kernel_dot_eq_one (x d : ι → K) (hx : x ≠ 0)
    (hd : ¬ ∃ a : K, d = a • x) :
    ∃ v : ι → K, dotProduct x v = 0 ∧ dotProduct d v = 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    apply hx
    funext i
    exact h i
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ (d i / x i) * x j := by
    by_contra! h
    apply hd
    refine ⟨d i / x i, ?_⟩
    funext j
    exact h j
  let u : ι → K := Pi.single j 1 - (x j / x i) • Pi.single i 1
  have hxu : dotProduct x u = 0 := by
    dsimp only [u]
    rw [dotProduct_sub, dotProduct_smul]
    simp only [dotProduct_single, mul_one, smul_eq_mul]
    rw [div_mul_cancel₀ _ hi, sub_self]
  have hduval : dotProduct d u = d j - (d i / x i) * x j := by
    dsimp only [u]
    rw [dotProduct_sub, dotProduct_smul]
    simp only [dotProduct_single, mul_one, smul_eq_mul]
    ring
  have hdu : dotProduct d u ≠ 0 := by
    rw [hduval]
    exact sub_ne_zero.mpr hj
  refine ⟨(dotProduct d u)⁻¹ • u, ?_, ?_⟩
  · rw [dotProduct_smul, hxu, smul_zero]
  · rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hdu]

theorem modularDot_surjective_of_plane_surjective (q : ℕ) [Fact q.Prime]
    (x d : ι → ZMod q) (hx : x ≠ 0)
    (hd : ¬ ∃ a : ZMod q, d = a • x)
    (L : AddSubgroup (ι → ℤ))
    (hL : ∀ v : ι → ZMod q, dotProduct x v = 0 →
      ∃ w : L, ∀ i, ((w : ι → ℤ) i : ZMod q) = v i) :
    Function.Surjective ((modularDotHom q d).comp L.subtype) := by
  obtain ⟨v, hxv, hdv⟩ := exists_kernel_dot_eq_one x d hx hd
  intro a
  have hxa : dotProduct x (a • v) = 0 := by
    rw [dotProduct_smul, hxv, smul_zero]
  obtain ⟨w, hw⟩ := hL (a • v) hxa
  refine ⟨w, ?_⟩
  change dotProduct d (fun i => ((w : ι → ℤ) i : ZMod q)) = a
  simp only [hw]
  rw [dotProduct_smul, hdv, smul_eq_mul, mul_one]

theorem modular_equation_index (q : ℕ) [Fact q.Prime]
    (x d : ι → ZMod q) (hx : x ≠ 0)
    (hd : ¬ ∃ a : ZMod q, d = a • x)
    (L : AddSubgroup (ι → ℤ))
    (hL : ∀ v : ι → ZMod q, dotProduct x v = 0 →
      ∃ w : L, ∀ i, ((w : ι → ℤ) i : ZMod q) = v i) :
    (((modularDotHom q d).comp L.subtype).ker).index = q := by
  rw [AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr
      (modularDot_surjective_of_plane_surjective q x d hx hd L hL),
    AddSubgroup.card_top]
  simpa only [Nat.card_eq_fintype_card] using ZMod.card q

end Problem355.PlaneFunctional

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.EqualCoordinatePlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PlaneFunctional

variable {ι K : Type*} [Fintype ι] [Field K]

omit [Fintype ι] in
theorem coordinateDifference_ne_zero {i j : ι} (hij : i ≠ j) :
    (coordinateDifference i j : ι → K) ≠ 0 := by
  classical
  intro h
  have hi := congrFun h i
  simp [coordinateDifference, hij] at hi

omit [Fintype ι] in

theorem not_exists_smul_swap (x d : ι → K) (hd : d ≠ 0)
    (hx : ¬ ∃ a : K, x = a • d) : ¬ ∃ a : K, d = a • x := by
  rintro ⟨a, ha⟩
  have hapos : a ≠ 0 := by
    intro hz
    apply hd
    simpa [hz] using ha
  apply hx
  refine ⟨a⁻¹, ?_⟩
  rw [ha, smul_smul, inv_mul_cancel₀ hapos, one_smul]

theorem equalCoordinateSubgroup_index (q : ℕ) [Fact q.Prime]
    (x : ι → ZMod q) (hx : x ≠ 0) (i j : ι) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q, x = a • coordinateDifference i j)
    (L : AddSubgroup (ι → ℤ))
    (hL : ∀ v : ι → ZMod q, dotProduct x v = 0 →
      ∃ w : L, ∀ a, ((w : ι → ℤ) a : ZMod q) = v a) :
    (equalCoordinateSubgroup q L i j).index = q := by
  exact modular_equation_index q x (coordinateDifference i j) hx
    (not_exists_smul_swap x (coordinateDifference i j)
      (coordinateDifference_ne_zero hij) hspan) L hL

end Problem355.PlaneFunctional

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegralPlaneReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.IntegralPlaneReduction

theorem reducedNormal_ne_zero (q : ℕ) [Nontrivial (ZMod q)] (x z : Vector)
    (hz : dotProduct x z = 1) : reducedNormal q x ≠ 0 :=
  PlaneReduction.normal_reduction_ne_zero q x z hz

open scoped LinearAlgebra.Projectivization

theorem equalCoordinate_index (q : ℕ) [Fact q.Prime] (Λ : Submodule ℤ Vector)
    (x z : Vector) (hz : dotProduct x z = 1) (E : ℤ) (hE : IsUnit (E : ZMod q))
    (hΛ : ∀ w : Vector, E • w ∈ Λ) (i j : Fin 3) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q,
      reducedNormal q x = a • PlaneFunctional.coordinateDifference i j) :
    (PlaneFunctional.equalCoordinateSubgroup q (integralPlane Λ x).toAddSubgroup i j).index = q := by
  apply PlaneFunctional.equalCoordinateSubgroup_index q (reducedNormal q x)
    (reducedNormal_ne_zero q x z hz) i j hij hspan
  intro v hv
  obtain ⟨w, hwΛ, hwx, hwred⟩ :=
    PlaneReduction.lift_orthogonal_mem q x z hz E hE Λ hΛ v hv
  exact ⟨⟨w, hwΛ, hwx⟩, hwred⟩

end Problem355.IntegralPlaneReduction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.EqualCoordinatePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.EqualCoordinatePacking

open IntegralPlaneLattice

theorem embedding_injective (x : Vector) (L : Submodule ℤ Vector) :
    Function.Injective (embedding x L) :=
  (Submodule.subtype_injective _).comp (kernelEquivIn x L).injective

theorem equalLattice_le (q : ℕ) [Fact q.Prime] (x : Vector)
    (L : Submodule ℤ Vector) (i j : Fin 3) :
    equalLattice q x L i j ≤ latticeIn x L := by
  rintro v ⟨w, hw, rfl⟩
  exact (kernelEquivIn x L w).property

theorem equalLattice_relIndex (q : ℕ) [Fact q.Prime]
    (x z : Vector) (hz : dotProduct x z = 1)
    (L : Submodule ℤ Vector) (E : ℤ) (hE : IsUnit (E : ZMod q))
    (hL : ∀ v : Vector, E • v ∈ L) (i j : Fin 3) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j) :
    (equalLattice q x L i j).toAddSubgroup.relIndex (latticeIn x L).toAddSubgroup = q := by
  have htop : (⊤ : AddSubgroup (integerPlaneIn x L)).map
      (embedding x L).toAddMonoidHom = (latticeIn x L).toAddSubgroup := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (kernelEquivIn x L w).property
    · intro hv
      refine ⟨(kernelEquivIn x L).symm ⟨v, hv⟩, trivial, ?_⟩
      exact congrArg (fun w : latticeIn x L => (w : plane x))
        ((kernelEquivIn x L).apply_symm_apply ⟨v, hv⟩)
  change ((PlaneFunctional.equalCoordinateSubgroup q
    (integerPlaneIn x L).toAddSubgroup i j).map (embedding x L).toAddMonoidHom).relIndex
      (latticeIn x L).toAddSubgroup = q
  rw [← htop, AddSubgroup.relIndex_map_map_of_injective _ _ (embedding_injective x L),
    AddSubgroup.relIndex_top_right]
  exact IntegralPlaneReduction.equalCoordinate_index q L x z hz E hE hL i j hij hspan

theorem matrices_card_le (q : ℕ) [Fact q.Prime]
    (x z : Vector) (hz : dotProduct x z = 1)
    (L : Submodule ℤ Vector) (E : ℤ) (hE : IsUnit (E : ZMod q))
    (hL : ∀ v : Vector, E • v ∈ L) (i j : Fin 3) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j)
    (A : Finset (Fin 3 → Vector)) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ a ∈ A, ∀ k, a k ∈ integerPlaneIn x L)
    (hcoord : ∀ a ∈ A, ∀ k, (a k i : ZMod q) = (a k j : ZMod q))
    (hnorm : ∀ a ∈ A, ∀ k, ‖castVec (a k)‖ ≤ R)
    (hpair : ∀ a ∈ A, ∃ k l : Fin 3,
      LinearIndependent ℝ ![castVec (a k), castVec (a l)]) :
    (A.card : ℝ) ≤
      (9 * Real.pi * R ^ 2 / ((q : ℝ) * ZLattice.covolume (latticeIn x L))) ^ 3 := by
  classical
  have hEne : E ≠ 0 := by
    intro he
    have hu := hE.ne_zero
    simp [he] at hu
  let : IsZLattice ℝ (latticeIn x L) := latticeIn_isZLattice x z hz L E hEne hL
  let T : {a // a ∈ A} → Fin 3 → equalLattice q x L i j := fun a k =>
    row q x L i j ⟨a.val k, hrow a.val a.property k⟩ (hcoord a.val a.property k)
  have hTinj : Function.Injective T := by
    intro a b hab
    apply Subtype.ext
    funext k t
    have he := congrArg
      (fun v : equalLattice q x L i j => ((v : plane x) : Ambient) t)
      (congrFun hab k)
    change (a.val k t : ℝ) = (b.val k t : ℝ) at he
    exact_mod_cast he
  have hcard : (A.attach.image T).card = A.card := by
    rw [Finset.card_image_of_injective _ hTinj, Finset.card_attach]
  have hbound := FiniteIndexPlane.spanning_triples_card_le
    (plane_finrank x z hz) (equalLattice q x L i j) (latticeIn x L)
    (equalLattice_le q x L i j) q (Fact.out : q.Prime).pos
    (equalLattice_relIndex q x z hz L E hE hL i j hij hspan)
    (A.attach.image T) R hR
    (by
      intro b hb k
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact hnorm a.val a.property k)
    (by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨k, l, hkl⟩ := hpair a.val a.property
      refine ⟨k, l, LinearIndependent.of_comp (plane x).subtype ?_⟩
      convert hkl using 1
      ext t
      fin_cases t <;> rfl)
  rwa [hcard] at hbound

end Problem355.EqualCoordinatePacking

end

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

end Problem355.LatticeBox

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroEqualAdditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open MeasureTheory

namespace Problem355.ZeroEqualAdditional

theorem fiber_bound {X I h q r g W : ℝ}
    (hI : 0 < I) (hq : 0 < q) (hr : 0 < r) (hg : 0 < g)
    (hW : 0 ≤ W) (hpairing : g ^ 3 ≤ I * h ^ 2) :
    W * (9 * Real.pi * X ^ 2 / (q * (I * r / g))) ^ 3 ≤
      W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2 * r ^ 3) := by
  have hid : W * (9 * Real.pi * X ^ 2 / (q * (I * r / g))) ^ 3 =
      (W * (9 * Real.pi) ^ 3 * X ^ 6 / (q ^ 3 * I ^ 3 * r ^ 3)) * g ^ 3 := by
    field_simp
  rw [hid]
  calc
    (W * (9 * Real.pi) ^ 3 * X ^ 6 / (q ^ 3 * I ^ 3 * r ^ 3)) * g ^ 3 ≤
        (W * (9 * Real.pi) ^ 3 * X ^ 6 / (q ^ 3 * I ^ 3 * r ^ 3)) * (I * h ^ 2) :=
      mul_le_mul_of_nonneg_left hpairing (by positivity)
    _ = W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2 * r ^ 3) := by
      field_simp

theorem sum_shell_bound (S : Finset (Fin 3 → ℤ)) (R X I h q W : ℝ)
    (hR : 1 ≤ R) (hI : 0 < I) (hq : 0 < q) (hW : 0 ≤ W)
    (g F : (Fin 3 → ℤ) → ℝ)
    (hshell : ∀ x ∈ S, R ≤ ‖LatticeBox.realVector x‖ ∧
      ‖LatticeBox.realVector x‖ ≤ 2 * R)
    (hg : ∀ x ∈ S, 0 < g x)
    (hpairing : ∀ x ∈ S, g x ^ 3 ≤ I * h ^ 2)
    (hF : ∀ x ∈ S, F x ≤
      W * (9 * Real.pi * X ^ 2 /
        (q * (I * ‖LatticeBox.realVector x‖ / g x))) ^ 3) :
    ∑ x ∈ S, F x ≤
      125 * W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2) := by
  have hRp : 0 < R := by linarith
  let C := W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 /
    (q ^ 3 * I ^ 2 * R ^ 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (x : Fin 3 → ℤ) (hx : x ∈ S) : F x ≤ C := by
    have hr : 0 < ‖LatticeBox.realVector x‖ := hRp.trans_le (hshell x hx).1
    refine (hF x hx).trans ((fiber_bound hI hq hr (hg x hx) hW (hpairing x hx)).trans ?_)
    dsimp [C]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
    exact (hshell x hx).1
  have hc : (S.card : ℝ) ≤ 125 * R ^ 3 :=
    LatticeBox.card_le_onehundredtwentyfive_mul_cube hR S
      (fun x hx i => (LatticeBox.abs_coord_le_norm x i).trans (hshell x hx).2)
  calc
    ∑ x ∈ S, F x ≤ ∑ _x ∈ S, C := Finset.sum_le_sum hbound
    _ = (S.card : ℝ) * C := by simp
    _ ≤ (125 * R ^ 3) * C := mul_le_mul_of_nonneg_right hc hC
    _ = 125 * W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / (q ^ 3 * I ^ 2) := by
      dsimp [C]
      field_simp

end Problem355.ZeroEqualAdditional

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroEqualMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.ZeroEqualAdditional

open IntegralPlaneLattice

theorem weighted_matrix_shell_bound
    (q : ℕ) [Fact q.Prime] (L : Submodule ℤ (Fin 3 → ℤ))
    (E : ℤ) (hE : IsUnit (E : ZMod q)) (hL : ∀ v, E • v ∈ L)
    (i j : Fin 3) (hij : i ≠ j)
    (S : Finset (Fin 3 → ℤ)) (z : (Fin 3 → ℤ) → (Fin 3 → ℤ))
    (hz : ∀ x ∈ S, dotProduct x (z x) = 1)
    (hspan : ∀ x ∈ S, ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j)
    (A : (Fin 3 → ℤ) → Finset (Fin 3 → Fin 3 → ℤ))
    (weight : (Fin 3 → Fin 3 → ℤ) → ℝ)
    (R X I h W : ℝ) (hR : 1 ≤ R) (hX : 0 ≤ X) (hI : 0 < I) (hW : 0 ≤ W)
    (g : (Fin 3 → ℤ) → ℝ)
    (hshell : ∀ x ∈ S, R ≤ ‖LatticeBox.realVector x‖ ∧
      ‖LatticeBox.realVector x‖ ≤ 2 * R)
    (hg : ∀ x ∈ S, 0 < g x)
    (hpairing : ∀ x ∈ S, g x ^ 3 ≤ I * h ^ 2)
    (hcovol : ∀ x ∈ S, ZLattice.covolume (latticeIn x L) =
      I * ‖LatticeBox.realVector x‖ / g x)
    (hrow : ∀ x ∈ S, ∀ a ∈ A x, ∀ k, a k ∈ integerPlaneIn x L)
    (hcoord : ∀ x ∈ S, ∀ a ∈ A x, ∀ k, (a k i : ZMod q) = (a k j : ZMod q))
    (hnorm : ∀ x ∈ S, ∀ a ∈ A x, ∀ k, ‖castVec (a k)‖ ≤ X)
    (hpair : ∀ x ∈ S, ∀ a ∈ A x, ∃ k l : Fin 3,
      LinearIndependent ℝ ![castVec (a k), castVec (a l)])
    (hweight : ∀ x ∈ S, ∀ a ∈ A x, weight a ≤ W) :
    ∑ x ∈ S, ∑ a ∈ A x, weight a ≤
      125 * W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / ((q : ℝ) ^ 3 * I ^ 2) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  apply sum_shell_bound S R X I h q W hR hI hq hW g
    (fun x => ∑ a ∈ A x, weight a) hshell hg hpairing
  intro x hx
  have hc := EqualCoordinatePacking.matrices_card_le q x (z x) (hz x hx)
    L E hE hL i j hij (hspan x hx) (A x) X hX
    (hrow x hx) (hcoord x hx) (hnorm x hx) (hpair x hx)
  rw [hcovol x hx] at hc
  calc
    ∑ a ∈ A x, weight a ≤ ∑ _a ∈ A x, W := Finset.sum_le_sum (hweight x hx)
    _ = W * ((A x).card : ℝ) := by simp [mul_comm]
    _ ≤ W * (9 * Real.pi * X ^ 2 /
        ((q : ℝ) * (I * ‖LatticeBox.realVector x‖ / g x))) ^ 3 :=
      mul_le_mul_of_nonneg_left hc hW

end Problem355.ZeroEqualAdditional

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.RowLatticeEqualShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.RowLatticeEqualShell

open Matrix IntegralPlaneLattice PrimitiveNormal PairingDivisor
open scoped BigOperators

theorem weighted_matrix_shell_bound
    (q : ℕ) [Fact q.Prime] (L : Submodule ℤ (Fin 3 → ℤ))
    (E : ℕ) (hE : 0 < E) (hEq : IsUnit (E : ZMod q))
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (i j : Fin 3) (hij : i ≠ j)
    (S : Finset (Fin 3 → ℤ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hspan : ∀ x ∈ S, ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j)
    (F : (Fin 3 → ℤ) → Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hF : ∀ x ∈ S, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ k, A k ∈ L)
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ)
    (R N I h W₀ : ℝ) (hR : 1 ≤ R) (hN : 0 ≤ N)
    (hI : 0 < I) (hW₀ : 0 ≤ W₀)
    (hindex : (L.toAddSubgroup.index : ℝ) = I)
    (hEbound : (E : ℝ) ^ 3 ≤ I * h ^ 2)
    (hshell : ∀ x ∈ S, R ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ ≤ 2 * R)
    (hequal : ∀ x ∈ S, ∀ A ∈ F x, ∀ k, (A k i : ZMod q) = (A k j : ZMod q))
    (hcoord : ∀ x ∈ S, ∀ A ∈ F x, ∀ k l, |(A k l : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ S, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hW : ∀ x ∈ S, ∀ A ∈ F x, W A ≤ W₀) :
    (∑ x ∈ S, ∑ A ∈ F x, W A) ≤
      125 * (144 * Real.pi) ^ 3 * W₀ * N ^ 6 * h ^ 2 /
        ((q : ℝ) ^ 3 * I ^ 2) := by
  classical
  let z : (Fin 3 → ℤ) → Fin 3 → ℤ := fun x =>
    if hx : IsPrimitive x then
      Classical.choose ((isPrimitive_iff_exists_dot_eq_one x).mp hx)
    else 0
  have hz : ∀ x ∈ S, dotProduct x (z x) = 1 := by
    intro x hx
    dsimp [z]
    rw [dite_eq_left (hprimitive x hx)]
    exact Classical.choose_spec ((isPrimitive_iff_exists_dot_eq_one x).mp
      (hprimitive x hx))
  let g : (Fin 3 → ℤ) → ℝ := fun x => (pairingDivisor L.toAddSubgroup x : ℝ)
  have hgdata (x : Fin 3 → ℤ) (hx : x ∈ S) :
      0 < pairingDivisor L.toAddSubgroup x ∧ pairingDivisor L.toAddSubgroup x ∣ E :=
    pairingDivisor_pos_and_dvd L.toAddSubgroup x (z x) (hz x hx) E hE hcontain
  have hg : ∀ x ∈ S, 0 < g x := by
    intro x hx
    dsimp [g]
    exact_mod_cast (hgdata x hx).1
  have hg3 : ∀ x ∈ S, g x ^ 3 ≤ I * h ^ 2 := by
    intro x hx
    have hle : g x ≤ (E : ℝ) := by
      dsimp [g]
      exact_mod_cast Nat.le_of_dvd hE (hgdata x hx).2
    exact (pow_le_pow_left₀ (hg x hx).le hle 3).trans hEbound
  have hcov : ∀ x ∈ S, ZLattice.covolume (latticeIn x L) =
      I * ‖LatticeBox.realVector x‖ / g x := by
    intro x hx
    have hc := ZeroAffineShell.canonical_pairing_covolume x (hprimitive x hx)
      L E hE hcontain
    rw [hindex] at hc
    exact hc
  have hrow : ∀ x ∈ S, ∀ A ∈ F x, ∀ k, A k ∈ integerPlaneIn x L := by
    intro x hx A hA k
    refine ⟨(hF x hx A hA).2 k, ?_⟩
    change x ⬝ᵥ A k = 0
    rw [dotProduct_comm]
    exact congrFun (hF x hx A hA).1 k
  have hnorm : ∀ x ∈ S, ∀ A ∈ F x, ∀ k, ‖castVec (A k)‖ ≤ 4 * N := by
    intro x hx A hA k
    exact PlaneRowTransport.norm_rows_le_four_mul x
      ⟨A, (hF x hx A hA).1⟩ k hN (hcoord x hx A hA k)
  have hpair : ∀ x ∈ S, ∀ A ∈ F x, ∃ k l : Fin 3,
      LinearIndependent ℝ ![castVec (A k), castVec (A l)] := by
    intro x hx A hA
    obtain ⟨s, t, hs, ht, hne⟩ := hproj x hx A hA
    obtain ⟨k, _, hk⟩ := PlaneRowTransport.exists_minor_of_projected_columns_ne
      A s t hs ht hne
    refine ⟨k, 2, PlaneRowTransport.linearIndependent_of_minor_ne_zero
      (castVec (A k)) (castVec (A 2)) s t ?_⟩
    simp only [castVec_apply]
    exact_mod_cast hk
  have hb := ZeroEqualAdditional.weighted_matrix_shell_bound q L (E : ℤ)
    (by simpa using hEq) (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
    i j hij S z hz hspan F W R (4 * N) I h W₀ hR (by positivity) hI hW₀
    g hshell hg hg3 hcov hrow hequal hnorm hpair hW
  calc
    _ ≤ 125 * W₀ * (9 * Real.pi) ^ 3 * (4 * N) ^ 6 * h ^ 2 /
        ((q : ℝ) ^ 3 * I ^ 2) := hb
    _ = _ := by ring

end Problem355.RowLatticeEqualShell

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroDeterminantCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.ZeroDeterminantCount

open Matrix PrimitiveNormal
open scoped Matrix BigOperators
attribute [local instance] Classical.propDecidable

lemma RowData.h_one (D : RowData) : 1 ≤ D.h := one_le_pow₀ (by exact_mod_cast D.prime.one_le)
lemma RowData.I_pos (D : RowData) : 0 < D.I := pow_pos D.prime.pos _
lemma RowData.E_pos (D : RowData) : 0 < D.E := pow_pos D.prime.pos _
lemma RowData.cube (D : RowData) : (D.E : ℝ) ^ 3 ≤ (D.I : ℝ) * D.h ^ 2 := by
  simpa only [RowData.E, RowData.I, RowData.h, Nat.cast_pow] using
    MatrixSpecialRankTwo.prime_power_cube_bound D.B D.b D.e D.k D.prime.one_le D.e_le_k

theorem affine_shell_le (D : RowData) (q R : ℕ)
    (T : Finset IntVector) (hR : 0 < R)
    (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (N Ca : ℝ) (hN : 0 ≤ N) (hCa : 0 ≤ Ca)
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hweight : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col → W A ≤ Ca)
    (hexclude : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col →
      0 < W A → D.h ^ 2 < ‖toEuclidean x‖) :
    (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col), W A) ≤
      1024 * planeConstant * Ca * N ^ 6 / (D.I : ℝ) ^ 2 := by
  classical
  let F' := fun x => (F x).filter (fun A =>
    AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col)
  have hb := MatrixAffineShell.weighted_matrix_shell_le_of_short_exclusion
    T D.L D.C D.B R D.b D.e D.k D.prime hR D.e_le_k D.P D.Q D.diagonal
    hnorm hprimitive D.contains D.rows F'
    (fun x A hA => hF x A (Finset.mem_filter.mp hA).1)
    (fun _ A => W A) N Ca hN hCa
    (fun x hx A hA => hweight x hx A (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2)
    (fun x hx A hA => hcoord x hx A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA => hproj x hx A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA hw => hexclude x hx A (Finset.mem_filter.mp hA).1
      (Finset.mem_filter.mp hA).2 hw) D.index_eq
  convert hb using 1 ; simp only [RowData.I, Nat.cast_pow, planeConstant] ; ring

theorem additional_shell_le (D : RowData) (q : ℕ) [Fact q.Prime]
    (hEq : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
    (i j : Fin 3) (hij : i ≠ j) (T : Finset IntVector)
    (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (hspan : ∀ x ∈ T, ¬ ∃ a : ZMod q, (fun s => (x s : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j)
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x ∈ T, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (R N Cg : ℝ) (hR : 1 ≤ R)
    (hN : 0 ≤ N) (hCg : 0 ≤ Cg)
    (hnorm : ∀ x ∈ T, R ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ ≤ 2 * R)
    (hequal : ∀ x ∈ T, ∀ A ∈ F x, ∀ s, (A s i : ZMod q) = (A s j : ZMod q))
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hweight : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24) :
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
      125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hI : (0 : ℝ) < D.I := by exact_mod_cast D.I_pos
  have hb := RowLatticeEqualShell.weighted_matrix_shell_bound q D.L D.E D.E_pos
    hEq D.contains i j hij T hprimitive hspan F hF W R N D.I D.h
    (Cg * (q : ℝ) ^ 2 * D.h ^ 24) hR hN hI (by positivity)
    (by rw [D.index_eq]; rfl) D.cube hnorm hequal hcoord hproj hweight
  have hratio : D.h ^ 26 / (q : ℝ) ≤ 1 := (div_le_one hq).mpr hparam
  calc
    _ ≤ 125 * (144 * Real.pi) ^ 3 * (Cg * (q : ℝ) ^ 2 * D.h ^ 24) *
        N ^ 6 * D.h ^ 2 / ((q : ℝ) ^ 3 * (D.I : ℝ) ^ 2) := hb
    _ = (125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2) *
        (D.h ^ 26 / (q : ℝ)) := by
      unfold planeConstant
      field_simp
    _ ≤ (125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hratio (by unfold planeConstant; positivity)
    _ = _ := mul_one _

theorem special_shell_le (D : RowData) (q R : ℕ) (hq : 0 < q) (hR : 0 < R)
    (T : Finset IntVector) (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hnonzero : ∀ x ∈ T, x k ≠ 0)
    (hline : ∀ x ∈ T, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (N Cd : ℝ) (hN : 0 ≤ N) (hCd : 0 ≤ Cd)
    (hparam : D.h ^ 14 ≤ (q : ℝ))
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hweight : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cd * (q : ℝ) * D.h ^ 12) :
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
      512 * planeConstant * Cd * N ^ 6 / (D.I : ℝ) ^ 2 := by
  exact MatrixSpecialRankTwo.weighted_matrix_shell_le T D.L D.E D.I R q
    D.E_pos D.I_pos hR hq hprimitive D.contains D.index_eq hnorm
    i j k hki hkj hnonzero hline F hF (fun _ A => W A) N D.h Cd hN hCd
    hparam D.cube hweight hcoord hproj

end Problem355.ZeroDeterminantCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroCombinedShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.ZeroDeterminantCount

open Matrix PrimitiveNormal WeightedZeroPartition AuxiliaryThreeCase
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

private theorem additional_case_bound (D : RowData) (q R : ℕ) [Fact q.Prime]
    (hEq : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
    (T : Finset IntVector) (hR : 0 < R)
    (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (_ : ∀ x ∈ T, ∀ i, x i ≠ 0)
    (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (N Ca Cg Cd : ℝ)
    (hN : 0 ≤ N) (_ : 0 ≤ Ca) (hCg : 0 ≤ Cg) (_ : 0 ≤ Cd)
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
    (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
      ∃ C : Set (Fin 3 → ZMod q), AuxiliaryCap.IsCap C ∧
        ∀ i, residueColumns q A i ∈ C)
    (_ : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) → W A ≤ Ca)
    (_ : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) →
      0 < W A → D.h ^ 2 < ‖toEuclidean x‖)
    (hwall : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
    (_ : ∀ x ∈ T, ∀ A ∈ F x,
      (∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j) →
      W A ≤ Cd * (q : ℝ) * D.h ^ 12) (p : Fin 3) :
    (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
      EqualPair (residueColumns q A) p ∧
        ¬ ExceptionalVector (fun i => (x i : ZMod q)) p), W A) ≤
    125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2 := by
  let T' := T.filter (fun x => ¬ ExceptionalVector (fun i => (x i : ZMod q)) p)
  let F' := fun x => (F x).filter (fun A => EqualPair (residueColumns q A) p)
  have hij : (columnPair p).1 ≠ (columnPair p).2 := by
    fin_cases p <;> decide
  have hspan : ∀ x ∈ T', ¬ ∃ a : ZMod q,
      (fun s => (x s : ZMod q)) =
        a • PlaneFunctional.coordinateDifference (columnPair p).1 (columnPair p).2 := by
    intro x hx he
    apply (Finset.mem_filter.mp hx).2
    obtain ⟨a, ha⟩ := he
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    rw [ha]
    congr 1
    ext t
    simp only [PlaneFunctional.coordinateDifference, Pi.single_apply, Pi.sub_apply]
    split_ifs <;> rfl
  have hb := additional_shell_le D q hEq hparam (columnPair p).1 (columnPair p).2
    hij T' (fun x hx => hprimitive x (Finset.mem_filter.mp hx).1) hspan F'
    (fun x hx A hA => hF x A (Finset.mem_filter.mp hA).1) W (R : ℝ) N Cg
    (by exact_mod_cast hR) hN hCg
    (fun x hx => ⟨(hnorm x (Finset.mem_filter.mp hx).1).1,
      (hnorm x (Finset.mem_filter.mp hx).1).2.le⟩)
    (fun x hx A hA s => congrFun (Finset.mem_filter.mp hA).2 s)
    (fun x hx A hA => hcoord x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA => hproj x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA => hwall x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
  calc
    _ = ∑ x ∈ T', ∑ A ∈ F' x, W A := by
      simp only [T', F', Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hp : ExceptionalVector (fun i => (x i : ZMod q)) p
      · simp [hp]
      · simp [hp]
    _ ≤ _ := hb

private theorem special_case_bound (D : RowData) (q R : ℕ) [Fact q.Prime]
    (_ : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
    (T : Finset IntVector) (hR : 0 < R)
    (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (hnonzero : ∀ x ∈ T, ∀ i, x i ≠ 0)
    (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (N Ca Cg Cd : ℝ)
    (hN : 0 ≤ N) (_ : 0 ≤ Ca) (_ : 0 ≤ Cg) (hCd : 0 ≤ Cd)
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
    (_ : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
      ∃ C : Set (Fin 3 → ZMod q), AuxiliaryCap.IsCap C ∧
        ∀ i, residueColumns q A i ∈ C)
    (_ : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) → W A ≤ Ca)
    (_ : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) →
      0 < W A → D.h ^ 2 < ‖toEuclidean x‖)
    (_ : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
    (hwdist : ∀ x ∈ T, ∀ A ∈ F x,
      (∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j) →
      W A ≤ Cd * (q : ℝ) * D.h ^ 12) (p : Fin 3) :
    (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
      EqualPair (residueColumns q A) p ∧
        ExceptionalVector (fun i => (x i : ZMod q)) p ∧
        ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j), W A) ≤
    512 * planeConstant * Cd * N ^ 6 / (D.I : ℝ) ^ 2 := by
  let T' := T.filter (fun x => ExceptionalVector (fun i => (x i : ZMod q)) p)
  let F' := fun x => (F x).filter (fun A => EqualPair (residueColumns q A) p ∧
    ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j)
  let l : Fin 3 := ![2, 1, 0] p
  have hli : l ≠ (columnPair p).1 := by fin_cases p <;> decide
  have hlj : l ≠ (columnPair p).2 := by fin_cases p <;> decide
  have h14 : D.h ^ 14 ≤ (q : ℝ) :=
    (pow_le_pow_right₀ D.h_one (by norm_num : 14 ≤ 26)).trans hparam
  have hb := special_shell_le D q R (Fact.out : q.Prime).pos hR T'
    (fun x hx => hprimitive x (Finset.mem_filter.mp hx).1)
    (fun x hx => hnorm x (Finset.mem_filter.mp hx).1)
    (columnPair p).1 (columnPair p).2 l hli hlj
    (fun x hx => hnonzero x (Finset.mem_filter.mp hx).1 l)
    (fun x hx => (Finset.mem_filter.mp hx).2) F'
    (fun x A hA => hF x A (Finset.mem_filter.mp hA).1) W N Cd hN hCd h14
    (fun x hx A hA => hcoord x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA => hproj x (Finset.mem_filter.mp hx).1 A (Finset.mem_filter.mp hA).1)
    (fun x hx A hA => hwdist x (Finset.mem_filter.mp hx).1 A
      (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2.2)
  have heq : (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A =>
      EqualPair (residueColumns q A) p ∧
        ExceptionalVector (fun i => (x i : ZMod q)) p ∧
        ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j), W A) =
      ∑ x ∈ T', ∑ A ∈ F' x, W A := by
    simp only [T', F', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hp : ExceptionalVector (fun i => (x i : ZMod q)) p
    · simp [hp]
    · simp [hp]
  rw [heq]
  exact hb

private theorem combine_case_bounds (D : RowData) (q : ℕ) [Fact q.Prime]
    (T : Finset IntVector) (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (F : IntVector → Finset IntMatrix) (W : IntMatrix → ℝ) (N Ca Cg Cd : ℝ)
    (hW : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
    (hcap : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
      ∃ C : Set (Fin 3 → ZMod q), AuxiliaryCap.IsCap C ∧
        ∀ i, residueColumns q A i ∈ C)
    (haff : (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => AffineIndependent (ZMod q)
      (A.map (Int.castRingHom (ZMod q))).col), W A) ≤
      1024 * planeConstant * Ca * N ^ 6 / (D.I : ℝ) ^ 2)
    (hadd : ∀ p : Fin 3,
      (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => EqualPair (residueColumns q A) p ∧
        ¬ ExceptionalVector (fun i => (x i : ZMod q)) p), W A) ≤
      125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2)
    (hspecial : ∀ p : Fin 3,
      (∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => EqualPair (residueColumns q A) p ∧
        ExceptionalVector (fun i => (x i : ZMod q)) p ∧
        ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j), W A) ≤
      512 * planeConstant * Cd * N ^ 6 / (D.I : ℝ) ^ 2) :
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
      (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) * planeConstant * N ^ 6 /
        (D.I : ℝ) ^ 2 := by
  let faff := fun x => ∑ A ∈ (F x).filter
    (fun A => AffineIndependent (ZMod q) (residueColumns q A)), W A
  let fadd := fun p x => ∑ A ∈ (F x).filter (fun A =>
    EqualPair (residueColumns q A) p ∧
      ¬ ExceptionalVector (fun i => (x i : ZMod q)) p), W A
  let fspecial := fun p x => ∑ A ∈ (F x).filter (fun A =>
    EqualPair (residueColumns q A) p ∧
      ExceptionalVector (fun i => (x i : ZMod q)) p ∧
      ∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j), W A
  have hpoint (x : IntVector) (hx : x ∈ T) :
      (∑ A ∈ F x, W A) ≤ faff x + ∑ p : Fin 3, (fadd p x + fspecial p x) := by
    have hh := matrix_sum_le_three_case_sums q x (hprimitive x hx) (F x) W
      (hW x hx) (hcap x hx)
    simpa only [faff, fadd, fspecial, exceptionalVector_reduction] using hh
  have haff' : (∑ x ∈ T, faff x) ≤
      1024 * planeConstant * Ca * N ^ 6 / (D.I : ℝ) ^ 2 := by
    calc
      _ = ∑ x ∈ T, ∑ A ∈ (F x).filter (fun A => AffineIndependent (ZMod q)
          (A.map (Int.castRingHom (ZMod q))).col), W A := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr
        · apply Finset.filter_congr
          intro A hA
          rfl
        · intro A hA
          rfl
      _ ≤ _ := haff
  calc
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
        ∑ x ∈ T, (faff x + ∑ p : Fin 3, (fadd p x + fspecial p x)) :=
      Finset.sum_le_sum hpoint
    _ = (∑ x ∈ T, faff x) + ∑ p : Fin 3,
        ((∑ x ∈ T, fadd p x) + (∑ x ∈ T, fspecial p x)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    _ ≤ (1024 * planeConstant * Ca * N ^ 6 / (D.I : ℝ) ^ 2) +
        ∑ _p : Fin 3, ((125 * planeConstant * Cg * N ^ 6 / (D.I : ℝ) ^ 2) +
          (512 * planeConstant * Cd * N ^ 6 / (D.I : ℝ) ^ 2)) := by
      apply add_le_add haff'
      exact Finset.sum_le_sum fun p _ => add_le_add (hadd p) (hspecial p)
    _ = _ := by simp; ring

theorem combined_shell_le (D : RowData) (q R : ℕ) [Fact q.Prime]
    (hEq : IsUnit (D.E : ZMod q)) (hparam : D.h ^ 26 ≤ (q : ℝ))
    (T : Finset IntVector) (hR : 0 < R)
    (hprimitive : ∀ x ∈ T, IsPrimitive x)
    (hnonzero : ∀ x ∈ T, ∀ i, x i ≠ 0)
    (hnorm : ∀ x ∈ T, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (F : IntVector → Finset IntMatrix)
    (hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ i, A i ∈ D.L)
    (W : IntMatrix → ℝ) (N Ca Cg Cd : ℝ)
    (hN : 0 ≤ N) (hCa : 0 ≤ Ca) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd)
    (hcoord : ∀ x ∈ T, ∀ A ∈ F x, ∀ i j, |(A i j : ℝ)| ≤ 2 * N)
    (hproj : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
      A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t)
    (hW : ∀ x ∈ T, ∀ A ∈ F x, 0 ≤ W A)
    (hcap : ∀ x ∈ T, ∀ A ∈ F x, 0 < W A →
      ∃ C : Set (Fin 3 → ZMod q), AuxiliaryCap.IsCap C ∧
        ∀ i, residueColumns q A i ∈ C)
    (hwaff : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) → W A ≤ Ca)
    (hexclude : ∀ x ∈ T, ∀ A ∈ F x,
      AffineIndependent (ZMod q) (residueColumns q A) →
      0 < W A → D.h ^ 2 < ‖toEuclidean x‖)
    (hwall : ∀ x ∈ T, ∀ A ∈ F x, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
    (hwdist : ∀ x ∈ T, ∀ A ∈ F x,
      (∃ i j : Fin 3, residueColumns q A i ≠ residueColumns q A j) →
      W A ≤ Cd * (q : ℝ) * D.h ^ 12) :
    (∑ x ∈ T, ∑ A ∈ F x, W A) ≤
      (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) * planeConstant * N ^ 6 /
        (D.I : ℝ) ^ 2 := by
  have haff := affine_shell_le D q R T hR hprimitive hnorm F hF W N Ca hN hCa
    hcoord hproj hwaff hexclude
  have hadd := additional_case_bound D q R hEq hparam T hR hprimitive hnonzero hnorm F hF W N Ca Cg Cd hN hCa hCg hCd hcoord hproj hW hcap hwaff hexclude hwall hwdist
  have hspecial := special_case_bound D q R hEq hparam T hR hprimitive hnonzero hnorm F hF W N Ca Cg Cd hN hCa hCg hCd hcoord hproj hW hcap hwaff hexclude hwall hwdist
  exact combine_case_bounds D q T hprimitive F W N Ca Cg Cd hW hcap haff hadd hspecial

end Problem355.ZeroDeterminantCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.WeightedNormalReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimitiveNormal

open Matrix
open scoped Matrix BigOperators

lemma mem_normalBox (X : ℤ) (w : Vector) : w ∈ normalBox X ↔
    IsPrimitive w ∧ (∀ i, w i ≠ 0) ∧ (∀ i, |w i| ≤ 2 * X ^ 2) := by
  simp only [normalBox, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp, hn⟩
    exact ⟨hp, hn, fun i => abs_le.mpr ⟨hlo i, hhi i⟩⟩
  · rintro ⟨hp, hn, hb⟩
    exact ⟨⟨fun i => (abs_le.mp (hb i)).1, fun i => (abs_le.mp (hb i)).2⟩, hp, hn⟩

lemma normalBox_norm_bounds {X : ℤ} {w : Vector} (hw : w ∈ normalBox X) :
    1 ≤ ‖toEuclidean w‖ ∧ ‖toEuclidean w‖ ≤ 6 * (X : ℝ) ^ 2 := by
  obtain ⟨hp, _, hb⟩ := (mem_normalBox X w).mp hw
  refine ⟨one_le_norm_of_ne_zero w hp.ne_zero, ?_⟩
  have h := norm_le_three_mul_of_coordinate_bound w (2 * (X : ℝ) ^ 2)
    (by positivity) (fun i => by exact_mod_cast hb i)
  nlinarith

lemma exists_normalBox_kernel (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hdet : A.det = 0) (hheight : ∀ i, A 2 i ≠ 0)
    (hproj : ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ i j, |A i j| ≤ X) :
    ∃ w ∈ normalBox X, A *ᵥ w = 0 := by
  obtain ⟨w, hp, hk, hn, hb⟩ :=
    exists_primitive_right_null_of_projections A hdet hheight hproj X hX hbound
  exact ⟨w, (mem_normalBox X w).mpr ⟨hp, hn, hb⟩, hk⟩

theorem weighted_count_le_sum_normal_fibers
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ) (hW : ∀ A ∈ S, 0 ≤ W A)
    (hdet : ∀ A ∈ S, A.det = 0) (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 0 ≤ X) (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X) :
    (∑ A ∈ S, W A) ≤
      ∑ w ∈ normalBox X, ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A := by
  classical
  calc
    (∑ A ∈ S, W A) ≤ ∑ A ∈ S, ∑ w ∈ normalBox X,
        if A *ᵥ w = 0 then W A else 0 := by
      apply Finset.sum_le_sum
      intro A hA
      obtain ⟨w, hw, hk⟩ := exists_normalBox_kernel A (hdet A hA) (hheight A hA)
        (hproj A hA) X hX (hbound A hA)
      have hs := Finset.single_le_sum (s := normalBox X)
        (f := fun w => if A *ᵥ w = 0 then W A else 0)
        (fun x hx => by split_ifs <;> first | exact hW A hA | rfl) hw
      simpa [hk] using hs
    _ = ∑ w ∈ normalBox X, ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      rw [Finset.sum_filter]

end Problem355.PrimitiveNormal

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroNormalDyadic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimitiveNormal

open Matrix
open scoped Matrix BigOperators

theorem weighted_count_le_of_normal_shell_bound
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ) (hW : ∀ A ∈ S, 0 ≤ W A)
    (hdet : ∀ A ∈ S, A.det = 0) (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 1 ≤ X) (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X)
    {K : ℝ} (hK : 0 ≤ K)
    (hshell : ∀ i : ℕ,
      ∑ w ∈ (normalBox X).filter (fun w =>
        (2 : ℝ) ^ i ≤ ‖toEuclidean w‖ ∧ ‖toEuclidean w‖ < 2 ^ (i + 1)),
        ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A ≤ K) :
    ∑ A ∈ S, W A ≤ K * (Real.log (12 * (X : ℝ) ^ 2) / Real.log 2) := by
  classical
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hR : (1 : ℝ) ≤ 6 * (X : ℝ) ^ 2 := by nlinarith
  have hagg := Anisotropic.sum_le_of_single_dyadic_shell_estimates
    (normalBox X) (fun w => ‖toEuclidean w‖)
    (fun w => ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A)
    hR hK
    (fun w _ => Finset.sum_nonneg (fun A hA => hW A (Finset.mem_filter.mp hA).1))
    (fun w hw => normalBox_norm_bounds hw) hshell
  have hcover := weighted_count_le_sum_normal_fibers S W hW hdet hheight hproj
    X (by omega) hbound
  simpa only [show (2 : ℝ) * (6 * (X : ℝ) ^ 2) = 12 * (X : ℝ) ^ 2 by ring] using
    hcover.trans hagg

lemma normal_range_log_le {X : ℝ} (hX : 1 ≤ X) :
    Real.log (12 * X ^ 2) / Real.log 2 ≤
      4 * (Real.log (2 * X) / Real.log 2) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpos : 0 < 12 * X ^ 2 := by positivity
  have hsq : 1 ≤ X ^ 2 := by nlinarith
  have hfour : 12 * X ^ 2 ≤ (2 * X) ^ 4 := by
    nlinarith [sq_nonneg (X ^ 2 - 1)]
  have hlog := Real.log_le_log hpos hfour
  rw [Real.log_pow] at hlog
  have hquot := div_le_div_of_nonneg_right hlog hlog2.le
  simpa [mul_div_assoc] using hquot

theorem weighted_count_le_log_of_normal_shell_bound
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ) (hW : ∀ A ∈ S, 0 ≤ W A)
    (hdet : ∀ A ∈ S, A.det = 0) (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (X : ℤ) (hX : 1 ≤ X) (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ X)
    {K : ℝ} (hK : 0 ≤ K)
    (hshell : ∀ i : ℕ,
      ∑ w ∈ (normalBox X).filter (fun w =>
        (2 : ℝ) ^ i ≤ ‖toEuclidean w‖ ∧ ‖toEuclidean w‖ < 2 ^ (i + 1)),
        ∑ A ∈ S.filter (fun A => A *ᵥ w = 0), W A ≤ K) :
    ∑ A ∈ S, W A ≤ 4 * K * (Real.log (2 * (X : ℝ)) / Real.log 2) := by
  have h := weighted_count_le_of_normal_shell_bound S W hW hdet hheight hproj
    X hX hbound hK hshell
  have hxR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hmul := mul_le_mul_of_nonneg_left (normal_range_log_le hxR) hK
  calc
    _ ≤ K * (Real.log (12 * (X : ℝ) ^ 2) / Real.log 2) := h
    _ ≤ K * (4 * (Real.log (2 * (X : ℝ)) / Real.log 2)) := hmul
    _ = _ := by ring

end Problem355.PrimitiveNormal

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

theorem weighted_count_le_log
    (D : RowData) (q N : ℕ) [Fact q.Prime]
    (hN : 1 ≤ N) (hEq : IsUnit (D.E : ZMod q))
    (hparam : D.h ^ 26 ≤ (q : ℝ))
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (W : Matrix (Fin 3) (Fin 3) ℤ → ℝ)
    (Ca Cg Cd : ℝ) (hCa : 0 ≤ Ca) (hCg : 0 ≤ Cg) (hCd : 0 ≤ Cd)
    (hW : ∀ A ∈ S, 0 ≤ W A)
    (hdet : ∀ A ∈ S, A.det = 0)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ D.L)
    (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ (2 * N : ℕ))
    (hcap : ∀ A ∈ S, 0 < W A → ∃ T : Set (Fin 3 → ZMod q),
      AuxiliaryCap.IsCap T ∧ ∀ i, (A.map (Int.castRingHom (ZMod q))).col i ∈ T)
    (haffine : ∀ A ∈ S,
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col → W A ≤ Ca)
    (hwide : ∀ A ∈ S, W A ≤ Cg * (q : ℝ) ^ 2 * D.h ^ 24)
    (hdistinct : ∀ A ∈ S,
      (∃ i j : Fin 3, (A.map (Int.castRingHom (ZMod q))).col i ≠
        (A.map (Int.castRingHom (ZMod q))).col j) →
      W A ≤ Cd * (q : ℝ) * D.h ^ 12)
    (hexclude : ∀ A ∈ S, ∀ x : Fin 3 → ℤ, IsPrimitive x → A *ᵥ x = 0 →
      AffineIndependent (ZMod q) (A.map (Int.castRingHom (ZMod q))).col →
      0 < W A → D.h ^ 2 < ‖toEuclidean x‖) :
    (∑ A ∈ S, W A) ≤ countConstant Ca Cg Cd * (N : ℝ) ^ 6 /
      (D.I : ℝ) ^ 2 * (Real.log (4 * (N : ℝ)) / Real.log 2) := by
  classical
  let K : ℝ := (1024 * Ca + 3 * (125 * Cg + 512 * Cd)) *
    planeConstant * (N : ℝ) ^ 6 / (D.I : ℝ) ^ 2
  have hK : 0 ≤ K := by dsimp [K, planeConstant]; positivity
  have htotal := PrimitiveNormal.weighted_count_le_log_of_normal_shell_bound
    S W hW hdet hheight hproj (2 * N) (by omega)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound) hK
  have hshell : ∀ i : ℕ,
      ∑ x ∈ (normalBox (2 * N)).filter (fun x =>
        (2 : ℝ) ^ i ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ < 2 ^ (i + 1)),
        ∑ A ∈ S.filter (fun A => A *ᵥ x = 0), W A ≤ K := by
    intro i
    let T := (normalBox (2 * N)).filter (fun x =>
      (2 : ℝ) ^ i ≤ ‖toEuclidean x‖ ∧ ‖toEuclidean x‖ < 2 ^ (i + 1))
    let F := fun x => S.filter (fun A => A *ᵥ x = 0)
    have hp : ∀ x ∈ T, IsPrimitive x := by
      intro x hx
      exact ((mem_normalBox _ x).mp (Finset.mem_filter.mp hx).1).1
    have hxne : ∀ x ∈ T, ∀ j, x j ≠ 0 := by
      intro x hx
      exact ((mem_normalBox _ x).mp (Finset.mem_filter.mp hx).1).2.1
    have hn : ∀ x ∈ T, ((2 ^ i : ℕ) : ℝ) ≤ ‖toEuclidean x‖ ∧
        ‖toEuclidean x‖ < 2 * ((2 ^ i : ℕ) : ℝ) := by
      intro x hx
      have hh := (Finset.mem_filter.mp hx).2
      simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_succ, mul_comm] using hh
    have hF : ∀ x, ∀ A ∈ F x, A *ᵥ x = 0 ∧ ∀ j, A j ∈ D.L := by
      intro x A hA
      exact ⟨(Finset.mem_filter.mp hA).2, hrows A (Finset.mem_filter.mp hA).1⟩
    have hc : ∀ x ∈ T, ∀ A ∈ F x, ∀ j k, |(A j k : ℝ)| ≤ 2 * (N : ℝ) := by
      intro x hx A hA j k
      exact_mod_cast hbound A (Finset.mem_filter.mp hA).1 j k
    have hpr : ∀ x ∈ T, ∀ A ∈ F x, ∃ s t : Fin 3,
        A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
        PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t := by
      intro x hx A hA
      have ha := (Finset.mem_filter.mp hA).1
      exact ⟨0, 1, hheight A ha 0, hheight A ha 1, hproj A ha 0 1 (by decide)⟩
    exact ZeroDeterminantCount.combined_shell_le D q (2 ^ i) hEq hparam T
      (pow_pos (by decide) _) hp hxne hn F hF W (N : ℝ) Ca Cg Cd
      (Nat.cast_nonneg _) hCa hCg hCd
      hc hpr
      (fun x hx A hA => hW A (Finset.mem_filter.mp hA).1)
      (fun x hx A hA hw => hcap A (Finset.mem_filter.mp hA).1 hw)
      (fun x hx A hA ha => haffine A (Finset.mem_filter.mp hA).1 ha)
      (fun x hx A hA ha hw => hexclude A (Finset.mem_filter.mp hA).1 x
        (hp x hx) (Finset.mem_filter.mp hA).2 ha hw)
      (fun x hx A hA => hwide A (Finset.mem_filter.mp hA).1)
      (fun x hx A hA hne => hdistinct A (Finset.mem_filter.mp hA).1 hne)
  have hb := htotal hshell
  convert hb using 1 ; dsimp [K, countConstant] ; push_cast ; ring_nf

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

theorem weighted_count_le_log_oai
    (D : RowData) (q N : ℕ) [Fact q.Prime]
    (hN : 1 ≤ N) (hEq : IsUnit (D.E : ZMod q))
    (hparam : D.h ^ 26 ≤ (q : ℝ))
    (L : AuxiliarySampling.Law q ((D.B ^ D.k) ^ 2))
    (S : Finset (Matrix (Fin 3) (Fin 3) ℤ))
    (hdet : ∀ A ∈ S, A.det = 0)
    (hrows : ∀ A ∈ S, ∀ i, A i ∈ D.L)
    (hheight : ∀ A ∈ S, ∀ i, A 2 i ≠ 0)
    (hproj : ∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
      ((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) ≠
      ((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j))
    (hbound : ∀ A ∈ S, ∀ i j, |A i j| ≤ (2 * N : ℕ)) :
    (∑ A ∈ S, auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col) ≤
      countConstant * (N : ℝ) ^ 6 / (D.I : ℝ) ^ 2 *
        (Real.log (4 * (N : ℝ)) / Real.log 2) := by
  apply ZeroGlobalCount.weighted_count_le_log D q N hN hEq hparam S
    (fun A => auxiliaryWeight q L.size L.weight L.sets
      (A.map (Int.castRingHom (ZMod q))).col)
    8 (2 * 2000 ^ 6) (4 * 2000 ^ 3)
    (by norm_num) (by positivity) (by positivity)
    (fun A _ => auxiliaryWeight_nonneg q L.size L.weight L.sets L.weight_nonneg _)
    hdet hrows hheight hproj hbound
  · intro A hA hpositive
    obtain ⟨ω, hω⟩ := L.exists_outcome_of_weight_pos
      (A.map (Int.castRingHom (ZMod q))).col hpositive
    exact ⟨L.sets ω, L.isCap ω, hω⟩
  · intro A hA hAI
    exact L.weight_le_eight _ hAI
  · intro A hA
    simpa only [RowData.h, Nat.cast_pow] using
      L.weight_le_two_main_square (A.map (Int.castRingHom (ZMod q))).col
  · intro A hA hne
    simpa only [RowData.h, Nat.cast_pow] using
      L.weight_le_four_main_square (A.map (Int.castRingHom (ZMod q))).col hne
  · intro A hA x hx hkernel hAI hpositive
    simpa only [RowData.h, Nat.cast_pow] using
      L.kernel_norm_gt_main_square A hpositive hAI hx.ne_zero hkernel

end Problem355.AuxiliaryZeroCount

end

end OAI
end

theorem solution : type_of% @OAI.Problem355.AuxiliaryZeroCount.weighted_count_le_log_oai := @OAI.Problem355.AuxiliaryZeroCount.weighted_count_le_log_oai
