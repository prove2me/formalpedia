-- Prove2me | solution 1 for InventoryBounds.two_point_estimation_information
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:25:49.908605+00:00
-- url     : https://prove2.me/submissions/6fdf0e56-7f6a-41e5-8b81-7aa92d005194

import Definitions.Def_InventoryBounds_StationaryValuation
import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open InventoryBounds

namespace S214LC

/-- `x log(x/y) ≥ x - y`. -/
lemma xlog_ge (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 0 < x → 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp [hy]
  have hy' := hxy hx'
  have h := Real.log_le_sub_one_of_pos (div_pos hy' hx')
  rw [show Real.log (x / y) = - Real.log (y / x) by
    rw [← Real.log_inv, inv_div]]
  have : x * (y / x - 1) = y - x := by field_simp
  nlinarith

def w (ρ : ℝ) (b : Bool) : ℝ := if b then ρ else 1 - ρ

lemma w_pos (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) (b : Bool) : 0 < w ρ b := by
  cases b <;> simp [w] <;> linarith

lemma sw_eq {M : ℕ} (ρ : ℝ) (z : Fin M → Bool) : sampleWeight ρ z = ∏ i, w ρ (z i) := rfl

lemma sw_pos {M : ℕ} (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) (z : Fin M → Bool) :
    0 < sampleWeight ρ z := by
  rw [sw_eq]; exact Finset.prod_pos fun i _ => w_pos ρ h0 h1 _

lemma sum_w (ρ : ℝ) : ∑ b : Bool, w ρ b = 1 := by simp [w]

lemma expect_coord {M : ℕ} (ρ : ℝ) (i : Fin M) (g : Bool → ℝ) :
    ∑ z : Fin M → Bool, sampleWeight ρ z * g (z i) = ∑ b : Bool, w ρ b * g b := by
  classical
  have h := Fintype.prod_sum (fun (j : Fin M) (b : Bool) => w ρ b * (if j = i then g b else 1))
  have lhs : ∏ j : Fin M, ∑ b : Bool, w ρ b * (if j = i then g b else 1) =
      ∑ b : Bool, w ρ b * g b := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj; simp [hj, w]
    · simp
  rw [lhs] at h
  rw [h]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib, sw_eq]
  congr 1
  rw [Finset.prod_ite_eq']; simp

lemma sum_sw {M : ℕ} (ρ : ℝ) : ∑ z : Fin M → Bool, sampleWeight ρ z = 1 := by
  have := expect_coord (M := M) ρ
  classical
  have h := Fintype.prod_sum (fun (_ : Fin M) (b : Bool) => w ρ b)
  simp only [sum_w, Finset.prod_const_one] at h
  rw [h]; rfl

lemma tensor {M : ℕ} (ρ₀ ρ₁ : ℝ) (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1)
    (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) :
    ∑ z : Fin M → Bool, sampleWeight ρ₁ z * Real.log (sampleWeight ρ₁ z / sampleWeight ρ₀ z) =
      (M : ℝ) * binaryKL ρ₁ ρ₀ := by
  have hlog : ∀ z : Fin M → Bool, Real.log (sampleWeight ρ₁ z / sampleWeight ρ₀ z) =
      ∑ i, Real.log (w ρ₁ (z i) / w ρ₀ (z i)) := by
    intro z
    rw [sw_eq, sw_eq, ← Finset.prod_div_distrib, Real.log_prod]
    intro i _
    exact (div_pos (w_pos ρ₁ hρ₁ hρ₁1 _) (w_pos ρ₀ hρ₀ hρ₀1 _)).ne'
  simp_rw [hlog, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [expect_coord ρ₁ _ (fun b => Real.log (w ρ₁ b / w ρ₀ b))]
  simp [w, binaryKL]
  ring


lemma group {ι : Type*} [Fintype ι] (P₁ P₀ u : ι → ℝ) (h1 : ∀ z, 0 < P₁ z) (h0 : ∀ z, 0 < P₀ z)
    (hu : ∀ z, 0 ≤ u z) :
    (∑ z, P₁ z * u z) * Real.log ((∑ z, P₁ z * u z) / ∑ z, P₀ z * u z) ≤
      ∑ z, P₁ z * u z * Real.log (P₁ z / P₀ z) := by
  set A := ∑ z, P₁ z * u z
  set B := ∑ z, P₀ z * u z
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun z _ => mul_nonneg (h1 z).le (hu z)
  rcases hA0.eq_or_lt with hA | hA
  · have hz : ∀ z, P₁ z * u z = 0 := by
      intro z
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => mul_nonneg (h1 z).le (hu z))).mp
        hA.symm z (Finset.mem_univ z)
      exact this
    rw [← hA]; simp [hz]
  have hB : 0 < B := by
    rcases (Finset.sum_nonneg fun z _ => mul_nonneg (h0 z).le (hu z) : (0:ℝ) ≤ B).eq_or_lt
      with hB | hB
    · exfalso
      have hz : ∀ z, P₀ z * u z = 0 := fun z =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => mul_nonneg (h0 z).le (hu z))).mp
          hB.symm z (Finset.mem_univ z)
      have : A = 0 := Finset.sum_eq_zero fun z _ => by
        have := hz z
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (h0 z).ne'
        · rw [h, mul_zero]
      linarith
    · exact hB
  set c := A / B with hc
  have hcpos : 0 < c := div_pos hA hB
  have hterm : ∀ z, P₁ z * u z - P₀ z * u z * c ≤
      P₁ z * u z * Real.log (P₁ z / P₀ z) - P₁ z * u z * Real.log c := by
    intro z
    rcases (hu z).eq_or_lt with hz | hz
    · rw [← hz]; simp
    have hx := xlog_ge (P₁ z * u z) (P₀ z * u z * c) (mul_nonneg (h1 z).le (hu z))
      (by have := h0 z; positivity) (fun _ => by have := h0 z; positivity)
    have e : Real.log (P₁ z * u z / (P₀ z * u z * c)) = Real.log (P₁ z / P₀ z) - Real.log c := by
      rw [← Real.log_div (div_pos (h1 z) (h0 z)).ne' hcpos.ne']
      congr 1
      have := (h0 z).ne'; have := hz.ne'
      field_simp
    rw [e] at hx; linarith
  have hsum := Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => hterm z
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hsum
  have : A - B * c = 0 := by rw [hc]; field_simp; ring
  linarith

lemma kl_mono (a b η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2) (ha : 1 - η ≤ a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hbη : b ≤ η) :
    (1 - 2 * η) * Real.log ((1 - η) / η) ≤ binaryKL a b := by
  have ha0 : 0 < a := by linarith
  set c := 1 - η with hcdef
  have hc0 : 0 < c := by linarith
  -- step 1: kl(a, η) ≤ kl(a, b)
  have step1 : binaryKL a η ≤ binaryKL a b := by
    unfold binaryKL
    have L1 := Real.one_sub_inv_le_log_of_pos (div_pos hη hb)
    have L2 := Real.one_sub_inv_le_log_of_pos (div_pos (by linarith : (0:ℝ) < 1 - η)
      (by linarith : (0:ℝ) < 1 - b))
    have e1 : Real.log (a / b) = Real.log (a / η) + Real.log (η / b) := by
      rw [← Real.log_mul (div_pos ha0 hη).ne' (div_pos hη hb).ne']
      congr 1; field_simp
    have e2 : (1 - a) * Real.log ((1 - a) / (1 - b)) =
        (1 - a) * Real.log ((1 - a) / (1 - η)) + (1 - a) * Real.log ((1 - η) / (1 - b)) := by
      rcases (sub_nonneg.mpr ha1).eq_or_lt with h | h
      · rw [← h]; simp
      rw [← mul_add, ← Real.log_mul (div_pos h (by linarith)).ne' (div_pos (by linarith)
        (by linarith)).ne']
      congr 2
      have : (1 - η) ≠ 0 := by linarith
      have : (1 - b) ≠ 0 := by linarith
      field_simp
    rw [e1, e2]
    rw [inv_div] at L1 L2
    have k1 : a * (1 - b / η) ≤ a * Real.log (η / b) := mul_le_mul_of_nonneg_left L1 ha0.le
    have k2 : (1 - a) * (1 - (1 - b) / (1 - η)) ≤ (1 - a) * Real.log ((1 - η) / (1 - b)) :=
      mul_le_mul_of_nonneg_left L2 (by linarith)
    have k3 : 0 ≤ a * (1 - b / η) + (1 - a) * (1 - (1 - b) / (1 - η)) := by
      have e : a * (1 - b / η) + (1 - a) * (1 - (1 - b) / (1 - η)) =
          (η - b) * (a - η) / (η * (1 - η)) := by
        have : (1 - η) ≠ 0 := by linarith
        field_simp; ring
      rw [e]; apply div_nonneg
      · apply mul_nonneg <;> linarith
      · apply mul_nonneg <;> linarith
    linarith
  -- step 2: (1-2η) log(c/η) ≤ kl(a, η)
  have hlogpos : 0 < Real.log (c / η) := Real.log_pos (by rw [one_lt_div hη]; linarith)
  have klac : 0 ≤ a * Real.log (a / c) + (1 - a) * Real.log ((1 - a) / (1 - c)) := by
    have x1 := xlog_ge a c ha0.le hc0.le (fun _ => hc0)
    have x2 := xlog_ge (1 - a) (1 - c) (by linarith) (by linarith) (fun _ => by linarith)
    have : a * Real.log (a / c) ≥ a - c := x1
    have : (1 - a) * Real.log ((1 - a) / (1 - c)) ≥ (1 - a) - (1 - c) := x2
    linarith
  have step2 : (1 - 2 * η) * Real.log (c / η) ≤ binaryKL a η := by
    unfold binaryKL
    have e1 : Real.log (a / η) = Real.log (a / c) + Real.log (c / η) := by
      rw [← Real.log_mul (div_pos ha0 hc0).ne' (div_pos hc0 hη).ne']
      congr 1; field_simp
    have e2 : (1 - a) * Real.log ((1 - a) / (1 - η)) =
        (1 - a) * Real.log ((1 - a) / (1 - c)) - (1 - a) * Real.log (c / η) := by
      rcases (sub_nonneg.mpr ha1).eq_or_lt with h | h
      · rw [← h]; simp
      have h1c : 1 - c = η := by rw [hcdef]; ring
      rw [h1c, ← mul_sub, ← Real.log_div (div_pos h hη).ne' (div_pos hc0 hη).ne']
      congr 2
      rw [hcdef]
      have : (1 - η) ≠ 0 := by linarith
      field_simp
    rw [e1, e2]
    nlinarith
  linarith

end S214LC

open S214LC in
theorem solution (M : ℕ)
    (κ : Kernel (Fin M → Bool) ℝ) [IsMarkovKernel κ]
    (ρ₀ ρ₁ v₀ v₁ ε η : ℝ)
    (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1)
    (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hε : 0 < ε) (hη : 0 < η) (hη2 : η < 1 / 2)
    (hsep : 2 * ε < v₁ - v₀)
    (hs₀ : 1 - η ≤ estimatorSuccess κ ρ₀ v₀ ε)
    (hs₁ : 1 - η ≤ estimatorSuccess κ ρ₁ v₁ ε) :
    (1 - 2 * η) * Real.log ((1 - η) / η) ≤ (M : ℝ) * binaryKL ρ₁ ρ₀ := by
  set P₁ : (Fin M → Bool) → ℝ := sampleWeight ρ₁
  set P₀ : (Fin M → Bool) → ℝ := sampleWeight ρ₀
  have hP₁ : ∀ z, 0 < P₁ z := sw_pos ρ₁ hρ₁ hρ₁1
  have hP₀ : ∀ z, 0 < P₀ z := sw_pos ρ₀ hρ₀ hρ₀1
  set I₁ := Set.Icc (v₁ - ε) (v₁ + ε)
  set I₀ := Set.Icc (v₀ - ε) (v₀ + ε)
  set f : (Fin M → Bool) → ℝ := fun z => (κ z I₁).toReal
  set g : (Fin M → Bool) → ℝ := fun z => (κ z I₀).toReal
  have hf0 : ∀ z, 0 ≤ f z := fun z => ENNReal.toReal_nonneg
  have hg0 : ∀ z, 0 ≤ g z := fun z => ENNReal.toReal_nonneg
  have hdisj : Disjoint I₀ I₁ := by
    rw [Set.disjoint_left]
    intro x hx0 hx1
    simp only [I₀, I₁, Set.mem_Icc] at hx0 hx1
    linarith
  have hfg : ∀ z, f z + g z ≤ 1 := by
    intro z
    have hu : κ z I₀ + κ z I₁ ≤ 1 := by
      rw [← measure_union hdisj measurableSet_Icc]; exact prob_le_one
    have hne0 : κ z I₀ ≠ ⊤ := measure_ne_top _ _
    have hne1 : κ z I₁ ≠ ⊤ := measure_ne_top _ _
    have := ENNReal.toReal_mono ENNReal.one_ne_top hu
    rw [ENNReal.toReal_add hne0 hne1] at this
    simp only [f, g]; simpa [add_comm] using this
  have hf1 : ∀ z, f z ≤ 1 := fun z => by linarith [hfg z, hg0 z]
  set a := ∑ z, P₁ z * f z with ha_def
  set b := ∑ z, P₀ z * f z with hb_def
  have ha : 1 - η ≤ a := hs₁
  have hsum1 : ∑ z, P₁ z = 1 := sum_sw ρ₁
  have hsum0 : ∑ z, P₀ z = 1 := sum_sw ρ₀
  have ha1 : a ≤ 1 := by
    calc a ≤ ∑ z, P₁ z := Finset.sum_le_sum fun z _ => by
          have := hP₁ z; nlinarith [hf1 z]
      _ = 1 := hsum1
  have hb : b ≤ η := by
    have h2 : b + ∑ z, P₀ z * g z ≤ 1 := by
      rw [hb_def, ← Finset.sum_add_distrib, ← hsum0]
      exact Finset.sum_le_sum fun z _ => by
        have := hP₀ z; nlinarith [hfg z]
    have : 1 - η ≤ ∑ z, P₀ z * g z := hs₀
    linarith
  have hbpos : 0 < b := by
    rcases (Finset.sum_nonneg fun z _ => mul_nonneg (hP₀ z).le (hf0 z) : (0:ℝ) ≤ b).eq_or_lt
      with h | h
    · exfalso
      have hz : ∀ z, f z = 0 := fun z => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => mul_nonneg (hP₀ z).le (hf0 z))).mp
          h.symm z (Finset.mem_univ z)
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' (hP₀ z).ne'
        · exact h'
      have : a = 0 := Finset.sum_eq_zero fun z _ => by rw [hz z, mul_zero]
      linarith
    · exact h
  -- grouping
  have G1 := group P₁ P₀ f hP₁ hP₀ hf0
  have G2 := group P₁ P₀ (fun z => 1 - f z) hP₁ hP₀ (fun z => by linarith [hf1 z])
  have e1 : ∑ z, P₁ z * (1 - f z) = 1 - a := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum1, ha_def]
  have e0 : ∑ z, P₀ z * (1 - f z) = 1 - b := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum0, hb_def]
  rw [e1, e0] at G2
  have hsplit : ∑ z, P₁ z * Real.log (P₁ z / P₀ z) =
      ∑ z, P₁ z * f z * Real.log (P₁ z / P₀ z) +
        ∑ z, P₁ z * (1 - f z) * Real.log (P₁ z / P₀ z) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => by ring
  have hKL : binaryKL a b ≤ (M : ℝ) * binaryKL ρ₁ ρ₀ := by
    rw [← tensor ρ₀ ρ₁ hρ₀ hρ₀1 hρ₁ hρ₁1]
    show _ ≤ ∑ z, P₁ z * Real.log (P₁ z / P₀ z)
    rw [hsplit]
    unfold binaryKL
    linarith
  exact (kl_mono a b η hη hη2 ha ha1 hbpos hb).trans hKL
