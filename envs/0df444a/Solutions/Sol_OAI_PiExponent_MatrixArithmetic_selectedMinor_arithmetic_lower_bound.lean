-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.selectedMinor_arithmetic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T17:03:32.651446+00:00
-- url     : https://prove2.me/submissions/864d8609-4998-4374-a971-f8cbb19f8bb5

import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_clearing_bound

namespace OAI.PiExponent

open scoped BigOperators
open Filter Topology

theorem mem_realWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans h

theorem mem_strictWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ strictWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) < H := by
  classical
  simp only [strictWeightedSimplex, Finset.mem_filter, mem_realWeightedSimplex hw,
    and_iff_right_iff_imp]
  exact fun h => h.le

end OAI.PiExponent

namespace OAI.PiExponent.InterpolationMatrix

open scoped BigOperators

theorem column_mem_iff {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (a : Fin (m + 1) → ℕ) :
    a ∈ PiExponent.realWeightedSimplex (columnWeights w0 w) H ↔
      w0 * (a 0 : ℝ) + ∑ i, w i * (a i.succ : ℝ) ≤ H := by
  have hp : ∀ i, 0 < columnWeights w0 w i := by
    intro i
    refine Fin.cases hw0 (fun j => hw j) i
  rw [PiExponent.mem_realWeightedSimplex hp, Fin.sum_univ_succ]
  rfl

theorem row_mem_iff {m : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (b : Fin (m + 1) → ℕ) :
    b ∈ PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H ↔
      v0 * (b 0 : ℝ) + (∑ i, w i * (b i.succ : ℝ)) / θ < H := by
  have hp : ∀ i, 0 < rowWeights v0 θ w i := by
    intro i
    refine Fin.cases hv0 (fun j => div_pos (hw j) hθ) i
  rw [PiExponent.mem_strictWeightedSimplex hp, Fin.sum_univ_succ]
  simp only [rowWeights, Fin.cases_zero, Fin.cases_succ, div_mul_eq_mul_div,
    Finset.sum_div]

theorem column_weight_le {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (c : Column w0 w H) :
    w0 * (c.1 0 : ℝ) + ∑ i, w i * (c.1 i.succ : ℝ) ≤ H :=
  (column_mem_iff hw0 hw c.1).mp c.2

theorem row_weight_lt {m K : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (ρ : Row K v0 θ w H) :
    v0 * (ρ.2.1 0 : ℝ) + (∑ i, w i * (ρ.2.1 i.succ : ℝ)) / θ < H :=
  (row_mem_iff hv0 hθ hw ρ.2.1).mp ρ.2.2

end OAI.PiExponent.InterpolationMatrix

namespace OAI.PiExponent.Arithmetic


theorem log_lcmUpto_le (n : ℕ) :
    Real.log (Nat.lcmUpto n : ℝ) ≤ lcmConstant * n := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  exact Chebyshev.psi_le_const_mul_self (by positivity)

theorem log_lcm_power_product_le {ι : Type*} (s : Finset ι) (T e : ι → ℕ) :
    Real.log (∏ i ∈ s, (Nat.lcmUpto (T i) : ℝ) ^ e i) ≤
      lcmConstant * ∑ i ∈ s, (e i : ℝ) * T i := by
  rw [Real.log_prod (by intro i hi; exact pow_ne_zero _ (by exact_mod_cast Nat.lcmUpto_ne_zero (T i)))]
  simp_rw [Real.log_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left (log_lcmUpto_le (T i)) (Nat.cast_nonneg (e i) : (0 : ℝ) ≤ e i)
  nlinarith only [h]

theorem log_lcm_floor_product_le {ι : Type*} (s : Finset ι)
    (T : ι → ℕ) (w : ι → ℝ) (H : ℝ) (hH : 0 ≤ H) (hw : ∀ i ∈ s, 0 < w i) :
    Real.log (∏ i ∈ s, (Nat.lcmUpto (T i) : ℝ) ^ ⌊H / w i⌋₊) ≤
      H * lcmConstant * ∑ i ∈ s, (T i : ℝ) / w i := by
  calc
    _ ≤ lcmConstant * ∑ i ∈ s, (⌊H / w i⌋₊ : ℝ) * T i :=
      log_lcm_power_product_le s T _
    _ ≤ lcmConstant * ∑ i ∈ s, (H / w i) * T i := by
      apply mul_le_mul_of_nonneg_left _ lcmConstant_pos.le
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (T i))
      exact Nat.floor_le (div_nonneg hH (hw i hi).le)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem sum_ceil_truncation_div_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (F v : ℝ) (hF : 0 ≤ F) (hv : 0 < v) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, (⌈F * w i / v⌉₊ : ℝ) / w i) ≤
      F * s.card / v + ∑ i ∈ s, 1 / w i := by
  calc
    _ ≤ ∑ i ∈ s, (F * w i / v + 1) / w i := by
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ (hw i hi).le
      exact (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hF (hw i hi).le) hv.le)).le
    _ = ∑ i ∈ s, (F / v + 1 / w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [(hw i hi).ne', hv.ne']
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const]; simp; ring

theorem truncation_denominator_log_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (F v H : ℝ) (hF : 0 ≤ F) (hv : 0 < v) (hH : 0 < H)
    (hw : ∀ i ∈ s, 0 < w i) :
    Real.log (∏ i ∈ s,
      (Nat.lcmUpto (⌈F * w i / v⌉₊) : ℝ) ^ ⌊H / w i⌋₊) / H ≤
      lcmConstant * F * s.card / v + lcmConstant * ∑ i ∈ s, 1 / w i := by
  apply (div_le_iff₀ hH).mpr
  calc
    _ ≤ H * lcmConstant * ∑ i ∈ s, (⌈F * w i / v⌉₊ : ℝ) / w i :=
      log_lcm_floor_product_le s _ w H hH.le hw
    _ ≤ H * lcmConstant * (F * s.card / v + ∑ i ∈ s, 1 / w i) := by
      exact mul_le_mul_of_nonneg_left (sum_ceil_truncation_div_le s w F v hF hv hw)
        (mul_pos hH lcmConstant_pos).le
    _ = _ := by ring

theorem column_log_cost_le {ι : Type*} (s : Finset ι) (a q : ι → ℕ) :
    (∑ i ∈ s, (a i : ℝ) * Real.log (q i)) ≤
      ∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ) := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)

theorem sum_exponents_le_weight_div {ι : Type*} (s : Finset ι)
    (a : ι → ℕ) (w : ι → ℝ) (wmin : ℝ) (hmin : 0 < wmin)
    (hw : ∀ i ∈ s, wmin ≤ w i) :
    (∑ i ∈ s, (a i : ℝ)) ≤ (∑ i ∈ s, (a i : ℝ) * w i) / wmin := by
  apply (le_div_iff₀ hmin).mpr
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hw i hi) (Nat.cast_nonneg _))

theorem row_log_cost_lower {ι : Type*} (s : Finset ι)
    (a q : ι → ℕ) (wmin U : ℝ) (hmin : 0 < wmin)
    (hw : ∀ i ∈ s, wmin ≤ (⌈Real.log (q i)⌉₊ : ℝ))
    (hbudget : (∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ)) ≤ U) :
    (∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ)) - U / wmin ≤
      ∑ i ∈ s, (a i : ℝ) * Real.log (q i) := by
  have hsum := sum_exponents_le_weight_div s a (fun i => (⌈Real.log (q i)⌉₊ : ℝ))
    wmin hmin hw
  have hsumU : (∑ i ∈ s, (a i : ℝ)) ≤ U / wmin :=
    hsum.trans (div_le_div_of_nonneg_right hbudget hmin.le)
  have hceil : (∑ i ∈ s, (a i : ℝ) * (⌈Real.log (q i)⌉₊ : ℝ)) ≤
      (∑ i ∈ s, (a i : ℝ) * Real.log (q i)) + ∑ i ∈ s, (a i : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left
      (Nat.ceil_lt_add_one (Real.log_natCast_nonneg (q i))).le (Nat.cast_nonneg (a i) : (0 : ℝ) ≤ a i)
    nlinarith only [h]
  linarith

theorem normalized_arithmetic_bound (M H b E δ logD columnCost rowCost logAbsDet : ℝ)
    (hM : 0 < M) (hH : 0 < H)
    (hclear : -M * logD - columnCost + rowCost ≤ logAbsDet)
    (hden : logD ≤ H * E)
    (hcol : columnCost ≤ M * H)
    (hrow : M * H * b - M * H * δ ≤ rowCost) :
    -(1 - b) - (E + δ) ≤ logAbsDet / (M * H) := by
  apply (le_div_iff₀ (mul_pos hM hH)).mpr
  have hd := mul_le_mul_of_nonneg_left hden hM.le
  nlinarith only [hclear, hd, hcol, hrow]

end OAI.PiExponent.Arithmetic

namespace OAI.PiExponent.MatrixArithmetic

open scoped BigOperators

theorem log_denominator_le {m : ℕ} {q : Fin m → ℕ} (F v0 H : ℝ)
    (hF : 0 ≤ F) (hv0 : 0 < v0) (hH : 0 < H)
    (hw : ∀ i, 0 < logWeights q i) :
    Real.log (denominator q (truncationOrders q F v0) H) ≤
      H * (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i) := by
  have h := Arithmetic.truncation_denominator_log_le Finset.univ
    (logWeights q) F v0 H hF hv0 hH (fun i _ => hw i)
  rw [div_le_iff₀ hH] at h
  simpa [denominator, truncationOrders, mul_comm H] using h

theorem actual_row_card_pos {m K : ℕ} {v0 θ H : ℝ} {q : Fin m → ℕ}
    (hK : 0 < K) (hv0 : 0 < v0) (hθ : 0 < θ) (hH : 0 < H)
    (hw : ∀ i, 0 < logWeights q i) :
    0 < Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) := by
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨⟨0, hK⟩, ⟨fun _ => 0, ?_⟩⟩⟩
  apply (InterpolationMatrix.row_mem_iff hv0 hθ hw _).mpr
  simpa using hH

theorem ceil_log_weight_pos {q : ℕ} (hq : 2 ≤ q) :
    0 < (⌈Real.log (q : ℝ)⌉₊ : ℝ) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  exact lt_of_lt_of_le (Real.log_pos hqR) (Nat.le_ceil _)

theorem column_log_cost_le_H {m : ℕ} {w0 H : ℝ} (q : Fin m → ℕ)
    (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (c : PiExponent.InterpolationMatrix.Column w0
      (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) :
    (∑ i, (c.1 i.succ : ℝ) * Real.log (q i : ℝ)) ≤ H := by
  have hb := PiExponent.InterpolationMatrix.column_weight_le hw0
    (fun i => ceil_log_weight_pos (hq i)) c
  have hc := PiExponent.Arithmetic.column_log_cost_le Finset.univ
    (fun i => c.1 i.succ) q
  have h0 : 0 ≤ w0 * (c.1 0 : ℝ) := mul_nonneg hw0.le (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ i, (c.1 i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉₊ : ℝ) := hc
    _ = ∑ i, (⌈Real.log (q i : ℝ)⌉₊ : ℝ) * (c.1 i.succ : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ ≤ H := by linarith

theorem selected_column_log_cost_le {m K : ℕ} {w0 v0 θ H : ℝ}
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : PiExponent.InterpolationMatrix.Row K v0 θ
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H →
      PiExponent.InterpolationMatrix.Column w0
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) :
    (∑ ρ, ∑ i, ((selection ρ).1 i.succ : ℝ) * Real.log (q i : ℝ)) ≤
      (Fintype.card (PiExponent.InterpolationMatrix.Row K v0 θ
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) : ℝ) * H := by
  calc
    _ ≤ ∑ ρ, H := Finset.sum_le_sum (fun ρ hρ => column_log_cost_le_H q hq hw0 (selection ρ))
    _ = _ := by simp

theorem row_weighted_cost_le {m K : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i)
    (ρ : PiExponent.InterpolationMatrix.Row K v0 θ w H) :
    (∑ i, (ρ.2.1 i.succ : ℝ) * w i) ≤ H * θ := by
  have hb := PiExponent.InterpolationMatrix.row_weight_lt hv0 hθ hw ρ
  have h0 : 0 ≤ v0 * (ρ.2.1 0 : ℝ) := mul_nonneg hv0.le (Nat.cast_nonneg _)
  have hh : (∑ i, w i * (ρ.2.1 i.succ : ℝ)) / θ ≤ H := by linarith
  have hm := (div_le_iff₀ hθ).mp hh
  simpa only [mul_comm] using hm

end OAI.PiExponent.MatrixArithmetic

open OAI.PiExponent OAI.PiExponent.MatrixArithmetic
open scoped BigOperators

theorem solution {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    -(1 - meanRowWeight K v0 θ q H) -
      (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i + θ / wmin) ≤
      Real.log ‖(selectedMinor K w0 v0 θ F H p q selection).det‖ /
        ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have hM : 0 < (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) := by
    exact_mod_cast actual_row_card_pos hK hv0 hθ hH hw
  apply Arithmetic.normalized_arithmetic_bound _ _ _ _ _ _ _ _ _ hM hH
  · exact selectedMinor_clearing_bound p q hq hw0 selection hdet
  · exact log_denominator_le F v0 H hF hv0 hH hw
  · exact selected_column_log_cost_le q hq hw0 selection
  · have hrow (ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H) :=
      Arithmetic.row_log_cost_lower Finset.univ (fun i => ρ.2.1 i.succ) q
        wmin (H * θ) hmin (fun i _ => hwmin i)
        (row_weighted_cost_le hv0 hθ hw ρ)
    have hr := Finset.sum_le_sum (s := Finset.univ) (fun ρ _ => hrow ρ)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hr
    have hb :
        (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H *
          meanRowWeight K v0 θ q H = rowWeightedSum K v0 θ q H := by
      unfold meanRowWeight
      field_simp [(mul_pos hM hH).ne']
    rw [hb]
    simpa only [rowWeightedSum, rowCost, logWeights, mul_div_assoc, mul_assoc] using hr
