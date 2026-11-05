-- Prove2me | solution 1 for MultiItemRev.KBundling.explicit_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:15:29.885786+00:00
-- url     : https://prove2.me/submissions/875d9aad-3492-4343-b417-27b82d95dd10

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Theorems.Thm_MultiItemRev_KBundling_power_of_two_bound
import Theorems.Thm_MultiItemRev_KBundling_rev_mono_goods
import Theorems.Thm_MultiItemRev_KBundling_proposition_13_i

open MeasureTheory
open scoped NNReal ENNReal

namespace KBExplicitAux
open MultiItemRev.Decomp

lemma meas_sum {ι : Type*} [Fintype ι] : Measurable (fun x : ι → ℝ≥0 => ∑ i, x i) := by
  fun_prop

/-- The law of `X₁+⋯+X_{n+n'}` is the convolution of the laws of the two block sums. -/
lemma map_sum_pi_add (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (n n' : ℕ) :
    (Measure.pi (fun _ : Fin (n + n') => ν)).map (fun x => ∑ i, x i) =
      (((Measure.pi (fun _ : Fin n => ν)).map (fun x => ∑ i, x i)).prod
        ((Measure.pi (fun _ : Fin n' => ν)).map (fun x => ∑ i, x i))).map
          (fun p => p.1 + p.2) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (n + n') => ν)
    (finSumFinEquiv (m := n) (n := n'))).map_eq
  have h2 := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : Fin n ⊕ Fin n' => ℝ≥0) (fun _ => ν)).map_eq
  rw [← h1, ← h2, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
    Measure.map_map meas_sum (by fun_prop), Measure.map_prod_map _ _ meas_sum meas_sum,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
  rw [← Fintype.sum_equiv (finSumFinEquiv (m := n) (n := n'))
    (fun i => (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n' => ℝ≥0)).symm p i)]
  · rw [Fintype.sum_sum_type]
    rfl
  · intro i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]

lemma jointLaw_oneGood (a b : Measure ℝ≥0) [IsProbabilityMeasure a] [IsProbabilityMeasure b] :
    jointLaw (oneGood a) (oneGood b) =
      (a.prod b).map (fun p => (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Unit => ℝ≥0)).symm
        (fun _ => p.1, fun _ => p.2)) := by
  unfold jointLaw oneGood
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  rfl

lemma srev_jointLaw_oneGood (a b : Measure ℝ≥0) [IsProbabilityMeasure a]
    [IsProbabilityMeasure b] :
    SRev (jointLaw (oneGood a) (oneGood b)) = Rev1 a + Rev1 b := by
  unfold SRev
  rw [Fintype.sum_sum_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [jointLaw_oneGood]
  congr 2
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have : ((fun x : Unit ⊕ Unit → ℝ≥0 => x (Sum.inl default)) ∘
        fun p : ℝ≥0 × ℝ≥0 => (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Unit => ℝ≥0)).symm
          (fun _ => p.1, fun _ => p.2)) = Prod.fst := by
      funext p; rfl
    rw [this, Measure.map_fst_prod]; simp
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have : ((fun x : Unit ⊕ Unit → ℝ≥0 => x (Sum.inr default)) ∘
        fun p : ℝ≥0 × ℝ≥0 => (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Unit => ℝ≥0)).symm
          (fun _ => p.1, fun _ => p.2)) = Prod.snd := by
      funext p; rfl
    rw [this, Measure.map_snd_prod]; simp

lemma brev_jointLaw_oneGood (a b : Measure ℝ≥0) [IsProbabilityMeasure a]
    [IsProbabilityMeasure b] :
    BRev (jointLaw (oneGood a) (oneGood b)) = Rev1 ((a.prod b).map (fun p => p.1 + p.2)) := by
  unfold BRev
  rw [jointLaw_oneGood, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 2
  funext p
  simp only [Function.comp_apply, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton]
  rfl

/-- `B_{2n} ≤ 2(w+1) B_n` from Proposition 13 (i). -/
lemma brev_double (w : ℝ) (hw : w * Real.exp (w + 1) = 1) (ν : Measure ℝ≥0)
    [IsProbabilityMeasure ν] (n : ℕ) :
    BRev (Measure.pi (fun _ : Fin (n + n) => ν)) ≤
      ENNReal.ofReal (2 * (w + 1)) * BRev (Measure.pi (fun _ : Fin n => ν)) := by
  set ν' := (Measure.pi (fun _ : Fin n => ν)).map (fun x => ∑ i, x i) with hν'
  have : IsProbabilityMeasure ν' := Measure.isProbabilityMeasure_map meas_sum.aemeasurable
  have h13 := MultiItemRev.KBundling.proposition_13_i w hw ν' ν'
  rw [srev_jointLaw_oneGood, brev_jointLaw_oneGood, ← map_sum_pi_add] at h13
  have hw0 : 0 < w := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (Real.exp_pos (w + 1)).le
    linarith
  have hBn : BRev (Measure.pi (fun _ : Fin n => ν)) = Rev1 ν' := rfl
  have hB2 : BRev (Measure.pi (fun _ : Fin (n + n) => ν)) =
      Rev1 ((Measure.pi (fun _ : Fin (n + n) => ν)).map (fun x => ∑ i, x i)) := rfl
  rw [hBn, hB2]
  calc Rev1 ((Measure.pi (fun _ : Fin (n + n) => ν)).map (fun x => ∑ i, x i))
      = ENNReal.ofReal (w + 1) * (ENNReal.ofReal (1 / (w + 1)) *
          Rev1 ((Measure.pi (fun _ : Fin (n + n) => ν)).map (fun x => ∑ i, x i))) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith), mul_one_div_cancel (by linarith),
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (w + 1) * (Rev1 ν' + Rev1 ν') := by gcongr
    _ = ENNReal.ofReal (2 * (w + 1)) * Rev1 ν' := by
        rw [← two_mul, ← mul_assoc, mul_comm (ENNReal.ofReal (w + 1)) 2,
          ENNReal.ofReal_mul (by norm_num)]
        simp

end KBExplicitAux

open KBExplicitAux in
theorem solution (w : ℝ) (hw : w * Real.exp (w + 1) = 1)
    (k : ℕ) (hk : 2 ≤ k) (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin k => ν)) ≤
      ENNReal.ofReal (8 * (w + 1) * (Real.logb 2 (k : ℝ) + 2)) *
        MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) := by
  have hw0 : 0 < w := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (Real.exp_pos (w + 1)).le
    linarith
  set j := Nat.log 2 k with hj
  have hk0 : k ≠ 0 := by omega
  have hjle : 2 ^ j ≤ k := Nat.pow_log_le_self 2 hk0
  have hklt : k < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  -- R_k ≤ R_{2^{j+1}}
  have hR := (MultiItemRev.KBundling.rev_mono_goods k (2 ^ (j + 1)) hklt.le ν).1
  -- B_{2^j} ≤ B_k
  have hBk := (MultiItemRev.KBundling.rev_mono_goods (2 ^ j) k hjle ν).2
  -- R_{2^{j+1}} ≤ 4 (j+2) B_{2^{j+1}}
  have hP := MultiItemRev.KBundling.power_of_two_bound (j + 1) (by omega) ν
  have hlogb : Real.logb 2 ((2 ^ (j + 1) : ℕ) : ℝ) = (j : ℝ) + 1 := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  rw [hlogb] at hP
  -- B_{2^{j+1}} ≤ 2(w+1) B_{2^j}
  have hD := brev_double w hw ν (2 ^ j)
  have h2 : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by ring
  rw [h2] at hD
  -- j ≤ log₂ k
  have hjlog : (j : ℝ) ≤ Real.logb 2 (k : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hk0)]
    rw [Real.rpow_natCast]
    exact_mod_cast hjle
  calc MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin k => ν))
      ≤ MultiItemRev.Decomp.Rev (Measure.pi (fun _ : Fin (2 ^ (j + 1)) => ν)) := hR
    _ ≤ ENNReal.ofReal (4 * ((j : ℝ) + 1 + 1)) *
          MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin (2 ^ (j + 1)) => ν)) := hP
    _ ≤ ENNReal.ofReal (4 * ((j : ℝ) + 1 + 1)) * (ENNReal.ofReal (2 * (w + 1)) *
          MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin (2 ^ j) => ν))) := by gcongr
    _ ≤ ENNReal.ofReal (4 * ((j : ℝ) + 1 + 1)) * (ENNReal.ofReal (2 * (w + 1)) *
          MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν))) := by gcongr
    _ = ENNReal.ofReal (8 * (w + 1) * ((j : ℝ) + 2)) *
          MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring
    _ ≤ ENNReal.ofReal (8 * (w + 1) * (Real.logb 2 (k : ℝ) + 2)) *
          MultiItemRev.Decomp.BRev (Measure.pi (fun _ : Fin k => ν)) := by
        gcongr
