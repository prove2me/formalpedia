-- Prove2me | solution 1 for HermitekLEAN.truncCirclePoly_tendsto_circleSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:54.312883+00:00
-- url     : https://prove2.me/submissions/e7ba88db-aa54-4b13-85c8-8f8463fa586c

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_phi_explicit
public import Theorems.Thm_HermitekLEAN_phi_polar
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_continuous_Phi
public import Theorems.Thm_HermitekLEAN_integrable_weightedDiag
public import Theorems.Thm_HermitekLEAN_integrable_weightedCross
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_inner
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_truncate
public import Theorems.Thm_HermitekLEAN_truncate_mem_Hk
public import Theorems.Thm_HermitekLEAN_truncate_normSq
public import Theorems.Thm_HermitekLEAN_truncate_circle
public import Theorems.Thm_HermitekLEAN_integrable_truncate_normSq_exp
public import Theorems.Thm_HermitekLEAN_circle_representation_hermiteCoeff
public import Theorems.Thm_PhaseRetrieval_integral_norm_sq_fourier_sum

attribute [local simp] HermitekLEAN.qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private lemma circleL2Sq_finFourierPoly {D : ℕ} (c : Fin D → ℂ) :
    circleL2Sq (fun t : Circle => ∑ k : Fin D, c k * fourier (k.val : ℤ) t) =
      ∑ k : Fin D, ‖c k‖ ^ 2 := by
  let frequencies : Fin D ↪ ℤ :=
    ⟨fun i => (i.val : ℤ), fun i j h => Fin.ext (Nat.cast_injective h)⟩
  have hfrequencies (i : Fin D) : frequencies i = (i.val : ℤ) := rfl
  simpa only [circleL2Sq, HermiteLEAN.circleL2Sq, hfrequencies] using
    PhaseRetrieval.integral_norm_sq_fourier_sum (period := T) frequencies c
private theorem continuous_finiteHermiteSum (k : ℕ) {D : ℕ} (a : Fin D → ℂ) :
    Continuous (finiteHermiteSum k a) := by
  unfold finiteHermiteSum
  exact continuous_finsetSum _ (fun m _ => continuous_const.mul (continuous_Phi k m.1))
private lemma weightedNormSq_eq_re_weightedInner (F : ℂ → ℂ) :
    weightedNormSq F = Complex.re (weightedInner F F) := by
  unfold HermitekLEAN.weightedNormSq HermiteLEAN.weightedNormSq
  unfold HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  have hfun :
      (fun z : ℂ => F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ))
        = fun z : ℂ => ((‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
    funext z
    rw [show F z * (starRingEnd ℂ) (F z) = ((‖F z‖ ^ 2 : ℝ) : ℂ) by
      simpa only [ofReal_pow] using Complex.mul_conj' (F z)]
    simp
  rw [hfun, integral_complex_ofReal]
  simp
private lemma weightedInner_conj_symm (F G : ℂ → ℂ) :
    weightedInner F G = star (weightedInner G F) := by
  unfold HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  change _ = (starRingEnd ℂ) _
  rw [map_mul]
  have hpi : (starRingEnd ℂ) ((1 : ℂ) / ↑Real.pi) = (1 : ℂ) / ↑Real.pi := by
    rw [map_div₀, map_one, Complex.conj_ofReal]
  rw [hpi]
  congr 1
  rw [show (starRingEnd ℂ)
    (∫ z : ℂ, G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2))) =
    ∫ z : ℂ, (starRingEnd ℂ)
      (G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2)))
    from (integral_conj (f := fun z =>
      G z * (starRingEnd ℂ) (F z) * ↑(Real.exp (-‖z‖ ^ 2)))).symm]
  congr 1
  ext z
  simp only [map_mul, starRingEnd_self_apply, Complex.conj_ofReal]
  ac_rfl
private lemma integrable_finiteHermiteSum_weightedCross
    (k : ℕ) {D n : ℕ} (a : Fin D → ℂ) :
    Integrable (fun z : ℂ =>
      finiteHermiteSum k a z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  unfold finiteHermiteSum
  have hEq :
      (fun z : ℂ =>
        (∑ m : Fin D, a m * Phi k m.1 z) * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ))
        =
      fun z : ℂ =>
        ∑ m : Fin D, a m * (Phi k m.1 z * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    funext z
    calc
      (∑ m : Fin D, a m * Phi k m.1 z) * (starRingEnd ℂ) (Phi k n z) *
          (Real.exp (-‖z‖ ^ 2) : ℂ)
        = ∑ m : Fin D,
            (a m * Phi k m.1 z) *
              ((starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
              rw [mul_assoc, ← Finset.sum_mul]
      _ = ∑ m : Fin D,
          a m * (Phi k m.1 z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            ac_rfl
  rw [hEq]
  refine MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin D)) ?_
  intro m hm
  exact
    (integrable_weightedCross k m.1 n).const_mul (a m)
private lemma integrable_truncate_weightedCross
    (k J n : ℕ) (G : ℂ → ℂ) :
    Integrable (fun z : ℂ =>
      truncate k J G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  exact
    (integrable_finiteHermiteSum_weightedCross (k := k) (n := n)
      (a := fun m : Fin (J + 1) => hermiteCoeff k G m.1))
private theorem weightedInner_add_left_of_integrable
    (F G H : ℂ → ℂ)
    (hF : Integrable
      (fun z : ℂ => F z * (starRingEnd ℂ) (H z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))
    (hG : Integrable
      (fun z : ℂ => G z * (starRingEnd ℂ) (H z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :
    weightedInner (F + G) H = weightedInner F H + weightedInner G H := by
  have hsum := congrArg (fun t : ℂ => (1 / Real.pi : ℂ) * t) (integral_add hF hG)
  simpa only [weightedInner, HermiteLEAN.weightedInner, one_div, Pi.add_apply, add_mul, ofReal_exp,
    ofReal_neg, ofReal_pow, mul_comm, mul_add, mul_left_comm, mul_assoc] using hsum
private theorem weightedInner_finset_sum_left
    {α : Type*}
    (s : Finset α)
    (f : α → ℂ → ℂ)
    (g : ℂ → ℂ)
    (hf : ∀ a ∈ s,
      Integrable
        (fun z : ℂ => f a z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :
    weightedInner (fun z => Finset.sum s (fun a => f a z)) g =
      Finset.sum s (fun a => weightedInner (f a) g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [weightedInner, HermiteLEAN.weightedInner]
  | @insert a s ha ih =>
      have hf' :
          ∀ b ∈ s,
            Integrable
              (fun z : ℂ => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
        simp_all only [ofReal_exp, ofReal_neg, ofReal_pow, mem_insert, forall_eq_or_imp,
          implies_true]
      have hfa :
          Integrable
            (fun z : ℂ => f a z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) :=
        hf a (Finset.mem_insert_self a s)
      simp_rw [Finset.sum_insert ha]
      have hsumInt :
          Integrable
            (fun z : ℂ =>
              (Finset.sum s (fun b => f b z)) * (starRingEnd ℂ) (g z) *
                (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
        have hsumInt' :
            Integrable
              (fun z : ℂ =>
                Finset.sum s
                  (fun b => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) :=
          MeasureTheory.integrable_finsetSum s (fun b hb => hf' b hb)
        have hEq :
            (fun z : ℂ =>
              (Finset.sum s (fun b => f b z)) * (starRingEnd ℂ) (g z) *
                (Real.exp (-‖z‖ ^ 2) : ℂ)) =
              fun z : ℂ =>
                Finset.sum s
                  (fun b => f b z * (starRingEnd ℂ) (g z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
          funext z
          rw [mul_assoc, Finset.sum_mul]
          simp [mul_left_comm, mul_comm]
        exact hEq.symm ▸ hsumInt'
      change weightedInner ((fun z : ℂ => f a z) + fun z => Finset.sum s (fun b => f b z)) g =
        weightedInner (f a) g + Finset.sum s (fun a => weightedInner (f a) g)
      rw [weightedInner_add_left_of_integrable (F := fun z => f a z)
        (G := fun z => Finset.sum s (fun b => f b z)) (H := g) hfa hsumInt]
      rw [ih hf']
private lemma hermiteCoeff_sub_truncate
    (k J : ℕ) (G : ℂ → ℂ) (n : ℕ) :
    hermiteCoeff k (fun z : ℂ => G z - truncate k J G z) n =
      if _h : n < J + 1 then 0 else hermiteCoeff k G n := by
  unfold hermiteCoeff
  let fG : ℂ → ℂ := fun z : ℂ =>
    G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  let fT : ℂ → ℂ := fun z : ℂ =>
    truncate k J G z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  let fR : ℂ → ℂ := fun z : ℂ =>
    (G z - truncate k J G z) * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
  have hT : Integrable fT := by
    unfold fT
    simpa only [ofReal_exp, ofReal_neg, ofReal_pow, mul_comm, mul_left_comm, mul_assoc] using
      (integrable_truncate_weightedCross k J n G)
  by_cases hG : Integrable fG
  · have hEq :
        weightedInner (fun z : ℂ => G z - truncate k J G z) (Phi k n) =
          weightedInner G (Phi k n) - weightedInner (truncate k J G) (Phi k n) := by
      unfold weightedInner HermiteLEAN.weightedInner
      calc
        (1 / Real.pi : ℂ) * ∫ z : ℂ, fR z
          = (1 / Real.pi : ℂ) * ∫ z : ℂ, (fG z - fT z) := by
              congr with z
              unfold fR fG fT
              ring
        _ = (1 / Real.pi : ℂ) * ((∫ z : ℂ, fG z) - ∫ z : ℂ, fT z) := by
              simpa only [one_div, ofReal_exp, ofReal_neg, ofReal_pow, mul_eq_mul_left_iff,
                inv_eq_zero, ofReal_eq_zero, pi_ne_zero, or_false, fG, fT, fR] using
                congrArg (fun t : ℂ => (1 / Real.pi : ℂ) * t)
                  (MeasureTheory.integral_sub hG hT)
        _ = weightedInner G (Phi k n) - weightedInner (truncate k J G) (Phi k n) := by
              unfold weightedInner HermiteLEAN.weightedInner
              ring
    rw [hEq]
    have htruncate :
        weightedInner (truncate k J G) (Phi k n) =
          if h : n < J + 1 then hermiteCoeff k G n else 0 := by
      simpa only [Order.lt_add_one_iff, hermiteCoeff, dite_eq_ite] using
        (hermiteCoeff_truncate (k := k) (J := J) (G := G) n)
    have hGcoeff : weightedInner G (Phi k n) = hermiteCoeff k G n := rfl
    by_cases hn : n < J + 1
    · simp [hn, htruncate, hGcoeff]
    · simp [hn, htruncate, hGcoeff]
  · have hGnot : ¬ Integrable fG := hG
    have hR : ¬ Integrable fR := by
      intro hR
      apply hGnot
      have hEq : fG = fun z : ℂ => fR z + fT z := by
        funext z
        unfold fR fG fT
        ring
      simp_all only [integrable_add_iff_integrable_right', not_true_eq_false]
    have hzeroG : weightedInner G (Phi k n) = 0 := by
      change (1 / Real.pi : ℂ) * ∫ z : ℂ, fG z = 0
      rw [MeasureTheory.integral_undef hGnot]
      ring
    have hzeroR :
        weightedInner (fun z : ℂ => G z - truncate k J G z) (Phi k n) = 0 := by
      change (1 / Real.pi : ℂ) * ∫ z : ℂ, fR z = 0
      rw [MeasureTheory.integral_undef hR]
      ring
    simp_all only [not_false_eq_true, Order.lt_add_one_iff, dite_eq_ite, ite_self]
private lemma summable_nat_pow_mul_pow_div_factorial_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)) := by
  let f : ℕ → ℝ := fun n => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)
  rw [← @summable_nat_add_iff ℝ _ _ _ _ m]
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ))) ?_ ?_ ?_
  · intro n
    positivity
  · intro n
    have hdesc_nat : (n + 1) ^ m ≤ (n + m).descFactorial m := by
      simpa only [Nat.add_comm, Nat.add_assoc, add_tsub_cancel_left, Nat.add_left_comm] using
        (Nat.pow_sub_le_descFactorial (n + m) m)
    have hpow_real :
        ((n + m + 1 : ℝ) ^ m) ≤
          (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by
      have hdesc : ((n + 1 : ℝ) ^ m) ≤ (((n + m).descFactorial m : ℕ) : ℝ) := by
        exact_mod_cast hdesc_nat
      calc
        ((n + m + 1 : ℝ) ^ m) ≤ (((m + 1 : ℝ) * (n + 1)) ^ m) := by
          gcongr
          nlinarith only []
        _ = (m + 1 : ℝ) ^ m * (n + 1 : ℝ) ^ m := by rw [mul_pow]
        _ ≤ (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by gcongr
    have hfact :
        (Nat.factorial n : ℝ) * (((n + m).descFactorial m : ℕ) : ℝ) =
          (Nat.factorial (n + m) : ℝ) := by
      have hfact_nat : (n.factorial * (n + m).descFactorial m) = (n + m).factorial := by
        simpa only [Nat.add_comm, add_tsub_cancel_left, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.factorial_mul_descFactorial (show m ≤ n + m by omega))
      exact_mod_cast hfact_nat
    have hcalc :
        (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) * x ^ (n + m)) /
            (Nat.factorial (n + m) : ℝ)
          = ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := by
      rw [pow_add, ← hfact]
      have hnfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hndesc_nat : (n + m).descFactorial m ≠ 0 :=
        Nat.ne_of_gt (Nat.descFactorial_pos.mpr (show m ≤ n + m by omega))
      have hndesc : (((n + m).descFactorial m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hndesc_nat
      field_simp [hnfact, hndesc]
    calc
      f (n + m)
          = ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) / (Nat.factorial (n + m) : ℝ) := by simp [f]
      _ ≤ (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) * x ^ (n + m)) /
            (Nat.factorial (n + m) : ℝ) := by
              have hpowx :
                  ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                    ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                      x ^ (n + m) := mul_le_mul_of_nonneg_right hpow_real (pow_nonneg hx _)
              have hfacpos : 0 < (Nat.factorial (n + m) : ℝ) := by positivity
              rw [div_le_iff₀ hfacpos]
              calc
                ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                    ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                      x ^ (n + m) := hpowx
                _ =
                    ((((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) *
                        x ^ (n + m)) / (Nat.factorial (n + m) : ℝ)) *
                      (Nat.factorial (n + m) : ℝ) := by
                        have hfacne : (Nat.factorial (n + m) : ℝ) ≠ 0 := by positivity
                        field_simp [hfacne]
      _ = ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := hcalc
  · simpa only [mul_comm, mul_left_comm, pow_add, mul_assoc] using
      (Real.summable_pow_div_factorial x).mul_left ((m + 1 : ℝ) ^ m * x ^ m)
private lemma factorial_ratio_le_pow_succ {n k j : ℕ} (hjn : j ≤ n) (hjk : j ≤ k) :
    (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) ≤ (n + 1 : ℝ) ^ k := by
  have hnat : n.descFactorial j ≤ (n + 1) ^ k := by
    calc
      n.descFactorial j ≤ n ^ j := Nat.descFactorial_le_pow _ _
      _ ≤ (n + 1) ^ j := Nat.pow_le_pow_left n.le_succ _
      _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (Nat.succ_pos _) hjk
  have hdiv_nat : n.descFactorial j = n.factorial / (n - j).factorial := by
    rw [Nat.descFactorial_eq_div hjn]
  have hdiv : (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) = n.descFactorial j := by
    rw [hdiv_nat, Nat.cast_div (Nat.factorial_dvd_factorial (Nat.sub_le n j))]
    positivity
  rw [hdiv]
  exact_mod_cast hnat
private lemma choose_partial_sum_le_pow_two (k n : ℕ) :
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ)) ≤ (2 : ℝ) ^ k := by
  calc
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ))
      ≤ Finset.sum (Finset.range (k + 1)) (fun j => (Nat.choose k j : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · simp_all only [range_subset_range, add_le_add_iff_right, min_le_iff, Std.le_refl,
              true_or]
          · simp_all only [mem_range, Order.lt_add_one_iff, le_inf_iff, true_and, not_le,
              Nat.cast_nonneg, implies_true]
    _ = (2 : ℝ) ^ k := by exact_mod_cast Nat.sum_range_choose k
private lemma phi_norm_le_majorant {k n : ℕ} {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖Phi k n z‖ ≤ ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
      Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
  let S := Finset.range (min k n + 1)
  let term : ℕ → ℂ := fun j =>
    (-1 : ℂ) ^ j * ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
      z ^ (n - j) * star z ^ (k - j)
  let common : ℝ := ((n + 1 : ℝ) ^ k) * R ^ k * R ^ n
  rw [phi_explicit]
  have hsum_norm : ‖Finset.sum S term‖ ≤ Finset.sum S (fun j => ‖term j‖) := norm_sum_le _ _
  have hterm_bound : ∀ j ∈ S, ‖term j‖ ≤ (Nat.choose k j : ℝ) * common := by
    intro j hj
    have hjk : j ≤ k := by
      simp [S] at hj
      omega
    have hjn : j ≤ n := by
      simp [S] at hj
      omega
    have hratio := factorial_ratio_le_pow_succ hjn hjk
    have hz1 : ‖z‖ ^ (n - j) ≤ R ^ n := by
      calc
        ‖z‖ ^ (n - j) ≤ R ^ (n - j) := by exact pow_le_pow_left₀ (norm_nonneg _) hz _
        _ ≤ R ^ n := by exact pow_le_pow_right₀ hR (Nat.sub_le _ _)
    have hz2 : ‖z‖ ^ (k - j) ≤ R ^ k := by
      calc
        ‖z‖ ^ (k - j) ≤ R ^ (k - j) := by exact pow_le_pow_left₀ (norm_nonneg _) hz _
        _ ≤ R ^ k := by exact pow_le_pow_right₀ hR (Nat.sub_le _ _)
    calc
      ‖term j‖
        = (Nat.choose k j : ℝ) * ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
            ‖z‖ ^ (n - j) * ‖z‖ ^ (k - j) := by
            dsimp [term]
            simp [norm_pow]
      _ ≤ (Nat.choose k j : ℝ) * ((n + 1 : ℝ) ^ k) * R ^ n * R ^ k := by gcongr
      _ = (Nat.choose k j : ℝ) * common := by
            dsimp [common]
            ac_rfl
  have hsum_bound :
      Finset.sum S (fun j => ‖term j‖) ≤ Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) :=
    Finset.sum_le_sum (fun j hj => hterm_bound j hj)
  have hsum_factor :
      Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) =
        (Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common := by rw [Finset.sum_mul]
  have hfront_nonneg :
      0 ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ := norm_nonneg _
  have hfront :
      ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ =
        ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) := by
    rw [one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      one_div]
  calc
    ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) * Finset.sum S term‖
      ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
          Finset.sum S (fun j => ‖term j‖) := by
            exact le_trans (norm_mul_le _ _) <|
              mul_le_mul_of_nonneg_left hsum_norm (norm_nonneg _)
    _ ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
          Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) :=
            mul_le_mul_of_nonneg_left hsum_bound hfront_nonneg
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) := by rw [hfront]
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          ((Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common) := by rw [hsum_factor]
    _ ≤ ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
          (((2 : ℝ) ^ k) * common) := by
            gcongr
            exact choose_partial_sum_le_pow_two k n
    _ = ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by
            dsimp [common]
            rw [div_eq_mul_inv]
            ring
private lemma truncate_tendsto_pointwise {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) (z : ℂ) :
    Filter.Tendsto (fun J => truncate k J G z) Filter.atTop (nhds (G z)) := by
  have hH := hG.2 z
  -- hH : HasSum (fun n => hermiteCoeff k G n * Phi k n z) (G z)
  -- HasSum means Tendsto of partial sums over Finsets
  -- We need the sequential version through range(J+1)
  have hseq : Filter.Tendsto
      (fun J => ∑ n ∈ Finset.range J, hermiteCoeff k G n * Phi k n z)
      Filter.atTop (nhds (G z)) :=
    hH.tendsto_sum_nat
  -- truncate k J G z = ∑ n : Fin (J+1), hermiteCoeff k G n.1 * Phi k n.1 z
  -- = ∑ n ∈ range(J+1), hermiteCoeff k G n * Phi k n z
  change Filter.Tendsto (fun J =>
    ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * Phi k n.1 z) Filter.atTop (nhds (G z))
  have hrw : (fun J => ∑ n : Fin (J + 1), hermiteCoeff k G n.1 * Phi k n.1 z) =
      (fun J => ∑ n ∈ Finset.range (J + 1), hermiteCoeff k G n * Phi k n z) := by
    ext J; rw [Finset.sum_range]
  rw [hrw]
  exact hseq.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
private theorem aestronglyMeasurable_of_mem_Hk {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) :
    AEStronglyMeasurable G volume := by
  apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop) (f := fun J => truncate k J G)
  · exact fun J => (continuous_finiteHermiteSum k _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => truncate_tendsto_pointwise hG z)
private lemma integrable_Phi_conj_G_exp {k : ℕ} {G : ℂ → ℂ} (n : ℕ)
    (hG : G ∈ Hk k)
    (hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) :
    Integrable (fun z : ℂ =>
      Phi k n z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  -- Bound: ‖Phi_n * conj G * exp‖ ≤ (‖Phi_n‖² + ‖G‖²) * exp
  -- Both ‖Phi_n‖² exp and ‖G‖² exp are integrable.
  have hDiag := integrable_weightedDiag k n
  have hBound : Integrable (fun z : ℂ =>
      (‖Phi k n z‖ ^ 2 + ‖G z‖ ^ 2) * rexp (-‖z‖ ^ 2)) := by
    have : (fun z : ℂ => (‖Phi k n z‖ ^ 2 + ‖G z‖ ^ 2) * rexp (-‖z‖ ^ 2)) =
        (fun z => ‖Phi k n z‖ ^ 2 * rexp (-‖z‖ ^ 2) + ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2)) := by ext z; ring
    rw [this]; exact hDiag.add hInt
  apply MeasureTheory.Integrable.mono' hBound
  · have hG_aesm : AEStronglyMeasurable G volume := aestronglyMeasurable_of_mem_Hk hG
    exact (((continuous_Phi k n).aestronglyMeasurable.mul
      (hG_aesm.star)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_neg.comp ((continuous_pow 2).comp
          continuous_norm)))).aestronglyMeasurable)
  · filter_upwards with z
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (exp_nonneg _)]
    nlinarith only [sq_nonneg (‖Phi k n z‖ - ‖G z‖), exp_nonneg (-‖z‖ ^ 2 : ℝ)]
private theorem gaussianWeight_nonneg (z : ℂ) : 0 ≤ gaussianWeight z := by
  unfold gaussianWeight
  positivity
private theorem gaussianWeight_sq (z : ℂ) :
    gaussianWeight z ^ 2 = (1 / Real.pi) * Real.exp (-‖z‖ ^ 2) := by
  unfold gaussianWeight
  have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have hsqrt : Real.sqrt Real.pi ^ 2 = Real.pi := by rw [Real.sq_sqrt hpi]
  have hexp :
      Real.exp (-(‖z‖ ^ 2) / 2) ^ 2 = Real.exp (-‖z‖ ^ 2) := by
    calc
      Real.exp (-(‖z‖ ^ 2) / 2) ^ 2
          = Real.exp (-(‖z‖ ^ 2) / 2) * Real.exp (-(‖z‖ ^ 2) / 2) := by ring
      _ = Real.exp (-(‖z‖ ^ 2) / 2 + -(‖z‖ ^ 2) / 2) := by rw [← Real.exp_add]
      _ = Real.exp (-‖z‖ ^ 2) := by congr 1; ring
  rw [div_pow, hexp, hsqrt]
  field_simp [Real.pi_ne_zero]
private theorem continuous_gaussianWeight : Continuous gaussianWeight := by
  unfold gaussianWeight
  exact
    (Real.continuous_exp.comp
      ((continuous_neg.comp (continuous_norm.pow 2)).div_const 2)).div_const _
private theorem aestronglyMeasurable_gaussianScale
    {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (gaussianScale F) volume :=
  (Complex.continuous_ofReal.comp continuous_gaussianWeight).aestronglyMeasurable.mul hF
private theorem weightedNormSq_eq_integral_sq_norm_gaussianScale
    (G : ℂ → ℂ) :
    weightedNormSq G = ∫ z : ℂ, ‖gaussianScale G z‖ ^ 2 := by
  unfold weightedNormSq HermiteLEAN.weightedNormSq
  have hEq :
      (fun z : ℂ => ‖gaussianScale G z‖ ^ 2) =
        fun z : ℂ => (1 / Real.pi) * (‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
    funext z
    rw [show ‖gaussianScale G z‖ ^ 2 =
        gaussianWeight z ^ 2 * ‖G z‖ ^ 2 by
          unfold gaussianScale
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (gaussianWeight_nonneg z)]
          ring]
    rw [gaussianWeight_sq]
    ac_rfl
  rw [hEq, MeasureTheory.integral_const_mul]
private theorem memLp_two_gaussianScale_of_integrable
    {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F volume)
    (hInt : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    MeasureTheory.MemLp (gaussianScale F) 2 volume := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm ?_).2 ?_
  · exact aestronglyMeasurable_gaussianScale hF
  · refine hInt.const_mul (1 / Real.pi) |>.congr ?_
    filter_upwards with z
    rw [show ‖gaussianScale F z‖ ^ 2 =
        gaussianWeight z ^ 2 * ‖F z‖ ^ 2 by
          unfold gaussianScale
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (gaussianWeight_nonneg z)]
          ring]
    rw [gaussianWeight_sq]
    ac_rfl
private theorem integrable_of_memLp_two_gaussianScale
    {F : ℂ → ℂ} (hF : MeasureTheory.MemLp (gaussianScale F) 2 volume) :
    Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
  have hint := (MeasureTheory.memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  refine (hint.const_mul Real.pi).congr ?_
  filter_upwards with z
  simp only [gaussianScale, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussianWeight_nonneg z), mul_pow, gaussianWeight_sq]
  field_simp [Real.pi_ne_zero]
private theorem integrable_weighted_square_sub
    {F G : ℂ → ℂ} (hF : AEStronglyMeasurable F volume)
    (hG : AEStronglyMeasurable G volume)
    (hIntF : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)))
    (hIntG : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    Integrable (fun z : ℂ => ‖F z - G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
  have hscale : gaussianScale (fun z => F z - G z) = gaussianScale F - gaussianScale G := by
    funext z
    exact mul_sub _ _ _
  apply integrable_of_memLp_two_gaussianScale
  rw [hscale]
  exact (memLp_two_gaussianScale_of_integrable hF hIntF).sub
    (memLp_two_gaussianScale_of_integrable hG hIntG)
private theorem weightedNorm_eq_lpNorm_gaussianScale
    {F : ℂ → ℂ}
    (hF : AEStronglyMeasurable F volume)
    (_hInt : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    weightedNorm F = MeasureTheory.lpNorm (gaussianScale F) 2 volume := by
  have hmeas : AEStronglyMeasurable (gaussianScale F) volume :=
    aestronglyMeasurable_gaussianScale hF
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := volume) (p := (2 : NNReal)) (f := gaussianScale F) htwo hmeas
  change weightedNorm F = MeasureTheory.lpNorm (gaussianScale F) (↑(2 : NNReal)) volume
  rw [hlp]
  change weightedNorm F = (∫ z : ℂ, ‖gaussianScale F z‖ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)
  have hsq :
      (∫ z : ℂ, ‖gaussianScale F z‖ ^ (2 : ℝ)) = weightedNormSq F := by
    simpa only [rpow_ofNat] using (weightedNormSq_eq_integral_sq_norm_gaussianScale F).symm
  rw [hsq]
  unfold weightedNorm HermiteLEAN.weightedNorm
  rw [Real.sqrt_eq_rpow]
  norm_num
private theorem weightedInner_eq_l2Inner
    (F G : ℂ → ℂ)
    (hF : MeasureTheory.MemLp (gaussianScale F) 2 volume)
    (hG : MeasureTheory.MemLp (gaussianScale G) 2 volume) :
    weightedInner F G = @inner ℂ _ _ (hG.toLp (gaussianScale G)) (hF.toLp (gaussianScale F)) := by
  let FLp : MeasureTheory.Lp ℂ 2 volume := hF.toLp (gaussianScale F)
  let GLp : MeasureTheory.Lp ℂ 2 volume := hG.toLp (gaussianScale G)
  have hEq :
      (fun z : ℂ => inner ℂ (GLp z) (FLp z)) =ᵐ[volume]
        (fun z : ℂ =>
          ((1 / Real.pi : ℂ) *
            (F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ)))) := by
    filter_upwards [hG.coeFn_toLp, hF.coeFn_toLp] with z hzG hzF
    rw [hzG, hzF, RCLike.inner_apply']
    unfold gaussianScale
    have hgw :
        (((gaussianWeight z : ℝ) : ℂ) * ((gaussianWeight z : ℝ) : ℂ)) =
          (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
      have hsq := gaussianWeight_sq z
      rw [sq] at hsq
      exact_mod_cast hsq
    rw [show (starRingEnd ℂ) (↑(gaussianWeight z) * G z) * (↑(gaussianWeight z) * F z) =
      ↑(gaussianWeight z) * ↑(gaussianWeight z) * (F z * (starRingEnd ℂ) (G z)) from by
        simp [map_mul]
        ring, hgw]
    push_cast
    ac_rfl
  calc
    weightedInner F G
        = ∫ z : ℂ, ((1 / Real.pi : ℂ) *
            (F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ))) := by
              unfold weightedInner HermiteLEAN.weightedInner
              exact
                (MeasureTheory.integral_const_mul
                  (r := (1 / Real.pi : ℂ))
                  (f := fun z : ℂ =>
                    F z * (starRingEnd ℂ) (G z) * (Real.exp (-‖z‖ ^ 2) : ℂ))).symm
    _ = ∫ z : ℂ, inner ℂ (GLp z) (FLp z) := by
          symm
          exact integral_congr_ae hEq
    _ = @inner ℂ _ _ GLp FLp := by
          exact
            (MeasureTheory.L2.inner_def (𝕜 := ℂ) GLp FLp).symm
private theorem weightedInner_norm_le_of_integrable
    {F G : ℂ → ℂ}
    (hFmeas : AEStronglyMeasurable F volume)
    (hGmeas : AEStronglyMeasurable G volume)
    (hFint : Integrable (fun z : ℂ => ‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)))
    (hGint : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * Real.exp (-‖z‖ ^ 2))) :
    ‖weightedInner F G‖ ≤ weightedNorm F * weightedNorm G := by
  let hFmem := memLp_two_gaussianScale_of_integrable hFmeas hFint
  let hGmem := memLp_two_gaussianScale_of_integrable hGmeas hGint
  calc
    ‖weightedInner F G‖
        = ‖@inner ℂ _ _ (hGmem.toLp (gaussianScale G)) (hFmem.toLp (gaussianScale F))‖ := by
            rw [weightedInner_eq_l2Inner F G hFmem hGmem]
    _ ≤ ‖hGmem.toLp (gaussianScale G)‖ * ‖hFmem.toLp (gaussianScale F)‖ := norm_inner_le_norm _ _
    _ = MeasureTheory.lpNorm (gaussianScale G) 2 volume *
          MeasureTheory.lpNorm (gaussianScale F) 2 volume := by
            rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp,
              ← MeasureTheory.toReal_eLpNorm hGmem.aestronglyMeasurable,
              ← MeasureTheory.toReal_eLpNorm hFmem.aestronglyMeasurable]
    _ = weightedNorm G * weightedNorm F := by
          rw [← weightedNorm_eq_lpNorm_gaussianScale hGmeas hGint,
            ← weightedNorm_eq_lpNorm_gaussianScale hFmeas hFint]
    _ = weightedNorm F * weightedNorm G := by ring
private lemma bessel_truncate_le {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k)
    (hInt : Integrable (fun z : ℂ => ‖G z‖ ^ 2 * rexp (-‖z‖ ^ 2))) (J : ℕ) :
    weightedNormSq (truncate k J G) ≤ weightedNormSq G := by
  -- Step 1: ⟨trunc, G⟩ expanded via finite sum in first argument
  set a := fun n : Fin (J + 1) => hermiteCoeff k G n.1
  -- Each cross integral is integrable:
  have hCross : ∀ m : Fin (J + 1),
      Integrable (fun z : ℂ => (a m * Phi k m.1 z) * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
    intro m
    have h1 := integrable_Phi_conj_G_exp (k := k) m.1 hG hInt
    have heq : (fun z : ℂ => (a m * Phi k m.1 z) * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ)) =
      (fun z : ℂ => a m * (Phi k m.1 z * (starRingEnd ℂ) (G z) *
        (Real.exp (-‖z‖ ^ 2) : ℂ))) := by ext z; ring
    rw [heq]; exact h1.const_mul _
  -- ⟨truncate_J G, G⟩ via finite sum expansion
  have hInnerTG : weightedInner (truncate k J G) G =
      ∑ n : Fin (J + 1), a n * (starRingEnd ℂ) (hermiteCoeff k G n.1) := by
    change weightedInner (finiteHermiteSum k a) G = _
    unfold finiteHermiteSum
    rw [weightedInner_finset_sum_left Finset.univ (fun m => fun z => a m * Phi k m.1 z) G
        (fun m _ => hCross m)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    -- ⟨c * Phi_n, G⟩ = c * conj(⟨G, Phi_n⟩)
    have h1 : weightedInner (fun z => a n * Phi k n.1 z) G =
        a n * weightedInner (Phi k n.1) G := by
      unfold weightedInner HermiteLEAN.weightedInner
      conv_lhs => rw [show (fun z : ℂ => a n * Phi k (↑n) z *
          (starRingEnd ℂ) (G z) * ↑(rexp (-‖z‖ ^ 2))) =
        (fun z => a n * (Phi k (↑n) z * (starRingEnd ℂ) (G z) *
          ↑(rexp (-‖z‖ ^ 2)))) from by ext z; ring]
      rw [show (∫ z : ℂ, a n * (Phi k (↑n) z * (starRingEnd ℂ) (G z) *
          ↑(rexp (-‖z‖ ^ 2)))) = a n * (∫ z : ℂ, (Phi k (↑n) z *
          (starRingEnd ℂ) (G z) * ↑(rexp (-‖z‖ ^ 2)))) from
        MeasureTheory.integral_const_mul _ _]
      ac_rfl
    rw [h1]
    have h2 : weightedInner (Phi k n.1) G =
        (starRingEnd ℂ) (weightedInner G (Phi k n.1)) :=
      weightedInner_conj_symm (Phi k n.1) G
    rw [h2]; rfl
  -- Simplify: a n * conj(a n) = ‖a n‖² (as complex)
  have hInnerTG' : weightedInner (truncate k J G) G =
      (∑ n : Fin (J + 1), ‖a n‖ ^ 2 : ℝ) := by
    rw [hInnerTG]; push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [a]
    rw [show hermiteCoeff k G ↑n * (starRingEnd ℂ) (hermiteCoeff k G ↑n) =
        ((‖hermiteCoeff k G ↑n‖ ^ 2 : ℝ) : ℂ) from by
      simpa only [ofReal_pow] using Complex.mul_conj' (hermiteCoeff k G ↑n)]; push_cast; ring
  -- Also: ⟨truncate, truncate⟩ = ∑ ‖a_n‖²
  have hInnerTT : weightedInner (truncate k J G) (truncate k J G) =
      (∑ n : Fin (J + 1), ‖a n‖ ^ 2 : ℝ) := by
    change weightedInner (finiteHermiteSum k a) (finiteHermiteSum k a) = _
    rw [finiteHermiteSum_inner]; push_cast
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show a n * star (a n) = ((‖a n‖ ^ 2 : ℝ) : ℂ) from by
      simpa only [RCLike.star_def, ofReal_pow] using Complex.mul_conj' (a n)]; push_cast; ring
  -- From the equalities: ⟨trunc, G⟩ = ⟨trunc, trunc⟩ (= ∑ ‖a_n‖²)
  have hCrossZero : weightedInner (truncate k J G) G =
      weightedInner (truncate k J G) (truncate k J G) := by rw [hInnerTG', hInnerTT]
  have hpi_nonneg : 0 ≤ (1 / Real.pi : ℝ) := by
    rw [one_div, inv_nonneg]
    exact Real.pi_pos.le
  have hnonnegative (F : ℂ → ℂ) : 0 ≤ weightedNormSq F := by
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    exact mul_nonneg hpi_nonneg (integral_nonneg fun z =>
      mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
  have hreal : weightedNormSq (truncate k J G) ≤ ‖weightedInner (truncate k J G) G‖ := by
    rw [weightedNormSq_eq_re_weightedInner, ← hCrossZero]
    exact Complex.re_le_norm _
  have hbound := weightedInner_norm_le_of_integrable (F := truncate k J G) (G := G)
    (continuous_finiteHermiteSum k _).aestronglyMeasurable
    (aestronglyMeasurable_of_mem_Hk hG)
    (integrable_truncate_normSq_exp k J G) hInt
  have hT_square : weightedNorm (truncate k J G) ^ 2 = weightedNormSq (truncate k J G) :=
    Real.sq_sqrt (hnonnegative _)
  have hG_square : weightedNorm G ^ 2 = weightedNormSq G := Real.sq_sqrt (hnonnegative _)
  have hT_nonnegative : 0 ≤ weightedNorm (truncate k J G) := Real.sqrt_nonneg _
  by_cases hzero : weightedNorm (truncate k J G) = 0
  · rw [← hT_square, hzero, zero_pow (by decide)]
    exact hnonnegative G
  · have hpositive : 0 < weightedNorm (truncate k J G) :=
      lt_of_le_of_ne hT_nonnegative (Ne.symm hzero)
    have hnorm_le : weightedNorm (truncate k J G) ≤ weightedNorm G :=
      le_of_mul_le_mul_left (by
        simpa only [← hT_square, pow_two] using hreal.trans hbound) hpositive
    rw [← hT_square, ← hG_square]
    exact pow_le_pow_left₀ hT_nonnegative hnorm_le 2
private lemma summable_sq_Phi_eval (k : ℕ) (z : ℂ) :
    Summable (fun n => ‖Phi k n z‖ ^ 2) := by
  let R : ℝ := max 1 ‖z‖
  have hR : 1 ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hzR : ‖z‖ ≤ R := by
    dsimp [R]
    exact le_max_right _ _
  let C : ℝ := (((2 : ℝ) ^ k) ^ 2 * (R ^ k) ^ 2) / (Nat.factorial k : ℝ)
  have hbase0 :
      Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (2 * k)) * (R ^ 2) ^ n / (Nat.factorial n : ℝ)) := by
    apply summable_nat_pow_mul_pow_div_factorial_nonneg
    positivity
  have hbase :
      Summable (fun n : ℕ => (((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
    refine hbase0.congr ?_
    intro n
    rw [← pow_mul, ← pow_mul]
    simp [pow_mul, Nat.mul_comm]
  have hmajorant :
      Summable (fun n : ℕ => C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)))
          := hbase.mul_left C
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_ hmajorant
  intro n
  have hphi := phi_norm_le_majorant (k := k) (n := n) (R := R) hR hzR
  have hrhs_nonneg :
      0 ≤ ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
        Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) := by positivity
  have hphi_sq :
      ‖Phi k n z‖ ^ 2 ≤
        (((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hphi 2
  have hsqrt_ne : Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) ≠ 0 := by positivity
  calc
    ‖Phi k n z‖ ^ 2
      ≤ (((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
          Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) ^ 2 := hphi_sq
    _ = C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
      dsimp [C]
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (by positivity)]
private lemma summable_sq_qkn (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (fun n => |qkn k n r| ^ 2) := by
  let t0 : Circle := QuotientAddGroup.mk 0
  let c : ℝ := ‖circleLeadingFactor k r‖ ^ 2
  have hc_ne : c ≠ 0 := by
    dsimp [c, circleLeadingFactor]
    rw [sq_eq_zero_iff, norm_eq_zero, Complex.ofReal_eq_zero]
    exact div_ne_zero (pow_ne_zero k (ne_of_gt hr))
      (by positivity : Real.sqrt ((Nat.factorial k : ℕ) : ℝ) ≠ 0)
  have hphi_sq :
      ∀ n : ℕ,
        ‖Phi k n (circlePoint r t0)‖ ^ 2 = c * |qkn k n r| ^ 2 := by
    intro n
    have hphi := phi_polar (k := k) (n := n) (r := r) hr t0
    have hfourk : ‖(fourier (-(k : ℤ)) t0 : ℂ)‖ ^ 2 = 1 := by simp [t0]
    have hfourn : ‖(fourier (n : ℤ) t0 : ℂ)‖ ^ 2 = 1 := by simp [t0]
    rw [hphi, norm_mul, norm_mul, mul_pow, mul_pow, hfourk,
      norm_mul, mul_pow, hfourn,
      Complex.norm_real, Real.norm_eq_abs,
      show ‖circleLeadingFactor k r‖ ^ 2 = c by rfl]
    ac_rfl
  have hsPhi := summable_sq_Phi_eval k (circlePoint r t0)
  have hsScaled : Summable (fun n => c⁻¹ * (‖Phi k n (circlePoint r t0)‖ ^ 2)) := hsPhi.mul_left c⁻¹
  simp_all only [ne_eq, sq_abs, not_false_eq_true, inv_mul_cancel_left₀]
private lemma sum_range_sq_hermiteCoeff_le {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) :
    ∀ J, ∑ n ∈ Finset.range J, ‖hermiteCoeff k G n‖ ^ 2 ≤ weightedNormSq G := by
  intro J
  by_cases hJ : J = 0
  · subst hJ
    simp only [Finset.range_zero, Finset.sum_empty]
    unfold weightedNormSq HermiteLEAN.weightedNormSq
    positivity
  · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
    rw [show ∑ n ∈ Finset.range (J' + 1), ‖hermiteCoeff k G n‖ ^ 2 =
        ∑ n : Fin (J' + 1), ‖hermiteCoeff k G n.1‖ ^ 2 by rw [Finset.sum_range]]
    rw [← truncate_normSq k J' G]
    exact bessel_truncate_le hG hG.1 J'
private lemma summable_sq_hermiteCoeff {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) :
    Summable (fun n => ‖hermiteCoeff k G n‖ ^ 2) :=
  summable_of_sum_range_le (fun _ => sq_nonneg _) (sum_range_sq_hermiteCoeff_le hG)
private lemma summable_circleCoeff_norm {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) {r : ℝ}
    (hr : 0 < r) :
    Summable (fun n => ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖) := by
  have hcoeff := summable_sq_hermiteCoeff hG
  have hqkn := summable_sq_qkn k hr
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ ((hcoeff.add hqkn).div_const 2)
  intro n
  have hmul :
      ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ ≤
        ‖hermiteCoeff k G n‖ * |qkn k n r| := by simp [Complex.norm_real, Real.norm_eq_abs]
  have hAMGM :
      ‖hermiteCoeff k G n‖ * |qkn k n r| ≤
        (‖hermiteCoeff k G n‖ ^ 2 + |qkn k n r| ^ 2) / 2 := by
    linarith only [sq_nonneg (‖hermiteCoeff k G n‖ - |qkn k n r|)]
  exact hmul.trans hAMGM
private lemma summable_circleCoeff_sq {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) {r : ℝ}
    (hr : 0 < r) :
    Summable (fun n => ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖ ^ 2) := by
  let d : ℕ → ℝ := fun n => ‖hermiteCoeff k G n * (qkn k n r : ℂ)‖
  have hd : Summable d := summable_circleCoeff_norm hG hr
  let M : ℝ := ∑' n : ℕ, d n
  have hM_nonneg : 0 ≤ M := tsum_nonneg fun n => norm_nonneg _
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg (d n)) ?_ (hd.mul_left M)
  intro n
  have hd_le : d n ≤ M := by
    have hsingle :=
      hd.sum_le_tsum ({n} : Finset ℕ) (fun _ _ => norm_nonneg _)
    simpa only [Complex.norm_mul, norm_real, norm_eq_abs, ge_iff_le, sum_singleton, M, d] using
      hsingle
  have hd_nonneg : 0 ≤ d n := norm_nonneg _
  have hmul : d n * d n ≤ M * d n := mul_le_mul_of_nonneg_right hd_le hd_nonneg
  simpa only [Complex.norm_mul, norm_real, norm_eq_abs, pow_two, ge_iff_le, d] using hmul
private theorem norm_toLp_sq (F : C(Circle, ℂ)) :
    ‖ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F‖ ^ 2 = circleL2Sq F := by
  let f := ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F
  have h := congrArg RCLike.re (@MeasureTheory.L2.inner_def Circle ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re] at h
  · simp only [← norm_sq_eq_re_inner] at h
    refine h.trans ?_
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2)
      (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) F] with t ht
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) ht
  · exact MeasureTheory.L2.integrable_inner f f
private theorem summable_circle_continuous (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    Summable (fun n : ℕ => c n • fourier (T := T) (n : ℤ)) := by
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm, mul_one] using hc
private theorem circleL2Sq_tendsto_partial_fourier_sums
    (c : ℕ → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    Filter.Tendsto
      (fun J : ℕ => circleL2Sq (fun t : Circle =>
        ∑ n : Fin (J + 1), c n.1 * fourier (n.1 : ℤ) t))
      Filter.atTop (nhds (circleL2Sq (fun t : Circle => ∑' n : ℕ, c n * fourier (n : ℤ) t))) := by
  let F : ℕ → C(Circle, ℂ) := fun n => c n • fourier (n : ℤ)
  have hF : Summable F := summable_circle_continuous c hc
  have hpartial : Filter.Tendsto (fun J => ∑ n ∈ Finset.range (J + 1), F n)
      Filter.atTop (nhds (∑' n, F n)) :=
    hF.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hLp := ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).continuous.tendsto
    (∑' n, F n)).comp hpartial
  have hnorm := hLp.norm.pow 2
  simp only [Function.comp_apply, norm_toLp_sq] at hnorm
  have hvalue : (fun t : Circle => (∑' n, F n) t) =
      (fun t : Circle => ∑' n : ℕ, c n * fourier (n : ℤ) t) := by
    funext t
    exact ((ContinuousMap.evalCLM ℂ t).hasSum hF.hasSum).tsum_eq.symm
  rw [show circleL2Sq ((∑' n, F n : C(Circle, ℂ)) : Circle → ℂ) =
      circleL2Sq (fun t : Circle => ∑' n : ℕ, c n * fourier (n : ℤ) t) from
    congrArg circleL2Sq hvalue] at hnorm
  convert hnorm using 1
  ext J
  apply congrArg circleL2Sq
  funext t
  simp only [F, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, Finset.sum_range]
private theorem circleSeries_l2_identity_canonical :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ r : ℝ,
          0 < r →
            circleL2Sq (circleSeries k (hermiteCoeff k G) r) =
              ∑' n : ℕ, ‖hermiteCoeff k G n‖ ^ 2 * |qkn k n r| ^ 2 := by
  intro k G hG r hr
  let c : ℕ → ℂ := fun n => hermiteCoeff k G n * (qkn k n r : ℂ)
  have hc_norm : Summable (fun n => ‖c n‖) := by
    simpa only [c, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      summable_circleCoeff_norm (k := k) (G := G) hG hr
  have hc_sq : Summable (fun n => ‖c n‖ ^ 2) := by
    simpa only [c, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow] using
      summable_circleCoeff_sq (k := k) (G := G) hG hr
  have hCircleTendsto :
      Filter.Tendsto (fun J : ℕ => ∑ n : Fin (J + 1), ‖c n.1‖ ^ 2)
        Filter.atTop
        (nhds (circleL2Sq (fun t : Circle => ∑' n : ℕ, c n * fourier (n : ℤ) t))) := by
    simpa only [circleL2Sq_finFourierPoly] using
      circleL2Sq_tendsto_partial_fourier_sums c hc_norm
  have hsum :
      Filter.Tendsto (fun J : ℕ => ∑ n : Fin (J + 1), ‖c n.1‖ ^ 2)
        Filter.atTop (nhds (∑' n : ℕ, ‖c n‖ ^ 2)) := by
    simpa only [Function.comp_def, Finset.sum_range] using
      hc_sq.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  change circleL2Sq (fun t : Circle =>
      ∑' n : ℕ, hermiteCoeff k G n * (qkn k n r : ℂ) * fourier (n : ℤ) t) = _
  simpa only [c, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow] using
    tendsto_nhds_unique hCircleTendsto hsum
private lemma sub_truncate_mem_Hk {k : ℕ} {G : ℂ → ℂ} (hG : G ∈ Hk k) (J : ℕ) :
    (fun z => G z - truncate k J G z) ∈ Hk k := by
  refine ⟨?_, ?_⟩
  · exact integrable_weighted_square_sub (aestronglyMeasurable_of_mem_Hk hG)
      (continuous_finiteHermiteSum k _).aestronglyMeasurable hG.1
      (integrable_truncate_normSq_exp k J G)
  · intro z
    have hGz := hG.2 z
    have hTzH := (truncate_mem_Hk k J G).2 z
    have hcoeff_decomp : ∀ n,
        weightedInner (fun z' => G z' - truncate k J G z') (Phi k n) =
          weightedInner G (Phi k n) - weightedInner (truncate k J G) (Phi k n) := by
      intro n
      have h1 := hermiteCoeff_sub_truncate k J G n
      have h2 := hermiteCoeff_truncate (k := k) (J := J) (G := G) n
      simp only [hermiteCoeff] at h1 h2
      rw [h1]
      by_cases hn : n < J + 1 <;> simp [hn, h2]
    have hterm : ∀ n,
        weightedInner (fun z' => G z' - truncate k J G z') (Phi k n) * Phi k n z =
          weightedInner G (Phi k n) * Phi k n z -
            weightedInner (truncate k J G) (Phi k n) * Phi k n z := by
      intro n
      rw [hcoeff_decomp]
      ring
    simp_rw [hterm]
    exact hGz.sub hTzH
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∀ r : ℝ,
          0 < r →
            ∀ ε : ℝ,
              0 < ε →
                ∃ J0 : ℕ,
                  ∀ J ≥ J0,
                    circleL2Sq
                        (truncCirclePoly k r J G - circleSeries k (hermiteCoeff k G) r) ≤
                      ε := by
  intro k G hG r hr ε hε
  let d : ℕ → ℝ := fun n => ‖hermiteCoeff k G n‖ ^ 2 * |qkn k n r| ^ 2
  have hd : Summable d := by
    refine (summable_circleCoeff_sq hG hr).congr ?_
    intro n
    dsimp [d]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    ring
  have htail := tendsto_sum_nat_add d
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨J0, hJ0⟩ := htail ε hε
  refine ⟨J0, fun J hJ => ?_⟩
  let HJ : ℂ → ℂ := fun z => G z - truncate k J G z
  have hHJ : HJ ∈ Hk k := sub_truncate_mem_Hk hG J
  have hpoint :
      truncCirclePoly k r J G - circleSeries k (hermiteCoeff k G) r =
        fun t : Circle => -circleSeries k (hermiteCoeff k HJ) r t := by
    ext t
    let c : ℂ := circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ)
    have hc_ne : c ≠ 0 := by
      dsimp [c, circleLeadingFactor]
      apply mul_ne_zero
      · exact Complex.ofReal_ne_zero.mpr <|
          div_ne_zero (pow_ne_zero k (ne_of_gt hr))
            (by positivity : Real.sqrt ((Nat.factorial k : ℕ) : ℝ) ≠ 0)
      · simp_all
    have hGcircle := circle_representation_hermiteCoeff (k := k) (G := G) hG r hr t
    have hTcircle := truncate_circle k J G hr t
    have hHcircle := circle_representation_hermiteCoeff (k := k) (G := HJ) hHJ r hr t
    have hmain :
        c * (circleSeries k (hermiteCoeff k G) r t - truncCirclePoly k r J G t) =
          c * circleSeries k (hermiteCoeff k HJ) r t := by
      calc
        c * (circleSeries k (hermiteCoeff k G) r t - truncCirclePoly k r J G t)
            = c * circleSeries k (hermiteCoeff k G) r t - c * truncCirclePoly k r J G t := by ring
        _ = circleSeries k (hermiteCoeff k G) r t * circleLeadingFactor k r *
              ↑(-↑k • t).toCircle -
              truncCirclePoly k r J G t * circleLeadingFactor k r * ↑(-↑k • t).toCircle := by
              dsimp [c]
              ring
        _ = G (circlePoint r t) - truncate k J G (circlePoint r t) := by
              dsimp [c] at hGcircle hTcircle
              rw [hGcircle, hTcircle]
              ring
        _ = HJ (circlePoint r t) := by rfl
        _ = c * circleSeries k (hermiteCoeff k HJ) r t := by exact hHcircle
    have hcancel :
        circleSeries k (hermiteCoeff k G) r t - truncCirclePoly k r J G t =
          circleSeries k (hermiteCoeff k HJ) r t := mul_left_cancel₀ hc_ne hmain
    calc
      truncCirclePoly k r J G t - circleSeries k (hermiteCoeff k G) r t
          = -(circleSeries k (hermiteCoeff k G) r t - truncCirclePoly k r J G t) := by ring
      _ = -circleSeries k (hermiteCoeff k HJ) r t := by rw [hcancel]
  have hL2eq :
      circleL2Sq (truncCirclePoly k r J G - circleSeries k (hermiteCoeff k G) r) =
        circleL2Sq (circleSeries k (hermiteCoeff k HJ) r) := by
    unfold circleL2Sq
    refine integral_congr_ae ?_
    filter_upwards with t
    have ht := congrFun hpoint t
    simp [ht]
  have hcanon :=
    circleSeries_l2_identity_canonical (k := k) (G := HJ) hHJ r hr
  have hcoeff :
      ∀ n,
        ‖hermiteCoeff k HJ n‖ ^ 2 * |qkn k n r| ^ 2 =
          if n < J + 1 then 0 else d n := by
    intro n
    rw [show hermiteCoeff k HJ n = if n < J + 1 then 0 else hermiteCoeff k G n by
      exact hermiteCoeff_sub_truncate k J G n]
    by_cases hn : n < J + 1
    · simp [hn, d]
    · simp [hn, d]
  have hcanon' :
      circleL2Sq (circleSeries k (hermiteCoeff k HJ) r) =
        ∑' n : ℕ, if n < J + 1 then 0 else d n := by
    simp_all
  have hshift :
      (∑' n : ℕ, if n < J + 1 then 0 else d n) = ∑' n : ℕ, d (n + (J + 1)) := by
    let f : ℕ → ℝ := fun n => if n < J + 1 then 0 else d n
    change ∑' n, f n = ∑' n, d (n + (J + 1))
    have hkey : ∑' c, f (c + (J + 1)) = ∑' c, d (c + (J + 1)) := by
      apply tsum_congr
      intro c
      dsimp [f]
      have hnot : ¬ (c + (J + 1) < J + 1) := by exact Nat.not_lt_of_ge (Nat.le_add_left (J + 1) c)
      rw [if_neg hnot]
    rw [← hkey]
    have hinj : Function.Injective (fun n : ℕ => n + (J + 1)) := by
      intro a b hab
      exact Nat.add_right_cancel hab
    have hsupp : Function.support f ⊆ Set.range (fun n : ℕ => n + (J + 1)) := by
      intro b hb
      simp only [f, Function.mem_support, ne_eq] at hb
      by_cases hlt : b < J + 1
      · simp [hlt] at hb
      · push Not at hlt
        exact ⟨b - (J + 1), show b - (J + 1) + (J + 1) = b from Nat.sub_add_cancel hlt⟩
    exact (Function.Injective.tsum_eq hinj hsupp).symm
  have htail_small :
      ∑' n : ℕ, d (n + (J + 1)) < ε := by
    have hJ1 : J0 ≤ J + 1 := le_trans hJ (Nat.le_succ J)
    have hJtail := hJ0 (J + 1) hJ1
    rw [dist_zero_right] at hJtail
    have hnonneg : 0 ≤ ∑' n : ℕ, d (n + (J + 1)) := by exact tsum_nonneg fun n => by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hJtail
  calc
    circleL2Sq (truncCirclePoly k r J G - circleSeries k (hermiteCoeff k G) r)
        = circleL2Sq (circleSeries k (hermiteCoeff k HJ) r) := hL2eq
    _ = ∑' n : ℕ, if n < J + 1 then 0 else d n := hcanon'
    _ = ∑' n : ℕ, d (n + (J + 1)) := hshift
    _ ≤ ε := le_of_lt htail_small
end HermitekLEAN
