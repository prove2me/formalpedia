-- Prove2me | solution 1 for HermitekLEAN.circleSeries_l2_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:43.857994+00:00
-- url     : https://prove2.me/submissions/f8ad8ddb-6c3e-4cbe-b54e-cfc2ec14bb92

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
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_finiteCirclePoly_l2_identity
attribute [local simp] HermitekLEAN.qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private theorem sum_Icc_eq_sum_Fin {α : Type*} [AddCommMonoid α]
    (N L : ℕ) (hL : 1 ≤ L) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc N (N + L - 1), f n =
      ∑ m : Fin L, f (N + m.val) := by
  symm
  apply Finset.sum_nbij (fun (m : Fin L) => N + m.val)
  · intro m _
    exact Finset.mem_Icc.mpr ⟨Nat.le_add_right N m.val, by omega⟩
  · intro a _ b _ hab
    exact Fin.ext (Nat.add_left_cancel hab)
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    refine ⟨⟨n - N, by omega⟩, Finset.mem_univ _, ?_⟩
    simp_all only [coe_Icc, Set.mem_Icc, and_self, add_tsub_cancel_of_le]
  · simp_all only [mem_univ, imp_self, implies_true]
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
    ∀ {k : ℕ} {G : ℂ → ℂ} {g : ℕ → ℂ},
      G ∈ Hk k →
        G = hermiteSeries k g →
          Summable (fun n => ‖g n‖ ^ 2) →
          ∀ r : ℝ,
            0 < r →
              circleL2Sq (circleSeries k g r) =
                ∑' n : ℕ, ‖g n‖ ^ 2 * |qkn k n r| ^ 2 := by
  intro k G g _hG _hEq hg r hr
  let c : ℕ → ℂ := fun n => g n * (qkn k n r : ℂ)
  have hqkn := summable_sq_qkn k hr
  have hc_norm : Summable (fun n => ‖c n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ ((hg.add hqkn).div_const 2)
    intro n
    have hmul :
        ‖g n * (qkn k n r : ℂ)‖ ≤ ‖g n‖ * |qkn k n r| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
    have hAMGM :
        ‖g n‖ * |qkn k n r| ≤ (‖g n‖ ^ 2 + |qkn k n r| ^ 2) / 2 := by
      linarith only [sq_nonneg (‖g n‖ - |qkn k n r|)]
    exact hmul.trans hAMGM
  have hc_sq : Summable (fun n => ‖c n‖ ^ 2) := by
    let d' : ℕ → ℝ := fun n => ‖c n‖
    have hd' : Summable d' := by simpa [d', c] using hc_norm
    let M' : ℝ := ∑' n : ℕ, d' n
    have hM'_nonneg : 0 ≤ M' := tsum_nonneg fun n => norm_nonneg _
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg (d' n)) ?_ (hd'.mul_left M')
    intro n
    have hd'_le : d' n ≤ M' := by
      have hsingle := hd'.sum_le_tsum ({n} : Finset ℕ) (fun _ _ => norm_nonneg _)
      simpa [M', d'] using hsingle
    have hd'_nonneg : 0 ≤ d' n := norm_nonneg _
    have hmul : d' n * d' n ≤ M' * d' n := mul_le_mul_of_nonneg_right hd'_le hd'_nonneg
    simpa [pow_two, d'] using hmul
  have hpoly_eq :
      ∀ J,
        finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1) =
          fun t : Circle => ∑ n : Fin (J + 1), g n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t := by
    intro J
    let aJ : Fin (J + 1) → ℂ := fun n => g n.1
    ext t
    change
      Finset.sum (Finset.Icc 0 (0 + (J + 1) - 1))
          (fun n => (if h : n < J + 1 then aJ ⟨n, h⟩ * (qkn k n r : ℂ) else 0) * fourier (n : ℤ)
              t) =
        ∑ n : Fin (J + 1), g n.1 * (qkn k n.1 r : ℂ) * fourier (n.1 : ℤ) t
    rw [sum_Icc_eq_sum_Fin 0 (J + 1) (Nat.succ_le_succ (Nat.zero_le J))]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hx' : (x : ℕ) < J + 1 := x.isLt
    simp [aJ, hx']
  have hCircleTendsto :
      Filter.Tendsto
        (fun J => circleL2Sq (finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1)))
        Filter.atTop
        (nhds (circleL2Sq (circleSeries k g r))) := by
    change Filter.Tendsto _ Filter.atTop
      (nhds (circleL2Sq (fun t : Circle => ∑' n : ℕ,
        g n * (qkn k n r : ℂ) * fourier (n : ℤ) t)))
    simpa only [hpoly_eq, c] using
      circleL2Sq_tendsto_partial_fourier_sums c hc_norm
  let d : ℕ → ℝ := fun n => |qkn k n r| ^ 2 * ‖g n‖ ^ 2
  have hd : Summable d := by
    refine hc_sq.congr ?_
    intro n
    dsimp [d, c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hsum_tendsto :
      Filter.Tendsto
        (fun J => ∑ n : Fin (J + 1), d n.1)
        Filter.atTop
        (nhds (∑' n : ℕ, d n)) := by
    have hnat :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range J, d n) Filter.atTop (nhds (∑' n : ℕ, d n)) :=
      (hd.hasSum_iff_tendsto_nat).1 hd.hasSum
    have hshift :
        Filter.Tendsto (fun J => ∑ n ∈ Finset.range (J + 1), d n) Filter.atTop
          (nhds (∑' n : ℕ, d n)) :=
      hnat.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
    simpa [d, Finset.sum_range] using hshift
  have hsum_tendsto' :
      Filter.Tendsto
        (fun J => ∑ n : Fin (J + 1), |qkn k n.1 r| ^ 2 * ‖g n.1‖ ^ 2)
        Filter.atTop
        (nhds (∑' n : ℕ, |qkn k n r| ^ 2 * ‖g n‖ ^ 2)) := by simpa [d] using hsum_tendsto
  have hEqSeq :
      (fun J => circleL2Sq (finiteCirclePoly k r (fun n : Fin (J + 1) => g n.1))) =
        (fun J => ∑ n : Fin (J + 1), |qkn k n.1 r| ^ 2 * ‖g n.1‖ ^ 2) := by
    ext J
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (finiteCirclePoly_l2_identity (k := k) (D := J + 1) (r := r) (a := fun n : Fin (J + 1) => g
          n.1))
  apply tendsto_nhds_unique hCircleTendsto
  rw [hEqSeq]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsum_tendsto'
end HermitekLEAN
