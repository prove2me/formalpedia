-- Prove2me | solution 1 for OAI.StandardMapEntropy.BridgeScalarControl.prefix_dirichlet_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:22:52.648621+00:00
-- url     : https://prove2.me/submissions/c876b46d-7c98-408d-8591-4ab79537febd

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

lemma linearSolution_step (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    linearSolution v a b (n + 2) =
      v (n + 1) * linearSolution v a b (n + 1) - linearSolution v a b n := rfl

lemma linearSolution_decomposition (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    linearSolution v a b n = a * sSolution v n + b * tSolution v n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [sSolution, tSolution]
  | one => simp [sSolution, tSolution]
  | more n h₀ h₁ =>
    rw [linearSolution_step, h₀, h₁]
    dsimp only [sSolution, tSolution] at *
    rw [linearSolution_step, linearSolution_step]
    ring

lemma boundaryValue_unique (v : ℕ → ℝ) (j : ℕ) (hj : tSolution v j ≠ 0)
    (b : ℝ) (hb : linearSolution v 1 b j = 0) : b = boundaryValue v j := by
  rw [linearSolution_decomposition] at hb
  apply (eq_div_iff hj).mpr
  linarith

open scoped Matrix.Norms.Operator

open Filter
open scoped Topology

open Metric

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_PlaneGeometry
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma abs_dot_le_norm_mul (z w : ℂ) : |dot z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have h0 := sq_nonneg (wedge z w)
  have hs : (dot z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma abs_wedge_le_norm_mul (z w : ℂ) : |wedge z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have hs : (wedge z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith [sq_nonneg (dot z w)]
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma wedge_add_left (z w a : ℂ) : wedge (z+w) a = wedge z a + wedge w a := by
  simp [wedge]; ring
lemma wedge_smul_left (t : ℝ) (z w : ℂ) : wedge (t • z) w = t*wedge z w := by
  simp [wedge]; ring
lemma wedge_refl (z : ℂ) : wedge z z = 0 := by dsimp [wedge]; ring
lemma wedge_swap (z w : ℂ) : wedge z w = -wedge w z := by dsimp [wedge]; ring
lemma wedge_sine_triangle (a b c : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    |wedge a c| ≤ |wedge a b|+|wedge b c| := by
  have he : wedge a c = dot b a * wedge b c + wedge b a * wedge (quarterTurn b) c := by
    conv_lhs => rw [unit_expansion b a hb]
    rw [wedge_add_left, wedge_smul_left, wedge_smul_left]
  rw [he]
  calc
    _ ≤ |dot b a| * |wedge b c|+|wedge b a| * |wedge (quarterTurn b) c| := by
      simpa only [abs_mul] using abs_add_le (dot b a * wedge b c) (wedge b a * wedge (quarterTurn b) c)
    _ ≤ |wedge b c|+|wedge b a| := by
      have h1 : |dot b a|≤1 := by simpa [ha,hb] using abs_dot_le_norm_mul b a
      have h2 : |wedge (quarterTurn b) c|≤1 := by simpa [norm_quarterTurn,hb,hc] using abs_wedge_le_norm_mul (quarterTurn b) c
      nlinarith [abs_nonneg (wedge b c), abs_nonneg (wedge b a)]
    _ = _ := by rw [wedge_swap b a, abs_neg]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_PlaneTransfer
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma dot_quarterTurn_right (a z : ℂ) : dot a (quarterTurn z) = -wedge a z := by
  simp [dot,wedge,quarterTurn]; ring
lemma expanded_projection_bound {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A‖*|dot a z| ≤ ‖A z‖ := by
  have hs := h.norm_map_sq a ha hA z
  have hnon := mul_nonneg (sq_nonneg (wedge a z)) (sq_nonneg (‖A‖⁻¹))
  have hsq : (‖A‖*|dot a z|)^2≤‖A z‖^2 := by nlinarith [sq_abs (dot a z)]
  exact (sq_le_sq₀ (mul_nonneg (norm_nonneg A) (abs_nonneg _)) (norm_nonneg _)).mp hsq
lemma two_singular_upper {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A z‖ ≤ ‖A‖*|dot a z| + ‖A‖⁻¹*|wedge a z| := by
  have hd := orthogonal_image_of_max A a ha hA
  have hs := h.norm_map_sq a ha hA (quarterTurn a)
  rw [dot_quarterTurn,wedge_quarterTurn,ha] at hs
  have hb : ‖A (quarterTurn a)‖=‖A‖⁻¹ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))).mp
    simpa using hs
  conv_lhs => rw [unit_expansion a z ha]
  rw [map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(dot a z : ℝ) • A a‖+‖(wedge a z : ℝ) • A (quarterTurn a)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hA,hb]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TransferCore
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma transferStepInv_norm (v : ℝ) : ‖transferStepInv v‖ ≤ |v|+1 := by
  rw [← (transferStep_area v).norm_inverse (transferStepInv_area v) (transferStep_inv v) (transferStepInv_inv v)]
  exact transferStep_norm v

lemma transferProduct_pair (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    transferProduct v n ⟨b,a⟩ = ⟨linearSolution v a b (n+1),linearSolution v a b n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [transferProduct,ContinuousLinearMap.comp_apply,ih]
    apply Complex.ext <;> simp only [transferStep_re,transferStep_im,linearSolution_step]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeLinear
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma wedge_quarterTurn_both (a b : ℂ) : wedge (quarterTurn a) (quarterTurn b)=wedge a b := by
  simp [wedge,quarterTurn]
  ring
lemma wedge_chain_bound (s : ℕ → ℂ) (e : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hu : ∀ i, a ≤ i → i ≤ b → ‖s i‖=1)
    (he : ∀ i, a ≤ i → i < b → |wedge (s i) (s (i+1))| ≤ e i) :
    |wedge (s a) (s b)| ≤ ∑ i ∈ Finset.Ico a b, e i := by
  induction b,hab using Nat.le_induction with
  | base => simp [wedge_refl]
  | succ b hab ih =>
    have hh:=ih (fun i hai hib => hu i hai (by omega)) (fun i hai hib => he i hai (by omega))
    have ht:=wedge_sine_triangle (s a) (s b) (s (b+1)) (hu a le_rfl (by omega))
      (hu b hab (by omega)) (hu (b+1) (by omega) le_rfl)
    rw [Finset.sum_Ico_succ_top hab]
    exact ht.trans (add_le_add hh (he b hab (by omega)))

lemma stable_direction_step {A B : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A)
    (a b : ℂ) (ha : ‖a‖=1) (_hb : ‖b‖=1)
    (hAa : ‖A a‖=‖A‖) (hBb : ‖B (quarterTurn b)‖=‖B‖⁻¹)
    (M : ℝ) (hB : 0 < ‖B‖) (hstep : ∀ z, ‖A z‖ ≤ M*‖B z‖) :
    |wedge (quarterTurn a) (quarterTurn b)| ≤ M/(‖A‖*‖B‖) := by
  have hpos : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2
  have hp:=expanded_projection_bound hA a ha hAa (quarterTurn b)
  rw [dot_quarterTurn_right] at hp
  have hs:=hstep (quarterTurn b)
  rw [hBb] at hs
  rw [wedge_quarterTurn_both]
  apply (le_div_iff₀ (mul_pos hpos hB)).mpr
  rw [abs_neg] at hp
  have hh := mul_le_mul_of_nonneg_right (hp.trans hs) hB.le
  calc
    _ = (‖A‖*|wedge a b|)*‖B‖ := by ring
    _  ≤  (M*‖B‖⁻¹)*‖B‖ := hh
    _ = M := by field_simp

lemma stable_prefix_finite_bound (A : ℕ → ℂ →L[ℝ] ℂ) (a : ℕ → ℂ)
    (D : ℕ → ℝ) (M : ℝ) (l B : ℕ) (hl : 1 ≤ l) (hlB : l ≤ B)
    (harea : ∀ i, 1 ≤ i → i ≤ B → PlaneAreaPreserving (A i))
    (hunit : ∀ i, 1 ≤ i → i ≤ B → ‖a i‖=1)
    (hnorm : ∀ i, 1 ≤ i → i ≤ B → ‖A i‖=D i)
    (hmax : ∀ i, 1 ≤ i → i ≤ B → ‖A i (a i)‖=D i)
    (hstable : ∀ i, 1 ≤ i → i ≤ B → ‖A i (quarterTurn (a i))‖=(D i)⁻¹)
    (hstep : ∀ i, 1 ≤ i → i < B → ∀ z, ‖A i z‖ ≤ M*‖A (i+1) z‖) :
    ‖A l (quarterTurn (a B))‖ ≤ (D l)⁻¹+D l*∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)) := by
  have hpos (i : ℕ) (hi : 1 ≤ i) (hiB : i ≤ B) : 0 < ‖A i‖ :=
    lt_of_lt_of_le zero_lt_one (harea i hi hiB).singular_pair.choose_spec.2.2.2.2
  have hchain:=wedge_chain_bound (fun i => quarterTurn (a i))
    (fun i => M/(D i*D (i+1))) l B hlB
    (fun i hli hiB => by rw [norm_quarterTurn]; exact hunit i (by omega) hiB)
    (by
      intro i hli hiB
      have hh:=stable_direction_step (harea i (by omega) (by omega)) (a i) (a (i+1))
        (hunit i (by omega) (by omega)) (hunit (i+1) (by omega) (by omega))
        (by rw [hmax i (by omega) (by omega),hnorm i (by omega) (by omega)])
        (by rw [hstable (i+1) (by omega) (by omega),hnorm (i+1) (by omega) (by omega)])
        M (hpos (i+1) (by omega) (by omega)) (hstep i (by omega) hiB)
      simpa only [hnorm i (by omega) (by omega),hnorm (i+1) (by omega) (by omega)] using hh)
  rw [wedge_quarterTurn_both] at hchain
  have hup:=two_singular_upper (harea l hl hlB) (a l) (hunit l hl hlB)
    (by rw [hmax l hl hlB,hnorm l hl hlB]) (quarterTurn (a B))
  rw [dot_quarterTurn_right,abs_neg,hnorm l hl hlB] at hup
  have hw:=abs_wedge_le_norm_mul (a l) (quarterTurn (a B))
  rw [norm_quarterTurn,hunit l hl hlB,hunit B (by omega) le_rfl,mul_one] at hw
  have hD : 0 ≤ D l := by rw [← hnorm l hl hlB]; exact norm_nonneg _
  calc
    _  ≤  D l*|wedge (a l) (a B)|+(D l)⁻¹*|wedge (a l) (quarterTurn (a B))| := hup
    _  ≤  D l*(∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)))+(D l)⁻¹*1 :=
      add_le_add (mul_le_mul_of_nonneg_left hchain hD) (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hD))
    _ = _ := by ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeScalar
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma geometric_Ico_bound (q : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1/2) (l B : ℕ) :
    ∑ i ∈ Finset.Ico l B, q^i ≤ 2*q^l := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add,mul_comm (q^l)]
  rw [← Finset.sum_mul]
  have hs : ∑ i ∈ Finset.range (B-l), q^i ≤ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (B-l), (1/2:ℝ)^i := by gcongr
      _ ≤ 2 := sum_geometric_two_le (B-l)
  exact mul_le_mul_of_nonneg_right hs (pow_nonneg hq _)
lemma stable_error_sum (M c : ℝ) (D : ℕ → ℝ) (l B : ℕ) (hM : 1 < M)
    (_hc : 0 < c) (hq : M ^ (-2*c) ≤ 1/2) (_hl : 1 ≤ l) (_hlB : l ≤ B)
    (hD : ∀ i, l ≤ i → i ≤ B → M^(c*(i:ℝ)) ≤ D i) :
    ∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)) ≤ 2*M^(1-c-2*c*(l:ℝ)) := by
  have hpos : 0 < M := by linarith
  have hqpos : 0 ≤ M ^ (-2*c) := Real.rpow_nonneg hpos.le _
  have hpoint (i : ℕ) (hi : i ∈ Finset.Ico l B) :
      M/(D i*D (i+1)) ≤ M^(1-c)*(M^(-2*c))^i := by
    obtain ⟨hli,hiB⟩:=Finset.mem_Ico.mp hi
    have hDi := hD i hli (by omega)
    have hDi' := hD (i+1) (by omega) (by omega)
    have hi0 : 0 < D i := (Real.rpow_pos_of_pos hpos _).trans_le hDi
    have hi1 : 0 < D (i+1) := (Real.rpow_pos_of_pos hpos _).trans_le hDi'
    calc
      _ ≤ M/(M^(c*(i:ℝ))*M^(c*((i+1:ℕ):ℝ))) := by
        apply div_le_div_of_nonneg_left hpos.le (by positivity)
        exact mul_le_mul hDi hDi' (Real.rpow_nonneg hpos.le _) hi0.le
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one M]
        rw [← Real.rpow_add hpos,← Real.rpow_sub hpos,← Real.rpow_mul_natCast,← Real.rpow_add hpos]
        · congr 1
          push_cast
          ring
        · exact hpos.le
  calc
    _ ≤ ∑ i ∈ Finset.Ico l B, M^(1-c)*(M^(-2*c))^i := Finset.sum_le_sum hpoint
    _ = M^(1-c)*∑ i ∈ Finset.Ico l B, (M^(-2*c))^i := by rw [Finset.mul_sum]
    _ ≤ M^(1-c)*(2*(M^(-2*c))^l) :=
      mul_le_mul_of_nonneg_left (geometric_Ico_bound _ hqpos hq l B) (Real.rpow_nonneg hpos.le _)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hpos.le]
      have hh:=Real.rpow_add hpos (1-c) ((-2*c)*(l:ℝ))
      rw [show 1-c-2*c*(l:ℝ)=1-c+(-2*c)*(l:ℝ) by ring,hh]
      ring
lemma stable_prefix_power_bound (M : ℝ) (D : ℕ → ℝ) (l B : ℕ)
    (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2) (hl : 1 ≤ l) (hlB : l ≤ B)
    (hD : ∀ i, l ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ D i)
    (hu : D l ≤ M^(l:ℝ)) :
    (D l)⁻¹+D l*∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)) ≤ 3*M^(-(47/50:ℝ)*(l:ℝ)) := by
  have hp : 0 < M := by linarith
  have hlR : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hsum:=stable_error_sum M (49/50) D l B hM (by norm_num) (by convert hq using 1 ; norm_num) hl hlB hD
  have hDl :=hD l le_rfl hlB
  have hDpos : 0 < D l := (Real.rpow_pos_of_pos hp _).trans_le hDl
  have hinv : (D l)⁻¹ ≤ M^(-(49/50:ℝ)*(l:ℝ)) := by
    rw [neg_mul,Real.rpow_neg hp.le]
    exact inv_le_inv₀ hDpos (Real.rpow_pos_of_pos hp _) |>.mpr hDl
  have hi : M^(-(49/50:ℝ)*(l:ℝ)) ≤ M^(-(47/50:ℝ)*(l:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hM.le (by nlinarith)
  have hmul : D l*(∑ i ∈ Finset.Ico l B, M/(D i*D (i+1))) ≤ 2*M^(-(47/50:ℝ)*(l:ℝ)) := by
    calc
      _ ≤ M^(l:ℝ)*(2*M^(1-49/50-2*(49/50)*(l:ℝ))) :=
        mul_le_mul hu hsum (Finset.sum_nonneg fun i hi => by
          have hi':=Finset.mem_Ico.mp hi
          have h0 := (Real.rpow_pos_of_pos hp _).trans_le (hD i hi'.1 (by omega))
          have h1 := (Real.rpow_pos_of_pos hp _).trans_le (hD (i+1) (by omega) (by omega))
          positivity) (Real.rpow_nonneg hp.le _)
      _ = 2*M^((l:ℝ)+(1-49/50-2*(49/50)*(l:ℝ))) := by rw [Real.rpow_add hp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM.le (by linarith)) (by norm_num)
  nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_StablePrefix
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma transferProduct_back_step (v : ℕ → ℝ) (i : ℕ) (M : ℝ)
    (hv : |v (i+1)|+1 ≤ M) (z : ℂ) :
    ‖transferProduct v i z‖ ≤ M*‖transferProduct v (i+1) z‖ := by
  have he : transferStepInv (v (i+1)) (transferProduct v (i+1) z)=transferProduct v i z := by
    simp [transferProduct]
  rw [← he]
  exact ((transferStepInv _).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right ((transferStepInv_norm _).trans hv) (norm_nonneg _))

lemma prefix_stable_vector (v : ℕ → ℝ) (M : ℝ) (B : ℕ) (_hB : 1 ≤ B)
    (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2)
    (hv : ∀ i, 1 ≤ i → i ≤ B → |v i|+1 ≤ M)
    (hg : ∀ i, 1 ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ ‖transferProduct v i‖) :
    ∃ s : ℂ, ‖s‖=1 ∧ ‖transferProduct v B s‖=‖transferProduct v B‖⁻¹ ∧
      ∀ l, 1 ≤ l → l ≤ B → ‖transferProduct v l s‖ ≤ 3*M^(-(47/50:ℝ)*(l:ℝ)) := by
  choose a ha hmax horth hstable hnorm using fun i => (transferProduct_area v i).singular_pair
  refine ⟨quarterTurn (a B),by rw [norm_quarterTurn,ha],hstable B,?_⟩
  intro l hl hlB
  have hb:=stable_prefix_finite_bound (transferProduct v) a (fun i => ‖transferProduct v i‖) M l B hl hlB
    (fun i _ _ => transferProduct_area v i) (fun i _ _ => ha i) (fun _ _ _ => rfl)
    (fun i _ _ => hmax i) (fun i _ _ => hstable i)
    (fun i hi hiB z => transferProduct_back_step v i M (hv (i+1) (by omega) (by omega)) z)
  apply hb.trans
  apply stable_prefix_power_bound M _ l B hM hq hl hlB
  · exact fun i hli hiB => hg i (by omega) hiB
  · simpa only [Real.rpow_natCast] using (transferProduct_norm_bounds v M l (by linarith)
      (fun i hi hil => hv i hi (by omega))).2
lemma vertical_im_lower (s : ℂ) (hu : ‖s‖=1) (hs : |s.re| ≤ 1/4) : 3/4 ≤ |s.im| := by
  have hh:=Complex.norm_le_abs_re_add_abs_im s
  rw [hu] at hh
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeKernel
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma real_axes_decomposition (s : ℂ) : s=s.re • (1:ℂ)+s.im • Complex.I := by
  apply Complex.ext <;> simp
lemma row_axes_decomposition (row : ℂ →L[ℝ] ℝ) (s : ℂ) :
    row s=s.re*row 1+s.im*row Complex.I := by
  conv_lhs => rw [real_axes_decomposition s]
  simp only [map_add,map_smul,smul_eq_mul]

lemma normalized_kernel_from_stable (row : ℂ →L[ℝ] ℝ) (s : ℂ) (D : ℝ)
    (hD : 0 < D) (hu : ‖s‖=1) (hs : |s.re| ≤ 1/4)
    (hrow : D/3 ≤ |row 1|) (hsmall : |row s| ≤ D⁻¹) :
    ∃ (u : ℂ) (e : ℝ), u.im=1 ∧ row u=0 ∧
      u=(s.im)⁻¹ • s+e • (1:ℂ) ∧ |e| ≤ 6/D^2 := by
  have him := vertical_im_lower s hu hs
  have hsim : s.im ≠ 0 := abs_pos.mp (by linarith : 0 < |s.im|)
  have hr1 : row 1 ≠ 0 := abs_pos.mp (by linarith : 0 < |row 1|)
  let u : ℂ := (-row Complex.I/row 1) • (1:ℂ)+Complex.I
  let e := -row s/(row 1*s.im)
  refine ⟨u,e,?_,?_,?_,?_⟩
  · simp [u]
  · simp only [u,map_add,map_smul,smul_eq_mul]
    field_simp
    ring
  · have haxes:=row_axes_decomposition row s
    apply Complex.ext
    · simp only [u,Complex.add_re,Complex.smul_re,Complex.one_re,smul_eq_mul,mul_one,Complex.I_re,add_zero]
      dsimp [e]
      field_simp
      nlinarith
    · simp only [u,Complex.add_im,Complex.smul_im,Complex.one_im,smul_eq_mul,mul_zero,Complex.I_im,zero_add,add_zero]
      exact (inv_mul_cancel₀ hsim).symm
  · have hden : 0 < |row 1| *|s.im| := mul_pos (abs_pos.mpr hr1) (abs_pos.mpr hsim)
    dsimp [e]
    rw [abs_div,abs_neg,abs_mul]
    apply (div_le_iff₀ hden).mpr
    have hprod : D/6 ≤ |row 1| *|s.im| := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 6/D^2)
    have he : (6/D^2)*(D/6)=D⁻¹ := by field_simp
    rw [he] at hh
    exact hsmall.trans hh
lemma eligible_row_contraction (A : ℕ → ℂ →L[ℝ] ℂ) (s u : ℂ) (e M D : ℝ)
    (B l : ℕ) (_hl : 1 ≤ l) (hlB : l ≤ B) (hM : 1 < M)
    (hu : ‖s‖=1) (hs : |s.re| ≤ 1/4)
    (heq : u=(s.im)⁻¹ • s+e • (1:ℂ)) (he : |e| ≤ 6/D^2)
    (hD : M^((49/50:ℝ)*(B:ℝ)) ≤ D)
    (hstable : ‖A l s‖ ≤ 3*M^(-(47/50:ℝ)*(l:ℝ)))
    (hup : ‖A l‖ ≤ M^(l:ℝ)) :
    ‖A l u‖ ≤ 12*M^(-(47/50:ℝ)*(l:ℝ)) := by
  have hp : 0 < M := by linarith
  have hDpos : 0 < D := (Real.rpow_pos_of_pos hp _).trans_le hD
  have him:=vertical_im_lower s hu hs
  have hi : |(s.im)⁻¹| ≤ 2 := by
    rw [abs_inv]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < |s.im|)).mpr
    linarith
  have he' : |e| ≤ 6*M^(-(49/25:ℝ)*(B:ℝ)) := by
    calc
      _ ≤ 6/D^2 := he
      _ ≤ 6/(M^((49/50:ℝ)*(B:ℝ)))^2 := by gcongr
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hp.le,div_eq_mul_inv,← Real.rpow_neg hp.le]
        congr 2
        ring
  have herror : |e| * M^(l:ℝ) ≤ 6*M^(-(47/50:ℝ)*(l:ℝ)) := by
    calc
      _ ≤ 6*M^(-(49/25:ℝ)*(B:ℝ))*M^(l:ℝ) := mul_le_mul_of_nonneg_right he' (Real.rpow_nonneg hp.le _)
      _ = 6*M^(-(49/25:ℝ)*(B:ℝ)+(l:ℝ)) := by rw [Real.rpow_add hp]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM.le ?_) (by norm_num)
        have hlR : (l:ℝ) ≤ B := by exact_mod_cast hlB
        have hl0 : (0:ℝ) ≤ l := Nat.cast_nonneg l
        linarith
  rw [heq,map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(s.im)⁻¹ • A l s‖+‖e • A l 1‖ := norm_add_le _ _
    _ = |(s.im)⁻¹| *‖A l s‖+|e| *‖A l 1‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ 2*(3*M^(-(47/50:ℝ)*(l:ℝ)))+|e| *M^(l:ℝ) := by
      apply add_le_add (mul_le_mul hi hstable (norm_nonneg _) (by norm_num))
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact ((A l).le_opNorm 1).trans (by simpa using hup)
    _ ≤ _ := by linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeEligibility
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma prefix_stable_vertical (v : ℕ → ℝ) (M : ℝ) (B : ℕ)
    (hB : 1 ≤ B) (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2)
    (hsmall : 3*M^(-(47/50:ℝ)) ≤ 1/4)
    (hv : ∀ i, 1 ≤ i → i ≤ B → |v i|+1 ≤ M)
    (hg : ∀ i, 1 ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ ‖transferProduct v i‖) :
    ∃ s : ℂ, ‖s‖=1 ∧ |s.re| ≤ 1/4 ∧ ‖transferProduct v B s‖=‖transferProduct v B‖⁻¹ ∧
      ∀ l, 1 ≤ l → l ≤ B → ‖transferProduct v l s‖ ≤ 3*M^(-(47/50:ℝ)*(l:ℝ)) := by
  obtain ⟨s,hu,hs,hpref⟩:=prefix_stable_vector v M B hB hM hq hv hg
  refine ⟨s,hu,?_,hs,hpref⟩
  have hh:=hpref 1 le_rfl hB
  have hc : (transferProduct v 1 s).im=s.re := rfl
  calc
    _ = |(transferProduct v 1 s).im| := congrArg abs hc.symm
    _ ≤ ‖transferProduct v 1 s‖ := Complex.abs_im_le_norm _
    _ ≤ 3*M^(-(47/50:ℝ)) := by simpa using hh
    _ ≤ _ := hsmall
lemma initial_kernel_dirichlet (v : ℕ → ℝ) (J : ℕ) (u : ℂ)
    (_hui : u.im=1) (_hJ : 1 ≤ J) (huj : linearSolution v 1 u.re J=0)
    (ht : tSolution v J ≠ 0) :
    ∀ p, linearSolution v 1 u.re p=dirichletSolution v J p := by
  have hb:=boundaryValue_unique v J ht u.re huj
  intro p
  rw [hb]
  rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeDirichlet
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma eligible_dirichlet_bound (v : ℕ → ℝ) (M D : ℝ) (B J : ℕ)
    (hM : 1 < M) (hJ : 1 ≤ J) (hJB : J ≤ B+1)
    (hD : M^((49/50:ℝ)*(B:ℝ)) ≤ D)
    (hv : ∀ p, 1 ≤ p → p ≤ B → |v p|+1 ≤ M)
    (s : ℂ) (hs : ‖s‖=1) (hver : |s.re| ≤ 1/4)
    (hpref : ∀ p, 1 ≤ p → p ≤ B → ‖transferProduct v p s‖ ≤ 3*M^(-(47/50:ℝ)*(p:ℝ)))
    (row : ℂ →L[ℝ] ℝ) (hroweq : ∀ z, row z=linearSolution v z.im z.re J)
    (hsmall : |row s| ≤ D⁻¹) (hrow : D/3 ≤ |row 1|) :
    tSolution v J ≠ 0 ∧ ∀ p, 1 ≤ p → p < J →
      |dirichletSolution v J p| ≤ 12*M^(-(9/10:ℝ)*(p:ℝ)) := by
  have hMp : 0 < M := by linarith
  have hDp : 0 < D := (Real.rpow_pos_of_pos hMp _).trans_le hD
  have ht : tSolution v J ≠ 0 := by
    have hr : row 1≠0 := abs_pos.mp (by linarith : 0 < |row 1|)
    simpa only [hroweq,Complex.one_im,Complex.one_re,tSolution] using hr
  obtain ⟨u,e,hui,hru,heq,he⟩:=normalized_kernel_from_stable row s D hDp hs hver hrow hsmall
  have huj : linearSolution v 1 u.re J=0 := by simpa only [hroweq,hui] using hru
  have heqU :=initial_kernel_dirichlet v J u hui hJ huj ht
  refine ⟨ht,?_⟩
  intro p hp hpJ
  have hpB : p ≤ B := by omega
  have hup : ‖transferProduct v p‖ ≤ M^(p:ℝ) := by
    simpa only [Real.rpow_natCast] using (transferProduct_norm_bounds v M p (by linarith)
      (fun i hi hip => hv i hi (by omega))).2
  have hc:=eligible_row_contraction (transferProduct v) s u e M D B p hp hpB hM hs hver heq he
    hD (hpref p hp hpB) hup
  have hu3 : (⟨u.re,1⟩:ℂ)=u := by apply Complex.ext <;> simp [hui]
  have he : (transferProduct v p u).im=dirichletSolution v J p := by
    rw [← hu3,transferProduct_pair]
    exact heqU p
  calc
    _ = |(transferProduct v p u).im| := congrArg abs he.symm
    _ ≤ ‖transferProduct v p u‖ := Complex.abs_im_le_norm _
    _ ≤ 12*M^(-(47/50:ℝ)*(p:ℝ)) := hc
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM.le ?_) (by norm_num)
      have : (0:ℝ) ≤ p := Nat.cast_nonneg _
      linarith

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ClosedEligibility
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma eligible_prefix_dirichlet (v : ℕ → ℝ) (M : ℝ) (B J : ℕ)
    (hB : 2 ≤ B) (hJ : J=B ∨ J=B+1) (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2)
    (hsmall : 3*M^(-(47/50:ℝ)) ≤ 1/4)
    (hv : ∀ i, 1 ≤ i → i ≤ B → |v i|+1 ≤ M)
    (hg : ∀ i, 1 ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ ‖transferProduct v i‖)
    (hrow : ‖transferProduct v B‖/3 ≤ |tSolution v J|) :
    tSolution v J ≠ 0 ∧ ∀ p, 1 ≤ p → p < J →
      |dirichletSolution v J p| ≤ 12*M^(-(9/10:ℝ)*(p:ℝ)) := by
  obtain ⟨s,hu,hver,hs,hpref⟩:=prefix_stable_vertical v M B (by omega) hM hq hsmall hv hg
  have hpair (z : ℂ) : transferProduct v B z=
      ⟨linearSolution v z.im z.re (B+1),linearSolution v z.im z.re B⟩ := by
    exact transferProduct_pair v z.im z.re B
  rcases hJ with hJ|hJ
  · subst J
    apply eligible_dirichlet_bound v M ‖transferProduct v B‖ B B hM (by omega) (by omega)
      (hg B (by omega) le_rfl) hv s hu hver hpref (Complex.imCLM.comp (transferProduct v B))
    · intro z; change (transferProduct v B z).im=_; rw [hpair]
    · exact (Complex.abs_im_le_norm _).trans_eq hs
    · simpa only [ContinuousLinearMap.comp_apply,Complex.imCLM_apply,hpair,Complex.one_im,
        Complex.one_re,tSolution] using hrow
  · subst J
    apply eligible_dirichlet_bound v M ‖transferProduct v B‖ B (B+1) hM (by omega) le_rfl
      (hg B (by omega) le_rfl) hv s hu hver hpref (Complex.reCLM.comp (transferProduct v B))
    · intro z; change (transferProduct v B z).re=_; rw [hpair]
    · exact (Complex.abs_re_le_norm _).trans_eq hs
    · simpa only [ContinuousLinearMap.comp_apply,Complex.reCLM_apply,hpair,Complex.one_im,
        Complex.one_re,tSolution] using hrow

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeScalars
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma BridgeScalarControl.prefix_dirichlet_q44_oai {k : ℝ} (h : BridgeScalarControl k)
    (B n : ℕ) (hn : 1 ≤ n) (hB : B=n ∨ B=n+1) (hBn : 2 ≤ B)
    (z : ℝ × ℝ) (hz : prefixEligible k B (n+1) z) :
    tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0 ∧ ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)) := by
  have hJ : n+1=B ∨ n+1=B+1 := by rcases hB with rfl|rfl <;> omega
  have hh := eligible_prefix_dirichlet (orbitCoefficient k z.1 z.2) (growthBase k) B (n+1)
    hBn hJ (by have := growthBase_ge_four k h.nonneg; linarith) h.prefix_geom h.prefix_small
    (fun i _ _ => potential_bound k _ h.nonneg) hz.1 hz.2
  exact ⟨hh.1,fun p hp hpn => hh.2 p hp (by omega)⟩
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.BridgeScalarControl.prefix_dirichlet_q44_oai := @OAI.StandardMapEntropy.BridgeScalarControl.prefix_dirichlet_q44_oai
