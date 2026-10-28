-- Prove2me | solution 1 for OAI.StandardMapEntropy.actual_fast_bridge_product
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T00:27:53.366682+00:00
-- url     : https://prove2.me/submissions/400d45bf-bd90-4af2-ab09-e408df86c6eb

import Mathlib
import Definitions.Def_StandardMapEntropy
import Definitions.Def_OAIQ2St000
import Theorems.Thm_OAI_StandardMapEntropy_actual_backward_slice
import Theorems.Thm_OAI_StandardMapEntropy_actual_compact_graph_labels_full

section
-- module Solutions.OAIQ2_Std.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

theorem measurePreserving_standardMap (k : ℝ) : MeasurePreserving (standardMap k) area area := by
  unfold area
  have hkick : MeasurePreserving
      (fun z : Torus => (z.1, z.2 + kick k z.1))
        ((volume : Measure Circle).prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure Circle)).skew_product
      (g := fun x y : Circle => y + kick k x) ?_ ?_
    · exact measurable_snd.add ((continuous_kick k).measurable.comp measurable_fst)
    · exact Filter.Eventually.of_forall (fun x => map_add_right_eq_self volume (kick k x))
  convert (measurePreserving_add_prod (volume : Measure Circle) volume).comp hkick using 1
  funext z
  simp only [Function.comp_apply, standardMap, kick]
  congr 1
  abel

lemma recurrenceCoordinates_involutive : Function.Involutive recurrenceCoordinates := by
  intro z
  apply Prod.ext <;> simp [recurrenceCoordinates]

lemma standardMap_conjugacy (k : ℝ) (z : Torus) :
    recurrenceCoordinates (standardMap k z) =
      recurrenceMap k (recurrenceCoordinates z) := by
  apply Prod.ext <;> simp only [recurrenceCoordinates, recurrenceMap, standardMap, kick, two_smul]
  · abel
  · abel

lemma hasDerivAt_phi (k x : ℝ) : HasDerivAt (phi k) (potential k x) x := by
  have hs : HasDerivAt (fun y : ℝ => Real.sin (2 * Real.pi * y))
      (Real.cos (2 * Real.pi * x) * (2 * Real.pi)) x := by
    simpa using ((hasDerivAt_id x).const_mul (2 * Real.pi)).sin
  have hl : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  convert! hl.add (hs.const_mul k) using 1
  unfold potential
  ring

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

lemma liftedOrbit_step (k q₀ q₁ : ℝ) (n : ℕ) :
    liftedOrbit k q₀ q₁ (n + 2) =
      phi k (liftedOrbit k q₀ q₁ (n + 1)) - liftedOrbit k q₀ q₁ n := rfl

lemma drawdown_nonneg (z : ℕ → ℝ) (c : ℝ) (n : ℕ) : 0 ≤ drawdown z c n := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma drawdown_ge_drop (z : ℕ → ℝ) (c : ℝ) (j l : ℕ) (hl : l ≤ j) :
    z l - z j + c * ((j : ℝ) - (l : ℝ)) ≤ drawdown z c j := by
  induction j with
  | zero =>
    have : l = 0 := by omega
    simp [this, drawdown]
  | succ j ih =>
    by_cases hlj : l = j + 1
    · simpa [hlj] using drawdown_nonneg z c (j + 1)
    · have hl' : l ≤ j := by omega
      have hi := ih hl'
      have hm : drawdown z c j + c + z j - z (j + 1) ≤ drawdown z c (j + 1) :=
        le_max_right _ _
      push_cast
      nlinarith only [hi, hm]

lemma drawdown_pos_of_bad (z : ℕ → ℝ) (c : ℝ) (j : ℕ)
    (h : ∃ l < j, z j - z l < c * ((j : ℝ) - (l : ℝ))) :
    0 < drawdown z c j := by
  obtain ⟨l, hlj, hdrop⟩ := h
  have hg := drawdown_ge_drop z c j l hlj.le
  linarith

lemma drawdown_step_account (z : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (hz : z (n + 1) - z n ≤ 1) :
    (if 0 < drawdown z c (n + 1) then 1 - c else 0) ≤
      1 - (z (n + 1) - z n) + drawdown z c n - drawdown z c (n + 1) := by
  split_ifs with hp
  · have he : drawdown z c (n + 1) = drawdown z c n + c + z n - z (n + 1) := by
      change max 0 (drawdown z c n + c + z n - z (n + 1)) = _
      apply max_eq_right
      change 0 < max 0 (drawdown z c n + c + z n - z (n + 1)) at hp
      rcases lt_max_iff.mp hp with hp | hp
      · exact False.elim ((lt_irrefl _) hp)
      · exact hp.le
    rw [he]
    linarith
  · have he : drawdown z c (n + 1) = 0 :=
      le_antisymm (not_lt.mp hp) (drawdown_nonneg z c _)
    rw [he]
    linarith [drawdown_nonneg z c n]

lemma drawdown_account_sum (z : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (1 - (z (n + 1) - z n) + drawdown z c n - drawdown z c (n + 1))) =
      (N : ℝ) - (z N - z 0) - drawdown z c N := by
  induction N with
  | zero => simp [drawdown]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma drawdown_count (z : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hz : ∀ n < N, z (n + 1) - z n ≤ 1) :
    (((Finset.range N).filter (fun n => 0 < drawdown z c (n + 1))).card : ℝ) * (1 - c) ≤
      (N : ℝ) - (z N - z 0) := by
  classical
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun n hn =>
    drawdown_step_account z c n (hz n (Finset.mem_range.mp hn)))
  rw [drawdown_account_sum] at hsum
  have hc :
      (((Finset.range N).filter (fun n => 0 < drawdown z c (n + 1))).card : ℝ) * (1 - c) =
      ∑ n ∈ Finset.range N, if 0 < drawdown z c (n + 1) then 1 - c else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← hc] at hsum
  linarith [drawdown_nonneg z c N]

theorem shortfall_count (z : ℕ → ℝ) (c : ℝ) (hc : c < 1) (N : ℕ)
    (hz : ∀ n < N, z (n + 1) - z n ≤ 1) :
    (((Finset.range N).filter fun n =>
      ∃ l < n + 1, z (n + 1) - z l < c * ((n + 1 : ℕ) - (l : ℝ))).card : ℝ) ≤
      ((N : ℝ) - (z N - z 0)) / (1 - c) := by
  classical
  have hsub : ((Finset.range N).filter fun n =>
        ∃ l < n + 1, z (n + 1) - z l < c * ((n + 1 : ℕ) - (l : ℝ))) ⊆
      ((Finset.range N).filter fun n => 0 < drawdown z c (n + 1)) := by
    intro n hn
    obtain ⟨hnN, hbad⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnN, drawdown_pos_of_bad z c (n + 1) hbad⟩
  have hcard :
      (((Finset.range N).filter fun n =>
        ∃ l < n + 1, z (n + 1) - z l < c * ((n + 1 : ℕ) - (l : ℝ))).card : ℝ) ≤
      (((Finset.range N).filter fun n => 0 < drawdown z c (n + 1))).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  exact (mul_le_mul_of_nonneg_right hcard (sub_nonneg.mpr hc.le)).trans
    (drawdown_count z c N hz)

lemma potential_lipschitz (k x y : ℝ) (hk : 0 ≤ k) :
    |potential k y - potential k x| ≤ (2 * Real.pi * growthBase k) * |y - x| := by
  have hK : 0 ≤ 2 * Real.pi * k := by positivity
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hid : potential k y - potential k x =
      (2 * Real.pi * k) * (Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * x)) := by
    unfold potential
    ring
  rw [hid, abs_mul, abs_of_nonneg hK]
  have hdiff : |2 * Real.pi * y - 2 * Real.pi * x| = (2 * Real.pi) * |y - x| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hπ]
  calc
    (2 * Real.pi * k) * |Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * x)| ≤
        (2 * Real.pi * k) * ((2 * Real.pi) * |y - x|) := by
      apply mul_le_mul_of_nonneg_left _ hK
      rw [← hdiff]
      exact Real.abs_cos_sub_cos_le _ _
    _ ≤ (2 * Real.pi * growthBase k) * |y - x| := by
      have h : 2 * Real.pi * k ≤ growthBase k := by unfold growthBase; linarith
      have h' := mul_le_mul_of_nonneg_right h (mul_nonneg hπ (abs_nonneg (y - x)))
      nlinarith only [h']

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
-- module Solutions.OAIQ2_Std.StandardMap_PlaneGeometry
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
-- module Solutions.OAIQ2_Std.StandardMap_PlaneTransfer
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
-- module Solutions.OAIQ2_Std.StandardMap_TransferCore
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

lemma transferStepInv_area (v : ℝ) : PlaneAreaPreserving (transferStepInv v) := by
  intro z w; simp [wedge]; ring
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
lemma transferProductInv_area (v : ℕ → ℝ) (n : ℕ) : PlaneAreaPreserving (transferProductInv v n) := by
  induction n with
  | zero => intro z w; rfl
  | succ n ih => exact ih.comp (transferStepInv_area _)
lemma transferProduct_inverse (v : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    transferProduct v n (transferProductInv v n z)=z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [transferProduct, transferProductInv,ContinuousLinearMap.comp_apply,ih,transferStep_inv]
lemma transferProductInv_inverse (v : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    transferProductInv v n (transferProduct v n z)=z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [transferProduct, transferProductInv,ContinuousLinearMap.comp_apply,transferStepInv_inv,ih]
lemma transferProduct_norm_inverse (v : ℕ → ℝ) (n : ℕ) :
    ‖transferProduct v n‖=‖transferProductInv v n‖ :=
  (transferProduct_area v n).norm_inverse (transferProductInv_area v n)
    (transferProduct_inverse v n) (transferProductInv_inverse v n)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ObservationTransport
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
lemma transferStep_difference_bound (v w : ℝ) : ‖transferStep v-transferStep w‖ ≤ |v-w| := by
  apply (transferStep v-transferStep w).opNorm_le_bound (abs_nonneg _)
  intro z
  have he : (transferStep v-transferStep w) z=((v-w)*z.re : ℝ) := by
    apply Complex.ext <;> simp only [sub_apply,Complex.sub_re,Complex.sub_im,
      transferStep_re,transferStep_im,Complex.ofReal_re,Complex.ofReal_im] <;> ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)

lemma transferProduct_difference_bound (v w : ℕ → ℝ) (M δ : ℝ) (n : ℕ)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hv : ∀ i, 1 ≤ i → i ≤ n → |v i|+1 ≤ M)
    (hw : ∀ i, 1 ≤ i → i ≤ n → |w i|+1 ≤ M)
    (hd : ∀ i, 1 ≤ i → i ≤ n → |v i-w i| ≤ δ) :
    ‖transferProduct v n-transferProduct w n‖ ≤ (n:ℝ)*δ*M^n := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
    have hvn : ‖transferProduct v n‖ ≤ M^n :=
      (transferProduct_norm_bounds v M n (by linarith) (fun i hi hin => hv i hi (by omega))).2
    have hwn : ‖transferStep (w (n+1))‖ ≤ M := (transferStep_norm _).trans (hw _ (by omega) le_rfl)
    have hdn := (transferStep_difference_bound (v (n+1)) (w (n+1))).trans (hd _ (by omega) le_rfl)
    have hpn := ih (fun i hi hin => hv i hi (by omega)) (fun i hi hin => hw i hi (by omega))
      (fun i hi hin => hd i hi (by omega))
    have he : transferProduct v (n+1)-transferProduct w (n+1)=
        (transferStep (v (n+1))-transferStep (w (n+1))).comp (transferProduct v n)+
        (transferStep (w (n+1))).comp (transferProduct v n-transferProduct w n) := by
      apply ContinuousLinearMap.ext
      intro z
      simp only [transferProduct,sub_apply,add_apply,
        ContinuousLinearMap.comp_apply,map_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖(transferStep (v (n+1))-transferStep (w (n+1))).comp (transferProduct v n)‖+
          ‖(transferStep (w (n+1))).comp (transferProduct v n-transferProduct w n)‖ := norm_add_le _ _
      _ ≤ δ*M^n+M*((n:ℝ)*δ*M^n) := add_le_add
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hdn hvn (norm_nonneg _) hδ))
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hwn hpn (norm_nonneg _) (by linarith)))
      _ ≤ δ*M^(n+1)+M*((n:ℝ)*δ*M^n) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hM (Nat.le_succ n)) hδ) le_rfl
      _ = _ := by rw [pow_succ]; push_cast; ring

lemma log_lipschitz_above_one (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y| := by
  have hh := (convex_Ici (1:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.log) (f' := fun x => x⁻¹) (C := 1)
    (fun z hz => (Real.hasDerivAt_log (by have : 1 ≤ z := hz; linarith : z ≠ 0)).hasDerivWithinAt)
    (fun z hz => by
      change 1 ≤ z at hz
      change |z⁻¹| ≤ 1
      rw [abs_of_nonneg (inv_nonneg.mpr (by linarith))]
      exact inv_le_one_of_one_le₀ hz) hy hx
  simpa only [Real.norm_eq_abs,one_mul] using hh

lemma transfer_log_difference_bound (v w : ℕ → ℝ) (M δ : ℝ) (n : ℕ)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hv : ∀ i, 1 ≤ i → i ≤ n → |v i|+1 ≤ M)
    (hw : ∀ i, 1 ≤ i → i ≤ n → |w i|+1 ≤ M)
    (hd : ∀ i, 1 ≤ i → i ≤ n → |v i-w i| ≤ δ) :
    |Real.log ‖transferProduct v n‖-Real.log ‖transferProduct w n‖| ≤ (n:ℝ)*δ*M^n := by
  exact (log_lipschitz_above_one _ _
    (transferProduct_norm_bounds v M n (by linarith) hv).1
    (transferProduct_norm_bounds w M n (by linarith) hw).1).trans
    ((abs_norm_sub_norm_le _ _).trans (transferProduct_difference_bound v w M δ n hM hδ hv hw hd))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_LiftDynamics
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
lemma liftIter_add (k : ℝ) (i j : ℤ) (z : ℝ × ℝ) :
    liftIter k (i+j) z=liftIter k i (liftIter k j z) := by
  simp only [liftIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma liftIter_nat (k : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    liftIter k n z=(liftedOrbit k z.2 z.1 (n+1),liftedOrbit k z.2 z.1 n) := by
  induction n with
  | zero => simp [liftIter,liftedOrbit]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_comm,liftIter_add,ih]
    simp only [liftIter,zpow_one]
    change (phi k (liftedOrbit k z.2 z.1 (n+1))-liftedOrbit k z.2 z.1 n,
      liftedOrbit k z.2 z.1 (n+1))=_
    rfl
lemma phi_lipschitz (k : ℝ) (hk : 0 ≤ k) :
    LipschitzWith (⟨growthBase k-1,by have := growthBase_ge_four k hk; linarith⟩ : NNReal) (phi k) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_phi k x).differentiableAt
  · intro x
    change |deriv (phi k) x| ≤ growthBase k-1
    rw [(hasDerivAt_phi k x).deriv]
    linarith [potential_bound k x hk]
lemma liftStep_lipschitz (k : ℝ) (hk : 0 ≤ k) :
    LipschitzWith (⟨growthBase k,by have := growthBase_ge_four k hk; linarith⟩ : NNReal) (liftStep k) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Prod.dist_eq, liftStep_apply,liftStep_apply]
  change max (dist (phi k z.1-z.2) (phi k w.1-w.2)) (dist z.1 w.1) ≤ _
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have h1 : dist z.1 w.1 ≤ dist z w := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : dist z.2 w.2 ≤ dist z w := by rw [Prod.dist_eq]; exact le_max_right _ _
  refine max_le ?_ ?_
  · calc
      _ ≤ dist (phi k z.1) (phi k w.1)+dist z.2 w.2 := dist_sub_sub_le _ _ _ _
      _ ≤ (growthBase k-1)*dist z.1 w.1+dist z.2 w.2 := add_le_add ((phi_lipschitz k hk).dist_le_mul _ _) le_rfl
      _ ≤ (growthBase k-1)*dist z w+dist z w := add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith)) h2
      _ = _ := by change _ = growthBase k*dist z w; ring
  · exact h1.trans (le_mul_of_one_le_left (dist_nonneg) hM)
lemma liftStep_symm_lipschitz (k : ℝ) (hk : 0 ≤ k) :
    LipschitzWith (⟨growthBase k,by have := growthBase_ge_four k hk; linarith⟩ : NNReal) (liftStep k).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hh := (liftStep_lipschitz k hk).dist_le_mul z.swap w.swap
  change dist (liftStep k z.swap) (liftStep k w.swap) ≤ growthBase k*dist z.swap w.swap at hh
  change dist ((liftStep k).symm z) ((liftStep k).symm w) ≤ growthBase k*dist z w
  simpa only [liftStep_apply,liftStep_symm_apply,Prod.dist_eq,Prod.fst_swap,Prod.snd_swap,
    max_comm] using hh
lemma liftIter_lipschitz (k : ℝ) (hk : 0 ≤ k) (i : ℤ) (z w : ℝ × ℝ) :
    dist (liftIter k i z) (liftIter k i w) ≤ growthBase k^i.natAbs*dist z w := by
  cases i with
  | ofNat n =>
    have hh := ((liftStep_lipschitz k hk).iterate n).dist_le_mul z w
    change dist ((⇑(liftStep k))^[n] z) ((⇑(liftStep k))^[n] w) ≤ growthBase k^n*dist z w at hh
    change dist (liftIter k (n:ℤ) z) (liftIter k (n:ℤ) w) ≤ growthBase k^n*dist z w
    simpa only [liftIter,zpow_natCast,Equiv.Perm.coe_pow] using hh
  | negSucc n =>
    have hh := ((liftStep_symm_lipschitz k hk).iterate (n+1)).dist_le_mul z w
    change dist ((⇑(liftStep k).symm)^[n+1] z) ((⇑(liftStep k).symm)^[n+1] w) ≤ growthBase k^(n+1)*dist z w at hh
    change dist (liftIter k (Int.negSucc n) z) (liftIter k (Int.negSucc n) w) ≤ growthBase k^(n+1)*dist z w
    simpa only [liftIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_SegmentObservations
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
lemma liftSegmentTransfer_eq (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) :
    liftSegmentTransfer k z a n=transferProduct
      (orbitCoefficient k (liftIter k a z).2 (liftIter k a z).1) n := by
  unfold liftSegmentTransfer
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [transferProduct,ih]
    congr 2
    unfold liftSegmentCoefficient orbitCoefficient
    rw [show a+((n+1:ℕ):ℤ)-1=(n:ℤ)+a by push_cast; ring,liftIter_add,liftIter_nat]
lemma liftSegmentCoefficient_near (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (a b : ℤ)
    (i r : ℕ) (hwin : (a+(i:ℤ)-1-b).natAbs ≤ r) :
    |liftSegmentCoefficient k z a i-liftSegmentCoefficient k w a i| ≤
      (2*Real.pi*growthBase k)*(growthBase k^r*dist (liftIter k b z) (liftIter k b w)) := by
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have hshift (v : ℝ × ℝ) : liftIter k (a+(i:ℤ)-1) v=
      liftIter k (a+(i:ℤ)-1-b) (liftIter k b v) := by
    rw [← liftIter_add]; congr 1; ring
  have hdist := liftIter_lipschitz k hk (a+(i:ℤ)-1-b) (liftIter k b z) (liftIter k b w)
  have hfst : |(liftIter k (a+(i:ℤ)-1) z).1-(liftIter k (a+(i:ℤ)-1) w).1| ≤
      growthBase k^r*dist (liftIter k b z) (liftIter k b w) := by
    rw [← Real.dist_eq]
    calc
      _ ≤ dist (liftIter k (a+(i:ℤ)-1) z) (liftIter k (a+(i:ℤ)-1) w) := by
        rw [Prod.dist_eq]; exact le_max_left _ _
      _ ≤ growthBase k^(a+(i:ℤ)-1-b).natAbs*dist (liftIter k b z) (liftIter k b w) := by
        rw [hshift z,hshift w]; exact hdist
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM hwin) dist_nonneg
  exact (potential_lipschitz k _ _ hk).trans
    (mul_le_mul_of_nonneg_left hfst (by have := growthBase_ge_four k hk; positivity))
lemma liftShortfall_transport (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (a b : ℤ)
    (n r : ℕ) (hn : 0 < n)
    (hwin : ∀ i, 1 ≤ i → i ≤ n → (a+(i:ℤ)-1-b).natAbs ≤ r) :
    |liftShortfall k z a n-liftShortfall k w a n| ≤
      ((2*Real.pi*growthBase k)/Real.log (growthBase k))*growthBase k^(r+n)*
        dist (liftIter k b z) (liftIter k b w) := by
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hp : 0 < Real.log (growthBase k) := Real.log_pos hM
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hδ : 0 ≤ (2*Real.pi*growthBase k)*(growthBase k^r*dist (liftIter k b z) (liftIter k b w)) := by positivity
  have hh := transfer_log_difference_bound (liftSegmentCoefficient k z a) (liftSegmentCoefficient k w a)
    (growthBase k) _ n hM.le hδ
    (fun i _ _ => liftSegmentCoefficient_bound k hk z a i)
    (fun i _ _ => liftSegmentCoefficient_bound k hk w a i)
    (fun i hi hin => liftSegmentCoefficient_near k hk z w a b i r (hwin i hi hin))
  unfold liftShortfall
  rw [sub_sub_sub_comm,sub_self,zero_sub,abs_neg,← sub_div,abs_div,
    abs_of_pos (mul_pos hnp hp)]
  calc
    _ ≤ ((n:ℝ)*((2*Real.pi*growthBase k)*(growthBase k^r*dist (liftIter k b z) (liftIter k b w)))*growthBase k^n)/
        ((n:ℝ)*Real.log (growthBase k)) := div_le_div_of_nonneg_right hh (mul_pos hnp hp).le
    _ = _ := by rw [pow_add]; field_simp
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_BridgeLinear
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
-- module Solutions.OAIQ2_Std.StandardMap_BridgeScalar
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
-- module Solutions.OAIQ2_Std.StandardMap_StablePrefix
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
lemma Complex.norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re|+|z.im| := by
  have he : z = (z.re : ℂ)+z.im*Complex.I := by apply Complex.ext <;> simp
  calc
    ‖z‖ = ‖(z.re : ℂ)+z.im*Complex.I‖ := congrArg norm he
    _ ≤ ‖(z.re : ℂ)‖+‖(z.im : ℂ)*Complex.I‖ := norm_add_le _ _
    _ = _ := by simp
lemma vertical_im_lower (s : ℂ) (hu : ‖s‖=1) (hs : |s.re| ≤ 1/4) : 3/4 ≤ |s.im| := by
  have hh:=Complex.norm_le_abs_re_add_abs_im s
  rw [hu] at hh
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_BridgeKernel
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
-- module Solutions.OAIQ2_Std.StandardMap_BridgeEligibility
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
lemma PlaneAreaPreserving.eligible_row {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A)
    (s : ℂ) (hu : ‖s‖=1) (hs : |s.re| ≤ 1/4) (hstable : ‖A s‖=‖A‖⁻¹) :
    ‖A‖/3 ≤ |(A 1).re| ∨ ‖A‖/3 ≤ |(A 1).im| := by
  have him := vertical_im_lower s hu hs
  have hD : 0 < ‖A‖ := by obtain ⟨a,ha,hb,hc,hd,he⟩:=hA.singular_pair; linarith
  have hw := abs_wedge_le_norm_mul (A 1) (A s)
  rw [hA,hstable] at hw
  have haxes : wedge 1 s=s.im := by simp [wedge]
  rw [haxes] at hw
  have hlow : (3/4)*‖A‖ ≤ ‖A 1‖ := by
    have hh:=mul_le_mul_of_nonneg_right (him.trans hw) hD.le
    simpa only [mul_assoc,inv_mul_cancel₀ hD.ne',mul_one] using hh
  have hup:=Complex.norm_le_abs_re_add_abs_im (A 1)
  by_contra hh
  push Not at hh
  linarith
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
-- module Solutions.OAIQ2_Std.StandardMap_BridgeDirichlet
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
-- module Solutions.OAIQ2_Std.StandardMap_GraphCalculus
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
lemma hasStrictDerivAt_phi (k x : ℝ) : HasStrictDerivAt (phi k) (potential k x) x := by
  have h := ((hasStrictDerivAt_id x).const_mul 2).add
    (((Real.hasStrictDerivAt_sin (2*Real.pi*x)).comp x
      ((hasStrictDerivAt_id x).const_mul (2*Real.pi))).const_mul k)
  convert! h using 1
  dsimp only [potential]
  ring

lemma hasStrictFDerivAt_liftedOrbit (k q a : ℝ) (n : ℕ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 n)
      (sSolution (orbitCoefficient k q a) n • ContinuousLinearMap.fst ℝ ℝ ℝ+
       tSolution (orbitCoefficient k q a) n • ContinuousLinearMap.snd ℝ ℝ ℝ) (q,a) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [sSolution,tSolution,linearSolution] using
      (hasStrictFDerivAt_fst : HasStrictFDerivAt (Prod.fst : ℝ × ℝ → ℝ) _ (q,a))
  | one => simpa [sSolution,tSolution,linearSolution] using
      (hasStrictFDerivAt_snd : HasStrictFDerivAt (Prod.snd : ℝ × ℝ → ℝ) _ (q,a))
  | more n h0 h1 =>
    have h := ((hasStrictDerivAt_phi k (liftedOrbit k q a (n+1))).comp_hasStrictFDerivAt (q,a) h1).sub h0
    apply h.congr_fderiv
    apply ContinuousLinearMap.ext
    intro z
    change potential k (liftedOrbit k q a (n+1)) *
      (sSolution (orbitCoefficient k q a) (n+1)*z.1+tSolution (orbitCoefficient k q a) (n+1)*z.2)-
      (sSolution (orbitCoefficient k q a) n*z.1+tSolution (orbitCoefficient k q a) n*z.2) =
      (orbitCoefficient k q a (n+1)*sSolution (orbitCoefficient k q a) (n+1)-sSolution (orbitCoefficient k q a) n)*z.1+
      (orbitCoefficient k q a (n+1)*tSolution (orbitCoefficient k q a) (n+1)-tSolution (orbitCoefficient k q a) n)*z.2
    dsimp only [orbitCoefficient]
    ring

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_GraphParameterContinuity
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
lemma continuous_liftedOrbit_pair (k : ℝ) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 n) :=
  continuous_iff_continuousAt.mpr (fun z =>
    (hasStrictFDerivAt_liftedOrbit k z.1 z.2 n).continuousAt)
lemma continuousOn_linearSolution_params {α : Type*} [TopologicalSpace α]
    (s : Set α) (v : α → ℕ → ℝ) (a b : α → ℝ)
    (hv : ∀ n, ContinuousOn (fun x => v x n) s)
    (ha : ContinuousOn a s) (hb : ContinuousOn b s) (n : ℕ) :
    ContinuousOn (fun x => linearSolution (v x) (a x) (b x) n) s := by
  induction n using Nat.twoStepInduction with
  | zero => exact ha
  | one => exact hb
  | more n h0 h1 => exact ((hv (n+1)).mul h1).sub h0
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_GraphSubsetCalculus
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

lemma hasFDerivWithinAt_of_regular_level {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (F : E × ℝ → ℝ) (b : E → ℝ) (s : Set E) (x : E)
    (A : E →L[ℝ] ℝ) (t : ℝ)
    (hD : HasStrictFDerivAt F
      (A.comp (ContinuousLinearMap.fst ℝ E ℝ)+t • ContinuousLinearMap.snd ℝ E ℝ) (x,b x))
    (ht : t ≠ 0) (hb : ContinuousWithinAt b s x)
    (hlevel : ∀ᶠ y in 𝓝[s] x, F (y,b y)=F (x,b x)) :
    HasFDerivWithinAt b ((-t⁻¹) • A) s x := by
  let L : (E × ℝ) →L[ℝ] ℝ :=
    A.comp (ContinuousLinearMap.fst ℝ E ℝ)+t • ContinuousLinearMap.snd ℝ E ℝ
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := t⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
  let ψ := hD.implicitFunctionOfProdDomain hInv
  have he : ∀ᶠ y in 𝓝[s] x, ψ y=b y := by
    have hpair : Tendsto (fun y => (y,b y)) (𝓝[s] x) (𝓝 (x,b x)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.prodMk_nhds hb
    filter_upwards [hpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),hlevel] with y hy hy'
    exact hy.mp hy'
  have he0 : ψ x=b x := ((hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv).self_of_nhds).mp rfl
  have hd := (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hInv).hasFDerivAt.hasFDerivWithinAt (s := s)
  have heq : -(L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse.comp
      (L.comp (ContinuousLinearMap.inl ℝ E ℝ)) = (-t⁻¹) • A := by
    apply ContinuousLinearMap.ext
    intro z
    have hh : (L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse
        ((L.comp (ContinuousLinearMap.inl ℝ E ℝ)) z)=t⁻¹*A z := by
      apply hInv.inverse_apply_eq.mpr
      simp [L,ht]
    change -((L.comp (ContinuousLinearMap.inr ℝ E ℝ)).inverse
      ((L.comp (ContinuousLinearMap.inl ℝ E ℝ)) z))=(-t⁻¹)*A z
    rw [hh,neg_mul]
  change HasFDerivWithinAt ψ _ s x at hd
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq (EventuallyEq.symm he) he0.symm
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ChangeVariablesBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measure_image_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) (f : E → E)
    (D : E → E →L[ℝ] E) (c C : ℝ) (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hinj : InjOn f s)
    (hlo : ∀ x ∈ s, c ≤ |(D x).det|) (hhi : ∀ x ∈ s, |(D x).det| ≤ C) :
    ENNReal.ofReal c*μ s ≤ μ (f '' s) ∧ μ (f '' s) ≤ ENNReal.ofReal C*μ s := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image μ hs hD hinj]
  constructor
  · calc
      _ = ∫⁻ x in s, ENNReal.ofReal c ∂μ := by simp
      _ ≤ _ := setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hlo x hx))
  · calc
      _ ≤ ∫⁻ x in s, ENNReal.ofReal C ∂μ :=
        setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hhi x hx))
      _ = _ := by simp

lemma weighted_image_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) (f : E → E)
    (D : E → E →L[ℝ] E) (c C : ℝ) (g : E → ℝ≥0∞) (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (hinj : InjOn f s)
    (hlo : ∀ x ∈ s, c ≤ |(D x).det|) (hhi : ∀ x ∈ s, |(D x).det| ≤ C) :
    ENNReal.ofReal c*(∫⁻ x in s, g (f x) ∂μ) ≤ ∫⁻ x in f '' s, g x ∂μ ∧
      (∫⁻ x in f '' s, g x ∂μ) ≤ ENNReal.ofReal C*(∫⁻ x in s, g (f x) ∂μ) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hD hinj g]
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hs (fun x hx => mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hlo x hx)) (by positivity))
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hs (fun x hx => mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hhi x hx)) (by positivity))

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_GraphJacobians
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma planeMatrix_det (a b c d : ℝ) : (planeMatrix a b c d).det=a*d-b*c := by
  change (planeMatrix a b c d).toLinearMap.det=_
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Module.Basis.coe_finTwoProd_repr]

lemma label_graph_derivative (Q : ℝ × ℝ → ℝ) (X : ℝ × ℝ → ℝ)
    (S : Set (ℝ × ℝ)) (z : ℝ × ℝ) (yc a b u v : ℝ)
    (hQ : HasStrictFDerivAt Q (planeDual u v) (X z,z.2))
    (hR : HasStrictFDerivAt Q (planeDual a b) (z.1,yc))
    (hu : u ≠ 0) (hX : ContinuousWithinAt X S z)
    (hlevel : ∀ᶠ w in 𝓝[S] z, Q (X w,w.2)=Q (w.1,yc))
    (hlevel0 : Q (X z,z.2)=Q (z.1,yc)) :
    HasFDerivWithinAt (fun w => (X w,w.2)) (planeMatrix (a/u) (-v/u) 0 1) S z := by
  let F : (ℝ × ℝ) × ℝ → ℝ := fun w => Q (w.2,w.1.2)-Q (w.1.1,yc)
  let A := planeDual (-a) v
  have hD : HasStrictFDerivAt F
      (A.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+u • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (z,X z) := by
    have hp1 := hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (z,X z))
    have hp2 := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := z)).comp (z,X z) (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (z,X z)))
    have hp3 := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := z)).comp (z,X z) (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (z,X z)))
    have hh := (hQ.comp (z,X z) (hp1.prodMk hp2)).sub
      (hR.comp (z,X z) (hp3.prodMk (hasStrictFDerivAt_const yc (z,X z))))
    apply hh.congr_fderiv
    apply ContinuousLinearMap.ext
    intro w
    change u*w.2+v*w.1.2-(a*w.1.1+b*0)=(-a*w.1.1+v*w.1.2)+u*w.2
    ring
  have hx := hasFDerivWithinAt_of_regular_level F X S z A u hD hu hX (by
    filter_upwards [hlevel] with w hw
    dsimp only [F]
    rw [hw,hlevel0]; ring)
  have ht := hx.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).hasFDerivWithinAt
  apply ht.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  apply Prod.ext
  · change (-u⁻¹)*((-a)*w.1+v*w.2)=a/u*w.1+(-v/u)*w.2
    ring
  · change w.2=0*w.1+1*w.2
    ring

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_RecenteredGraphs
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
lemma hasStrictFDerivAt_liftedOrbit_swap (k x y : ℝ) (n : ℕ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => liftedOrbit k z.2 z.1 n)
      (planeDual (tSolution (orbitCoefficient k y x) n)
        (sSolution (orbitCoefficient k y x) n)) (x,y) := by
  have h := (hasStrictFDerivAt_liftedOrbit k y x n).comp (x,y)
    ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (x,y))).prodMk
      (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (x,y))))
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  change sSolution (orbitCoefficient k y x) n*w.2+tSolution (orbitCoefficient k y x) n*w.1=tSolution (orbitCoefficient k y x) n*w.1+sSolution (orbitCoefficient k y x) n*w.2
  ring

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_WeightedChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma product_slice_bound (E I : Set ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ≥0∞)
    (K : ℝ≥0∞) (hE : MeasurableSet E) (_hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I)
    (hslice : ∀ x ∈ E, ∫⁻ y in I, T.indicator f (x,y) ≤ K) :
    (∫⁻ z in T, f z) ≤ K*volume E := by
  have he : (∫⁻ z in T, f z) = ∫⁻ z in E ×ˢ I, T.indicator f z := by
    rw [lintegral_indicator hT,Measure.restrict_restrict hT,inter_eq_left.mpr hsub]
  rw [he]
  change (∫⁻ z, T.indicator f z ∂(volume.prod volume).restrict (E ×ˢ I)) ≤ _
  rw [← Measure.prod_restrict]
  calc
    _ ≤ ∫⁻ x in E, ∫⁻ y in I, T.indicator f (x,y) := lintegral_prod_le _
    _ ≤ ∫⁻ x in E, K := setLIntegral_mono' hE hslice
    _ = _ := by simp

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TorusIntegral
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy

lemma unit_cell_integral (g : Torus → ℝ≥0∞) (hg : Measurable g) (a b : ℝ) :
    (∫⁻ z in Ioc a (a+1) ×ˢ Ioc b (b+1), g (liftProjection z)) = ∫⁻ z, g z ∂area := by
  have h := (AddCircle.measurePreserving_mk (1:ℝ) a).prod (AddCircle.measurePreserving_mk (1:ℝ) b)
  rw [Measure.prod_restrict] at h
  exact h.lintegral_comp hg

lemma interval_four_cell_cover (x : ℝ) (hx : x ∈ Ioc (-2:ℝ) 2) :
    ∃ j : Fin 4, x ∈ Ioc ((j:ℝ)-2) ((j:ℝ)-2+1) := by
  by_cases h1 : x ≤ -1
  · exact ⟨0,by norm_num at *; exact ⟨hx.1,h1⟩⟩
  by_cases h2 : x ≤ 0
  · exact ⟨1,by norm_num at *; exact ⟨by linarith,h2⟩⟩
  by_cases h3 : x ≤ 1
  · exact ⟨2,by norm_num at *; exact ⟨by linarith,h3⟩⟩
  · exact ⟨3,by norm_num at *; exact ⟨by linarith,hx.2⟩⟩

lemma bounded_lift_integral (g : Torus → ℝ≥0∞) (hg : Measurable g)
    (S : Set (ℝ × ℝ)) (hS : S ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2) :
    (∫⁻ z in S, g (liftProjection z)) ≤ 16*(∫⁻ z, g z ∂area) := by
  let cell : (Fin 4 × Fin 4) → Set (ℝ × ℝ) := fun j =>
    Ioc ((j.1:ℝ)-2) ((j.1:ℝ)-2+1) ×ˢ Ioc ((j.2:ℝ)-2) ((j.2:ℝ)-2+1)
  have hcover : S ⊆ ⋃ j, cell j := by
    intro z hz
    obtain ⟨i,hi⟩ := interval_four_cell_cover z.1 (hS hz).1
    obtain ⟨j,hj⟩ := interval_four_cell_cover z.2 (hS hz).2
    exact mem_iUnion.mpr ⟨(i,j),hi,hj⟩
  calc
    _ ≤ ∫⁻ z in ⋃ j, cell j, g (liftProjection z) := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ z in cell j, g (liftProjection z) := lintegral_iUnion_le _ _
    _ = _ := by simp only [cell,unit_cell_integral g hg,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]; norm_num
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
  funext z
  simp only [Function.comp_apply,standardMap_conjugacy,torusStep_apply]
  rw [recurrenceCoordinates_involutive z]
lemma measurePreserving_torusStep_symm (k : ℝ) : MeasurePreserving (torusStep k).symm area area :=
  (measurePreserving_torusStep k).symm (torusStep_measurableEquiv k)
lemma torusIter_add (k : ℝ) (i j : ℤ) (z : Torus) :
    torusIter k (i+j) z=torusIter k i (torusIter k j z) := by
  simp only [torusIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma measurePreserving_torusIter (k : ℝ) (i : ℤ) : MeasurePreserving (torusIter k i) area area := by
  cases i with
  | ofNat n =>
      change MeasurePreserving (torusIter k (n : ℤ)) area area
      simpa only [torusIter,zpow_natCast,Equiv.Perm.coe_pow] using (measurePreserving_torusStep k).iterate n
  | negSucc n => simpa only [torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using
      (measurePreserving_torusStep_symm k).iterate (n+1)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ClosedEligibility
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
lemma fast_prefix_row (v : ℕ → ℝ) (M : ℝ) (B : ℕ)
    (hB : 2 ≤ B) (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2)
    (hsmall : 3*M^(-(47/50:ℝ)) ≤ 1/4)
    (hv : ∀ i, 1 ≤ i → i ≤ B → |v i|+1 ≤ M)
    (hg : ∀ i, 1 ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ ‖transferProduct v i‖) :
    ∃ J : ℕ, (J=B ∨ J=B+1) ∧ ‖transferProduct v B‖/3 ≤ |tSolution v J| := by
  obtain ⟨s,hu,hver,hs,_⟩:=prefix_stable_vertical v M B (by omega) hM hq hsmall hv hg
  have he : transferProduct v B 1=⟨linearSolution v 0 1 (B+1),linearSolution v 0 1 B⟩ := transferProduct_pair v 0 1 B
  rcases (transferProduct_area v B).eligible_row s hu hver hs with hr|hr
  · refine ⟨B+1,Or.inr rfl,?_⟩
    simpa only [he,tSolution] using hr
  · refine ⟨B,Or.inl rfl,?_⟩
    simpa only [he,tSolution] using hr

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

lemma continuous_transferStep : Continuous transferStep := by
  apply Metric.continuous_iff.mpr
  intro v ε hε
  refine ⟨ε,hε,?_⟩
  intro w hw
  rw [dist_eq_norm]
  exact (transferStep_difference_bound w v).trans_lt (by simpa only [Real.dist_eq] using hw)

lemma continuous_transferProduct_params {α : Type*} [TopologicalSpace α]
    (v : α → ℕ → ℝ) (hv : ∀ n, Continuous (fun x => v x n)) (n : ℕ) :
    Continuous (fun x => transferProduct (v x) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (continuous_transferStep.comp (hv (n+1))).clm_comp ih

lemma continuous_orbitCoefficient_pair (k : ℝ) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => orbitCoefficient k z.1 z.2 n) := by
  have h := continuous_liftedOrbit_pair k n
  unfold orbitCoefficient potential
  exact continuous_const.add (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul h)))

lemma isClosed_prefixEligible (k : ℝ) (B J : ℕ) :
    IsClosed {z : ℝ × ℝ | prefixEligible k B J z} := by
  have hc n := continuous_transferProduct_params (fun z : ℝ × ℝ => orbitCoefficient k z.1 z.2)
    (continuous_orbitCoefficient_pair k) n
  have ht : Continuous (fun z : ℝ × ℝ => tSolution (orbitCoefficient k z.1 z.2) J) := by
    rw [← continuousOn_univ]
    exact continuousOn_linearSolution_params univ (fun z : ℝ × ℝ => orbitCoefficient k z.1 z.2) (fun _ => 0) (fun _ => 1) (fun p => (continuous_orbitCoefficient_pair k p).continuousOn)
      continuousOn_const continuousOn_const J
  simp only [prefixEligible,ofPred_and,ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le continuous_const (hc i).norm
  · exact isClosed_le ((hc B).norm.div_const 3) ht.abs
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TorusObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_cosine : Continuous cosine := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  change Continuous (fun x : ℝ => cosine (x : Circle))
  simpa only [cosine_coe,Function.comp_def,Pi.mul_apply,id_eq] using
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
lemma continuous_torusPotential (k : ℝ) : Continuous (torusPotential k) :=
  continuous_const.add (continuous_const.mul continuous_cosine)
lemma continuous_torusSegmentCoefficient (k : ℝ) (a : ℤ) (i : ℕ) :
    Continuous (fun z => torusSegmentCoefficient k z a i) :=
  (continuous_torusPotential k).comp (continuous_fst.comp (continuous_torusIter k _))
lemma continuous_torusSegmentTransfer (k : ℝ) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusSegmentTransfer k z a n) :=
  continuous_transferProduct_params (fun z i => torusSegmentCoefficient k z a i)
    (fun i => continuous_torusSegmentCoefficient k a i) n
lemma continuous_torusShortfall (k : ℝ) (hk : 0 ≤ k) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusShortfall k z a n) := by
  apply continuous_const.sub
  apply Continuous.div_const
  exact (continuous_torusSegmentTransfer k a n).norm.log
    (fun z => by have := (torusSegmentTransfer_norm_bounds k hk z a n).1; linarith)
lemma torusShortfall_shift (k : ℝ) (z : Torus) (a b : ℤ) (n : ℕ) :
    torusShortfall k (torusIter k b z) a n=torusShortfall k z (a+b) n := by
  have he : torusSegmentCoefficient k (torusIter k b z) a=torusSegmentCoefficient k z (a+b) := by
    funext i
    unfold torusSegmentCoefficient
    rw [← torusIter_add]
    congr 3
    ring
  simp only [torusShortfall,torusSegmentTransfer,he]
lemma shortfall_observation_transport (k : ℝ) (hk : 0 ≤ k) {R : ℕ}
    (a : Fin R → ℤ) (n : Fin R → ℕ) (hn : ∀ i, 0 < n i)
    (F : (Fin R → ℝ) → ℝ) (L : NNReal) (hF : LipschitzWith L F)
    (b : ℤ) (r : ℕ) (hlen : ∀ i, n i ≤ 2*r)
    (hwin : ∀ i j, 1 ≤ j → j ≤ n i → (a i+(j:ℤ)-1-b).natAbs ≤ r)
    (z w : ℝ × ℝ) :
    |F (fun i => torusShortfall k (liftProjection z) (a i) (n i))-
      F (fun i => torusShortfall k (liftProjection w) (a i) (n i))| ≤
    L*(((2*Real.pi*growthBase k)/Real.log (growthBase k))*growthBase k^(3*r)*
        dist (liftIter k b z) (liftIter k b w)) := by
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have hcoeff : 0 ≤ (2*Real.pi*growthBase k)/Real.log (growthBase k) := by
    have := Real.log_pos (by have := growthBase_ge_four k hk; linarith : 1 < growthBase k)
    positivity
  have hd : dist (fun i => torusShortfall k (liftProjection z) (a i) (n i))
      (fun i => torusShortfall k (liftProjection w) (a i) (n i)) ≤
      ((2*Real.pi*growthBase k)/Real.log (growthBase k))*growthBase k^(3*r)*
        dist (liftIter k b z) (liftIter k b w) := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    rw [Real.dist_eq,torusShortfall_lift,torusShortfall_lift]
    apply (liftShortfall_transport k hk z w (a i) b (n i) r (hn i) (hwin i)).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hM (by have := hlen i; omega)) hcoeff) dist_nonneg
  rw [← Real.dist_eq]
  exact (hF.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
lemma continuous_shortfall_observation (k : ℝ) (hk : 0 ≤ k) {R : ℕ}
    (a : Fin R → ℤ) (n : Fin R → ℕ) (F : (Fin R → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun z => F (fun i => torusShortfall k z (a i) (n i))) :=
  hF.comp (continuous_pi (fun i => continuous_torusShortfall k hk (a i) (n i)))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_EndpointTransport
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
lemma graph_endpoint_close (k : ℝ) (hk : 0 ≤ k) (z w : ℝ × ℝ) (n B : ℕ) (hn : 1 ≤ n)
    (hB : B=n ∨ B=n+1)
    (hterm : liftedOrbit k z.2 z.1 (n+1)=liftedOrbit k w.2 w.1 (n+1))
    (hbound : ∀ i : Fin n,
      |liftedOrbit k z.2 z.1 (i+1)-liftedOrbit k w.2 w.1 (i+1)| ≤
        8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) :
    dist (liftIter k (B:ℤ) z) (liftIter k (B:ℤ) w) ≤
      8/growthBase k^((4/5:ℝ)*(B-1:ℕ)) := by
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have hMn : 0 ≤ 8/growthBase k^((4/5:ℝ)*(n:ℝ)) := by positivity
  have hn' : n-1+1=n := by omega
  have hlast := hbound (⟨n-1,by omega⟩ : Fin n)
  have hreal : ((n-1:ℕ):ℝ)+1=n := by exact_mod_cast hn'
  simp only [hn',hreal] at hlast
  have he : dist (liftIter k (B:ℤ) z) (liftIter k (B:ℤ) w) ≤
      8/growthBase k^((4/5:ℝ)*(n:ℝ)) := by
    rcases hB with rfl|rfl
    · rw [liftIter_nat,liftIter_nat,Prod.dist_eq,Real.dist_eq,Real.dist_eq,hterm,sub_self,abs_zero]
      exact max_le hMn hlast
    · rw [liftIter_nat,liftIter_nat,Prod.dist_eq,Real.dist_eq,Real.dist_eq,liftedOrbit_step,
        liftedOrbit_step,hterm,sub_self,abs_zero]
      have he : |phi k (liftedOrbit k w.2 w.1 (n+1))-liftedOrbit k z.2 z.1 n-
          (phi k (liftedOrbit k w.2 w.1 (n+1))-liftedOrbit k w.2 w.1 n)| =
          |liftedOrbit k z.2 z.1 n-liftedOrbit k w.2 w.1 n| := by
        rw [sub_sub_sub_cancel_left,abs_sub_comm]
      rw [he]
      exact max_le hlast hMn
  apply he.trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hM
  have hle : (B-1:ℕ) ≤ n := by rcases hB with rfl|rfl <;> omega
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by norm_num)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_LiftEventMeasure
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measurable_liftProjection : Measurable liftProjection :=
  (((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd)).measurable
lemma bounded_lift_event (A : Set Torus) (V : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hV : MeasurableSet V) (hb : V ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2)
    (hp : ∀ z ∈ V, liftProjection z ∈ A) : volume V ≤ 16*area A := by
  have hh := bounded_lift_integral (A.indicator (fun _ => (1:ℝ≥0∞)))
    (measurable_const.indicator hA) V hb
  have he : (∫⁻ z in V, A.indicator (fun _ => (1:ℝ≥0∞)) (liftProjection z))=volume V := by
    calc
      _ = ∫⁻ z in V, (1:ℝ≥0∞) := setLIntegral_congr_fun hV (fun z hz => indicator_of_mem (hp z hz) _)
      _ = _ := by simp
  rw [he,lintegral_indicator hA] at hh
  simpa using hh
lemma scaled_product_slice_bound (E I : Set ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ≥0∞)
    (d K : ℝ≥0∞) (hd : d ≠ ∞) (hE : MeasurableSet E) (hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I)
    (hslice : ∀ x ∈ E, d*(∫⁻ y in I, T.indicator f (x,y)) ≤ K) :
    d*(∫⁻ z in T, f z) ≤ K*volume E := by
  have hi (z : ℝ × ℝ) : T.indicator (fun w => d*f w) z=d*T.indicator f z := by
    by_cases hz : z ∈ T <;> simp [hz]
  have hh := product_slice_bound E I T (fun z => d*f z) K hE hI hT hsub (by
    intro x hx
    simpa only [hi,lintegral_const_mul' _ _ hd] using hslice x hx)
  simpa only [lintegral_const_mul' _ _ hd] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ScaledChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma scaled_weighted_chart_product (E I : Set ℝ) (T A V : Set (ℝ × ℝ))
    (f : (ℝ × ℝ) → (ℝ × ℝ)) (D : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (g : ℝ × ℝ → ℝ≥0∞) (c C : ℝ) (d K : ℝ≥0∞) (hd : d ≠ ∞)
    (hE : MeasurableSet E) (hI : MeasurableSet I) (hT : MeasurableSet T)
    (hsub : T ⊆ E ×ˢ I) (hA : A ⊆ f '' T) (hV : f '' (E ×ˢ I) ⊆ V)
    (hD : ∀ z ∈ E ×ˢ I, HasFDerivWithinAt f (D z) (E ×ˢ I) z)
    (hinj : InjOn f (E ×ˢ I))
    (hlo : ∀ z ∈ E ×ˢ I, c ≤ |(D z).det|)
    (hhi : ∀ z ∈ E ×ˢ I, |(D z).det| ≤ C)
    (hslice : ∀ x ∈ E, d*(∫⁻ y in I, T.indicator (g ∘ f) (x,y)) ≤ K) :
    (ENNReal.ofReal c*volume I)*d*(∫⁻ z in A, g z) ≤
      ENNReal.ofReal C*K*volume V := by
  have hw := (weighted_image_bounds volume T f D c C g hT
    (fun z hz => (hD z (hsub hz)).mono hsub) (hinj.mono hsub)
    (fun z hz => hlo z (hsub hz)) (fun z hz => hhi z (hsub hz))).2
  have hf : d*(∫⁻ z in A, g z) ≤ ENNReal.ofReal C*(K*volume E) := by
    calc
      _ ≤ d*(ENNReal.ofReal C*(∫⁻ z in T, g (f z))) :=
        mul_le_mul_of_nonneg_left ((lintegral_mono_set hA).trans hw) (by positivity)
      _ = ENNReal.ofReal C*(d*(∫⁻ z in T, g (f z))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (scaled_product_slice_bound E I T (g ∘ f) d K hd hE hI hT hsub hslice) (by positivity)
  have hl := (measure_image_bounds volume (E ×ˢ I) f D c C (hE.prod hI) hD hinj hlo hhi).1
  have hv : (ENNReal.ofReal c*volume I)*volume E ≤ volume V := by
    calc
      _ = ENNReal.ofReal c*volume (E ×ˢ I) := by
        change _ = ENNReal.ofReal c*(volume.prod volume) (E ×ˢ I)
        rw [Measure.prod_prod]; ac_rfl
      _ ≤ volume (f '' (E ×ˢ I)) := hl
      _ ≤ volume V := measure_mono hV
  calc
    _ = (ENNReal.ofReal c*volume I)*(d*(∫⁻ z in A, g z)) := by ring
    _ ≤ (ENNReal.ofReal c*volume I)*(ENNReal.ofReal C*(K*volume E)) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ = (ENNReal.ofReal C*K)*((ENNReal.ofReal c*volume I)*volume E) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_BackwardSlice
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_liftProjection : Continuous liftProjection :=
  (((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd))
lemma interval_small_move (y y' : ℝ) (hy : y ∈ Icc (0:ℝ) 1) (hmove : |y'-y| ≤ 1) :
    y' ∈ Ioc (-2:ℝ) 2 := by
  have hh := abs_le.mp hmove
  constructor <;> linarith [hy.1,hy.2,hh.1,hh.2]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CocycleAlgebra
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma transferProduct_concat (v : ℕ → ℝ) (m n : ℕ) :
    transferProduct v (m+n)=(transferProduct (fun i => v (m+i)) n).comp (transferProduct v m) := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
    rw [show m+(n+1)=(m+n)+1 by omega,transferProduct,ih,transferProduct]
    simp only [ContinuousLinearMap.comp_assoc,Nat.add_assoc]
lemma torusSegmentCoefficient_shift (k : ℝ) (z : Torus) (a : ℤ) (m : ℕ) :
    (fun i => torusSegmentCoefficient k z a (m+i))=torusSegmentCoefficient k z (a+(m:ℤ)) := by
  funext i
  unfold torusSegmentCoefficient
  congr 3
  push_cast
  ring
lemma torusSegmentTransfer_concat (k : ℝ) (z : Torus) (a : ℤ) (m n : ℕ) :
    torusSegmentTransfer k z a (m+n)=
      (torusSegmentTransfer k z (a+(m:ℤ)) n).comp (torusSegmentTransfer k z a m) := by
  unfold torusSegmentTransfer
  rw [transferProduct_concat,torusSegmentCoefficient_shift]
lemma torusSegmentTransfer_shift (k : ℝ) (z : Torus) (a b : ℤ) (n : ℕ) :
    torusSegmentTransfer k (torusIter k b z) a n=torusSegmentTransfer k z (a+b) n := by
  unfold torusSegmentTransfer
  congr 1
  funext i
  unfold torusSegmentCoefficient
  rw [← torusIter_add]
  congr 3
  ring
lemma torusIter_neg_swap (k : ℝ) (n : ℕ) (z : Torus) :
    torusIter k (-(n:ℤ)) z=(torusIter k (n:ℤ) z.swap).swap := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ((n+1:ℕ):ℤ)=1+(n:ℤ) by omega,show -(1+(n:ℤ))=(-1)+(-(n:ℤ)) by ring,
      torusIter_add,torusIter_add,ih]
    simp only [torusIter,zpow_neg_one,zpow_one,Equiv.Perm.inv_def,torusStep_symm_apply,torusStep_apply,
      recurrenceMap,Prod.fst_swap,Prod.snd_swap,Prod.swap_prod_mk]
lemma norm_comp_planeSwap (A : ℂ →L[ℝ] ℂ) : ‖A.comp planeSwap‖=‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,norm_planeSwap] using A.le_opNorm (planeSwap z)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,planeSwap_invol,norm_planeSwap] using
      (A.comp planeSwap).le_opNorm (planeSwap z)
lemma norm_planeSwap_comp (A : ℂ →L[ℝ] ℂ) : ‖planeSwap.comp A‖=‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,norm_planeSwap] using A.le_opNorm z
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,norm_planeSwap] using (planeSwap.comp A).le_opNorm z
lemma torus_backward_pair_coordinate (k : ℝ) (z : Torus) (n : ℕ) :
    (torusIter k (-(n:ℤ)-1) z).1=(torusIter k (n:ℤ) z.swap).1 := by
  rw [show -(n:ℤ)-1=(-1)+(-(n:ℤ)) by ring,torusIter_add,torusIter_neg_swap]
  rfl
lemma torusSegmentTransfer_reverse_identity (k : ℝ) (z : Torus) (n : ℕ) (u : ℂ) :
    torusSegmentTransfer k z (-(n:ℤ)) n
      (planeSwap (torusSegmentTransfer k z.swap 0 n (planeSwap u)))=u := by
  induction n generalizing u with
  | zero => simp [torusSegmentTransfer,transferProduct]
  | succ n ih =>
    have hc : torusSegmentTransfer k z (-((n+1:ℕ):ℤ)) (n+1)=
        (torusSegmentTransfer k z (-(n:ℤ)) n).comp
          (transferStep (torusPotential k (torusIter k (-(n:ℤ)-1) z).1)) := by
      rw [show n+1=1+n by omega,torusSegmentTransfer_concat]
      congr 1
      · congr 1; push_cast; ring
      · simp only [torusSegmentTransfer,transferProduct,ContinuousLinearMap.comp_id,
          torusSegmentCoefficient]
        exact congrArg (fun t : ℤ => transferStep (torusPotential k (torusIter k t z).1)) (by omega)
    rw [hc]
    change torusSegmentTransfer k z (-(n:ℤ)) n
      (transferStep (torusPotential k (torusIter k (-(n:ℤ)-1) z).1)
        (planeSwap (transferStep (torusSegmentCoefficient k z.swap 0 (n+1))
          (torusSegmentTransfer k z.swap 0 n (planeSwap u)))))=u
    have hcoef : torusSegmentCoefficient k z.swap 0 (n+1)=
        torusPotential k (torusIter k (-(n:ℤ)-1) z).1 := by
      unfold torusSegmentCoefficient
      rw [show (0:ℤ)+((n+1:ℕ):ℤ)-1=(n:ℤ) by omega,torus_backward_pair_coordinate]
    rw [hcoef]
    have he (v : ℝ) (w : ℂ) : transferStep v (planeSwap (transferStep v w))=planeSwap w := by
      apply Complex.ext <;> simp
    rw [he]
    exact ih u
lemma torusSegmentTransfer_reverse_norm (k : ℝ) (z : Torus) (n : ℕ) :
    ‖torusSegmentTransfer k z.swap 0 n‖=‖torusSegmentTransfer k z (-(n:ℤ)) n‖ := by
  let A := torusSegmentTransfer k z (-(n:ℤ)) n
  let B := (planeSwap.comp (torusSegmentTransfer k z.swap 0 n)).comp planeSwap
  have hAB : ∀ u, A (B u)=u := torusSegmentTransfer_reverse_identity k z n
  have he : B=transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n := by
    ext u
    apply (show Function.Injective A from fun x y hxy => by
      have := congrArg (transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n) hxy
      simpa only [A,torusSegmentTransfer,transferProductInv_inverse] using this)
    rw [hAB]
    exact (transferProduct_inverse _ _ _).symm
  have hnorm : ‖B‖=‖torusSegmentTransfer k z.swap 0 n‖ := by
    dsimp only [B]
    rw [norm_comp_planeSwap,norm_planeSwap_comp]
  rw [← hnorm,he,← transferProduct_norm_inverse]
  rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_MiddleCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy

lemma bridgeMiddle_bounds (N i : ℕ) (hN : 100 ≤ N) (hi : i∈bridgeMiddle N) :
    2 ≤ i ∧ 2 ≤ N-i ∧ (N:ℝ)/3-1 ≤ (i:ℝ) ∧ (N:ℝ)/3-1 ≤ (N-i:ℕ) ∧ i ≤ N := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hi
  have hdiv := Nat.mod_lt N (by norm_num : 0 < 3)
  have hdiv' := Nat.mod_lt (2*N) (by norm_num : 0 < 3)
  have he := Nat.mod_add_div N 3
  have he' := Nat.mod_add_div (2*N) 3
  have h1 : 2 ≤ i := by omega
  have h2 : 2 ≤ N-i := by omega
  have h3 : N ≤ 3*i+2 := by omega
  have h4 : N ≤ 3*(N-i)+2 := by omega
  refine ⟨h1,h2,?_,?_,by omega⟩
  · have : (N:ℝ) ≤ 3*(i:ℝ)+2 := by exact_mod_cast h3
    linarith
  · have : (N:ℝ) ≤ 3*(N-i:ℕ)+2 := by exact_mod_cast h4
    linarith
lemma shortfall_count_sample (z : ℕ → ℝ) (c : ℝ) (hc : c < 1) (N : ℕ)
    (hz : ∀ j < N, z (j+1)-z j ≤ 1) (S : Finset ℕ)
    (hS : ∀ j∈S, 1 ≤ j ∧ j ≤ N ∧ ∃ l < j, z j-z l < c*((j:ℝ)-(l:ℝ))) :
    (S.card:ℝ) ≤ ((N:ℝ)-(z N-z 0))/(1-c) := by
  classical
  let D := (Finset.range N).filter fun j => ∃ l < j+1, z (j+1)-z l < c*((j+1:ℕ)-(l:ℝ))
  have hcard : S.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn (fun j => j-1)
    · intro j hj
      obtain ⟨hj1,hjN,l,hl,hbad⟩ := hS j hj
      change j-1∈D
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega),l,by omega,?_⟩
      simpa only [Nat.sub_add_cancel hj1] using hbad
    · intro i hi j hj he
      have := (hS i hi).1
      have := (hS j hj).1
      dsimp only at he
      omega
  exact (Nat.cast_le.mpr hcard).trans (shortfall_count z c hc N hz)
lemma middle_log_good_count (z : ℕ → ℝ) (N : ℕ) (hN : 100 ≤ N)
    (hz : ∀ j < N, z (j+1)-z j ≤ 1)
    (htotal : (999/1000:ℝ)*(N:ℝ) ≤ z N-z 0) :
    (N:ℝ)/5 ≤ (bridgeMiddleGood z N).card := by
  classical
  change (N:ℝ)/5 ≤ ((bridgeMiddle N).filter (MiddleLogGood z N)).card
  let S := bridgeMiddle N
  let E := S.filter fun i => ∃ j < i, z i-z j < (49/50:ℝ)*((i:ℝ)-(j:ℝ))
  let F := S.filter fun i => ∃ j, i < j ∧ j ≤ N ∧ z j-z i < (49/50:ℝ)*((j:ℝ)-(i:ℝ))
  let zr : ℕ → ℝ := fun j => z N-z (N-j)
  have hE : (E.card:ℝ) ≤ ((N:ℝ)-(z N-z 0))/(1-(49/50:ℝ)) := by
    apply shortfall_count_sample z (49/50) (by norm_num) N hz E
    intro i hi
    obtain ⟨hi,hb⟩ := Finset.mem_filter.mp hi
    have hh := bridgeMiddle_bounds N i hN hi
    exact ⟨by omega,hh.2.2.2.2,hb⟩
  have hzr : ∀ j < N, zr (j+1)-zr j ≤ 1 := by
    intro j hj
    have hh := hz (N-j-1) (by omega)
    have he : N-j-1+1=N-j := by omega
    have he' : N-(j+1)=N-j-1 := by omega
    dsimp [zr]
    rw [he] at hh
    rw [he']
    linarith
  have hF : (F.card:ℝ) ≤ ((N:ℝ)-(z N-z 0))/(1-(49/50:ℝ)) := by
    let D := F.image (fun i => N-i)
    have hinj : Set.InjOn (fun i => N-i) (↑F : Set ℕ) := by
      intro i hi j hj he
      dsimp only at he
      have hiN := (bridgeMiddle_bounds N i hN (Finset.mem_filter.mp hi).1).2.2.2.2
      have hjN := (bridgeMiddle_bounds N j hN (Finset.mem_filter.mp hj).1).2.2.2.2
      omega
    have hcD : D.card=F.card := Finset.card_image_of_injOn hinj
    have hh := shortfall_count_sample zr (49/50) (by norm_num) N hzr D (by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hi,l,hil,hlN,hbad⟩ := Finset.mem_filter.mp hi
      have hiN := (bridgeMiddle_bounds N i hN hi).2.2.2.2
      have hi2 := (bridgeMiddle_bounds N i hN hi).2.1
      refine ⟨by omega,by omega,N-l,by omega,?_⟩
      dsimp [zr]
      rw [Nat.sub_sub_self hiN,Nat.sub_sub_self hlN,Nat.cast_sub hiN,Nat.cast_sub hlN]
      linarith)
    rw [hcD] at hh
    simpa [zr] using hh
  have hbad : S.filter (fun i => ¬MiddleLogGood z N i)=E∪F := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_union,MiddleLogGood,E,F,not_and_or,not_forall,not_le,exists_prop]
    exact and_or_left
  norm_num at hE hF
  have hcardE : (E.card:ℝ) ≤ (N:ℝ)/20 := by linarith
  have hcardF : (F.card:ℝ) ≤ (N:ℝ)/20 := by linarith
  have hcardbad : ((S.filter (fun i => ¬MiddleLogGood z N i)).card:ℝ) ≤ (N:ℝ)/10 := by
    rw [hbad]
    have hh : ((E∪F).card:ℝ) ≤ (E.card:ℝ)+(F.card:ℝ) := by exact_mod_cast Finset.card_union_le E F
    linarith
  have hScard : (N:ℝ)/3-2 ≤ (S.card:ℝ) := by
    have he : S.card=2*N/3-N/3 := by simp [S,bridgeMiddle,Nat.card_Icc]
    rw [he]
    have hx : N ≤ 3*(2*N/3-N/3)+6 := by omega
    have hx' : (N:ℝ) ≤ 3*(2*N/3-N/3:ℕ)+6 := by exact_mod_cast hx
    linarith
  have hpartition : ((S.filter (MiddleLogGood z N)).card:ℝ)+
      ((S.filter (fun i => ¬MiddleLogGood z N i)).card:ℝ)=(S.card:ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=S) (p:=MiddleLogGood z N)
  have hNN : (100:ℝ) ≤ N := by exact_mod_cast hN
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ForwardChart
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
lemma forward_chart_jacobian (k : ℝ) (n : ℕ) (E I : Set ℝ) (X : ℝ × ℝ → ℝ) (yc : ℝ)
    (hX : ContinuousOn X (E ×ˢ I))
    (hlevel : ∀ s ∈ E, ∀ y ∈ I,
      liftedOrbit k y (X (s,y)) (n+1)=liftedOrbit k yc s (n+1))
    (ht : ∀ s ∈ E, ∀ y ∈ I, tSolution (orbitCoefficient k y (X (s,y))) (n+1) ≠ 0)
    (hr : ∀ s ∈ E, ∀ y ∈ I,
      Real.exp (-1152*Real.pi) ≤ |tSolution (orbitCoefficient k yc s) (n+1)|/
        |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ∧
      |tSolution (orbitCoefficient k yc s) (n+1)|/
        |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ≤ Real.exp (1152*Real.pi)) :
    ∃ J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      (∀ z ∈ E ×ˢ I, HasFDerivWithinAt (fun w => (X w,w.2)) (J z) (E ×ˢ I) z) ∧
      (∀ z ∈ E ×ˢ I, Real.exp (-1152*Real.pi) ≤ |(J z).det| ∧
        |(J z).det| ≤ Real.exp (1152*Real.pi)) := by
  let J := fun z : ℝ × ℝ => planeMatrix
    (tSolution (orbitCoefficient k yc z.1) (n+1)/tSolution (orbitCoefficient k z.2 (X z)) (n+1))
    (-sSolution (orbitCoefficient k z.2 (X z)) (n+1)/tSolution (orbitCoefficient k z.2 (X z)) (n+1)) 0 1
  refine ⟨J,?_,?_⟩
  · intro z hz
    apply label_graph_derivative (fun v : ℝ × ℝ => liftedOrbit k v.2 v.1 (n+1)) X (E ×ˢ I) z yc _ _ _ _
      (hasStrictFDerivAt_liftedOrbit_swap k (X z) z.2 (n+1))
      (hasStrictFDerivAt_liftedOrbit_swap k z.1 yc (n+1)) (ht z.1 hz.1 z.2 hz.2) (hX z hz)
      _ (hlevel z.1 hz.1 z.2 hz.2)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hlevel w.1 hw.1 w.2 hw.2
  · intro z hz
    simpa only [J,planeMatrix_det,mul_one,mul_zero,sub_zero,abs_div] using hr z.1 hz.1 z.2 hz.2
lemma forward_graph_lipschitz (I : Set ℝ) (X d : ℝ → ℝ) (a : ℝ)
    (hI : Convex ℝ I) (hd : ∀ y ∈ I, HasDerivAt X (d y) y)
    (hb : ∀ y ∈ I, |d y| ≤ a) (y z : ℝ) (hy : y ∈ I) (hz : z ∈ I) :
    |X y-X z| ≤ a*|y-z| := by
  have hh := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hd y hy).hasDerivWithinAt) (by intro y hy; simpa [Real.norm_eq_abs] using hb y hy) hz hy
  simpa only [Real.norm_eq_abs] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_BridgeScalars
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
lemma BridgeScalarControl.prefix_dirichlet {k : ℝ} (h : BridgeScalarControl k)
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

section
-- module Solutions.OAIQ2_Std.StandardMap_LocalSquareBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma actual_local_square_product (k : ℝ) (hc : BridgeScalarControl k)
    (np nm Bp Bm : ℕ) (hnp : 1 ≤ np) (hnm : 1 ≤ nm)
    (hBp : Bp=np ∨ Bp=np+1) (hBm : Bm=nm ∨ Bm=nm+1) (hBp2 : 2 ≤ Bp) (hBm2 : 2 ≤ Bm)
    (lx ux ly uy : ℝ) (hly : ly ≤ uy) (hlxlen : ux-lx < 1/4) (hlylen : uy-ly < 1/4)
    (hIx : Icc lx ux ⊆ Icc (0:ℝ) 1) (hIy : Icc ly uy ⊆ Icc (0:ℝ) 1)
    (W H : Torus → ℝ) (hW : Continuous W) (hH : Continuous H) (hW0 : ∀ z, 0 ≤ W z)
    (h δ : ℝ) (hδ : 0 ≤ δ) (hδh : δ < h/2)
    (hWp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(Bm:ℤ)) z) (liftIter k (-(Bm:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bm-1:ℕ)) → |W (liftProjection z)-W (liftProjection w)| ≤ δ)
    (hHp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (Bp:ℤ) z) (liftIter k (Bp:ℤ) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bp-1:ℕ)) → |H (liftProjection z)-H (liftProjection w)| ≤ δ) :
    (ENNReal.ofReal (Real.exp (-1152*Real.pi))*volume (Icc ly uy))*
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc lx ux))*
      (∫⁻ z in {z : ℝ × ℝ | z ∈ Icc lx ux ×ˢ Icc ly uy ∧
        prefixEligible k Bp (np+1) z.swap ∧ prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)},
        ENNReal.ofReal (W (liftProjection z))) ≤
    ENNReal.ofReal (Real.exp (1152*Real.pi))*
      (16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
        (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc lx ux))*
          ENNReal.ofReal δ*volume (Icc ly uy))*
      (16*area {z | h/2 < H z}) := by
  classical
  let Ix := Icc lx ux
  let Iy := Icc ly uy
  let square := Ix ×ˢ Iy
  let S : Set (ℝ × ℝ) := (Iy ×ˢ Ix) ∩
    {z | prefixEligible k Bp (np+1) z ∧ h ≤ H (liftProjection z.swap)}
  have hS : IsCompact S := by
    apply (isCompact_Icc.prod isCompact_Icc).inter_right
    exact (isClosed_prefixEligible k Bp (np+1)).inter
      (isClosed_le continuous_const (hH.comp (continuous_liftProjection.comp continuous_swap)))
  have hdir (z : ℝ × ℝ) (hz : z ∈ S) := hc.prefix_dirichlet Bp np hnp hBp hBp2 z hz.2.1
  obtain ⟨E,X,hE,hX,hXbase,hcover,hinj,hreg,hrep⟩ := actual_compact_graph_labels_full k np hnp
    hc.nonneg hc.graph_geom hc.graph_small S hS (fun z hz => (hdir z hz).1)
    (fun z hz => (hdir z hz).2) ly uy ly ⟨le_rfl,hly⟩ hlylen (fun z hz => hz.1.1)
  let f : (ℝ × ℝ) → (ℝ × ℝ) := fun z => (X z,z.2)
  have hfc : ContinuousOn f (E ×ˢ Iy) := hX.prodMk continuous_snd.continuousOn
  obtain ⟨J,hJ,hdet⟩ := forward_chart_jacobian k np E Iy X ly hX
    (fun s hs y hy => (hreg s hs y hy).1)
    (fun s hs y hy => (hreg s hs y hy).2.1)
    (fun s hs y hy => (hreg s hs y hy).2.2.2.2)
  let V := f '' (E ×ˢ Iy)
  have hV : IsCompact V := (hE.prod isCompact_Icc).image_of_continuousOn hfc
  have hVH : ∀ z ∈ V, liftProjection z ∈ {z | h/2 < H z} := by
    rintro z ⟨v,hv,rfl⟩
    obtain ⟨w,hw,hwX⟩ := hrep v.1 hv.1
    have hh := graph_endpoint_close k hc.nonneg (f v) w.swap np Bp hnp hBp
      (hwX v.2 hv.2).1 (hwX v.2 hv.2).2.2
    have htpt := hHp (f v) w.swap hh
    have hth := hw.2.2
    change h/2 < H (liftProjection (f v))
    have hab := (abs_le.mp htpt).1
    linarith
  have hVb : V ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2 := by
    rintro z ⟨v,hv,rfl⟩
    obtain ⟨w,hw,hwX⟩ := hrep v.1 hv.1
    have hy := hIy hv.2
    have hyw := hIy hw.1.1
    have hxw := hIx hw.1.2
    have hd : |v.2-w.1| ≤ 1 := by apply abs_le.mpr; constructor <;> linarith [hy.1,hy.2,hyw.1,hyw.2]
    have hmove := (hwX v.2 hv.2).2.1
    have ha0 : 0 ≤ 24/growthBase k^((4/5:ℝ)) := by
      have hp : 0 < growthBase k := by have := growthBase_ge_four k hc.nonneg; linarith
      positivity
    refine ⟨interval_small_move w.2 (X v) hxw (hmove.trans ?_),⟨by linarith [hy.1],by linarith [hy.2]⟩⟩
    nlinarith [hc.slope_small,abs_nonneg (v.2-w.1)]
  have hVm : volume V ≤ 16*area {z | h/2 < H z} :=
    bounded_lift_event _ V (isOpen_lt continuous_const hH).measurableSet hV.measurableSet hVb hVH
  let U : Set (ℝ × ℝ) := square ∩ {z | prefixEligible k Bm (nm+1) z}
  have hUcl : IsClosed U := (isClosed_Icc.prod isClosed_Icc).inter (isClosed_prefixEligible k Bm (nm+1))
  let T := (E ×ˢ Iy) ∩ f ⁻¹' U
  have hTcl : IsClosed T := hfc.preimage_isClosed_of_isClosed (hE.isClosed.prod isClosed_Icc) hUcl
  let A := {z : ℝ × ℝ | z ∈ square ∧ prefixEligible k Bp (np+1) z.swap ∧
    prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)}
  have hA : A ⊆ f '' T := by
    intro z hz
    have hzS : z.swap ∈ S := ⟨⟨hz.1.2,hz.1.1⟩,hz.2.1,by simpa only [Prod.swap_swap] using hz.2.2.2.le⟩
    obtain ⟨s,hs,hxs⟩ := hcover z.swap hzS
    change X (s,z.2)=z.1 at hxs
    refine ⟨(s,z.2),⟨⟨hs,hz.1.2⟩,?_⟩,?_⟩
    · change (X (s,z.2),z.2) ∈ U
      rw [hxs]
      exact ⟨hz.1,hz.2.2.1⟩
    · exact Prod.ext hxs rfl
  let c := Real.exp (-1152*Real.pi)
  let C := Real.exp (1152*Real.pi)
  let d := ENNReal.ofReal (c*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume Ix
  let K := 16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+d*ENNReal.ofReal δ*volume Iy
  have hslice (s : ℝ) (hs : s ∈ E) : d*(∫⁻ y in Iy, T.indicator ((fun z => ENNReal.ofReal (W (liftProjection z))) ∘ f) (s,y)) ≤ K := by
    let Xs : ℝ → ℝ := fun y => X (s,y)
    let Xs' : ℝ → ℝ := fun y => boundaryValue (orbitCoefficient k y (Xs y)) (np+1)
    let D : Set ℝ := Iy ∩ (fun y => (Xs y,y)) ⁻¹' U
    have hXs : ContinuousOn Xs Iy := hX.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨hs,hy⟩)
    have hDc : IsClosed D := (hXs.prodMk continuousOn_id).preimage_isClosed_of_isClosed isClosed_Icc hUcl
    have hxi (y : ℝ) (hy : y ∈ D) : Xs y ∈ Ix := hy.2.1.1
    have hxd (y : ℝ) (hy : y ∈ Iy) : HasStrictDerivAt Xs (Xs' y) y := (hreg s hs y hy).2.2.1
    have hxS (y : ℝ) (hy : y ∈ Iy) : |Xs' y| ≤ 24/growthBase k^((4/5:ℝ)) := (hreg s hs y hy).2.2.2.1
    have hxL (y : ℝ) (hy : y ∈ D) (z : ℝ) (hz : z ∈ D) :
        |Xs y-Xs z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z| :=
      forward_graph_lipschitz Iy Xs Xs' _ (convex_Icc ly uy)
        (fun y hy => (hxd y hy).hasDerivAt) hxS y z hy.1 hz.1
    have hdirD (y : ℝ) (hy : y ∈ D) := hc.prefix_dirichlet Bm nm hnm hBm hBm2 (Xs y,y) hy.2.2
    have hb := actual_backward_slice k nm Bm hnm hBm hc.nonneg hc.graph_geom hc.graph_small hc.slope_small
      D hDc.measurableSet Xs Xs' lx ux hlxlen hIx (fun y hy => hIy hy.1)
      hxi (fun y hy => hxd y hy.1) (fun y hy => hxS y hy.1) hxL
      (fun y hy => (hdirD y hy).1) (fun y hy => (hdirD y hy).2) W hW hW0 δ hδ hWp
    have he : (fun y => T.indicator ((fun z => ENNReal.ofReal (W (liftProjection z))) ∘ f) (s,y)) =
        D.indicator (fun y => ENNReal.ofReal (W (liftProjection (Xs y,y)))) := by
      funext y
      by_cases hy : y ∈ D
      · have ht : (s,y) ∈ T := ⟨⟨hs,hy.1⟩,hy.2⟩
        simp only [indicator_of_mem ht,indicator_of_mem hy,Function.comp_apply,f,Xs]
      · have ht : (s,y) ∉ T := fun ht => hy ⟨ht.1.2,ht.2⟩
        simp only [indicator_of_notMem ht,indicator_of_notMem hy]
    rw [he,setLIntegral_indicator hDc.measurableSet,inter_eq_left.mpr (show D ⊆ Iy from inter_subset_left)]
    apply hb.trans
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (measure_mono (show D ⊆ Iy from inter_subset_left)) (by positivity)
  have hb := scaled_weighted_chart_product E Iy T A V f J
    (fun z => ENNReal.ofReal (W (liftProjection z))) c C d K
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ)))))
    hE.measurableSet measurableSet_Icc hTcl.measurableSet inter_subset_left hA Subset.rfl
    hJ hinj (fun z hz => (hdet z hz).1) (fun z hz => (hdet z hz).2) hslice
  exact hb.trans (mul_le_mul_of_nonneg_left hVm (by positivity))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_GridBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma bridgeGrid_length (i : Fin 32) : bridgeGridHi i-bridgeGridLo i=1/32 := by
  unfold bridgeGridHi bridgeGridLo; ring
lemma bridgeGrid_order (i : Fin 32) : bridgeGridLo i ≤ bridgeGridHi i := by
  have := bridgeGrid_length i; linarith
lemma bridgeGrid_subset (i : Fin 32) : bridgeGridCell i ⊆ Icc (0:ℝ) 1 := by
  intro x hx
  have hi0 : (0:ℝ) ≤ i := by positivity
  have hi1 : (i:ℝ) < 32 := by exact_mod_cast i.isLt
  change (i:ℝ)/32 ≤ x ∧ x ≤ ((i:ℝ)+1)/32 at hx
  have hi2 : (i:ℝ) ≤ 31 := by exact_mod_cast (show (i:ℕ) ≤ 31 by omega)
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
lemma bridgeGrid_volume (i : Fin 32) : volume (bridgeGridCell i)=(1/32 : ℝ≥0∞) := by
  rw [bridgeGridCell,Real.volume_Icc,bridgeGrid_length,ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num
lemma bridgeGrid_cover (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ∃ i : Fin 32, x ∈ bridgeGridCell i := by
  let q := ⌊32*x⌋₊
  have hq0 : (q:ℝ) ≤ 32*x := Nat.floor_le (by linarith [hx.1])
  have hq1 : 32*x < (q:ℝ)+1 := Nat.lt_floor_add_one _
  by_cases hq : q < 32
  · refine ⟨⟨q,hq⟩,?_⟩
    change (q:ℝ)/32 ≤ x ∧ x ≤ ((q:ℝ)+1)/32
    constructor <;> linarith
  · have hq2 : (32:ℝ) ≤ q := by exact_mod_cast (show 32 ≤ q by omega)
    refine ⟨31,?_⟩
    change (31:ℝ)/32 ≤ x ∧ x ≤ (31+1:ℝ)/32
    constructor <;> linarith [hx.2]
lemma bridgeAreaScale_pos : 0 < bridgeAreaScale := by
  unfold bridgeAreaScale
  have hs : (0:ℝ≥0∞) < 1/32 := by norm_num
  positivity
lemma bridgeAreaScale_ne_top : bridgeAreaScale ≠ ∞ := by
  unfold bridgeAreaScale
  finiteness
lemma actual_grid_square_product (k : ℝ) (hc : BridgeScalarControl k)
    (np nm Bp Bm : ℕ) (hnp : 1 ≤ np) (hnm : 1 ≤ nm)
    (hBp : Bp=np ∨ Bp=np+1) (hBm : Bm=nm ∨ Bm=nm+1) (hBp2 : 2 ≤ Bp) (hBm2 : 2 ≤ Bm)
    (ix iy : Fin 32)
    (W H : Torus → ℝ) (hW : Continuous W) (hH : Continuous H) (hW0 : ∀ z, 0 ≤ W z)
    (h δ : ℝ) (hδ : 0 ≤ δ) (hδh : δ < h/2)
    (hWp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(Bm:ℤ)) z) (liftIter k (-(Bm:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bm-1:ℕ)) → |W (liftProjection z)-W (liftProjection w)| ≤ δ)
    (hHp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (Bp:ℤ) z) (liftIter k (Bp:ℤ) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bp-1:ℕ)) → |H (liftProjection z)-H (liftProjection w)| ≤ δ) :
    bridgeAreaScale *
      (∫⁻ z in {z : ℝ × ℝ | z ∈ bridgeGridCell ix ×ˢ bridgeGridCell iy ∧
        prefixEligible k Bp (np+1) z.swap ∧ prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)},
        ENNReal.ofReal (W (liftProjection z))) ≤
    bridgeLocalConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*area {z | h/2 < H z} := by
  have hh := actual_local_square_product k hc np nm Bp Bm hnp hnm hBp hBm hBp2 hBm2
    (bridgeGridLo ix) (bridgeGridHi ix) (bridgeGridLo iy) (bridgeGridHi iy)
    (bridgeGrid_order iy) (by rw [bridgeGrid_length]; norm_num) (by rw [bridgeGrid_length]; norm_num)
    (bridgeGrid_subset ix) (bridgeGrid_subset iy) W H hW hH hW0 h δ hδ hδh hWp hHp
  change (ENNReal.ofReal (Real.exp (-1152*Real.pi))*volume (bridgeGridCell iy))*
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (bridgeGridCell ix))*_ ≤
    ENNReal.ofReal (Real.exp (1152*Real.pi))*(16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (bridgeGridCell ix))*
        ENNReal.ofReal δ*volume (bridgeGridCell iy))*(16*area {z | h/2 < H z}) at hh
  rw [bridgeGrid_volume,bridgeGrid_volume] at hh
  have hMp : 0 < growthBase k := by have := growthBase_ge_four k hc.nonneg; linarith
  have ha0 : 0 ≤ 24/growthBase k^((4/5:ℝ)) := by positivity
  have ha2 : (24/growthBase k^((4/5:ℝ)))^2 ≤ 1/4 := by nlinarith [hc.slope_small]
  have hl : Real.exp (-1152*Real.pi)*(3/4) ≤ Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hu : ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2)) ≤ 1 := by
    apply (ENNReal.ofReal_le_one).mpr
    have hc1 : Real.exp (-1152*Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (by have := Real.pi_pos; linarith)
    calc
      _ ≤ Real.exp (-1152*Real.pi)*1 := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (24/growthBase k^((4/5:ℝ)))]) (Real.exp_pos _).le
      _ ≤ 1 := by simpa using hc1
  have hs : (1/32:ℝ≥0∞) ≤ 1 := by norm_num
  apply le_trans (mul_le_mul_of_nonneg_right (show bridgeAreaScale ≤
      (ENNReal.ofReal (Real.exp (-1152*Real.pi))*(1/32))*
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*(1/32)) from by
        unfold bridgeAreaScale; gcongr) (by positivity))
  apply hh.trans
  have he : (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*(1/32))*
       ENNReal.ofReal δ*(1/32) ≤ ENNReal.ofReal δ := by
    calc
      _ ≤ (1*1)*ENNReal.ofReal δ*1 := by gcongr
      _ = _ := by simp
  calc
    _ ≤ ENNReal.ofReal (Real.exp (1152*Real.pi))*(16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*(16*area {z | h/2 < H z}) := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp (1152*Real.pi))*(16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+16*ENNReal.ofReal δ)*(16*area {z | h/2 < H z}) := by gcongr; exact le_mul_of_one_le_left bot_le (by norm_num)
    _ = _ := by unfold bridgeLocalConstant; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ObservationExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma bridge_observation_exponent (N r B : ℕ) (hN : 100 ≤ N)
    (hr : (r:ℝ) ≤ (N:ℝ)/1000) (hB : (N:ℝ)/3-1 ≤ (B:ℝ)) (hB1 : 1 ≤ B) :
    2+(3*r:ℕ)-(4/5:ℝ)*(B-1:ℕ) ≤ -(1/10:ℝ)*(N:ℝ) := by
  have hBc : ((B-1:ℕ):ℝ)=(B:ℝ)-1 := by rw [Nat.cast_sub hB1]; norm_num
  rw [hBc,Nat.cast_mul,Nat.cast_ofNat]
  have hc : (100:ℝ) ≤ N := by exact_mod_cast hN
  linarith
lemma bridge_observation_scalar (M L : ℝ) (hM : 1 ≤ M) (hlog : 1 ≤ Real.log M)
    (hL : 0 ≤ L) (hLM : 16*Real.pi*L ≤ M)
    (N r B : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    (hB : (N:ℝ)/3-1 ≤ (B:ℝ)) (hB1 : 1 ≤ B) :
    L*(((2*Real.pi*M)/Real.log M)*M^(3*r)*(8/M^((4/5:ℝ)*(B-1:ℕ)))) ≤
      M^(-(1/10:ℝ)*(N:ℝ)) := by
  have hMp : 0 < M := by linarith
  have hlogp : 0 < Real.log M := by linarith
  have hden : 0 < M^((4/5:ℝ)*(B-1:ℕ)) := Real.rpow_pos_of_pos hMp _
  have hco : L*(2*Real.pi*M/Real.log M)*8 ≤ M^2 := by
    have hdiv : 2*Real.pi*M/Real.log M ≤ 2*Real.pi*M :=
      div_le_self (by positivity) hlog
    calc
      _ ≤ L*(2*Real.pi*M)*8 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv hL) (by norm_num)
      _ = (16*Real.pi*L)*M := by ring
      _ ≤ M*M := mul_le_mul_of_nonneg_right hLM hMp.le
      _ = M^2 := by ring
  calc
    _ = (L*(2*Real.pi*M/Real.log M)*8)*(M^(3*r)/M^((4/5:ℝ)*(B-1:ℕ))) := by ring
    _ ≤ M^2*(M^(3*r)/M^((4/5:ℝ)*(B-1:ℕ))) :=
      mul_le_mul_of_nonneg_right hco (by positivity)
    _ = M^(2+(3*r:ℕ)-(4/5:ℝ)*(B-1:ℕ)) := by
      rw [Real.rpow_sub hMp,Real.rpow_add hMp]
      simp only [Real.rpow_natCast,Real.rpow_two]
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hM
      (bridge_observation_exponent N r B hN hr hB hB1)
lemma endpoint_shortfall_observation (k : ℝ) (hk : 0 ≤ k) {R : ℕ}
    (a : Fin R → ℤ) (n : Fin R → ℕ) (hn : ∀ i, 0 < n i)
    (F : (Fin R → ℝ) → ℝ) (L : NNReal) (hF : LipschitzWith L F)
    (b : ℤ) (r N B : ℕ) (hlen : ∀ i, n i ≤ 2*r)
    (hwin : ∀ i j, 1 ≤ j → j ≤ n i → (a i+(j:ℤ)-1-b).natAbs ≤ r)
    (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    (hB : (N:ℝ)/3-1 ≤ (B:ℝ)) (hB1 : 1 ≤ B)
    (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
    (z w : ℝ × ℝ) (hd : dist (liftIter k b z) (liftIter k b w) ≤
      8/growthBase k^((4/5:ℝ)*(B-1:ℕ))) :
    |F (fun i => torusShortfall k (liftProjection z) (a i) (n i))-
      F (fun i => torusShortfall k (liftProjection w) (a i) (n i))| ≤
      growthBase k^(-(1/10:ℝ)*(N:ℝ)) := by
  have hMp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hh := shortfall_observation_transport k hk a n hn F L hF b r hlen hwin z w
  apply hh.trans
  apply le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hd (by positivity)) L.coe_nonneg)
  exact bridge_observation_scalar (growthBase k) L (by linarith [growthBase_ge_four k hk]) hlog L.coe_nonneg hLM
    N r B hN hr hB hB1
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_MiddlePrefixBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma isClosed_torusPrefixGrowth (k : ℝ) (B : ℕ) : IsClosed {z | torusPrefixGrowth k B z} := by
  simp only [torusPrefixGrowth,ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_torusSegmentTransfer k 0 i).norm
lemma torusPrefixGrowth_lift (k : ℝ) (B : ℕ) (z : ℝ × ℝ) :
    torusPrefixGrowth k B (liftProjection z) ↔
    ∀ i, 1 ≤ i → i ≤ B → growthBase k^((49/50:ℝ)*(i:ℝ)) ≤
      ‖transferProduct (orbitCoefficient k z.2 z.1) i‖ := by
  simp only [torusPrefixGrowth,torusSegmentTransfer_lift,liftSegmentTransfer_eq,liftIter_zero]
lemma prefix_row_cover (k : ℝ) (hc : BridgeScalarControl k) (B : ℕ) (hB : 2 ≤ B)
    (z : ℝ × ℝ) (hz : torusPrefixGrowth k B (liftProjection z.swap)) :
    prefixEligible k B B z ∨ prefixEligible k B (B+1) z := by
  have hg := (torusPrefixGrowth_lift k B z.swap).mp hz
  obtain ⟨J,hJ,hrow⟩ := fast_prefix_row (orbitCoefficient k z.1 z.2) (growthBase k) B hB
    (by linarith [growthBase_ge_four k hc.nonneg]) hc.prefix_geom hc.prefix_small
    (fun i _ _ => potential_bound k _ hc.nonneg) hg
  rcases hJ with rfl|rfl
  · exact Or.inl ⟨hg,hrow⟩
  · exact Or.inr ⟨hg,hrow⟩
lemma bridgeRowLength_pos (B : ℕ) (hB : 2 ≤ B) (b : Bool) : 1 ≤ bridgeRowLength B b := by
  cases b <;> simp only [bridgeRowLength,Bool.false_eq_true,ite_false,ite_true] <;> omega
lemma bridgeRowLength_choice (B : ℕ) (hB : 2 ≤ B) (b : Bool) :
    B=bridgeRowLength B b ∨ B=bridgeRowLength B b+1 := by
  cases b with
  | false => right; change B=B-1+1; omega
  | true => left; rfl
lemma prefix_row_cover_bool (k : ℝ) (hc : BridgeScalarControl k) (B : ℕ) (hB : 2 ≤ B)
    (z : ℝ × ℝ) (hz : torusPrefixGrowth k B (liftProjection z.swap)) :
    ∃ b : Bool, prefixEligible k B (bridgeRowLength B b+1) z := by
  rcases prefix_row_cover k hc B hB z hz with h|h
  · exact ⟨false,by simpa [bridgeRowLength,Nat.sub_add_cancel (show 1 ≤ B by omega)] using h⟩
  · exact ⟨true,by simpa [bridgeRowLength] using h⟩
lemma measurableSet_middlePrefixEvent (k : ℝ) (Bp Bm : ℕ) : MeasurableSet (middlePrefixEvent k Bp Bm) :=
  ((isClosed_torusPrefixGrowth k Bp).inter ((isClosed_torusPrefixGrowth k Bm).preimage continuous_swap)).measurableSet
lemma actual_middle_prefix_product (k : ℝ) (hc : BridgeScalarControl k)
    (Bp Bm : ℕ) (hBp : 2 ≤ Bp) (hBm : 2 ≤ Bm)
    (W H : Torus → ℝ) (hW : Continuous W) (hH : Continuous H) (hW0 : ∀ z, 0 ≤ W z)
    (h δ : ℝ) (hδ : 0 ≤ δ) (hδh : δ < h/2)
    (hWp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(Bm:ℤ)) z) (liftIter k (-(Bm:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bm-1:ℕ)) → |W (liftProjection z)-W (liftProjection w)| ≤ δ)
    (hHp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (Bp:ℤ) z) (liftIter k (Bp:ℤ) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bp-1:ℕ)) → |H (liftProjection z)-H (liftProjection w)| ≤ δ) :
    (∫⁻ z in middlePrefixEvent k Bp Bm ∩ {z | h < H z}, ENNReal.ofReal (W z) ∂area) ≤
      middleBridgeConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*area {z | h/2 < H z} := by
  classical
  let E := middlePrefixEvent k Bp Bm ∩ {z | h < H z}
  have hE : MeasurableSet E := (measurableSet_middlePrefixEvent k Bp Bm).inter (isOpen_lt continuous_const hH).measurableSet
  let cell := Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1
  let U := cell ∩ liftProjection ⁻¹' E
  let A : ((Fin 32 × Fin 32) × (Bool × Bool)) → Set (ℝ × ℝ) := fun j =>
    {z | z ∈ bridgeGridCell j.1.1 ×ˢ bridgeGridCell j.1.2 ∧
      prefixEligible k Bp (bridgeRowLength Bp j.2.1+1) z.swap ∧
      prefixEligible k Bm (bridgeRowLength Bm j.2.2+1) z ∧ h < H (liftProjection z)}
  have hcover : U ⊆ ⋃ j, A j := by
    intro z hz
    obtain ⟨ix,hix⟩ := bridgeGrid_cover z.1 ⟨hz.1.1.1.le,hz.1.1.2⟩
    obtain ⟨iy,hiy⟩ := bridgeGrid_cover z.2 ⟨hz.1.2.1.le,hz.1.2.2⟩
    obtain ⟨bp,hbp⟩ := prefix_row_cover_bool k hc Bp hBp z.swap (by simpa only [Prod.swap_swap] using hz.2.1.1)
    obtain ⟨bm,hbm⟩ := prefix_row_cover_bool k hc Bm hBm z hz.2.1.2
    exact mem_iUnion.mpr ⟨((ix,iy),(bp,bm)),⟨hix,hiy⟩,hbp,hbm,hz.2.2⟩
  have hu : (∫⁻ z in U, ENNReal.ofReal (W (liftProjection z)))=
      ∫⁻ z in E, ENNReal.ofReal (W z) ∂area := by
    have hi := unit_cell_integral (E.indicator (fun z => ENNReal.ofReal (W z)))
      (hW.measurable.ennreal_ofReal.indicator hE) 0 0
    simp only [zero_add] at hi
    rw [lintegral_indicator hE] at hi
    have hid : (fun z => E.indicator (fun z => ENNReal.ofReal (W z)) (liftProjection z))=
        (liftProjection ⁻¹' E).indicator (fun z => ENNReal.ofReal (W (liftProjection z))) := by
      funext z
      by_cases hz : liftProjection z ∈ E <;> simp [hz]
    rw [hid,setLIntegral_indicator (hE.preimage measurable_liftProjection)] at hi
    simpa only [U,cell,inter_comm] using hi
  let K := bridgeLocalConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*area {z | h/2 < H z}
  have hlocal (j : ((Fin 32 × Fin 32) × (Bool × Bool))) :
      bridgeAreaScale*(∫⁻ z in A j, ENNReal.ofReal (W (liftProjection z))) ≤ K :=
    actual_grid_square_product k hc (bridgeRowLength Bp j.2.1) (bridgeRowLength Bm j.2.2) Bp Bm
      (bridgeRowLength_pos Bp hBp _) (bridgeRowLength_pos Bm hBm _)
      (bridgeRowLength_choice Bp hBp _) (bridgeRowLength_choice Bm hBm _) hBp hBm j.1.1 j.1.2
      W H hW hH hW0 h δ hδ hδh hWp hHp
  have hsum : bridgeAreaScale*(∫⁻ z in E, ENNReal.ofReal (W z) ∂area) ≤ 4096*K := by
    rw [← hu]
    calc
      _ ≤ bridgeAreaScale*(∫⁻ z in ⋃ j, A j, ENNReal.ofReal (W (liftProjection z))) :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set hcover) bot_le
      _ ≤ bridgeAreaScale*(∑' j, ∫⁻ z in A j, ENNReal.ofReal (W (liftProjection z))) :=
        mul_le_mul_of_nonneg_left (lintegral_iUnion_le _ _) bot_le
      _ = ∑ j, bridgeAreaScale*(∫⁻ z in A j, ENNReal.ofReal (W (liftProjection z))) := by rw [tsum_fintype,Finset.mul_sum]
      _ ≤ ∑ _j : ((Fin 32 × Fin 32) × (Bool × Bool)), K := Finset.sum_le_sum (fun j _ => hlocal j)
      _ = 4096*K := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,nsmul_eq_mul]; norm_num
  have hd := (ENNReal.le_div_iff_mul_le (Or.inl bridgeAreaScale_pos.ne') (Or.inl bridgeAreaScale_ne_top)).mpr
    (show (∫⁻ z in E, ENNReal.ofReal (W z) ∂area)*bridgeAreaScale ≤ 4096*K by simpa only [mul_comm] using hsum)
  apply hd.trans_eq
  unfold K middleBridgeConstant
  simp only [div_eq_mul_inv]
  ac_rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_VectorGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma transferVector_norm_pos (v : ℕ → ℝ) (u : ℂ) (hu : u≠0) (j : ℕ) :
    0 < ‖transferProduct v j u‖ := by
  apply norm_pos_iff.mpr
  intro he
  have hh := congrArg (transferProductInv v j) he
  simp only [transferProductInv_inverse,map_zero] at hh
  exact hu hh
lemma transferVectorLog_step (M : ℝ) (hM : 1 < M) (v : ℕ → ℝ)
    (u : ℂ) (hu : u≠0) (j : ℕ) (hv : |v (j+1)|+1≤M) :
    transferVectorLog M v u (j+1)-transferVectorLog M v u j≤1 := by
  have hp := transferVector_norm_pos v u hu j
  have hp' := transferVector_norm_pos v u hu (j+1)
  have hs : ‖transferProduct v (j+1) u‖≤M*‖transferProduct v j u‖ := by
    change ‖transferStep (v (j+1)) (transferProduct v j u)‖≤_
    exact ((transferStep _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((transferStep_norm _).trans hv) (norm_nonneg _))
  have hl := Real.log_le_log hp' hs
  rw [Real.log_mul (by linarith : M≠0) hp.ne'] at hl
  unfold transferVectorLog
  rw [← sub_div]
  exact (div_le_one (Real.log_pos hM)).mpr (by linarith)
lemma transferVectorLog_interval (M : ℝ) (hM : 1 < M) (v : ℕ → ℝ)
    (u : ℂ) (hu : u≠0) (i l : ℕ) (c : ℝ)
    (hgood : c*(l:ℝ)≤transferVectorLog M v u (i+l)-transferVectorLog M v u i) :
    M^(c*(l:ℝ))≤‖transferProduct (fun j => v (i+j)) l‖ := by
  have hi := transferVector_norm_pos v u hu i
  have hil := transferVector_norm_pos v u hu (i+l)
  have hD : 0 < ‖transferProduct (fun j => v (i+j)) l‖ := by
    have := (transferProduct_area (fun j => v (i+j)) l).singular_pair.choose_spec.2.2.2.2
    linarith
  have hb : ‖transferProduct v (i+l) u‖≤
      ‖transferProduct (fun j => v (i+j)) l‖*‖transferProduct v i u‖ := by
    rw [transferProduct_concat]
    exact (transferProduct _ _).le_opNorm _
  have hl := Real.log_le_log hil hb
  rw [Real.log_mul hD.ne' hi.ne'] at hl
  apply (Real.rpow_le_iff_le_log (by linarith) hD).mpr
  unfold transferVectorLog at hgood
  rw [← sub_div] at hgood
  have hh := (le_div_iff₀ (Real.log_pos hM)).mp hgood
  linarith
lemma torus_middle_prefix_of_vector (k : ℝ) (hk : 0≤k) (z : Torus) (N i : ℕ)
    (hi : i≤N) (u : ℂ) (hu : u≠0)
    (hg : MiddleLogGood (transferVectorLog (growthBase k) (torusSegmentCoefficient k z 0) u) N i) :
    torusPrefixGrowth k (N-i) (torusIter k (i:ℤ) z) ∧
      torusPrefixGrowth k i (torusIter k (i:ℤ) z).swap := by
  have hM : 1 < growthBase k := by linarith [growthBase_ge_four k hk]
  constructor
  · intro l hl hli
    rw [torusSegmentTransfer_shift,zero_add]
    change growthBase k^((49/50:ℝ)*(l:ℝ))≤‖transferProduct (torusSegmentCoefficient k z (i:ℤ)) l‖
    rw [← zero_add (i:ℤ),← torusSegmentCoefficient_shift]
    apply transferVectorLog_interval (growthBase k) hM _ u hu i l (49/50)
    have hh := hg.2 (i+l) (by omega) (by omega)
    simpa only [Nat.cast_add,add_sub_cancel_left] using hh
  · intro l hl hli
    rw [torusSegmentTransfer_reverse_norm,torusSegmentTransfer_shift]
    change growthBase k^((49/50:ℝ)*(l:ℝ))≤‖transferProduct (torusSegmentCoefficient k z (-(l:ℤ)+(i:ℤ))) l‖
    have hei : -(l:ℤ)+(i:ℤ)=0+((i-l:ℕ):ℤ) := by omega
    rw [hei,← torusSegmentCoefficient_shift]
    apply transferVectorLog_interval (growthBase k) hM _ u hu (i-l) l (49/50)
    have hh := hg.1 (i-l) (by omega)
    rw [Nat.sub_add_cancel hli]
    simpa only [Nat.cast_sub hli,sub_sub_cancel] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_BridgeAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma measurableSet_torusFastBridge (k : ℝ) (N : ℕ) : MeasurableSet {z | torusFastBridge k z N} :=
  (isClosed_le continuous_const (continuous_torusSegmentTransfer k 0 N).norm).measurableSet
lemma torus_good_middles_count (k : ℝ) (hk : 0≤k) (N : ℕ) (hN : 100≤N)
    (z : Torus) (hz : torusFastBridge k z N) :
    (N:ℝ)/5≤(torusGoodMiddles k z N).card := by
  classical
  obtain ⟨u,hu,huN⟩ := exists_unit_opNorm (torusSegmentTransfer k z 0 N)
  have hu0 : u≠0 := by intro he; simp [he] at hu
  have hM : 1 < growthBase k := by linarith [growthBase_ge_four k hk]
  have hlog := Real.log_pos hM
  let zlog := transferVectorLog (growthBase k) (torusSegmentCoefficient k z 0) u
  have htotal : (999/1000:ℝ)*(N:ℝ)≤zlog N-zlog 0 := by
    have hh := Real.le_log_of_rpow_le (by linarith : 0 < growthBase k) hz
    dsimp only [zlog,transferVectorLog]
    change _≤Real.log ‖torusSegmentTransfer k z 0 N u‖/Real.log (growthBase k)-Real.log ‖u‖/Real.log (growthBase k)
    rw [huN,hu,Real.log_one,zero_div,sub_zero]
    exact (le_div_iff₀ hlog).mpr hh
  have hcount := middle_log_good_count zlog N hN (fun j _ =>
    transferVectorLog_step (growthBase k) hM _ u hu0 j (by
      obtain ⟨w,rfl⟩ := liftProjection_surjective z
      rw [torusSegmentCoefficient_lift]
      exact liftSegmentCoefficient_bound k hk w 0 (j+1))) htotal
  apply hcount.trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hg⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨hi,?_⟩
  exact torus_middle_prefix_of_vector k hk z N i (bridgeMiddle_bounds N i hN hi).2.2.2.2 u hu0 hg
lemma lintegral_count_cover {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (s : Finset ι)
    (E : ι → Set X) (hE : ∀ i∈s, MeasurableSet (E i)) (F : Set X) (hF : MeasurableSet F)
    (w : X → ℝ≥0∞) (hw : Measurable w) (a : ℝ)
    (hcount : ∀ z∈F, a≤(s.filter (fun i => z∈E i)).card) :
    ENNReal.ofReal a*(∫⁻ z in F, w z ∂μ)≤∑ i∈s, ∫⁻ z in E i, w z ∂μ := by
  classical
  have hpoint (z : X) : ENNReal.ofReal a*F.indicator w z≤∑ i∈s, (E i).indicator w z := by
    by_cases hz : z∈F
    · rw [Set.indicator_of_mem hz]
      have he : (∑ i∈s, (E i).indicator w z)=((s.filter (fun i => z∈E i)).card:ℝ≥0∞)*w z := by
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
      rw [he]
      apply mul_le_mul_of_nonneg_right _ bot_le
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hcount z hz)
    · simp only [Set.indicator_of_notMem hz,mul_zero]
      exact bot_le
  have hh := lintegral_mono hpoint (μ:=μ)
  rw [lintegral_const_mul _ (hw.indicator hF)] at hh
  rw [lintegral_indicator hF] at hh
  rw [lintegral_finsetSum _ (fun i hi => hw.indicator (hE i hi))] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator (hE i hi) _
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_MiddleObservationBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma shortfallObservation_shift (k : ℝ) {R : ℕ} (a : Fin R → ℤ) (n : Fin R → ℕ)
    (F : (Fin R → ℝ) → ℝ) (b : ℤ) (z : Torus) :
    shortfallObservation k a n F (torusIter k b z)=shortfallObservation k (fun j => a j+b) n F z := by
  unfold shortfallObservation
  congr 1
  funext j
  exact torusShortfall_shift k z (a j) b (n j)
lemma middle_observation_product (k : ℝ) (hc : BridgeScalarControl k)
    (N r i : ℕ) (hN : 100 ≤ N) (hi : i∈bridgeMiddle N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    {Rw Rh : ℕ} (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀ j, 0 < nw j) (hnh : ∀ j, 0 < nh j) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀ j, nw j ≤ 2*r) (hlenh : ∀ j, nh j ≤ 2*r)
    (hwinw : ∀ j l, 1 ≤ l → l ≤ nw j → (aw j+(l:ℤ)-1).natAbs ≤ r)
    (hwinh : ∀ j l, 1 ≤ l → l ≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs ≤ r)
    (hW0 : ∀ z, 0 ≤ shortfallObservation k aw nw Fw z)
    (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
    (h : ℝ) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ)) < h/2) :
    (∫⁻ z in (torusIter k (i:ℤ) ⁻¹' middlePrefixEvent k (N-i) i) ∩
      {z | h < shortfallObservation k ah nh Fh z},
      ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area) ≤ middleBridgeConstant*((∫⁻ z, ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+
        ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*
          area {z | h/2 < shortfallObservation k ah nh Fh z} := by
  have hiB := bridgeMiddle_bounds N i hN hi
  let Wi := shortfallObservation k (fun j => aw j-(i:ℤ)) nw Fw
  let Hi := shortfallObservation k (fun j => ah j-(i:ℤ)) nh Fh
  have hWi : Continuous Wi := continuous_shortfall_observation k hc.nonneg _ _ _ hFw.continuous
  have hHi : Continuous Hi := continuous_shortfall_observation k hc.nonneg _ _ _ hFh.continuous
  have hWiS (z : Torus) : Wi (torusIter k (i:ℤ) z)=shortfallObservation k aw nw Fw z := by
    dsimp only [Wi]
    rw [shortfallObservation_shift]
    simp only [sub_add_cancel]
  have hHiS (z : Torus) : Hi (torusIter k (i:ℤ) z)=shortfallObservation k ah nh Fh z := by
    dsimp only [Hi]
    rw [shortfallObservation_shift]
    simp only [sub_add_cancel]
  have hWi0 (z : Torus) : 0 ≤ Wi z := by
    have hh := hW0 (torusIter k (-(i:ℤ)) z)
    rw [← hWiS,← torusIter_add,add_neg_cancel,torusIter_zero] at hh
    exact hh
  have hMp : 0 < growthBase k := by linarith [growthBase_ge_four k hc.nonneg]
  have hh := actual_middle_prefix_product k hc (N-i) i hiB.2.1 hiB.1 Wi Hi hWi hHi hWi0
    h (growthBase k^(-(1/10:ℝ)*(N:ℝ))) (Real.rpow_nonneg hMp.le _) hδ
    (by
      intro z w hd
      apply endpoint_shortfall_observation k hc.nonneg _ nw hnw Fw L hFw (-(i:ℤ)) r N i
        hlenw _ hN hr hiB.2.2.1 (by omega) hlog hLM z w hd
      intro j l hl hln
      simpa only [sub_neg_eq_add,sub_add_cancel,show aw j-(i:ℤ)+(l:ℤ)-1+(i:ℤ)=aw j+(l:ℤ)-1 by ring] using hwinw j l hl hln)
    (by
      intro z w hd
      apply endpoint_shortfall_observation k hc.nonneg _ nh hnh Fh L hFh ((N-i:ℕ):ℤ) r N (N-i)
        hlenh _ hN hr hiB.2.2.2.1 (by omega) hlog hLM z w hd
      intro j l hl hln
      have he : ah j-(i:ℤ)+(l:ℤ)-1-((N-i:ℕ):ℤ)=ah j+(l:ℤ)-1-(N:ℤ) := by omega
      simpa only [he] using hwinh j l hl hln)
  have hmp := measurePreserving_torusIter k (i:ℤ)
  have hleft := hmp.setLIntegral_comp_preimage (s := middlePrefixEvent k (N-i) i ∩ {z | h < Hi z})
    ((measurableSet_middlePrefixEvent k (N-i) i).inter (isOpen_lt continuous_const hHi).measurableSet)
    (hWi.measurable.ennreal_ofReal)
  have hwint := hmp.lintegral_comp (hWi.measurable.ennreal_ofReal)
  rw [← hwint] at hh
  simp only [hWiS] at hh
  have hm : area {z | h/2 < Hi z}=area {z | h/2 < shortfallObservation k ah nh Fh z} := by
    symm
    simpa only [Set.preimage_ofPred_eq,hHiS] using hmp.measure_preimage (s := {z | h/2 < Hi z}) (show MeasurableSet {z | h/2 < Hi z} from (isOpen_lt continuous_const hHi).measurableSet).nullMeasurableSet
  rw [hm] at hh
  simpa only [Set.preimage_inter,Set.preimage_ofPred_eq,hWiS,hHiS] using hleft.trans_le hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_FastBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma actual_fast_bridge_product_oai (k : ℝ) (hc : BridgeScalarControl k)
    (N r : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    {Rw Rh : ℕ} (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀ j, 0 < nw j) (hnh : ∀ j, 0 < nh j) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀ j, nw j ≤ 2*r) (hlenh : ∀ j, nh j ≤ 2*r)
    (hwinw : ∀ j l, 1 ≤ l → l ≤ nw j → (aw j+(l:ℤ)-1).natAbs ≤ r)
    (hwinh : ∀ j l, 1 ≤ l → l ≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs ≤ r)
    (hW0 : ∀ z, 0 ≤ shortfallObservation k aw nw Fw z)
    (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
    (h : ℝ) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ)) < h/2) :
    (∫⁻ z in {z | torusFastBridge k z N} ∩ {z | h < shortfallObservation k ah nh Fh z},
      ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area) ≤
      fastBridgeConstant*((∫⁻ z, ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+
        ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*
          area {z | h/2 < shortfallObservation k ah nh Fh z} := by
  classical
  let W := shortfallObservation k aw nw Fw
  let H := shortfallObservation k ah nh Fh
  have hW : Continuous W := continuous_shortfall_observation k hc.nonneg _ _ _ hFw.continuous
  have hH : Continuous H := continuous_shortfall_observation k hc.nonneg _ _ _ hFh.continuous
  let E : ℕ → Set Torus := fun i => (torusIter k (i:ℤ) ⁻¹' middlePrefixEvent k (N-i) i) ∩ {z | h < H z}
  let F : Set Torus := {z | torusFastBridge k z N} ∩ {z | h < H z}
  have hE (i : ℕ) : MeasurableSet (E i) :=
    ((measurableSet_middlePrefixEvent k (N-i) i).preimage (continuous_torusIter k _).measurable).inter
      (isOpen_lt continuous_const hH).measurableSet
  have hF : MeasurableSet F := (measurableSet_torusFastBridge k N).inter (isOpen_lt continuous_const hH).measurableSet
  have hEeq : E = (fun i : ℕ => (torusIter k (i:ℤ) ⁻¹' middlePrefixEvent k (N-i) i) ∩ {z | h < H z}) := rfl
  clear_value E
  have hcovers := lintegral_count_cover area (bridgeMiddle N) E (fun i _ => hE i) F hF
    (fun z => ENNReal.ofReal (W z)) hW.measurable.ennreal_ofReal ((N:ℝ)/5) (by
      intro z hz
      have hcount := torus_good_middles_count k hc.nonneg N hN z hz.1
      apply hcount.trans
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro i hi
      simp only [torusGoodMiddles,Finset.mem_filter] at hi
      rw [Finset.mem_filter]
      refine ⟨hi.1,?_⟩
      rw [hEeq]
      exact ⟨hi.2,hz.2⟩)
  let K := middleBridgeConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+
      ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*area {z | h/2 < H z}
  have hsum : (∑ i∈bridgeMiddle N, ∫⁻ z in E i, ENNReal.ofReal (W z) ∂area) ≤ (N:ℝ≥0∞)*K := by
    calc
      _ ≤ ∑ _i∈bridgeMiddle N, K := Finset.sum_le_sum fun i hi => by
        rw [hEeq]
        exact middle_observation_product k hc N r i hN hi hr aw nw Fw ah nh Fh hnw hnh L hFw hFh
          hlenw hlenh hwinw hwinh hW0 hlog hLM h hδ
      _ = ((bridgeMiddle N).card:ℝ≥0∞)*K := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ bot_le
        apply Nat.cast_le.mpr
        calc
          (bridgeMiddle N).card ≤ (Finset.range N).card := Finset.card_le_card (by
            intro i hi
            have hb := bridgeMiddle_bounds N i hN hi
            exact Finset.mem_range.mpr (by omega))
          _ = N := Finset.card_range N
  have hpos : 0 < (N:ℝ)/5 := by
    have : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have hetop : ENNReal.ofReal ((N:ℝ)/5)≠∞ := ENNReal.ofReal_ne_top
  have hemul : (N:ℝ≥0∞)*K=ENNReal.ofReal ((N:ℝ)/5)*(5*K) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<5),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
    calc
      _ = ((N:ℝ≥0∞)/5*5)*K := by rw [ENNReal.div_mul_cancel (by norm_num : (5:ℝ≥0∞)≠0) (by norm_num : (5:ℝ≥0∞)≠∞)]
      _ = _ := by ac_rfl
  have htot := hcovers.trans hsum
  rw [hemul] at htot
  have hfinal := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hpos).ne' hetop).mp htot
  simpa only [F,W,H,K,fastBridgeConstant,mul_assoc] using hfinal
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.actual_fast_bridge_product_oai := @OAI.StandardMapEntropy.actual_fast_bridge_product_oai
