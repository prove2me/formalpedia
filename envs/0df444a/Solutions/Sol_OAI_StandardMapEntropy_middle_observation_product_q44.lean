-- Prove2me | solution 1 for OAI.StandardMapEntropy.middle_observation_product_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:43:53.652103+00:00
-- url     : https://prove2.me/submissions/916d9673-3dc0-4f0a-a7f9-2518c72d5a6b

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_actual_grid_square_product_q44

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
  all_goals try with_reducible_and_instances rfl
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
  all_goals try with_reducible_and_instances rfl
  unfold potential
  ring

lemma linearSolution_step (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    linearSolution v a b (n + 2) =
      v (n + 1) * linearSolution v a b (n + 1) - linearSolution v a b n := rfl

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
-- module Solutions.OAIQ44_CM.StandardMap_ObservationTransport
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
-- module Solutions.OAIQ44_CM.StandardMap_LiftDynamics
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
-- module Solutions.OAIQ44_CM.StandardMap_SegmentObservations
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusIntegral
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
lemma measurePreserving_recurrenceCoordinates : MeasurePreserving recurrenceCoordinates area area := by
  unfold area
  apply (MeasurePreserving.id (volume : Measure Circle)).skew_product
  · exact measurable_fst.sub measurable_snd
  · exact Eventually.of_forall fun x => (Measure.measurePreserving_sub_left (volume : Measure Circle) x).map_eq
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Function.comp_apply,standardMap_conjugacy,torusStep_apply]
  rw [recurrenceCoordinates_involutive z]
lemma measurePreserving_torusStep_symm (k : ℝ) : MeasurePreserving (torusStep k).symm area area :=
  (measurePreserving_torusStep k).symm (torusStep_measurableEquiv k)
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

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
-- module Solutions.OAIQ44_CM.StandardMap_LiftEventMeasure
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MiddleCount
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GridBridge
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ObservationExponential
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_MiddlePrefixBridge
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
    actual_grid_square_product_q44 k hc (bridgeRowLength Bp j.2.1) (bridgeRowLength Bm j.2.2) Bp Bm
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
-- module Solutions.OAIQ44_CM.StandardMap_MiddleObservationBridge
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
lemma middle_observation_product_q44_oai (k : ℝ) (hc : BridgeScalarControl k)
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

theorem solution : type_of% @OAI.StandardMapEntropy.middle_observation_product_q44_oai := @OAI.StandardMapEntropy.middle_observation_product_q44_oai
