-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_retained_distance_graph
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:31:51.128415+00:00
-- url     : https://prove2.me/submissions/adfd9683-2198-409e-b7dc-21c9374931e2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_uniform_regularized_original_graph_removal

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleMaskPeriodicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem thickening_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (r x : ℝ) :
    x+T ∈ thickening r G ↔ x ∈ thickening r G := by
  constructor
  · intro hx
    obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
    refine mem_thickening_iff.mpr ⟨z-T,?_,?_⟩
    · exact (hG (z-T)).mp (by simpa using hz)
    · simpa only [Real.dist_eq] using (show |x-(z-T)| < r by
        convert hd using 1; simp only [Real.dist_eq]; congr 1; ring)
  · intro hx
    obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
    exact mem_thickening_iff.mpr ⟨z+T,(hG z).mpr hz,by simpa using hd⟩

theorem thickenedIndicator_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (η : ℝ) :
    Function.Periodic (thickenedIndicator G η) T := by
  intro x
  classical
  simp only [thickenedIndicator,Set.indicator_apply,thickening_periodic hG]

theorem smoothAngleMask_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (η : ℝ) (hη : 0 < η) :
    Function.Periodic (smoothAngleMask G η hη) T := by
  intro x
  unfold smoothAngleMask
  simp only [convolution_def]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp := thickenedIndicator_periodic hG η (x-t)
  rw [show x+T-t = (x-t)+T by ring,hp]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicMeasure
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem DyadicSquare.descendant_side_pos (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : List (Bool × Bool)) : 0 < (Q.descendant p).side := by
  induction p generalizing Q with
  | nil => exact hQ
  | cons a p ih => exact ih _ (Q.child_side_pos hQ a.1 a.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem DyadicSquare.descendant_side (Q : DyadicSquare) (p : List (Bool × Bool)) :
    (Q.descendant p).side = Q.side / (2 : ℝ)^p.length := by
  induction p generalizing Q with
  | nil => simp [descendant]
  | cons a p ih =>
    simp only [descendant, ih, child, List.length_cons, pow_succ]
    ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem DyadicSquare.descendant_append (Q : DyadicSquare) (p q : CellPath) :
    Q.descendant (p++q) = (Q.descendant p).descendant q := by
  induction p generalizing Q with
  | nil => rfl
  | cons a p ih => exact ih (Q.child a.1 a.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_FrostmanProfileCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have hb : 1 < (2:ℝ)^lam := Real.one_lt_rpow (by norm_num) hlam
  obtain ⟨N₀,hN₀⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨N₀,fun N hN => ?_⟩
  have hh := hN₀.le.trans (pow_le_pow_right₀ hb.le hN)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm,
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleBumpScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function
open scoped ContDiff Topology

theorem angleBump_scale (η : ℝ) (hη : 0 < η) (x : ℝ) :
    angleBump η hη x = angleBump 1 zero_lt_one (η⁻¹*x) := by
  rw [ContDiffBump.apply,ContDiffBump.apply]
  simp only [angleBump,smul_eq_mul,sub_zero]
  congr 1 <;> field_simp

theorem angleBump_integral_scale (η : ℝ) (hη : 0 < η) :
    (∫ x : ℝ, angleBump η hη x) = η*(∫ x : ℝ, angleBump 1 zero_lt_one x) := by
  simp_rw [angleBump_scale η hη]
  rw [Measure.integral_comp_mul_left]
  simp [abs_of_pos hη,smul_eq_mul]

theorem angleBump_normed_scale (η : ℝ) (hη : 0 < η) (x : ℝ) :
    (angleBump η hη).normed volume x =
      η⁻¹*(angleBump 1 zero_lt_one).normed volume (η⁻¹*x) := by
  rw [ContDiffBump.normed_def,angleBump_scale,angleBump_integral_scale,ContDiffBump.normed_def]
  ring

theorem angleBump_normed_iteratedDeriv (η : ℝ) (hη : 0 < η) (j : ℕ) (x : ℝ) :
    iteratedDeriv j ((angleBump η hη).normed volume) x =
      η⁻¹*(η⁻¹)^j*iteratedDeriv j ((angleBump 1 zero_lt_one).normed volume) (η⁻¹*x) := by
  have he : (angleBump η hη).normed volume = fun x =>
      η⁻¹*(angleBump 1 zero_lt_one).normed volume (η⁻¹*x) := funext (angleBump_normed_scale η hη)
  rw [he,iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (angleBump 1 zero_lt_one).contDiff_normed]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleMaskDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem compactSupport_iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem iteratedDeriv_convolution_left {f g : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) (hg : LocallyIntegrable g volume)
    (j : ℕ) :
    iteratedDeriv j (f ⋆[lsmul ℝ ℝ,volume] g) =
      iteratedDeriv j f ⋆[lsmul ℝ ℝ,volume] g := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,ih]
    have hd : ContDiff ℝ 1 (iteratedDeriv j f) :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp
        (hf.of_le (by exact_mod_cast (le_top : (j+1:ℕ∞) ≤ ⊤)) : ContDiff ℝ (j+1:ℕ) f)).2
    funext x
    simpa only [iteratedDeriv_succ] using
      ((compactSupport_iteratedDeriv hfc j).hasDerivAt_convolution_left
        (lsmul ℝ ℝ) hd hg x).deriv

theorem angleDerivativeConstant_nonneg (j : ℕ) : 0 ≤ angleDerivativeConstant j :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem angleBump_derivative_L1 (η : ℝ) (hη : 0 < η) (j : ℕ) :
    (∫ x : ℝ, ‖iteratedDeriv j ((angleBump η hη).normed volume) x‖) =
      (η⁻¹)^j*angleDerivativeConstant j := by
  simp_rw [angleBump_normed_iteratedDeriv η hη j,norm_mul,Real.norm_eq_abs,abs_pow,
    abs_inv,abs_of_pos hη]
  rw [integral_const_mul,Measure.integral_comp_inv_mul_left
    (fun y : ℝ => |iteratedDeriv j ((angleBump 1 zero_lt_one).normed volume) y|) η]
  simp only [abs_of_pos hη,smul_eq_mul,angleDerivativeConstant,Real.norm_eq_abs]
  field_simp

theorem smoothAngleMask_derivative_bound (G : Set ℝ) (η : ℝ) (hη : 0 < η) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (smoothAngleMask G η hη) x‖ ≤
      (η⁻¹)^j*angleDerivativeConstant j := by
  rw [smoothAngleMask,iteratedDeriv_convolution_left
    (angleBump η hη).hasCompactSupport_normed (angleBump η hη).contDiff_normed
    (thickenedIndicator_locallyIntegrable G η),← angleBump_derivative_L1 η hη j]
  apply norm_integral_le_of_norm_le
  · exact (ContDiff.continuous_iteratedDeriv' j (angleBump η hη).contDiff_normed).integrable_of_hasCompactSupport
      (compactSupport_iteratedDeriv (angleBump η hη).hasCompactSupport_normed j) |>.norm
  · filter_upwards [] with t
    simp only [lsmul_apply,smul_eq_mul,norm_mul]
    have hb := thickenedIndicator_bounds G η (x-t)
    simp only [Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)).trans_eq (mul_one _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngleMasks
attribute [-instance] _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_derivatives (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (sourceTestMask G d hd) θ‖ ≤
      ((100:ℝ)^j*angleDerivativeConstant j)*(d⁻¹)^j := by
  apply (smoothAngleMask_derivative_bound _ _ _ _ _).trans_eq
  rw [inv_div,div_eq_mul_inv,mul_pow]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SymbolProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

 theorem iteratedDeriv_product_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℝ) (c : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (J : ℕ) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ S, ∀ n ≤ J, ∀ x, ‖iteratedDeriv n (f i) x‖ ≤ c i * d^n) :
    ∀ j ≤ J, ∀ x, ‖iteratedDeriv j (fun x => ∏ i ∈ S, f i x) x‖ ≤
      (∏ i ∈ S, c i) * ((S.card:ℝ)*d)^j := by
  induction S using Finset.induction_on with
  | empty =>
    intro j hj x
    cases j with
    | zero => simp
    | succ j => simp [iteratedDeriv_const]
  | @insert a S ha ih =>
    have hcS : ∀ i ∈ S, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hfS : ∀ i ∈ S, ContDiff ℝ ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hbS := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have ih := ih hcS hfS hbS
    intro j hj x
    have hfa : ContDiffAt ℝ j (f a) x :=
      ((hf a (Finset.mem_insert_self _ _)).of_le (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    have hfp : ContDiffAt ℝ j (fun x => ∏ i ∈ S, f i x) x :=
      ((contDiff_prod fun i hi => hfS i hi).of_le (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    rw [iteratedDeriv_fun_mul hfa hfp]
    calc
      _ ≤ ∑ k ∈ Finset.range (j+1),
          (j.choose k:ℝ) * (c a*d^k) * ((∏ i ∈ S, c i)*((S.card:ℝ)*d)^(j-k)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        simp only [norm_mul, Real.norm_natCast]
        have hca := hc a (Finset.mem_insert_self _ _)
        gcongr
        · exact hb a (Finset.mem_insert_self _ _) k (hk.trans hj) x
        · exact ih (j-k) ((Nat.sub_le _ _).trans hj) x
      _ = (c a * ∏ i ∈ S, c i) * (d+(S.card:ℝ)*d)^j := by
        rw [add_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by congr 2; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularBinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff Topology

theorem angularBinKernel_contDiff : ContDiff ℝ ∞ angularBinKernel :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem angularBinKernel_nonneg (t : ℝ) : 0 ≤ angularBinKernel t :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem angularBinKernel_two_terms {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    angularBinKernel t + angularBinKernel (t-1) = 1 := by
  unfold angularBinKernel
  rw [Real.smoothTransition.one_of_one_le (show 1 ≤ t+1 by linarith),
    Real.smoothTransition.zero_of_nonpos (show t-1 ≤ 0 by linarith),
    sub_add_cancel]
  ring

theorem angularBinKernel_translate_zero (t : ℝ) (k : ℤ)
    (hk : k ≠ ⌊t⌋ ∧ k ≠ ⌊t⌋+1) : angularBinKernel (t-k) = 0 := by
  have hlow := Int.floor_le t
  have hhigh := Int.lt_floor_add_one t
  by_cases h : k ≤ ⌊t⌋-1
  · apply angularBinKernel_zero_right
    have hh : (k : ℝ) ≤ (⌊t⌋ : ℝ)-1 := by exact_mod_cast h
    linarith
  · apply angularBinKernel_zero_left
    have hh : ⌊t⌋+2 ≤ k := by omega
    have hh : (⌊t⌋ : ℝ)+2 ≤ (k : ℝ) := by exact_mod_cast hh
    linarith

theorem angularBinKernel_floor_partition (t : ℝ) :
    angularBinKernel (t-(⌊t⌋ : ℤ)) + angularBinKernel (t-(⌊t⌋+1 : ℤ)) = 1 := by
  have h := angularBinKernel_two_terms (sub_nonneg.mpr (Int.floor_le t))
    (show t-(⌊t⌋ : ℤ) ≤ 1 by linarith [Int.lt_floor_add_one t])
  simpa only [Int.cast_add, Int.cast_one, sub_add_eq_sub_sub] using h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularBinSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set Filter
open scoped ContDiff Topology

theorem angularBinSelection_two_terms (p : ℤ → Prop) (t : ℝ) :
    angularBinSelection p t =
      (if p ⌊t⌋ then angularBinKernel (t-(⌊t⌋ : ℤ)) else 0) +
      (if p (⌊t⌋+1) then angularBinKernel (t-(⌊t⌋+1 : ℤ)) else 0) := by
  classical
  unfold angularBinSelection
  rw [tsum_eq_sum (s := {⌊t⌋, ⌊t⌋+1})]
  · simp [show ⌊t⌋ ≠ ⌊t⌋+1 by omega]
  · intro k hk
    have hz := angularBinKernel_translate_zero t k (by simpa using hk)
    simp [hz]

theorem angularBinSelection_bounds (p : ℤ → Prop) (t : ℝ) :
    0 ≤ angularBinSelection p t ∧ angularBinSelection p t ≤ 1 := by
  classical
  rw [angularBinSelection_two_terms]
  have h0 := angularBinKernel_nonneg (t-(⌊t⌋ : ℤ))
  have h1 := angularBinKernel_nonneg (t-(⌊t⌋+1 : ℤ))
  have he := angularBinKernel_floor_partition t
  split_ifs <;> constructor <;> linarith

theorem angularBinSelection_local (p : ℤ → Prop) (t : ℝ) :
    angularBinSelection p =ᶠ[𝓝 t] (fun u =>
      ∑ k ∈ Finset.Icc (⌊t⌋-2) (⌊t⌋+3), if p k then angularBinKernel (u-k) else 0) := by
  classical
  filter_upwards [Ioo_mem_nhds (show t-1 < t by linarith) (show t < t+1 by linarith)] with u hu
  unfold angularBinSelection
  apply tsum_eq_sum
  intro k hk
  have hz : angularBinKernel (u-k) = 0 := by
    have hk : k < ⌊t⌋-2 ∨ ⌊t⌋+3 < k := by simpa only [Finset.mem_Icc, not_and_or, not_le] using hk
    rcases hk with hk | hk
    · apply angularBinKernel_zero_right
      have hc : (k : ℝ) < (⌊t⌋ : ℝ)-2 := by exact_mod_cast hk
      linarith [Int.floor_le t, hu.1]
    · apply angularBinKernel_zero_left
      have hc : (⌊t⌋ : ℝ)+3 < (k : ℝ) := by exact_mod_cast hk
      linarith [Int.lt_floor_add_one t, hu.2]
  simp [hz]

theorem angularBinSelection_contDiff (p : ℤ → Prop) : ContDiff ℝ ∞ (angularBinSelection p) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro t
  apply ContDiffAt.congr_of_eventuallyEq _ (angularBinSelection_local p t)
  apply ContDiff.contDiffAt
  apply ContDiff.sum
  intro k _
  by_cases hk : p k
  · simp only [hk, ↓reduceIte]
    exact angularBinKernel_contDiff.comp (contDiff_id.sub contDiff_const)
  · simp only [hk, ↓reduceIte]
    exact contDiff_const

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTransform
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem measurable_sourceAngularTransform (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) (M : ℝ) (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2)) :
    Measurable (fun z : ℝ × UnitCircle => sourceAngularTransform ρ X M b z.1 z.2) := by
  have hf : Measurable (fun z : (ℝ × UnitCircle) × Plane =>
      Complex.exp (Complex.I * (z.1.1 : ℂ) * (inner ℝ (z.1.2 : Plane) z.2 : ℂ)) * b z.2 z.1.2) := by
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν := ρ.restrict X)).measurable
  exact (measurable_const (a := (M⁻¹ : ℝ))).smul hi

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleMaskCoordinates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_periodic (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Function.Periodic (sourceTestMask G d hd) (2*Real.pi) := by
  apply smoothAngleMask_periodic
  intro θ
  have he : sourceUnitDirection (θ+2*Real.pi) = sourceUnitDirection θ := by
    apply Subtype.ext
    simp only [sourceUnitDirection,sourceDirection,Real.cos_add_two_pi,Real.sin_add_two_pi]
  simp only [mem_preimage,he]

theorem circleTestMask_comp (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (θ : ℝ) :
    circleTestMask G d hd (sourceUnitDirection θ) = sourceTestMask G d hd θ := by
  unfold circleTestMask
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := (sourceTestMask_periodic G d hd).int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm,add_comm] using hp θ

theorem circleTestMask_angular_contDiff (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    ContDiff ℝ ∞ (fun θ => circleTestMask G d hd (sourceUnitDirection θ)) := by
  simpa only [circleTestMask_comp] using sourceTestMask_contDiff G d hd

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialAnchorMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem spatialAnchorMask_contDiff (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) :
    ContDiff ℝ ∞ (fun θ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection θ)) := by
  by_cases hx : ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier
  · obtain ⟨P,hP,hx⟩ := hx
    simpa only [spatialAnchorMask_eq Q hQ ρ n G d hd hP hx] using circleTestMask_angular_contDiff (G P) d hd
  · push Not at hx
    simp only [spatialAnchorMask_zero Q ρ n G d hd hx]
    exact contDiff_const

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTransformSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem angular_integrand_norm (r : ℝ) (ω : UnitCircle) (x : Plane)
    (b : Plane → UnitCircle → ℂ) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω‖ =
      ‖b x ω‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem sourceAngularTransform_norm_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) (M : ℝ) (hM : 0 < M) (b : Plane → UnitCircle → ℂ)
    (C : ℝ) (hC : ∀ x ∈ X, ∀ ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    ‖sourceAngularTransform ρ X M b r ω‖ ≤ C * (ρ X).toReal / M := by
  unfold sourceAngularTransform
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
  have hb := norm_setIntegral_le_of_norm_le_const (measure_lt_top ρ X)
    (fun x hx => (angular_integrand_norm r ω x b).trans_le (hC x hx ω))
  calc
    _ ≤ M⁻¹ * (C * (ρ X).toReal) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_PeriodicAngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set
open scoped ContDiff Topology

theorem angularBinSelection_periodic (p : ℤ → Prop) (n : ℤ)
    (hp : ∀ k, p (k+n) ↔ p k) : Function.Periodic (angularBinSelection p) (n : ℝ) := by
  intro t
  unfold angularBinSelection
  rw [← (Equiv.addRight n).tsum_eq]
  apply tsum_congr
  intro k
  change (if p (k+n) then angularBinKernel (t+(n:ℝ)-(k+n : ℤ)) else 0) = _
  rw [show t+(n:ℝ)-(k+n : ℤ) = t-k by push_cast; ring]
  simp only [hp]

theorem periodicAngularBin_periodic (n j : ℕ) :
    Function.Periodic (periodicAngularBin n j) (2*Real.pi) := by
  have hp := angularBinSelection_periodic (fun k => (k % (n : ℤ)).toNat = j) (n : ℤ)
    (fun k => by simp)
  intro θ
  unfold periodicAngularBin
  convert hp ((n : ℝ)/(2*Real.pi)*θ) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  field_simp

theorem periodicAngularBin_contDiff (n j : ℕ) : ContDiff ℝ ∞ (periodicAngularBin n j) :=
  (angularBinSelection_contDiff _).comp (contDiff_const.mul contDiff_id)

theorem angularBinResidue_lt {n : ℕ} (hn : 0 < n) (k : ℤ) :
    (k % (n : ℤ)).toNat < n := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have h0 := Int.emod_nonneg k hn'.ne'
  have h1 := Int.emod_lt_of_pos k hn'
  have he := Int.toNat_of_nonneg h0
  have ht : ((k % (n : ℤ)).toNat : ℤ) < n := by rwa [he]
  exact_mod_cast ht

theorem periodicAngularBin_partition {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    ∑ j ∈ Finset.range n, periodicAngularBin n j θ = 1 := by
  have hsum (k : ℤ) (w : ℝ) :
      (∑ j ∈ Finset.range n, if (k % (n : ℤ)).toNat = j then w else 0) = w := by
    calc
      _ = if (k % (n : ℤ)).toNat ∈ Finset.range n then w else 0 :=
        Finset.sum_ite_eq _ _ (fun _ => w)
      _ = _ := by simp [angularBinResidue_lt hn]
  unfold periodicAngularBin
  simp_rw [angularBinSelection_two_terms]
  rw [Finset.sum_add_distrib]
  let t := (n : ℝ)/(2*Real.pi)*θ
  convert (congrArg₂ (fun a b : ℝ => a+b)
    (hsum ⌊t⌋ (angularBinKernel (t-(⌊t⌋ : ℤ))))
    (hsum (⌊t⌋+1) (angularBinKernel (t-(⌊t⌋+1 : ℤ))))).trans
      (angularBinKernel_floor_partition t) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> split_ifs <;> rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SelectedAngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open scoped ContDiff Topology

theorem periodicAngularBin_sum (n : ℕ) (S : Finset ℕ) :
    (fun θ => ∑ j ∈ S, periodicAngularBin n j θ) =
      fun θ => angularBinSelection (fun k => (k % (n : ℤ)).toNat ∈ S)
        ((n : ℝ)/(2*Real.pi)*θ) := by
  funext θ
  have hsum (q : ℕ) (w : ℝ) :
      (∑ j ∈ S, if q = j then w else 0) = if q ∈ S then w else 0 :=
    Finset.sum_ite_eq _ _ (fun _ => w)
  simp only [periodicAngularBin, angularBinSelection_two_terms, Finset.sum_add_distrib]
  let t := (n : ℝ)/(2*Real.pi)*θ
  convert congrArg₂ (fun a b : ℝ => a+b)
    (hsum (⌊t⌋ % (n : ℤ)).toNat (angularBinKernel (t-(⌊t⌋ : ℤ))))
    (hsum ((⌊t⌋+1) % (n : ℤ)).toNat (angularBinKernel (t-(⌊t⌋+1 : ℤ)))) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> split_ifs <;> rfl
  congr 1 <;> split_ifs <;> rfl

theorem selectedAngularBins_bounds (n : ℕ) (S : Finset ℕ) (θ : ℝ) :
    0 ≤ ∑ j ∈ S, periodicAngularBin n j θ ∧
      (∑ j ∈ S, periodicAngularBin n j θ) ≤ 1 := by
  have he := congrFun (periodicAngularBin_sum n S) θ
  rw [he]
  exact angularBinSelection_bounds _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorMaskSymmetry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem spatialAnchorMask_derivative_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (fun φ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection φ)) θ‖ ≤
      ((100:ℝ)^j*angleDerivativeConstant j)*(d⁻¹)^j := by
  by_cases hx : ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier
  · obtain ⟨P,hP,hx⟩ := hx
    simpa only [spatialAnchorMask_eq Q hQ ρ n G d hd hP hx,circleTestMask_comp] using
      sourceTestMask_derivatives (G P) d hd j θ
  · push Not at hx
    simp only [spatialAnchorMask_zero Q ρ n G d hd hx,iteratedDeriv_fun_const_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (angleDerivativeConstant_nonneg j)) (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_NormalizedSymbolFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

theorem symbolDerivativeConstant_one_le (B : ℕ) : 1 ≤ symbolDerivativeConstant B := by
  have : 0 ≤ ∑ n ∈ Finset.range (B+1), (100:ℝ)^n * angleDerivativeConstant n :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (angleDerivativeConstant_nonneg n)
  unfold symbolDerivativeConstant
  linarith

theorem symbolDerivativeConstant_dominates {B n : ℕ} (hn : n ≤ B) :
    (100:ℝ)^n * angleDerivativeConstant n ≤ symbolDerivativeConstant B := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (B+1)) =>
      mul_nonneg (by positivity : 0 ≤ (100:ℝ)^i) (angleDerivativeConstant_nonneg i))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  unfold symbolDerivativeConstant
  linarith

theorem iteratedDeriv_shift (f : ℝ → ℝ) (j k : ℕ) :
    iteratedDeriv j (iteratedDeriv k f) = iteratedDeriv (j+k) f := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ,ih,Nat.succ_add,iteratedDeriv_succ]

theorem smooth_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

 theorem normalizedMaskFactor_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (d : ℝ) (k : ℕ) : ContDiff ℝ ∞ (normalizedMaskFactor w d k) :=
  contDiff_const.mul (smooth_iteratedDeriv hw k)

 theorem normalizedMaskFactor_derivative_bound {w : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hzero : ∀ θ, ‖w θ‖ ≤ 1)
    (hall : ∀ n θ, ‖iteratedDeriv n w θ‖ ≤
      ((100:ℝ)^n*angleDerivativeConstant n)*(d⁻¹)^n)
    {B k j : ℕ} (hkj : k+j ≤ B) (θ : ℝ) :
    ‖iteratedDeriv j (normalizedMaskFactor w d k) θ‖ ≤
      (symbolDerivativeConstant B)^k * (symbolDerivativeConstant B*d⁻¹)^j := by
  have hA := symbolDerivativeConstant_one_le B
  have hA0 : 0 ≤ symbolDerivativeConstant B := le_trans zero_le_one hA
  unfold normalizedMaskFactor
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_shift]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_pos hd]
  by_cases hz : j+k = 0
  · have hj : j = 0 := by omega
    have hk : k = 0 := by omega
    subst j; subst k
    simpa only [Nat.zero_add,pow_zero,one_mul,mul_one,iteratedDeriv_zero,Real.norm_eq_abs] using hzero θ
  · have hbudget : j+k ≤ B := by omega
    have hC : (100:ℝ)^(j+k)*angleDerivativeConstant (j+k) ≤
        symbolDerivativeConstant B^(j+k) := by
      apply (symbolDerivativeConstant_dominates hbudget).trans
      exact le_self_pow₀ hA (by omega)
    calc
      _ ≤ d^k * (((100:ℝ)^(j+k)*angleDerivativeConstant (j+k))*(d⁻¹)^(j+k)) :=
        mul_le_mul_of_nonneg_left (hall (j+k) θ) (by positivity)
      _ ≤ d^k * (symbolDerivativeConstant B^(j+k)*(d⁻¹)^(j+k)) := by gcongr
      _ = _ := by
        rw [pow_add,pow_add,mul_pow]
        have he : d^k*(d⁻¹)^k = 1 := by rw [← mul_pow,mul_inv_cancel₀ hd.ne',one_pow]
        calc
          _ = (d^k*(d⁻¹)^k) * (symbolDerivativeConstant B)^k *
              (symbolDerivativeConstant B)^j * (d⁻¹)^j := by ring
          _ = _ := by rw [he]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InheritedAngularSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem descriptorAngleMask_contDiff (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) :
    ContDiff ℝ ∞ (descriptorAngleMask Q ρ m N lam sig J i b x) :=
  spatialAnchorMask_contDiff Q hQ _ _ _ _ _ _

 theorem descriptorAngleMask_norm_le_one (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (θ : ℝ) :
    ‖descriptorAngleMask Q ρ m N lam sig J i b x θ‖ ≤ 1 := by
  have hb := descriptorSpatialMask_bounds Q hQ ρ m N lam sig J i b x (sourceUnitDirection θ)
  simpa only [descriptorAngleMask,Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2

 theorem descriptorAngleMask_derivatives (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (descriptorAngleMask Q ρ m N lam sig J i b x) θ‖ ≤
      ((100:ℝ)^j*angleDerivativeConstant j)*(sourceAngularRadius N sig (descriptorLength b))⁻¹^j :=
  spatialAnchorMask_derivative_bound Q hQ _ _ _ _ _ _ _ _

 theorem inheritedMaskProduct_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane)
    (K j : ℕ) (hK : ∑ a ∈ S, k a ≤ K) (D : ℝ) (hD : 0 ≤ D)
    (hscale : ∀ a ∈ S, (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹ ≤ D)
    (θ : ℝ) :
    ‖iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x) θ‖ ≤
      symbolDerivativeConstant (K+j)^(K+j) * ((S.card:ℝ)*D)^j := by
  let A := symbolDerivativeConstant (K+j)
  have hA : 1 ≤ A := symbolDerivativeConstant_one_le _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hk (a : ι) (ha : a ∈ S) : k a ≤ K :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha).trans hK
  have hh := iteratedDeriv_product_bound S
    (fun a => normalizedMaskFactor (descriptorAngleMask Q ρ m N lam sig J i (b a) (x a))
      (sourceAngularRadius N sig (descriptorLength (b a))) (k a))
    (fun a => A^(k a)) (A*D) (mul_nonneg hA0 hD) j
    (fun _ _ => pow_nonneg hA0 _) (fun a _ => normalizedMaskFactor_contDiff
      (descriptorAngleMask_contDiff Q hQ ρ m N lam sig J i (b a) (x a)) _ _)
    (fun a ha n hn θ => (normalizedMaskFactor_derivative_bound (sourceAngularRadius_pos _ _ _)
      (descriptorAngleMask_norm_le_one Q hQ ρ m N lam sig J i (b a) (x a))
      (descriptorAngleMask_derivatives Q hQ ρ m N lam sig J i (b a) (x a))
      (Nat.add_le_add (hk a ha) hn) θ).trans (by
        change A^(k a)*(A*_ )^n ≤ _
        have hp := sourceAngularRadius_pos N sig (descriptorLength (b a))
        gcongr
        exact hscale a ha)) j le_rfl θ
  change ‖iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x) θ‖ ≤ _ at hh
  apply hh.trans
  rw [Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ A^K * ((S.card:ℝ)*(A*D))^j := by
      apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hK) (by positivity)
    _ = A^(K+j)*((S.card:ℝ)*D)^j := by rw [pow_add,mul_pow,mul_pow]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_AnchorSymbolDropping
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem inheritedMaskProduct_zero_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane)
    (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K) (θ : ℝ) :
    ‖inheritedMaskProduct S b k Q ρ m N lam sig J i x θ‖ ≤ symbolDerivativeConstant K^K := by
  let D := ∑ a ∈ S, (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹
  have hp a : 0 ≤ (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹ :=
    inv_nonneg.mpr (sourceAngularRadius_pos _ _ _).le
  have hD : 0 ≤ D := Finset.sum_nonneg (fun a _ => hp a)
  have hh := inheritedMaskProduct_bound S b k Q hQ ρ m N lam sig J i x K 0 hK D hD
    (fun a ha => Finset.single_le_sum (fun a _ => hp a) ha) θ
  simpa using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InheritedCircleRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem periodic_sourceAngle {f : ℝ → ℝ} (hf : Function.Periodic f (2*Real.pi)) (θ : ℝ) :
    f (sourceAngle (sourceUnitDirection θ)) = f θ := by
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := hf.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm,add_comm] using hp θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_InheritedSymbolMeasurability
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set MeasureTheory
open scoped ContDiff Topology

 theorem spatialAnchorMask_derivative_formula (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) (j : ℕ) (θ : ℝ) :
    iteratedDeriv j (fun φ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection φ)) θ =
      ∑ P ∈ occupiedAnchorPaths Q ρ n,
        if x ∈ (Q.descendant P).carrier then iteratedDeriv j (sourceTestMask (G P) d hd) θ else 0 := by
  classical
  unfold spatialAnchorMask
  simp only [circleTestMask_comp]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro P _
    by_cases hx : x ∈ (Q.descendant P).carrier <;> simp [hx]
  · intro P _
    by_cases hx : x ∈ (Q.descendant P).carrier
    · simp only [hx, ↓reduceIte]
      exact ((sourceTestMask_contDiff (G P) d hd).of_le
        (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    · simp only [hx, ↓reduceIte]
      exact contDiffAt_const

 theorem measurable_spatialAnchorMask_derivative (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (j : ℕ) :
    Measurable (fun z : Plane × UnitCircle =>
      iteratedDeriv j (fun φ => spatialAnchorMask Q ρ n G d hd z.1 (sourceUnitDirection φ)) (sourceAngle z.2)) := by
  simp only [spatialAnchorMask_derivative_formula]
  apply Finset.measurable_sum
  intro P _
  apply Measurable.ite ((Q.descendant P).measurable.preimage measurable_fst) _ measurable_const
  exact ((smooth_iteratedDeriv (sourceTestMask_contDiff (G P) d hd) j).continuous.measurable.comp
    measurable_sourceAngle).comp measurable_snd

 theorem measurable_inheritedCircleSymbol {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (hh : Measurable h) :
    Measurable (fun z : Plane × UnitCircle => inheritedCircleSymbol S b k Q ρ m N lam sig J i h z.1 z.2) := by
  unfold inheritedCircleSymbol
  apply (hh.comp measurable_fst).mul
  apply Complex.measurable_ofReal.comp
  apply Finset.measurable_prod
  intro a _
  apply measurable_const.mul
  exact measurable_spatialAnchorMask_derivative Q ρ _ _ _ _ (k a)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleAngularBins
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem circleAngularBin_comp (n j : ℕ) (θ : ℝ) :
    circleAngularBin n j (sourceUnitDirection θ) = periodicAngularBin n j θ :=
  periodic_sourceAngle (periodicAngularBin_periodic n j) θ

 theorem circleAngularBin_continuous (n j : ℕ) : Continuous (circleAngularBin n j) := by
  let A := Icc (-Real.pi) Real.pi
  let : CompactSpace A := isCompact_iff_compactSpace.mp (show IsCompact A from isCompact_Icc)
  let f : A → UnitCircle := fun θ => sourceUnitDirection θ
  have hf : Continuous f := continuous_sourceUnitDirection.comp continuous_subtype_val
  have hs : Function.Surjective f := by
    intro dir
    refine ⟨⟨sourceAngle dir, (Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩,
      sourceUnitDirection_sourceAngle dir⟩
  apply (hf.isClosedMap.isQuotientMap hf hs).continuous_iff.mpr
  have he : circleAngularBin n j ∘ f = fun θ : A => periodicAngularBin n j θ := by
    funext θ
    exact circleAngularBin_comp n j θ
  rw [he]
  exact (periodicAngularBin_contDiff n j).continuous.comp continuous_subtype_val

 theorem circleAngularBin_partition {n : ℕ} (hn : 0 < n) (dir : UnitCircle) :
    ∑ j ∈ Finset.range n, circleAngularBin n j dir = 1 :=
  periodicAngularBin_partition hn (sourceAngle dir)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphConeCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

theorem graphConeCutoff_contDiff : ContDiff ℝ ∞ graphConeCutoff :=
  Complex.ofRealCLM.contDiff.comp graphConeBump.contDiff

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedConeKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ContDiff

theorem measurable_sourceConeCircle (axis : ℝ) : Measurable (sourceConeCircle axis) :=
  graphConeCutoff_contDiff.continuous.measurable.comp
    (measurable_sourceAngle.comp (sourceCircleRotate_isometry (-axis)).continuous.measurable)

theorem measurable_rotatedBinSelection (n : ℕ) (S : Finset ℕ) (axis : ℝ) :
    Measurable (rotatedBinSelection n S axis) := by
  apply Complex.measurable_ofReal.comp
  exact (Finset.measurable_sum S (fun j _ =>
    (circleAngularBin_continuous n j).measurable.comp
      (sourceCircleRotate_isometry (-axis)).continuous.measurable))

theorem sourceConeCircle_norm_le (axis : ℝ) (dir : UnitCircle) :
    ‖sourceConeCircle axis dir‖ ≤ 1 := by
  simp only [sourceConeCircle, graphConeCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg graphConeBump.nonneg]
  exact graphConeBump.le_one

theorem rotatedBinSelection_norm_le (n : ℕ) (S : Finset ℕ) (axis : ℝ) (dir : UnitCircle) :
    ‖rotatedBinSelection n S axis dir‖ ≤ 1 := by
  have hb := selectedAngularBins_bounds n S (sourceAngle (sourceCircleRotate (-axis) dir))
  simpa only [rotatedBinSelection, circleAngularBin, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb.1] using hb.2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphKernelBounds
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem inheritedCircleSymbol_norm_le {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Plane → ℂ) (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K)
    (x : Plane) (hx : ‖h x‖ ≤ 1) (ω : UnitCircle) :
    ‖inheritedCircleSymbol S b k Q ρ m N lam sig J i h x ω‖ ≤
      symbolDerivativeConstant K^K := by
  classical
  simp only [inheritedCircleSymbol, norm_mul, Complex.norm_real]
  exact (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans
    (by simpa using (inheritedMaskProduct_zero_bound S b k Q hQ ρ m N lam sig J i
      (fun _ => x) K hK (sourceAngle ω)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FiniteAngularSquare
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem finite_complex_norm_square {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ((‖∑ i ∈ S, f i‖^2 : ℝ) : ℂ) = ∑ i ∈ S, ∑ j ∈ S, f i * conj (f j) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem angular_integral_cross (f g : UnitCircle → ℂ) (c : ℝ) :
    (∫ u, ∫ w, c • (f u * conj (g w)) ∂sourceArcLength ∂sourceArcLength) =
      c • ((∫ u, f u ∂sourceArcLength) * conj (∫ w, g w ∂sourceArcLength)) := by
  simp_rw [integral_smul, integral_const_mul, integral_conj, integral_mul_const]

theorem bounded_shell_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W)
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) (hf : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ r, ‖f r‖ ≤ C) :
    Integrable (fun r => Ψ (r/R) • f r) := by
  have hb : Integrable (Set.indicator (Icc (R/4) (4*R)) (fun _ : ℝ => W*C)) :=
    (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  apply hb.mono ((hΨ.comp (measurable_id.div_const R)).aestronglyMeasurable.smul hf)
  filter_upwards with r
  by_cases hn : Ψ (r/R) = 0
  · simp [hn]
  · have hh := hs _ hn
    have hr : r ∈ Icc (R/4) (4*R) := by
      constructor
      · have := (lt_div_iff₀ hR).mp hh.1; linarith
      · have := (div_lt_iff₀ hR).mp hh.2; linarith
    change ‖Ψ (r/R) • f r‖ ≤ ‖Set.indicator (Icc (R/4) (4*R)) (fun _ : ℝ => W*C) r‖
    rw [Set.indicator_of_mem hr, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hW hC),
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hw _) (hc r) (norm_nonneg _) hW

theorem finite_angular_square_radial {ι : Type*} (S : Finset ι)
    (f : ι → ℝ × UnitCircle → ℂ) (hf : ∀ i ∈ S, Measurable (f i))
    (C : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hb : ∀ i ∈ S, ∀ p, ‖f i p‖ ≤ C i)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W) {R : ℝ} (hR : 0 < R) :
    (∫ r : ℝ, Ψ (r/R) • ((‖∑ i ∈ S, ∫ u, f i (r,u) ∂sourceArcLength‖^2 : ℝ) : ℂ)) =
      ∑ i ∈ S, ∑ j ∈ S, ∫ r : ℝ, ∫ u, ∫ w,
        Ψ (r/R) • (f i (r,u) * conj (f j (r,w))) ∂sourceArcLength ∂sourceArcLength := by
  let F := fun i r => ∫ u, f i (r,u) ∂sourceArcLength
  have hFm : ∀ i ∈ S, Measurable (F i) := fun i hi =>
    (hf i hi).stronglyMeasurable.integral_prod_right'.measurable
  have hFb (i : ι) (hi : i ∈ S) (r : ℝ) : ‖F i r‖ ≤ sourceArcLength.real univ * C i :=
    (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (fun u => hb i hi (r,u)))).trans_eq (mul_comm _ _)
  have hcross (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      Integrable (fun r : ℝ => Ψ (r/R) • (F i r * conj (F j r))) := by
    apply bounded_shell_integrable hΨ hs hW hw hR _
      ((hFm i hi).mul (Complex.continuous_conj.measurable.comp (hFm j hj))).aestronglyMeasurable
      (mul_nonneg (mul_nonneg (measureReal_nonneg (μ := sourceArcLength) (s := univ)) (hC i hi))
        (mul_nonneg (measureReal_nonneg (μ := sourceArcLength) (s := univ)) (hC j hj)))
    intro r
    change ‖F i r * conj (F j r)‖ ≤ (sourceArcLength.real univ * C i) * (sourceArcLength.real univ * C j)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hFb i hi r) (hFb j hj r) (norm_nonneg _)
      (mul_nonneg measureReal_nonneg (hC i hi))
  simp_rw [finite_complex_norm_square, Finset.smul_sum, angular_integral_cross]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum S (fun j hj => hcross i hi j hj))]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_finsetSum S (fun j hj => hcross i hi j hj)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedBinPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set
open scoped ContDiff

theorem rotatedBinSelection_complement {n : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) (axis : ℝ) (dir : UnitCircle) :
    rotatedBinSelection n (Finset.range n \ S) axis dir =
      1-rotatedBinSelection n S axis dir := by
  simp only [rotatedBinSelection, Finset.sum_sdiff_eq_sub hS, circleAngularBin_partition hn,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem inactive_rotated_complement (n : ℕ) (hn : 0 < n) (e : UnitCircle)
    (radius axis : ℝ) (dir : UnitCircle) :
    rotatedBinSelection n (Finset.range n \ inactiveAngularLabels n e radius) axis dir =
      1-rotatedBinSelection n (inactiveAngularLabels n e radius) axis dir :=
  rotatedBinSelection_complement hn _ (Finset.filter_subset _ _) axis dir

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_InactiveBinScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem dyadic_power_real (N : ℕ) (s : ℝ) :
    ((2 : ℝ)^N)^s = (2 : ℝ)^((N : ℝ)*s) := by
  rw [← Real.rpow_natCast (2 : ℝ) N, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem graphAngularScale_cap_inactive {sig κ c₀ : ℝ}
    (hgap : 10*sig < κ) (hc : 0 < c₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t : ℝ, κ*(N : ℝ) ≤ t →
      graphAngularScale N sig t c₀ = graphUncappedAngularScale N sig t := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (sub_pos.mpr hgap) c₀⁻¹
  refine ⟨N₀,?_⟩
  intro N hN t ht
  apply min_eq_right
  have hb : graphUncappedAngularScale N sig t ≤ ((2 : ℝ)^N)^(sig*10-κ) := by
    simp only [graphUncappedAngularScale, dyadic_power_real, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hp : 0 < ((2 : ℝ)^N)^(κ-10*sig) := by positivity
  have hi := inv_anti₀ (inv_pos.mpr hc) (hN₀ N hN)
  simp only [inv_inv] at hi
  apply hb.trans
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  rw [show sig*10-κ = -(κ-10*sig) by ring, Real.rpow_neg (by positivity)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SelectedDistanceAssembly
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem distanceBinIntegrand_measurable (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) (axis : ℝ) (n j : ℕ) :
    Measurable (distanceBinIntegrand ρ ν X Y M₁ M₂ b₁ b₂ axis n j) := by
  exact (((measurable_sourceConeCircle axis).comp measurable_snd |>.mul
    ((measurable_rotatedBinSelection n {j} axis).comp measurable_snd)).mul
    (measurable_sourceAngularTransform ρ X M₁ b₁ h₁)).mul
    (Complex.continuous_conj.measurable.comp (measurable_sourceAngularTransform ν Y M₂ b₂ h₂))

theorem distanceBinIntegrand_bound (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b₁ b₂ : Plane → UnitCircle → ℂ) {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    (axis : ℝ) (n j : ℕ) (z : ℝ × UnitCircle) :
    ‖distanceBinIntegrand ρ ν X Y M₁ M₂ b₁ b₂ axis n j z‖ ≤
      (B₁*(ρ X).toReal/M₁)*(B₂*(ν Y).toReal/M₂) := by
  have hw : ‖sourceConeCircle axis z.2 * rotatedBinSelection n {j} axis z.2‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (sourceConeCircle_norm_le axis z.2)
      (rotatedBinSelection_norm_le n {j} axis z.2) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  rw [distanceBinIntegrand, norm_mul, norm_mul, Complex.norm_conj]
  exact (mul_le_mul (mul_le_mul hw (sourceAngularTransform_norm_le ρ X M₁ hM₁ b₁ B₁
    (fun x _ => hb₁ x) z.1 z.2) (norm_nonneg _) (by norm_num))
    (sourceAngularTransform_norm_le ν Y M₂ hM₂ b₂ B₂ (fun y _ => hb₂ y) z.1 z.2)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem sourceDistanceF_selected_bins (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    (axis : ℝ) (n : ℕ) (S : Finset ℕ) (r : ℝ) :
    sourceDistanceF (fun dir => sourceConeCircle axis dir * rotatedBinSelection n S axis dir)
      (fun z => sourceAngularTransform ρ X M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ b₂ z.1 z.2) r =
      ∑ j ∈ S, ∫ u, distanceBinIntegrand ρ ν X Y M₁ M₂ b₁ b₂ axis n j (r,u) ∂sourceArcLength := by
  have he (u : UnitCircle) :
      sourceConeCircle axis u * rotatedBinSelection n S axis u * sourceAngularTransform ρ X M₁ b₁ r u *
        conj (sourceAngularTransform ν Y M₂ b₂ r u) =
      ∑ j ∈ S, distanceBinIntegrand ρ ν X Y M₁ M₂ b₁ b₂ axis n j (r,u) := by
    simp only [distanceBinIntegrand, rotatedBinSelection, Finset.sum_singleton, Complex.ofReal_sum,
      Finset.mul_sum, Finset.sum_mul]
  simp only [sourceDistanceF, he]
  apply integral_finsetSum
  intro j _
  exact Integrable.of_bound
    ((distanceBinIntegrand_measurable ρ ν X Y M₁ M₂ b₁ b₂ h₁ h₂ axis n j).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable _
    (Filter.Eventually.of_forall (fun u => distanceBinIntegrand_bound ρ ν X Y hM₁ hM₂ b₁ b₂
      hB₁ hB₂ hb₁ hb₂ axis n j (r,u)))

theorem sourceParentRetainedSelection_eq_bins (N : ℕ) (sig t : ℝ)
    (X Y : DyadicSquare) (A B : CellPath) (dir : UnitCircle) :
    1-sourceParentInactiveSelection N sig t X Y A B dir =
      rotatedBinSelection (angularBinCount (graphUncappedAngularScale N sig t))
        (sourceParentActiveLabels N sig t X Y A B) (sourceParentAxis X Y) dir := by
  exact (inactive_rotated_complement _ (angularBinCount_pos (by unfold graphUncappedAngularScale; positivity))
    _ _ _ _).symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFourTransformExpansion
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem sourceGraphFourTransform_profile_normalization
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane)
    (Mp Ma : Fin 4 → ℝ) (hM : ∀ i, Mp i ≠ 0) (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (r : ℝ) (u v : UnitCircle) :
    sourceGraphFourTransform ρ X Ma b W r u v =
      ((Mp 0/Ma 0)*(Mp 1/Ma 1)*(Mp 2/Ma 2)*(Mp 3/Ma 3)) •
        sourceGraphFourTransform ρ X Mp b W r u v := by
  simp only [sourceGraphFourTransform, sourceAngularTransform, Complex.real_smul,
    map_mul, map_inv₀, Complex.conj_ofReal, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_inv]
  have h0 : (Mp 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM 0)
  have h1 : (Mp 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM 1)
  have h2 : (Mp 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM 2)
  have h3 : (Mp 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM 3)
  field_simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphInheritedTransformChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem continuous_supported_bump_bound {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |Ψ t| ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (1/4:ℝ) 4)).exists_bound_of_continuousOn
    hΨ.continuousOn
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro t
  by_cases hz : Ψ t = 0
  · simp only [hz, abs_zero]; exact le_max_left _ _
  · exact (hC t (Ioo_subset_Icc_self (hsupp t hz))).trans (le_max_right _ _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_DistanceGraphCross
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem distanceBinIntegrand_cross (ρ ν : Measure Plane) (X Y X' Y' : Set Plane)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (axis : ℝ) (n j k : ℕ)
    (r : ℝ) (u w : UnitCircle) :
    distanceBinIntegrand ρ ν X Y M₁ M₂ b₁ b₂ axis n j (r,u) *
      conj (distanceBinIntegrand ρ ν X' Y' M₁ M₂ b₁ b₂ axis n k (r,w)) =
    sourceGraphFourTransform ![ρ,ν,ν,ρ] ![X,Y,Y',X'] ![M₁,M₂,M₂,M₁] ![b₁,b₂,b₂,b₁]
      (graphSourceWeight true true axis n j k) r u w := by
  simp only [sourceGraphFourTransform,graphSourceWeight,↓reduceIte,graphRotatedDistanceWeight_eq,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons,distanceBinIntegrand,map_mul,starRingEnd_self_apply]
  ring

theorem graphOriginalTerm_profile_normalization
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (Mp Ma : Fin 4 → ℝ)
    (hM : ∀ i, Mp i ≠ 0) (b : Fin 4 → Plane → UnitCircle → ℂ)
    (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ) :
    graphOriginalTerm ρ X Ma b distance plus axis δ v j k Ψ =
      ((Mp 0/Ma 0)*(Mp 1/Ma 1)*(Mp 2/Ma 2)*(Mp 3/Ma 3)) •
        graphOriginalTerm ρ X Mp b distance plus axis δ v j k Ψ := by
  unfold graphOriginalTerm
  simp_rw [sourceGraphFourTransform_profile_normalization ρ X Mp Ma hM b,
    smul_comm (Ψ _) ((Mp 0/Ma 0)*(Mp 1/Ma 1)*(Mp 2/Ma 2)*(Mp 3/Ma 3)), integral_smul]
  exact smul_comm _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentBinFamily
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceParentRetainedF_bin_sum (N : ℕ) (sig t : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ) :
    sourceParentRetainedF N sig t X Y ρ ν n M₁ M₂ b₁ b₂ r =
      ∑ e ∈ sourceParentBinLabels N sig t X Y ρ ν n,
        ∫ u, sourceParentBinIntegrand N sig t X Y ρ ν M₁ M₂ b₁ b₂ e (r,u) ∂sourceArcLength := by
  simp only [sourceParentRetainedF,sourceCellwiseDistanceF,sourceParentRetainedSelection_eq_bins,
    sourceParentBinLabels,Finset.sum_sigma,Finset.sum_product,sourceParentBinIntegrand]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  exact sourceDistanceF_selected_bins ρ ν _ _ hM₁ hM₂ b₁ b₂ h₁ h₂ hB₁ hB₂ hb₁ hb₂ _ _ _ r

theorem sourceParentBinLabels_spec {N n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {e : ParentDistanceBinLabel}
    (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    e.1.1 ∈ occupiedAnchorPaths X ρ n ∧ e.1.2 ∈ occupiedAnchorPaths Y ν n ∧
      e.2 ∈ sourceParentActiveLabels N sig t X Y e.1.1 e.1.2 := by
  rcases Finset.mem_sigma.mp he with ⟨hpaths, hbin⟩
  exact ⟨(Finset.mem_product.mp hpaths).1, (Finset.mem_product.mp hpaths).2, hbin⟩

theorem sourceParentBinLabels_length {N n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {e : ParentDistanceBinLabel}
    (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    e.1.1.length = n ∧ e.1.2.length = n := by
  obtain ⟨hA,hB,_⟩ := sourceParentBinLabels_spec he
  exact ⟨(mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hA).1,
    (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hB).1⟩

theorem sourceParentBinLabels_bin_lt {N n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {e : ParentDistanceBinLabel}
    (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    e.2 < angularBinCount (graphUncappedAngularScale N sig t) :=
  Finset.mem_range.mp (Finset.mem_sdiff.mp (sourceParentBinLabels_spec he).2.2).1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_OriginalShellIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceAngularShellMeasure_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hzero : ∀ t ≤ 0, Ψ t = 0) (f : ℝ → E) :
    (∫ r, f r ∂sourceAngularShellMeasure v Ψ) =
      ((2:ℝ)^v)⁻¹ • ∫ r : ℝ, Ψ (r/(2:ℝ)^v) • f r := by
  have hR : 0 < (2:ℝ)^v := by positivity
  rw [sourceAngularShellMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hpos _) hR.le)]
  have he : (fun r => (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v) • f r) =
      fun r => ((2:ℝ)^v)⁻¹ • (Ψ (r/(2:ℝ)^v) • f r) := by
    funext r
    rw [smul_smul]
    congr 1
    ring
  rw [he, integral_smul]
  congr 1
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : r ∈ Ioi (0:ℝ)
  · exact Set.indicator_of_mem hr _
  · have hz : Ψ (r/(2:ℝ)^v) = 0 := hzero _ (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hR.le)
    simp [hr,hz]

theorem sourceRadialSquareEnergy_complex (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t) (hzero : ∀ t ≤ 0, Ψ t = 0)
    (F : ℝ → ℂ) :
    (sourceRadialSquareEnergy a v Ψ F : ℂ) =
      ((2:ℝ)^(2*(v-a))) • (((2:ℝ)^v)⁻¹ •
        ∫ r : ℝ, Ψ (r/(2:ℝ)^v) • ((‖F r‖^2 : ℝ) : ℂ)) := by
  rw [sourceRadialSquareEnergy, Complex.ofReal_mul, ← integral_complex_ofReal]
  rw [sourceAngularShellMeasure_integral v hΨ hpos hzero]
  rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ParentGraphEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceParentRetainedEnergy_graph_sum (N : ℕ) (sig t a v : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W) :
    (sourceRadialSquareEnergy a v Ψ (sourceParentRetainedF N sig t X Y ρ ν n M₁ M₂ b₁ b₂) : ℂ) =
      ((2:ℝ)^(2*(v-a))) •
        ∑ e ∈ sourceParentBinLabels N sig t X Y ρ ν n,
        ∑ f ∈ sourceParentBinLabels N sig t X Y ρ ν n,
          sourceParentGraphTerm N sig t v X Y ρ ν M₁ M₂ b₁ b₂ Ψ e f := by
  let S := sourceParentBinLabels N sig t X Y ρ ν n
  let F := sourceParentBinIntegrand N sig t X Y ρ ν M₁ M₂ b₁ b₂
  let C := fun e : ParentDistanceBinLabel =>
    (B₁*(ρ (X.descendant e.1.1).carrier).toReal/M₁)*
      (B₂*(ν (Y.descendant e.1.2).carrier).toReal/M₂)
  have hFm : ∀ e ∈ S, Measurable (F e) := fun e _ =>
    distanceBinIntegrand_measurable ρ ν _ _ M₁ M₂ b₁ b₂ h₁ h₂ _ _ _
  have hCb : ∀ e ∈ S, ∀ p, ‖F e p‖ ≤ C e := fun e _ p =>
    distanceBinIntegrand_bound ρ ν _ _ hM₁ hM₂ b₁ b₂ hB₁ hB₂ hb₁ hb₂ _ _ _ p
  have hh := finite_angular_square_radial S F hFm C (fun e _ => by dsimp [C]; positivity)
    hCb hΨ hs hW hw (by positivity : 0 < (2:ℝ)^v)
  rw [sourceRadialSquareEnergy_complex a v hΨ hpos (fun t ht => by
    by_contra hn
    have := (hs t hn).1
    linarith)]
  simp_rw [sourceParentRetainedF_bin_sum N sig t X Y ρ ν n hM₁ hM₂ b₁ b₂ h₁ h₂ hB₁ hB₂ hb₁ hb₂]
  change ((2:ℝ)^(2*(v-a))) • (((2:ℝ)^v)⁻¹ •
    (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • ((‖∑ e ∈ S, ∫ u, F e (r,u) ∂sourceArcLength‖^2 : ℝ) : ℂ))) = _
  rw [hh]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  simp only [F, sourceParentBinIntegrand, distanceBinIntegrand_cross, sourceParentGraphTerm, graphOriginalTerm]

theorem sourceParentGraphTerm_profile_ratios (N : ℕ) (sig t v : ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hp₁ : Mp₁ ≠ 0) (hp₂ : Mp₂ ≠ 0)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (Ψ : ℝ → ℝ) (e f : ParentDistanceBinLabel) :
    sourceParentGraphTerm N sig t v X Y ρ ν Ma₁ Ma₂ b₁ b₂ Ψ e f =
      ((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) • sourceParentGraphTerm N sig t v X Y ρ ν Mp₁ Mp₂ b₁ b₂ Ψ e f := by
  unfold sourceParentGraphTerm
  rw [graphOriginalTerm_profile_normalization _ _ ![Mp₁,Mp₂,Mp₂,Mp₁] ![Ma₁,Ma₂,Ma₂,Ma₁]
    (by intro index; fin_cases index <;> first | exact hp₁ | exact hp₂)]
  congr 1
  change (Mp₁/Ma₁)*(Mp₂/Ma₂)*(Mp₂/Ma₂)*(Mp₁/Ma₁) = (Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ParentGraphIndices
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceParentGraphIndex_injective (A B : CellPath) : Function.Injective (sourceParentGraphIndex A B) := by
  classical
  rintro ⟨⟨⟨P,Q⟩,j⟩,⟨⟨P',Q'⟩,k⟩⟩ ⟨⟨⟨S,T⟩,l⟩,⟨⟨S',T'⟩,m⟩⟩ h
  simp only [sourceParentGraphIndex,Prod.mk.injEq,List.append_cancel_left_eq] at h
  obtain ⟨⟨⟨hP,hQ⟩,⟨hQ',hP'⟩⟩,⟨⟨hj,hk⟩,_⟩⟩ := h
  subst S; subst T; subst S'; subst T'; subst l; subst m
  rfl

theorem sourceParentGraphIndex_mem {N a n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {A B : CellPath} (hA : A.length = a) (hB : B.length = a)
    {e f : ParentDistanceBinLabel} (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n)
    (hf : f ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    sourceParentGraphIndex A B (e,f) ∈ graphNonedgeIndices (a+n)
      (angularBinCount (graphUncappedAngularScale N sig t)) := by
  classical
  obtain ⟨heP,heQ⟩ := sourceParentBinLabels_length he
  obtain ⟨hfP,hfQ⟩ := sourceParentBinLabels_length hf
  have hej := sourceParentBinLabels_bin_lt he
  have hfj := sourceParentBinLabels_bin_lt hf
  simp [graphNonedgeIndices,graphCellQuadIndices,sourceParentGraphIndex,mem_dyadicPaths,
    List.length_append,hA,hB,heP,heQ,hfP,hfQ,hej,hfj]

theorem sourceParentGraphIndices_subset {N a n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {A B : CellPath} (hA : A.length = a) (hB : B.length = a) :
    sourceParentGraphIndices N sig t X Y ρ ν n A B ⊆ graphNonedgeIndices (a+n)
      (angularBinCount (graphUncappedAngularScale N sig t)) := by
  classical
  intro q hq
  obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp hq
  exact sourceParentGraphIndex_mem hA hB (Finset.mem_product.mp hef).1 (Finset.mem_product.mp hef).2

theorem sourceParentGraphIndex_cells (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (e f : ParentDistanceBinLabel) (l : Fin 4) :
    graphQuadCells ![Q₁,Q₂,Q₂,Q₁] (sourceParentGraphIndex A B (e,f)).1 l =
      ![((Q₁.descendant A).descendant e.1.1),((Q₂.descendant B).descendant e.1.2),
        ((Q₂.descendant B).descendant f.1.2),((Q₁.descendant A).descendant f.1.1)] l := by
  fin_cases l <;> simp [graphQuadCells,graphQuadPath,sourceParentGraphIndex,DyadicSquare.descendant_append]

theorem sourceParentGraphIndices_parent (Q₁ Q₂ : DyadicSquare) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (A B : CellPath) (N n : ℕ) (sig t : ℝ) (ρ ν : Measure Plane)
    {q : GraphNonedgeIndex}
    (hq : q ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    (l : Fin 4) :
    (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] q.1 l).carrier ⊆
      (graphSlotParent true (Q₁.descendant A) (Q₂.descendant B) l).carrier := by
  classical
  obtain ⟨⟨e,f⟩,_,rfl⟩ := Finset.mem_image.mp hq
  rw [sourceParentGraphIndex_cells]
  fin_cases l <;> simp only [graphSlotParent,↓reduceIte] <;>
    apply DyadicSquare.descendant_subset <;>
    first | exact Q₁.descendant_side_pos hQ₁ A | exact Q₂.descendant_side_pos hQ₂ B

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ParentAbsoluteGraphAssembly
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceParentGraphTerm_absolute (N : ℕ) (sig t v : ℝ) (Q₁ Q₂ : DyadicSquare)
    (A B : CellPath) (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (Ψ : ℝ → ℝ) (e f : ParentDistanceBinLabel) :
    sourceParentGraphTerm N sig t v (Q₁.descendant A) (Q₂.descendant B) ρ ν M₁ M₂ b₁ b₂ Ψ e f =
      let q := sourceParentGraphIndex A B (e,f)
      graphOriginalTerm ![ρ,ν,ν,ρ]
        (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] q.1 l).carrier)
        ![M₁,M₂,M₂,M₁] ![b₁,b₂,b₂,b₁] true q.2.2
        (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B))
        (graphUncappedAngularScale N sig t) v q.2.1.1 q.2.1.2 Ψ := by
  dsimp only
  have hc : (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] (sourceParentGraphIndex A B (e,f)).1 l).carrier) =
      ![((Q₁.descendant A).descendant e.1.1).carrier,((Q₂.descendant B).descendant e.1.2).carrier,
        ((Q₂.descendant B).descendant f.1.2).carrier,((Q₁.descendant A).descendant f.1.1).carrier] := by
    funext l
    rw [sourceParentGraphIndex_cells]
    fin_cases l <;> rfl
  rw [hc]
  rfl

theorem sourceParentGraphSum_absolute (N n : ℕ) (sig t v : ℝ) (Q₁ Q₂ : DyadicSquare)
    (A B : CellPath) (ρ ν : Measure Plane) (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (Ψ : ℝ → ℝ) :
    (∑ e ∈ sourceParentBinLabels N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n,
      ∑ f ∈ sourceParentBinLabels N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n,
        sourceParentGraphTerm N sig t v (Q₁.descendant A) (Q₂.descendant B) ρ ν M₁ M₂ b₁ b₂ Ψ e f) =
    ∑ q ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B,
      graphOriginalTerm ![ρ,ν,ν,ρ] (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] q.1 l).carrier)
        ![M₁,M₂,M₂,M₁] ![b₁,b₂,b₂,b₁] true q.2.2
        (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B))
        (graphUncappedAngularScale N sig t) v q.2.1.1 q.2.1.2 Ψ := by
  classical
  rw [sourceParentGraphIndices,Finset.sum_image]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    exact sourceParentGraphTerm_absolute N sig t v Q₁ Q₂ A B ρ ν M₁ M₂ b₁ b₂ Ψ e f
  · exact fun x _ y _ h => sourceParentGraphIndex_injective A B h

theorem sourceParentRetainedEnergy_absolute_graph_sum (N : ℕ) (sig t a v : ℝ)
    (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ)
    {Ma₁ Ma₂ Mp₁ Mp₂ : ℝ} (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W) :
    (sourceRadialSquareEnergy a v Ψ (sourceParentRetainedF N sig t (Q₁.descendant A) (Q₂.descendant B)
      ρ ν n Ma₁ Ma₂ b₁ b₂) : ℂ) =
      ((2:ℝ)^(2*(v-a))) • (((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) •
        ∑ q ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B,
          graphOriginalTerm ![ρ,ν,ν,ρ] (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] q.1 l).carrier)
            ![Mp₁,Mp₂,Mp₂,Mp₁] ![b₁,b₂,b₂,b₁] true q.2.2
            (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B))
            (graphUncappedAngularScale N sig t) v q.2.1.1 q.2.1.2 Ψ) := by
  rw [sourceParentRetainedEnergy_graph_sum N sig t a v _ _ ρ ν n hMa₁ hMa₂ b₁ b₂
    h₁ h₂ hB₁ hB₂ hb₁ hb₂ hΨ hpos hs hW hw]
  simp_rw [sourceParentGraphTerm_profile_ratios N sig t v _ _ ρ ν Ma₁ Ma₂ Mp₁ Mp₂ hMp₁ hMp₂,
    ← Finset.smul_sum]
  rw [sourceParentGraphSum_absolute]

theorem graphProfileCoefficient_distance (N : ℕ) (m₁ m₂ : ℝ → ℝ) (a p : ℝ) :
    graphProfileCoefficient N ![m₁,m₂,m₂,m₁] a p =
      ((((2:ℝ)^N)^(-m₁ p)/((2:ℝ)^N)^(-m₁ a))^2)*
      ((((2:ℝ)^N)^(-m₂ p)/((2:ℝ)^N)^(-m₂ a))^2) := by
  simp only [graphProfileCoefficient,Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualDistanceGraphAssembly
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem sourceDistanceSlot_comp {α : Type*} (f : Fin 2 → α) :
    (fun l => f (sourceDistanceSlot l)) = ![f 0,f 1,f 1,f 0] := by
  funext l
  fin_cases l <;> rfl

theorem uniform_actual_retained_distance_graph_oai
    {sig κ c₀ : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ)
    (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) (K : ℕ) (lam T : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (J i : ℕ) (h : Fin 2 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N → κ*N ≤ (n:ℝ) →
    0 ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let t : ℝ := (a+n:ℕ)-a
    let θ := graphAngularScale N sig t c₀
    let I := sourceParentGraphIndices N sig t X Y (ρ 0) (ρ 1) n A B
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2
      (sourceParentAxis X Y) e.1.1 e.1.2
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
    let F := fun e : GraphNonedgeIndex => graphOriginalTerm ![ρ 0,ρ 1,ρ 1,ρ 0]
      (fun l => (graphQuadCells ![Q 0,Q 1,Q 1,Q 0] e.1 l).carrier)
      ![M 0,M 1,M 1,M 0] ![β 0,β 1,β 1,β 0] true e.2.2 (sourceParentAxis X Y) θ v e.2.1.1 e.2.1.2 Ψ
    ‖(sourceRadialSquareEnergy a v Ψ (sourceParentRetainedF N sig t X Y (ρ 0) (ρ 1) n
        (((2:ℝ)^N)^(-mass 0 a)) (((2:ℝ)^N)^(-mass 1 a)) (β 0) (β 1)) : ℂ) -
      ((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N ![mass 0,mass 1,mass 1,mass 0] a (a+n) •
        (∑ e ∈ graphRetainedIndices I N sig (a+n) true ![Q 0,Q 1,Q 1,Q 0] rep, F e))‖ ≤ ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₁,hrem⟩ := uniform_regularized_original_graph_removal hsig K lam T hΨ hs hc hcap
  obtain ⟨N₂,hcaps⟩ := graphAngularScale_cap_inactive hgap hc
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ hQs ρ mass B δ hd J i h hh hhb a n v
    hp hlow hu ht hLu hv A B' hA hB hsep
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let X := (Q 0).descendant A
  let Y := (Q 1).descendant B'
  let t : ℝ := (a+n:ℕ)-a
  have htval : t = n := by dsimp [t]; push_cast; ring
  have hθ := hcaps N ((le_max_right _ _).trans hN) t (by simpa only [htval] using hlow)
  have hX : 0 < X.side := (Q 0).descendant_side_pos (hQ 0) A
  have hY : 0 < Y.side := (Q 1).descendant_side_pos (hQ 1) B'
  have hXs : X.side ≤ (2:ℝ)^(-(a:ℝ)) := by
    dsimp [X]; rw [DyadicSquare.descendant_side,hA,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simpa only [one_div] using div_le_div_of_nonneg_right (hQs 0) (by positivity : (0:ℝ) ≤ 2^a)
  have hYs : Y.side ≤ (2:ℝ)^(-(a:ℝ)) := by
    dsimp [Y]; rw [DyadicSquare.descendant_side,hB,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simpa only [one_div] using div_le_div_of_nonneg_right (hQs 1) (by positivity : (0:ℝ) ≤ 2^a)
  let I := sourceParentGraphIndices N sig t X Y (ρ 0) (ρ 1) n A B'
  have hI : I ⊆ graphNonedgeIndices (a+n) (angularBinCount (graphAngularScale N sig t c₀)) := by
    rw [hθ]
    exact sourceParentGraphIndices_subset hA hB
  have hr := hrem N ((le_max_left _ _).trans hN)
    (fun l => S (sourceDistanceSlot l)) (fun l => d (sourceDistanceSlot l)) (fun l => k (sourceDistanceSlot l))
    (fun l => hcard _) (fun l => hK _) L (fun l => hL _)
    (fun l => Q (sourceDistanceSlot l)) (fun l => hQ _) (fun l => hQs _)
    (fun l => ρ (sourceDistanceSlot l)) (fun l => mass (sourceDistanceSlot l)) B δ (fun l => hd _)
    J i (fun l => h (sourceDistanceSlot l)) (fun l => hh _) (fun l => hhb _)
    a (a+n) v (Nat.cast_nonneg a) (by exact_mod_cast Nat.le_add_right a n) hp
    (by simpa only [Nat.cast_add] using hu) (by simpa only [Nat.cast_add,add_sub_cancel_left] using ht)
    (by simpa only [Nat.cast_add] using hLu) hv true X Y hX hY hXs hYs (fun _ => hsep)
    (sourceParentAxis X Y) I hI (by
      intro e he l
      rw [sourceDistanceSlot_comp]
      exact sourceParentGraphIndices_parent (Q 0) (Q 1) (hQ 0) (hQ 1) A B' N n sig t (ρ 0) (ρ 1) he l)
  dsimp only at hr ⊢
  simp only [sourceDistanceSlot_comp] at hr
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  have hb : ∀ (l : Fin 2) (x : Plane) (dir : UnitCircle), ‖β l x dir‖ ≤ symbolDerivativeConstant K^K := by
    intro l x dir
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) dir
  have he := sourceParentRetainedEnergy_absolute_graph_sum N sig t a v (Q 0) (Q 1) A B'
    (ρ 0) (ρ 1) n (Ma₁ := ((2:ℝ)^N)^(-mass 0 a)) (Ma₂ := ((2:ℝ)^N)^(-mass 1 a))
    (Mp₁ := ((2:ℝ)^N)^(-mass 0 (a+n))) (Mp₂ := ((2:ℝ)^N)^(-mass 1 (a+n)))
    (by positivity) (by positivity) (by positivity) (by positivity) (β 0) (β 1) (hm 0) (hm 1)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K) (hb 0) (hb 1) hΨ.continuous.measurable hpos hs hW hw
  rw [← graphProfileCoefficient_distance] at he
  rw [← hθ] at he
  rw [he]
  have hM4 := sourceDistanceSlot_comp (fun l => ((2:ℝ)^N)^(-mass l (a+n:ℕ)))
  have hβ4 := sourceDistanceSlot_comp β
  rw [hM4,hβ4] at hr
  simpa only [Nat.cast_add,X,Y,I,t,β] using hr

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_retained_distance_graph_oai := @OAI.PlanarFalconer.uniform_actual_retained_distance_graph_oai
