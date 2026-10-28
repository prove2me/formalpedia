-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_product_H_graph
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:31:06.199195+00:00
-- url     : https://prove2.me/submissions/be08913b-a94a-4d44-9eef-ea63dabf0e20

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
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem DyadicSquare.cover_children (Q : DyadicSquare) :
    Q.carrier = ((Q.child false false).carrier ∪ (Q.child false true).carrier) ∪
      ((Q.child true false).carrier ∪ (Q.child true true).carrier) := by
  ext z
  simp only [carrier, child, Bool.false_eq_true, ↓reduceIte,
    add_zero, mem_ofPred_eq, mem_union]
  constructor
  · intro hz
    by_cases hx : z 0 < Q.x + Q.side / 2 <;>
      by_cases hy : z 1 < Q.y + Q.side / 2
    · exact Or.inl (Or.inl ⟨hz.1,hx,hz.2.2.1,hy⟩)
    · exact Or.inl (Or.inr ⟨hz.1,hx,by linarith,by linarith [hz.2.2.2]⟩)
    · exact Or.inr (Or.inl ⟨by linarith,by linarith [hz.2.1],hz.2.2.1,hy⟩)
    · exact Or.inr (Or.inr ⟨by linarith,by linarith [hz.2.1],
        by linarith,by linarith [hz.2.2.2]⟩)
  · intro hz
    rcases hz with (hz | hz) | (hz | hz) <;>
      refine ⟨by linarith [hz.1,hz.2.1], by linarith [hz.1,hz.2.1],
        by linarith [hz.2.2.1,hz.2.2.2], by linarith [hz.2.2.1,hz.2.2.2]⟩

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
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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

theorem DyadicSquare.mem_descendant_at_depth (Q : DyadicSquare) (n : ℕ)
    {z : Plane} (hz : z ∈ Q.carrier) :
    ∃ p ∈ dyadicPaths n, z ∈ (Q.descendant p).carrier := by
  induction n generalizing Q with
  | zero => exact ⟨[],by simp, hz⟩
  | succ n ih =>
    have step (i j : Bool) (hz : z ∈ (Q.child i j).carrier) :
        ∃ p ∈ dyadicPaths (n+1), z ∈ (Q.descendant p).carrier := by
      obtain ⟨p,hp,hz⟩ := ih _ hz
      exact ⟨(i,j) :: p,by simpa using hp,hz⟩
    rw [Q.cover_children] at hz
    rcases hz with (hz | hz) | (hz | hz)
    · exact step false false hz
    · exact step false true hz
    · exact step true false hz
    · exact step true true hz

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
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicIntegralSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem DyadicSquare.biUnion_descendants (Q : DyadicSquare) (hQ : 0 < Q.side)
    (n : ℕ) : (⋃ P ∈ dyadicPaths n, (Q.descendant P).carrier) = Q.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨P, _, hx⟩ := mem_iUnion₂.mp hx
    exact Q.descendant_subset hQ P hx
  · intro hx
    obtain ⟨P, hP, hxP⟩ := Q.mem_descendant_at_depth n hx
    exact mem_iUnion₂.mpr ⟨P, hP, hxP⟩

theorem DyadicSquare.integral_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) (f : Plane → ℂ)
    (hf : IntegrableOn f Q.carrier ρ) :
    (∫ x in Q.carrier, f x ∂ρ) =
      ∑ P ∈ dyadicPaths n, ∫ x in (Q.descendant P).carrier, f x ∂ρ := by
  rw [← Q.biUnion_descendants hQ n]
  apply integral_biUnion_finset
  · exact fun P _ => (Q.descendant P).measurable
  · intro P hP S hS hne
    exact Q.descendants_disjoint hQ
      (((mem_dyadicPaths n P).mp hP).trans ((mem_dyadicPaths n S).mp hS).symm) hne
  · exact fun P _ => hf.mono_set (Q.descendant_subset hQ P)

theorem DyadicSquare.integral_split_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) (f : Plane → ℂ)
    (hf : IntegrableOn f Q.carrier ρ) :
    (∫ x in Q.carrier, f x ∂ρ) =
      ∑ P ∈ occupiedAnchorPaths Q ρ n, ∫ x in (Q.descendant P).carrier, f x ∂ρ := by
  classical
  rw [Q.integral_split hQ ρ n f hf]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hP hnot
  have hz : ρ (Q.descendant P).carrier = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hP, bot_lt_iff_ne_bot.mpr hne⟩)
  rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]

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

theorem integrableOn_angular_integrand (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2))
    (C : ℝ) (hC : ∀ x ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    IntegrableOn (fun x =>
      Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω) X ρ := by
  apply (integrable_const C).mono
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_id.prodMk measurable_const)
  · filter_upwards with x
    rw [angular_integrand_norm]
    exact (hC x ω).trans (le_abs_self C)

theorem sourceAngularTransform_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (n : ℕ) (Ma Mp : ℝ) (hMp : Mp ≠ 0)
    (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2))
    (C : ℝ) (hC : ∀ x ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ Q.carrier Ma b r ω =
      (Mp / Ma) • ∑ P ∈ occupiedAnchorPaths Q ρ n,
        sourceAngularTransform ρ (Q.descendant P).carrier Mp b r ω := by
  unfold sourceAngularTransform
  rw [Q.integral_split_occupied hQ ρ n _ (integrableOn_angular_integrand ρ _ b hb C hC r ω)]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, mul_inv_cancel₀ hMp, one_div]

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

theorem periodicAngularBin_bounds (n j : ℕ) (θ : ℝ) :
    0 ≤ periodicAngularBin n j θ ∧ periodicAngularBin n j θ ≤ 1 :=
  angularBinSelection_bounds _ _

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

 theorem circleAngularBin_bounds (n j : ℕ) (dir : UnitCircle) :
    0 ≤ circleAngularBin n j dir ∧ circleAngularBin n j dir ≤ 1 :=
  periodicAngularBin_bounds n j (sourceAngle dir)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularLabelEligibility
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem ineligible_symbol_zero_ae {ρ : Measure Plane} {X : Set Plane}
    {b : Plane → UnitCircle → ℂ} {n j : ℕ}
    (h : ¬ AngularLabelEligible ρ X b n j) {ω : UnitCircle}
    (hω : ω ∈ tsupport (circleAngularBin n j)) :
    ∀ᵐ x ∂ρ.restrict X, b x ω = 0 := by
  by_contra hh
  exact h ⟨ω,hω,hh⟩

theorem ineligible_transform_zero {ρ : Measure Plane} {X : Set Plane}
    {b : Plane → UnitCircle → ℂ} {n j : ℕ}
    (h : ¬ AngularLabelEligible ρ X b n j) (M r : ℝ) (ω : UnitCircle) :
    (circleAngularBin n j ω : ℂ) * sourceAngularTransform ρ X M b r ω = 0 := by
  by_cases hω : circleAngularBin n j ω = 0
  · simp [hω]
  · have he := ineligible_symbol_zero_ae h (subset_closure hω)
    have hi : (∫ x in X, Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (ω : Plane) x : ℂ))*b x ω ∂ρ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [he] with x hx
      simp [hx]
    simp only [sourceAngularTransform, hi, smul_zero, mul_zero]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ENNReal

theorem sourcePlaneWave_sub (r : ℝ) (ω : UnitCircle) (x y : Plane) :
    sourcePlaneWave r ω x * conj (sourcePlaneWave r ω y) =
      sourcePlaneWave r ω (x-y) := by
  simp only [sourcePlaneWave, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, ← Complex.exp_add, inner_sub_right, Complex.ofReal_sub]
  congr 1
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphSignPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem graphSignPlus_contDiff : ContDiff ℝ ∞ graphSignPlus := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_fst.add contDiff_snd).norm_sq ℝ).sub contDiff_const |>.div_const 2)

theorem graphSignMinus_contDiff : ContDiff ℝ ∞ graphSignMinus :=
  contDiff_const.sub graphSignPlus_contDiff

theorem graphSignPartition_bounds (p : Plane × Plane) :
    0 ≤ graphSignPlus p ∧ graphSignPlus p ≤ 1 ∧
    0 ≤ graphSignMinus p ∧ graphSignMinus p ≤ 1 ∧
    graphSignPlus p+graphSignMinus p = 1 := by
  have h₀ := Real.smoothTransition.nonneg ((‖p.1+p.2‖^2-1)/2)
  have h₁ := Real.smoothTransition.le_one ((‖p.1+p.2‖^2-1)/2)
  dsimp [graphSignPlus, graphSignMinus]
  exact ⟨h₀, h₁, sub_nonneg.mpr h₁, sub_le_self _ h₀, by ring⟩

theorem circleGraphSignPartition (p : UnitCircle × UnitCircle) :
    0 ≤ circleGraphSignPlus p ∧ 0 ≤ circleGraphSignMinus p ∧
      circleGraphSignPlus p+circleGraphSignMinus p = 1 :=
  ⟨(graphSignPartition_bounds (p.1,p.2)).1,
    (graphSignPartition_bounds (p.1,p.2)).2.2.1,
    (graphSignPartition_bounds (p.1,p.2)).2.2.2.2⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphEndpointContinuity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem circleGraphSignPlus_continuous : Continuous circleGraphSignPlus := by
  exact graphSignPlus_contDiff.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

theorem circleGraphSignMinus_continuous : Continuous circleGraphSignMinus := by
  exact graphSignMinus_contDiff.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

theorem graphBinWeight_continuous (n j k : ℕ) : Continuous (graphBinWeight n j k) :=
  ((circleAngularBin_continuous n j).comp continuous_fst).mul
    ((circleAngularBin_continuous n k).comp continuous_snd)

theorem graphProductWeight_continuous (plus : Bool) (n j k : ℕ) :
    Continuous (graphProductWeight plus n j k) := by
  cases plus <;> exact Complex.continuous_ofReal.comp
    ((graphBinWeight_continuous n j k).mul (by first
      | exact circleGraphSignMinus_continuous
      | exact circleGraphSignPlus_continuous))

theorem graphProductWeight_partition (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    graphProductWeight true n j k p + graphProductWeight false n j k p =
      (graphBinWeight n j k p : ℂ) := by
  simp only [graphProductWeight, Bool.false_eq_true, ↓reduceIte, ← Complex.ofReal_add]
  rw [← mul_add, (circleGraphSignPartition p).2.2, mul_one]

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

theorem graphBinWeight_bounds (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    0 ≤ graphBinWeight n j k p ∧ graphBinWeight n j k p ≤ 1 := by
  have hu := circleAngularBin_bounds n j p.1
  have hv := circleAngularBin_bounds n k p.2
  exact ⟨mul_nonneg hu.1 hv.1, by simpa [graphBinWeight] using mul_le_mul hu.2 hv.2 hv.1 zero_le_one⟩

theorem graphProductWeight_norm_le (plus : Bool) (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphProductWeight plus n j k p‖ ≤ 1 := by
  have hb := graphBinWeight_bounds n j k p
  have hs := graphSignPartition_bounds (p.1,p.2)
  cases plus <;> simp only [graphProductWeight, Bool.false_eq_true, ↓reduceIte,
    Complex.norm_real, Real.norm_eq_abs, circleGraphSignPlus, circleGraphSignMinus]
  · rw [abs_of_nonneg (mul_nonneg hb.1 hs.2.2.1)]
    exact (mul_le_mul hb.2 hs.2.2.2.1 hs.2.2.1 zero_le_one).trans_eq (by ring)
  · rw [abs_of_nonneg (mul_nonneg hb.1 hs.1)]
    exact (mul_le_mul hb.2 hs.2.1 hs.1 zero_le_one).trans_eq (by ring)

theorem graphFourKernel_measurable (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hW : Measurable W) :
    Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      graphFourKernel b W p.2 p.1.1 p.1.2.1 p.1.2.2) := by
  unfold graphFourKernel graphFourAmplitude sourcePlaneWave
  have h0 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 0 (p.2 0) p.1.2.1) := (hb 0).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 0, p.1.2.1)) from by fun_prop)
  have h1 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 1 (p.2 1) p.1.2.1) := (hb 1).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 1, p.1.2.1)) from by fun_prop)
  have h2 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 2 (p.2 2) p.1.2.2) := (hb 2).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 2, p.1.2.2)) from by fun_prop)
  have h3 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 3 (p.2 3) p.1.2.2) := (hb 3).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 3, p.1.2.2)) from by fun_prop)
  apply Measurable.mul
  · fun_prop
  · exact (((hW.comp (measurable_snd.comp measurable_fst)).mul
      (h0.mul (Complex.continuous_conj.measurable.comp h1))).mul
      (h2.mul (Complex.continuous_conj.measurable.comp h3)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RadialShellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem sourceAngularShellMeasure_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    sourceAngularShellMeasure v Ψ univ ≤ ENNReal.ofReal (4*B) := by
  let A : ℝ := (2:ℝ)^v
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  unfold sourceAngularShellMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (Ψ (r/A)/A)) ≤ _
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), (Iic (4*A)).indicator (fun _ => ENNReal.ofReal (B/A)) r := by
      apply lintegral_mono
      intro r
      dsimp only
      by_cases hr : r ≤ 4*A
      · rw [indicator_of_mem (show r ∈ Iic (4*A) from hr)]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb _) hA.le)
      · rw [indicator_of_notMem (show r ∉ Iic (4*A) from hr)]
        rw [hs _ ((lt_div_iff₀ hA).mpr (lt_of_not_ge hr)), zero_div, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (B/A) * ENNReal.ofReal (4*A) := by
      rw [lintegral_indicator measurableSet_Iic, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iic]
      rw [inter_comm, Ioi_inter_Iic, Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (4*B) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hB hA.le)]
      congr 1
      rw [mul_left_comm, div_mul_cancel₀ _ hA.ne']

theorem sourceAngularShellMeasure_finite (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) : IsFiniteMeasure (sourceAngularShellMeasure v Ψ) :=
  ⟨(sourceAngularShellMeasure_mass_le v Ψ hB hb hs).trans_lt ENNReal.ofReal_lt_top⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FiniteAngularSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

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

theorem graphFourKernel_endpoint_product
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u v : UnitCircle) (x : Fin 4 → Plane) :
    graphFourKernel b W x r u v = W (u,v) *
      ∏ i : Fin 4, (![fun y => sourcePlaneWave r u y * b 0 y u,
        fun y => conj (sourcePlaneWave r u y * b 1 y u),
        fun y => sourcePlaneWave r v y * b 2 y v,
        fun y => conj (sourcePlaneWave r v y * b 3 y v)] i) (x i) := by
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, graphFourKernel, graphFourAmplitude,
    ← sourcePlaneWave_sub, map_mul]
  ring

theorem sourceGraphFourTransform_endpoint_integral
    (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u v : UnitCircle) :
    sourceGraphFourTransform ρ X M b W r u v =
      ((M 0*M 1)*(M 2*M 3))⁻¹ •
        (∫ x, graphFourKernel b W x r u v ∂Measure.pi (fun i => (ρ i).restrict (X i))) := by
  simp_rw [graphFourKernel_endpoint_product, integral_const_mul]
  rw [integral_fintype_prod_eq_prod]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [integral_conj]
  simp only [sourceGraphFourTransform, sourceAngularTransform, sourcePlaneWave,
    Complex.real_smul, map_mul, map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv,
    Complex.ofReal_mul, mul_inv_rev]
  ring

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

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularProductEnergyIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ComplexConjugate

theorem sourceRealAngularMoment_measurable (U : ℝ × UnitCircle → ℂ) (hU : Measurable U) :
    Measurable (sourceRealAngularMoment U) :=
  (hU.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

theorem sourceRealAngularMoment_nonneg (U : ℝ × UnitCircle → ℂ) (r : ℝ) :
    0 ≤ sourceRealAngularMoment U r := integral_nonneg (fun _ => sq_nonneg _)

theorem integrable_circle_norm_square (U : UnitCircle → ℂ) (hU : Measurable U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, ‖U u‖ ≤ C) :
    Integrable (fun u => ‖U u‖^2) sourceArcLength := by
  apply Integrable.of_bound (hU.norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards with u
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb u)

theorem sourceRealAngularMoment_bound (U : ℝ × UnitCircle → ℂ) {C : ℝ}
    (hb : ∀ p, ‖U p‖ ≤ C) (r : ℝ) :
    sourceRealAngularMoment U r ≤ C^2*sourceArcLength.real univ := by
  have hC : 0 ≤ C := (norm_nonneg (U (r,sourceUnitDirection 0))).trans (hb _)
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with u
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb _)

theorem sourceAngularMoment_eq_ofReal (U : ℝ × UnitCircle → ℂ) (hU : Measurable U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ p, ‖U p‖ ≤ C) (r : ℝ) :
    sourceAngularMoment U r = ENNReal.ofReal (sourceRealAngularMoment U r) := by
  have hi := integrable_circle_norm_square (fun u => U (r,u))
    (hU.comp (measurable_const.prodMk measurable_id)) hC (fun u => hb (r,u))
  rw [sourceRealAngularMoment,ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  apply lintegral_congr
  intro u
  rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]

theorem sourceAngularH_finite_integral (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hbU : ∀ p, ‖U p‖ ≤ C) (hbV : ∀ p, ‖V p‖ ≤ D) :
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    (sourceAngularH a v Ψ U V).toReal = (2:ℝ)^(2*(v-a)) *
      ∫ r, sourceRealAngularMoment U r * sourceRealAngularMoment V r ∂sourceAngularShellMeasure v Ψ := by
  have hp (r : ℝ) : 0 ≤ sourceRealAngularMoment U r * sourceRealAngularMoment V r :=
    mul_nonneg (sourceRealAngularMoment_nonneg U r) (sourceRealAngularMoment_nonneg V r)
  have hi : Integrable (fun r => sourceRealAngularMoment U r * sourceRealAngularMoment V r)
      (sourceAngularShellMeasure v Ψ) := by
    apply Integrable.of_bound
      ((sourceRealAngularMoment_measurable U hU).mul (sourceRealAngularMoment_measurable V hV)).aestronglyMeasurable
      ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ))
    filter_upwards with r
    change ‖sourceRealAngularMoment U r * sourceRealAngularMoment V r‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (hp r)]
    exact mul_le_mul (sourceRealAngularMoment_bound U hbU r) (sourceRealAngularMoment_bound V hbV r)
      (sourceRealAngularMoment_nonneg V r) (by positivity)
  have he : sourceAngularH a v Ψ U V = ENNReal.ofReal ((2:ℝ)^(2*(v-a)) *
      ∫ r, sourceRealAngularMoment U r * sourceRealAngularMoment V r ∂sourceAngularShellMeasure v Ψ) := by
    simp only [sourceAngularH,sourceAngularMoment_eq_ofReal U hU hC hbU,sourceAngularMoment_eq_ofReal V hV hD hbV,
      ← ENNReal.ofReal_mul (sourceRealAngularMoment_nonneg U _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hp),
      ← ENNReal.ofReal_mul (by positivity)]
  rw [he]
  exact ⟨ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (mul_nonneg (by positivity) (integral_nonneg hp))⟩

theorem sourceAngularH_complex_integral (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hbU : ∀ p, ‖U p‖ ≤ C) (hbV : ∀ p, ‖V p‖ ≤ D) :
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) = ((2:ℝ)^(2*(v-a))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
        ((U (r,u)*conj (U (r,u))) * (V (r,w)*conj (V (r,w)))) ∂sourceArcLength ∂sourceArcLength) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  obtain ⟨hfin,he⟩ := sourceAngularH_finite_integral a v Ψ U V hU hV hC hD hbU hbV
  refine ⟨hfin,?_⟩
  rw [he,Complex.ofReal_mul,← integral_complex_ofReal]
  rw [sourceAngularShellMeasure_integral v hΨ hpos (fun t ht => by
    by_contra hn
    have := (hs t hn).1
    linarith)]
  change ((2:ℝ)^(2*(v-a))) • (_ : ℂ) = _
  congr 2
  apply integral_congr_ae
  filter_upwards with r
  simp only [integral_smul,integral_const_mul,integral_mul_const,Complex.mul_conj,
    Complex.normSq_eq_norm_sq,integral_complex_ofReal,sourceRealAngularMoment,Complex.ofReal_mul]

theorem sourceAngularH_original_four_transform (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (X Y : Set Plane)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) :
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform ρ X M₁ b₁ z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform ν Y M₂ b₂ z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) = ((2:ℝ)^(2*(v-a))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
        sourceGraphFourTransform ![ρ,ρ,ν,ν] ![X,X,Y,Y] ![M₁,M₁,M₂,M₂] ![b₁,b₁,b₂,b₂]
          (fun _ => 1) r u w ∂sourceArcLength ∂sourceArcLength) := by
  have he := sourceAngularH_complex_integral a v hΨ hpos hs hW hw
    (fun z => sourceAngularTransform ρ X M₁ b₁ z.1 z.2)
    (fun z => sourceAngularTransform ν Y M₂ b₂ z.1 z.2)
    (measurable_sourceAngularTransform ρ X M₁ b₁ h₁) (measurable_sourceAngularTransform ν Y M₂ b₂ h₂)
    (C := B₁*(ρ X).toReal/M₁) (D := B₂*(ν Y).toReal/M₂) (by positivity) (by positivity)
    (fun z => sourceAngularTransform_norm_le ρ X M₁ hM₁ b₁ B₁ (fun x _ => hb₁ x) z.1 z.2)
    (fun z => sourceAngularTransform_norm_le ν Y M₂ hM₂ b₂ B₂ (fun y _ => hb₂ y) z.1 z.2)
  simpa only [sourceGraphFourTransform,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,one_mul] using he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductGraphIndices
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceProductGraphIndex_injective (A B : CellPath) :
    Function.Injective (sourceProductGraphIndex A B) := by
  rintro ⟨⟨⟨P,P'⟩,⟨Q,Q'⟩⟩,s⟩ ⟨⟨⟨V,V'⟩,⟨W,W'⟩⟩,t⟩ he
  simpa only [sourceProductGraphIndex,Prod.mk.injEq,List.append_cancel_left_eq] using he

theorem sourceProductGraphIndices_subset {X Y : DyadicSquare} {ρ ν : Measure Plane}
    {a n m : ℕ} {A B : CellPath} (hA : A.length = a) (hB : B.length = a) :
    sourceProductGraphIndices X Y ρ ν n m A B ⊆ graphNonedgeIndices (a+n) m := by
  classical
  intro e he
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  simp only [sourceProductRelativeIndices,Finset.mem_product,Finset.mem_range,Finset.mem_univ,and_true] at hq
  have h0 := (Finset.mem_filter.mp hq.1.1.1).1
  have h1 := (Finset.mem_filter.mp hq.1.1.2).1
  have h2 := (Finset.mem_filter.mp hq.1.2.1).1
  have h3 := (Finset.mem_filter.mp hq.1.2.2).1
  simp only [mem_dyadicPaths] at h0 h1 h2 h3
  simp [graphNonedgeIndices,graphCellQuadIndices,sourceProductGraphIndex,mem_dyadicPaths,
    List.length_append,hA,hB,h0,h1,h2,h3,hq.2.1,hq.2.2]

theorem sourceProductGraphIndex_cells (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (e : GraphNonedgeIndex) (l : Fin 4) :
    graphQuadCells ![Q₁,Q₁,Q₂,Q₂] (sourceProductGraphIndex A B e).1 l =
      graphQuadCells ![Q₁.descendant A,Q₁.descendant A,Q₂.descendant B,Q₂.descendant B] e.1 l := by
  fin_cases l <;> simp [graphQuadCells,graphQuadPath,sourceProductGraphIndex,DyadicSquare.descendant_append]

theorem sourceProductGraphIndices_parent (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (A B : CellPath)
    (ρ ν : Measure Plane) (n m : ℕ) {e : GraphNonedgeIndex}
    (he : e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
    (l : Fin 4) :
    (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier ⊆
      (graphSlotParent false (Q₁.descendant A) (Q₂.descendant B) l).carrier := by
  classical
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp he
  rw [sourceProductGraphIndex_cells]
  fin_cases l <;> simp only [graphSlotParent,Bool.false_eq_true,↓reduceIte,graphQuadCells,graphQuadPath] <;>
    apply DyadicSquare.descendant_subset <;>
    first | exact Q₁.descendant_side_pos hQ₁ A | exact Q₂.descendant_side_pos hQ₂ B

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductTransformPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphProductWeight_total {m : ℕ} (hm : 0 < m) (p : UnitCircle × UnitCircle) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ∑ s : Bool, graphProductWeight s m j k p) = 1 := by
  simp only [Fintype.sum_bool,graphProductWeight_partition]
  simp only [graphBinWeight,← Complex.ofReal_sum,← Finset.mul_sum,
    circleAngularBin_partition hm,mul_one,Complex.ofReal_one]

theorem sourceGraphFourTransform_measurable
    (ρ : Fin 4 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ l, Measurable (fun p : Plane × UnitCircle => b l p.1 p.2)) (hW : Measurable W) :
    Measurable (fun p : ℝ × (UnitCircle × UnitCircle) => sourceGraphFourTransform ρ X M b W p.1 p.2.1 p.2.2) := by
  have hm := graphFourKernel_measurable b W hb hW
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi (fun l => (ρ l).restrict (X l)))
  simp_rw [sourceGraphFourTransform_endpoint_integral]
  exact (measurable_const (a := ((M 0*M 1)*(M 2*M 3))⁻¹)).smul hi.measurable

theorem sourceGraphFourTransform_bound
    (ρ : Fin 4 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ) (hM : ∀ l, 0 < M l)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (B : Fin 4 → ℝ) (hB : ∀ l, 0 ≤ B l) (hb : ∀ l x dir, ‖b l x dir‖ ≤ B l)
    (hW : ∀ p, ‖W p‖ ≤ 1) (r : ℝ) (u w : UnitCircle) :
    ‖sourceGraphFourTransform ρ X M b W r u w‖ ≤
      ((B 0*(ρ 0 (X 0)).toReal/M 0)*(B 1*(ρ 1 (X 1)).toReal/M 1))*
      ((B 2*(ρ 2 (X 2)).toReal/M 2)*(B 3*(ρ 3 (X 3)).toReal/M 3)) := by
  have ht := fun l dir => sourceAngularTransform_norm_le (ρ l) (X l) (M l) (hM l) (b l)
    (B l) (fun x _ => hb l x) r dir
  have hp (l : Fin 4) : 0 ≤ B l*(ρ l (X l)).toReal/M l :=
    div_nonneg (mul_nonneg (hB l) ENNReal.toReal_nonneg) (hM l).le
  simp only [sourceGraphFourTransform,norm_mul,Complex.norm_conj]
  calc
    _ ≤ 1*((B 0*(ρ 0 (X 0)).toReal/M 0)*(B 1*(ρ 1 (X 1)).toReal/M 1))*
        ((B 2*(ρ 2 (X 2)).toReal/M 2)*(B 3*(ρ 3 (X 3)).toReal/M 3)) := by
      exact mul_le_mul
        (mul_le_mul (hW (u,w)) (mul_le_mul (ht 0 u) (ht 1 u) (norm_nonneg _) (hp 0))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one)
        (mul_le_mul (ht 2 w) (ht 3 w) (norm_nonneg _) (hp 2))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg zero_le_one (mul_nonneg (hp 0) (hp 1)))
    _ = _ := by ring

theorem sourceGraphFourTransform_product_partition
    (X Y : DyadicSquare) (hX : 0 < X.side) (hY : 0 < Y.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n m : ℕ) (hm : 0 < m)
    (M₁ M₂ : ℝ) (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hb₁ : Measurable (fun p : Plane × UnitCircle => b₁ p.1 p.2))
    (hb₂ : Measurable (fun p : Plane × UnitCircle => b₂ p.1 p.2))
    (C₁ C₂ : ℝ) (hC₁ : ∀ x dir, ‖b₁ x dir‖ ≤ C₁) (hC₂ : ∀ x dir, ‖b₂ x dir‖ ≤ C₂)
    (r : ℝ) (u w : UnitCircle) :
    sourceGraphFourTransform ![ρ,ρ,ν,ν] ![X.carrier,X.carrier,Y.carrier,Y.carrier]
      ![M₁,M₁,M₂,M₂] ![b₁,b₁,b₂,b₂] (fun _ => 1) r u w =
    ∑ e ∈ sourceProductRelativeIndices X Y ρ ν n m,
      sourceGraphFourTransform ![ρ,ρ,ν,ν]
        (fun l => (graphQuadCells ![X,X,Y,Y] e.1 l).carrier)
        ![M₁,M₁,M₂,M₂] ![b₁,b₁,b₂,b₂] (graphProductWeight e.2.2 m e.2.1.1 e.2.1.2) r u w := by
  classical
  simp only [sourceProductRelativeIndices,Finset.sum_product]
  simp only [sourceGraphFourTransform,graphQuadCells,graphQuadPath,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,one_mul]
  simp only [← Finset.sum_mul,graphProductWeight_total hm,one_mul]
  rw [sourceAngularTransform_split X hX ρ n M₁ M₁ hM₁ b₁ hb₁ C₁ hC₁,
    sourceAngularTransform_split Y hY ν n M₂ M₂ hM₂ b₂ hb₂ C₂ hC₂]
  simp only [div_self hM₁,div_self hM₂,one_smul]
  simp only [← Finset.mul_sum,← Finset.sum_mul,← map_sum]

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
-- module Solutions.OAIQ038_FA.Falconer_Measures_FiniteProductIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem bounded_circle_pair_integral_measurable
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) (hF : Measurable F) :
    Measurable (fun r => ∫ u, ∫ w, F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength) := by
  have h : Measurable (fun p : (ℝ × UnitCircle) × UnitCircle => F (p.1.1,(p.1.2,p.2))) :=
    hF.comp (by fun_prop)
  exact h.stronglyMeasurable.integral_prod_right'.measurable.stronglyMeasurable.integral_prod_right'.measurable

theorem bounded_circle_pair_integral_norm
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) {C : ℝ}
    (hb : ∀ p, ‖F p‖ ≤ C) (r : ℝ) :
    ‖∫ u, ∫ w, F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength‖ ≤
      (C*sourceArcLength.real univ)*sourceArcLength.real univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards with u
  exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (fun w => hb (r,(u,w))))

theorem bounded_original_integral_sum {ι : Type*} (S : Finset ι)
    (F : ι → ℝ × (UnitCircle × UnitCircle) → ℂ)
    (hF : ∀ i ∈ S, Measurable (F i)) (C : ι → ℝ)
    (hC : ∀ i ∈ S, 0 ≤ C i) (hb : ∀ i ∈ S, ∀ p, ‖F i p‖ ≤ C i)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W) {R : ℝ} (hR : 0 < R) :
    (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/R) • (∑ i ∈ S, F i (r,(u,w)))
      ∂sourceArcLength ∂sourceArcLength) =
    ∑ i ∈ S, ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/R) • F i (r,(u,w))
      ∂sourceArcLength ∂sourceArcLength := by
  have hi (i : ι) (hi : i ∈ S) (r : ℝ) (u : UnitCircle) :
      Integrable (fun w => F i (r,(u,w))) sourceArcLength :=
    Integrable.of_bound ((hF i hi).comp (by fun_prop)).aestronglyMeasurable (C i)
      (Filter.Eventually.of_forall (fun w => hb i hi (r,(u,w))))
  have hj (i : ι) (hi : i ∈ S) (r : ℝ) :
      Integrable (fun u => ∫ w, F i (r,(u,w)) ∂sourceArcLength) sourceArcLength := by
    have hm : Measurable (fun p : UnitCircle × UnitCircle => F i (r,p)) :=
      (hF i hi).comp (by fun_prop)
    apply Integrable.of_bound hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (C i*sourceArcLength.real univ)
    filter_upwards with u
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (fun w => hb i hi (r,(u,w))))
  have hk (i : ι) (hi : i ∈ S) :
      Integrable (fun r => Ψ (r/R) • (∫ u, ∫ w, F i (r,(u,w)) ∂sourceArcLength ∂sourceArcLength)) :=
    bounded_shell_integrable hΨ hs hW hw hR _
      (bounded_circle_pair_integral_measurable (F i) (hF i hi)).aestronglyMeasurable
      (mul_nonneg (mul_nonneg (hC i hi) measureReal_nonneg) measureReal_nonneg)
      (bounded_circle_pair_integral_norm (F i) (hb i hi))
  simp_rw [integral_smul]
  have he (r : ℝ) :
      (∫ u, ∫ w, ∑ i ∈ S, F i (r,(u,w)) ∂sourceArcLength ∂sourceArcLength) =
      ∑ i ∈ S, ∫ u, ∫ w, F i (r,(u,w)) ∂sourceArcLength ∂sourceArcLength := by
    simp_rw [integral_finsetSum S (fun i hi' => hi i hi' r _)]
    exact integral_finsetSum S (fun i hi' => hj i hi' r)
  simp_rw [he,Finset.smul_sum]
  exact integral_finsetSum S hk

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductGraphEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceGraphFourTransform_original_sum {ι : Type*} (S : Finset ι)
    (ρ : Fin 4 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (X : ι → Fin 4 → Set Plane) (M : Fin 4 → ℝ) (hM : ∀ l, 0 < M l)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : ι → UnitCircle × UnitCircle → ℂ)
    (hb : ∀ l, Measurable (fun p : Plane × UnitCircle => b l p.1 p.2))
    (hW : ∀ i, Measurable (W i)) (hw : ∀ i p, ‖W i p‖ ≤ 1)
    (B : Fin 4 → ℝ) (hB : ∀ l, 0 ≤ B l) (hbound : ∀ l x dir, ‖b l x dir‖ ≤ B l)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) (v : ℝ) :
    (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
      (∑ i ∈ S, sourceGraphFourTransform ρ (X i) M b (W i) r u w)
      ∂sourceArcLength ∂sourceArcLength) =
    ∑ i ∈ S, ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
      sourceGraphFourTransform ρ (X i) M b (W i) r u w ∂sourceArcLength ∂sourceArcLength := by
  apply bounded_original_integral_sum S _
    (fun i _ => sourceGraphFourTransform_measurable ρ (X i) M b (W i) hb (hW i))
    (fun i => ((B 0*(ρ 0 (X i 0)).toReal/M 0)*(B 1*(ρ 1 (X i 1)).toReal/M 1))*
      ((B 2*(ρ 2 (X i 2)).toReal/M 2)*(B 3*(ρ 3 (X i 3)).toReal/M 3)))
    (fun i _ => by
      have h0 := hB 0; have h1 := hB 1; have h2 := hB 2; have h3 := hB 3
      have hm0 := hM 0; have hm1 := hM 1; have hm2 := hM 2; have hm3 := hM 3
      positivity)
    (fun i _ p => sourceGraphFourTransform_bound ρ (X i) M hM b (W i) B hB hbound (hw i) p.1 p.2.1 p.2.2)
    hΨ hs hC hc (by positivity)

theorem sourceAngularH_relative_graph_sum (a v : ℝ)
    (X Y : DyadicSquare) (hX : 0 < X.side) (hY : 0 < Y.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ) {θ : ℝ} (hθ : 0 < θ)
    {Ma₁ Ma₂ Mp₁ Mp₂ : ℝ} (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hb₁ : Measurable (fun p : Plane × UnitCircle => b₁ p.1 p.2))
    (hb₂ : Measurable (fun p : Plane × UnitCircle => b₂ p.1 p.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hbound₂ : ∀ x dir, ‖b₂ x dir‖ ≤ B₂)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) :
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform ρ X.carrier Ma₁ b₁ z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform ν Y.carrier Ma₂ b₂ z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) =
      ((2:ℝ)^(2*(v-a))) • (((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) •
        ∑ e ∈ sourceProductRelativeIndices X Y ρ ν n (angularBinCount θ),
          graphOriginalTerm ![ρ,ρ,ν,ν] (fun l => (graphQuadCells ![X,X,Y,Y] e.1 l).carrier)
            ![Mp₁,Mp₁,Mp₂,Mp₂] ![b₁,b₁,b₂,b₂] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ) := by
  classical
  let : ∀ l : Fin 4, IsFiniteMeasure (![ρ,ρ,ν,ν] l) := by
    intro l; fin_cases l <;> dsimp <;> infer_instance
  have hM : ∀ l : Fin 4, 0 < (![Mp₁,Mp₁,Mp₂,Mp₂] l) := by
    intro l; fin_cases l <;> first | exact hMp₁ | exact hMp₂
  have hb : ∀ l : Fin 4, Measurable (fun p : Plane × UnitCircle => (![b₁,b₁,b₂,b₂] l) p.1 p.2) := by
    intro l; fin_cases l <;> first | exact hb₁ | exact hb₂
  have hB : ∀ l : Fin 4, 0 ≤ (![B₁,B₁,B₂,B₂] l) := by
    intro l; fin_cases l <;> first | exact hB₁ | exact hB₂
  have hbound : ∀ (l : Fin 4) x dir, ‖(![b₁,b₁,b₂,b₂] l) x dir‖ ≤ (![B₁,B₁,B₂,B₂] l) := by
    intro l; fin_cases l <;> first | exact hbound₁ | exact hbound₂
  obtain ⟨hfin,he⟩ := sourceAngularH_original_four_transform a v hΨ hpos hs hC
    (fun t => (le_abs_self _).trans (hc t)) ρ ν X.carrier Y.carrier hMa₁ hMa₂ b₁ b₂ hb₁ hb₂
    hB₁ hB₂ hbound₁ hbound₂
  refine ⟨hfin,?_⟩
  rw [he]
  have hp (r : ℝ) (u w : UnitCircle) :
      sourceGraphFourTransform ![ρ,ρ,ν,ν] ![X.carrier,X.carrier,Y.carrier,Y.carrier]
        ![Ma₁,Ma₁,Ma₂,Ma₂] ![b₁,b₁,b₂,b₂] (fun _ => 1) r u w =
      ((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) •
        ∑ e ∈ sourceProductRelativeIndices X Y ρ ν n (angularBinCount θ),
          sourceGraphFourTransform ![ρ,ρ,ν,ν] (fun l => (graphQuadCells ![X,X,Y,Y] e.1 l).carrier)
            ![Mp₁,Mp₁,Mp₂,Mp₂] ![b₁,b₁,b₂,b₂]
            (graphProductWeight e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2) r u w := by
    rw [sourceGraphFourTransform_profile_normalization _ _ ![Mp₁,Mp₁,Mp₂,Mp₂] _ (fun l => ne_of_gt (hM l))]
    rw [sourceGraphFourTransform_product_partition X Y hX hY ρ ν n (angularBinCount θ)
      (angularBinCount_pos hθ) Mp₁ Mp₂ hMp₁.ne' hMp₂.ne' b₁ b₂ hb₁ hb₂ B₁ B₂ hbound₁ hbound₂]
    congr 1
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons]
    ring
  simp_rw [hp,smul_comm (Ψ _) ((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2),integral_smul]
  have hsum := sourceGraphFourTransform_original_sum
    (sourceProductRelativeIndices X Y ρ ν n (angularBinCount θ)) ![ρ,ρ,ν,ν]
    (fun e l => (graphQuadCells ![X,X,Y,Y] e.1 l).carrier) ![Mp₁,Mp₁,Mp₂,Mp₂] hM
    ![b₁,b₁,b₂,b₂]
    (fun e => graphProductWeight e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2) hb
    (fun e => (graphProductWeight_continuous e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2).measurable)
    (fun e => graphProductWeight_norm_le e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2)
    ![B₁,B₁,B₂,B₂] hB hbound hΨ hs hC hc v
  simp only [integral_smul] at hsum
  rw [hsum]
  simp only [graphOriginalTerm,graphSourceWeight,Bool.false_eq_true,↓reduceIte,integral_smul,← Finset.smul_sum]
  rw [smul_comm (((2:ℝ)^v)⁻¹)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_EligibleProductGraphSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem angular_label_eligible_of_transform_ne_zero {ρ : Measure Plane} {X : Set Plane}
    {b : Plane → UnitCircle → ℂ} {m j : ℕ} {u : UnitCircle} {M r : ℝ}
    (hu : circleAngularBin m j u ≠ 0) (ht : sourceAngularTransform ρ X M b r u ≠ 0) :
    AngularLabelEligible ρ X b m j := by
  by_contra h
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) ht (ineligible_transform_zero h M r u)

theorem sourceGraphFourTransform_product_eligible_of_ne_zero
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (plus : Bool) (m j k : ℕ) (r : ℝ) (u w : UnitCircle)
    (hn : sourceGraphFourTransform ρ X M b (graphProductWeight plus m j k) r u w ≠ 0) :
    GraphProductEligible ρ X b m j k := by
  have h := hn
  simp only [sourceGraphFourTransform,mul_ne_zero_iff,map_ne_zero] at h
  obtain ⟨⟨hW,h0,h1⟩,h2,h3⟩ := h
  have hu : circleAngularBin m j u ≠ 0 := by
    intro hz
    exact hW (by simp [graphProductWeight,graphBinWeight,hz])
  have hw : circleAngularBin m k w ≠ 0 := by
    intro hz
    exact hW (by simp [graphProductWeight,graphBinWeight,hz])
  intro l
  fin_cases l
  · exact angular_label_eligible_of_transform_ne_zero hu h0
  · exact angular_label_eligible_of_transform_ne_zero hu h1
  · exact angular_label_eligible_of_transform_ne_zero hw h2
  · exact angular_label_eligible_of_transform_ne_zero hw h3

theorem graphOriginalProductTerm_zero_of_ineligible
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (plus : Bool) (axis θ v : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ)
    (hn : ¬GraphProductEligible ρ X b (angularBinCount θ) j k) :
    graphOriginalTerm ρ X M b false plus axis θ v j k Ψ = 0 := by
  have hz (r : ℝ) (u w : UnitCircle) :
      sourceGraphFourTransform ρ X M b (graphProductWeight plus (angularBinCount θ) j k) r u w = 0 := by
    by_contra h
    exact hn (sourceGraphFourTransform_product_eligible_of_ne_zero ρ X M b plus _ j k r u w h)
  simp only [graphOriginalTerm,graphSourceWeight,Bool.false_eq_true,↓reduceIte,hz,smul_zero,integral_zero]

theorem graphOriginalProductSum_eligible (I : Finset GraphNonedgeIndex)
    (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (axis θ v : ℝ) (Ψ : ℝ → ℝ) :
    (∑ e ∈ I, graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M b
      false e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ) =
    ∑ e ∈ graphProductEligibleIndices I ρ Q b (angularBinCount θ),
      graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M b
        false e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ := by
  classical
  unfold graphProductEligibleIndices
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hnot
  apply graphOriginalProductTerm_zero_of_ineligible
  intro h
  exact hnot (Finset.mem_filter.mpr ⟨he,h⟩)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductAbsoluteGraphAssembly
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceProductGraphSum_absolute (v θ : ℝ) (Q₁ Q₂ : DyadicSquare)
    (A B : CellPath) (ρ ν : Measure Plane) (n : ℕ) (M₁ M₂ : ℝ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (Ψ : ℝ → ℝ) :
    (∑ e ∈ sourceProductRelativeIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n (angularBinCount θ),
      graphOriginalTerm ![ρ,ρ,ν,ν]
        (fun l => (graphQuadCells ![Q₁.descendant A,Q₁.descendant A,Q₂.descendant B,Q₂.descendant B] e.1 l).carrier)
        ![M₁,M₁,M₂,M₂] ![b₁,b₁,b₂,b₂] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ) =
    ∑ e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n (angularBinCount θ) A B,
      graphOriginalTerm ![ρ,ρ,ν,ν] (fun l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
        ![M₁,M₁,M₂,M₂] ![b₁,b₁,b₂,b₂] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ := by
  classical
  rw [sourceProductGraphIndices,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e _
    simp only [sourceProductGraphIndex_cells]
    rfl
  · exact fun x _ y _ h => sourceProductGraphIndex_injective A B h

theorem sourceAngularH_absolute_graph_sum (a v : ℝ)
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (A B : CellPath)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n : ℕ) {θ : ℝ} (hθ : 0 < θ)
    {Ma₁ Ma₂ Mp₁ Mp₂ : ℝ} (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hb₁ : Measurable (fun p : Plane × UnitCircle => b₁ p.1 p.2))
    (hb₂ : Measurable (fun p : Plane × UnitCircle => b₂ p.1 p.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hbound₂ : ∀ x dir, ‖b₂ x dir‖ ≤ B₂)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) :
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform ρ (Q₁.descendant A).carrier Ma₁ b₁ z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform ν (Q₂.descendant B).carrier Ma₂ b₂ z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) =
      ((2:ℝ)^(2*(v-a))) • (((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) •
        ∑ e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n (angularBinCount θ) A B,
          graphOriginalTerm ![ρ,ρ,ν,ν] (fun l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
            ![Mp₁,Mp₁,Mp₂,Mp₂] ![b₁,b₁,b₂,b₂] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ) := by
  have he := sourceAngularH_relative_graph_sum a v (Q₁.descendant A) (Q₂.descendant B)
    (Q₁.descendant_side_pos hQ₁ A) (Q₂.descendant_side_pos hQ₂ B) ρ ν n hθ
    hMa₁ hMa₂ hMp₁ hMp₂ b₁ b₂ hb₁ hb₂ hB₁ hB₂ hbound₁ hbound₂ hΨ hpos hs hC hc
  dsimp only at he ⊢
  rw [sourceProductGraphSum_absolute] at he
  exact he

theorem graphProfileCoefficient_product (N : ℕ) (m₁ m₂ : ℝ → ℝ) (a p : ℝ) :
    graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p =
      ((((2:ℝ)^N)^(-m₁ p)/((2:ℝ)^N)^(-m₁ a))^2)*
      ((((2:ℝ)^N)^(-m₂ p)/((2:ℝ)^N)^(-m₂ a))^2) := by
  simp only [graphProfileCoefficient,Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualProductGraphAssembly
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem sourceProductSlot_comp {α : Type*} (f : Fin 2 → α) :
    (fun l => f (sourceProductSlot l)) = ![f 0,f 0,f 1,f 1] := by
  funext l
  fin_cases l <;> rfl

theorem uniform_actual_product_H_graph_oai
    {sig c₀ : ℝ} (hsig : 0 < sig) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi)
    (K : ℕ) (lam T : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (J i : ℕ) (h : Fin 2 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N →
    0 ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let t : ℝ := (a+n:ℕ)-a
    let θ := graphAngularScale N sig t c₀
    let I := sourceProductGraphIndices X Y (ρ 0) (ρ 1) n (angularBinCount θ) A B
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) false e.2 0 e.1.1 e.1.2
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 0) X.carrier
      (((2:ℝ)^N)^(-mass 0 a)) (β 0) z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 1) Y.carrier
      (((2:ℝ)^N)^(-mass 1 a)) (β 1) z.1 z.2
    let F := fun e : GraphNonedgeIndex => graphOriginalTerm ![ρ 0,ρ 0,ρ 1,ρ 1]
      (fun l => (graphQuadCells ![Q 0,Q 0,Q 1,Q 1] e.1 l).carrier)
      ![M 0,M 0,M 1,M 1] ![β 0,β 0,β 1,β 1] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ‖((sourceAngularH a v Ψ U V).toReal : ℂ) -
      ((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N ![mass 0,mass 0,mass 1,mass 1] a (a+n) •
        (∑ e ∈ graphProductEligibleIndices
          (graphRetainedIndices I N sig (a+n) false ![Q 0,Q 0,Q 1,Q 1] rep)
          ![ρ 0,ρ 0,ρ 1,ρ 1] ![Q 0,Q 0,Q 1,Q 1] ![β 0,β 0,β 1,β 1] (angularBinCount θ), F e))‖ ≤ ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₀,hrem⟩ := uniform_regularized_original_graph_removal hsig K lam T hΨ hs hc hcap
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ hQs ρ mass B δ hd J i h hh hhb a n v
    hp hu ht hLu hv A B' hA hB
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let X := (Q 0).descendant A
  let Y := (Q 1).descendant B'
  let t : ℝ := (a+n:ℕ)-a
  let θ := graphAngularScale N sig t c₀
  have hX : 0 < X.side := (Q 0).descendant_side_pos (hQ 0) A
  have hY : 0 < Y.side := (Q 1).descendant_side_pos (hQ 1) B'
  have hXs : X.side ≤ (2:ℝ)^(-(a:ℝ)) := by
    dsimp [X]; rw [DyadicSquare.descendant_side,hA,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simpa only [one_div] using div_le_div_of_nonneg_right (hQs 0) (by positivity : (0:ℝ) ≤ 2^a)
  have hYs : Y.side ≤ (2:ℝ)^(-(a:ℝ)) := by
    dsimp [Y]; rw [DyadicSquare.descendant_side,hB,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simpa only [one_div] using div_le_div_of_nonneg_right (hQs 1) (by positivity : (0:ℝ) ≤ 2^a)
  let I := sourceProductGraphIndices X Y (ρ 0) (ρ 1) n (angularBinCount θ) A B'
  have hI : I ⊆ graphNonedgeIndices (a+n) (angularBinCount θ) := sourceProductGraphIndices_subset hA hB
  have hr := hrem N hN
    (fun l => S (sourceProductSlot l)) (fun l => d (sourceProductSlot l)) (fun l => k (sourceProductSlot l))
    (fun l => hcard _) (fun l => hK _) L (fun l => hL _)
    (fun l => Q (sourceProductSlot l)) (fun l => hQ _) (fun l => hQs _)
    (fun l => ρ (sourceProductSlot l)) (fun l => mass (sourceProductSlot l)) B δ (fun l => hd _)
    J i (fun l => h (sourceProductSlot l)) (fun l => hh _) (fun l => hhb _)
    a (a+n) v (Nat.cast_nonneg a) (by exact_mod_cast Nat.le_add_right a n) hp
    (by simpa only [Nat.cast_add] using hu) (by simpa only [Nat.cast_add,add_sub_cancel_left] using ht)
    (by simpa only [Nat.cast_add] using hLu) hv false X Y hX hY hXs hYs (by simp) 0 I hI (by
      intro e he l
      rw [sourceProductSlot_comp]
      exact sourceProductGraphIndices_parent (Q 0) (Q 1) (hQ 0) (hQ 1) A B' (ρ 0) (ρ 1) n (angularBinCount θ) he l)
  dsimp only at hr ⊢
  simp only [sourceProductSlot_comp] at hr
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  have hb : ∀ (l : Fin 2) (x : Plane) (dir : UnitCircle), ‖β l x dir‖ ≤ symbolDerivativeConstant K^K := by
    intro l x dir
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) dir
  obtain ⟨hfin,he⟩ := sourceAngularH_absolute_graph_sum a v (Q 0) (Q 1) (hQ 0) (hQ 1) A B' (ρ 0) (ρ 1) n
    (graphAngularScale_pos N sig t hc)
    (Ma₁ := ((2:ℝ)^N)^(-mass 0 a)) (Ma₂ := ((2:ℝ)^N)^(-mass 1 a))
    (Mp₁ := ((2:ℝ)^N)^(-mass 0 (a+n))) (Mp₂ := ((2:ℝ)^N)^(-mass 1 (a+n)))
    (by positivity) (by positivity) (by positivity) (by positivity) (β 0) (β 1) (hm 0) (hm 1)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K) (hb 0) (hb 1)
    hΨ.continuous.measurable hpos hs hW hw
  refine ⟨hfin,?_⟩
  rw [← graphProfileCoefficient_product] at he
  rw [he]
  have hM4 := sourceProductSlot_comp (fun l => ((2:ℝ)^N)^(-mass l (a+n:ℕ)))
  have hβ4 := sourceProductSlot_comp β
  rw [hM4,hβ4] at hr
  rw [← graphOriginalProductSum_eligible]
  simpa only [Nat.cast_add,X,Y,I,t,θ,β] using hr

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_product_H_graph_oai := @OAI.PlanarFalconer.uniform_actual_product_H_graph_oai
