-- Prove2me | solution 1 for OAI.PlanarFalconer.source_angular_direct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:10:09.634258+00:00
-- url     : https://prove2.me/submissions/75e8f6af-a488-43a9-a0c6-58f7d76f4568

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_product_estimate

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

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
-- module Solutions.OAIQ038_FA.Falconer_Geometry_ScaledDyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem DyadicSquare.center_mem (Q : DyadicSquare) (hQ : 0 < Q.side) : Q.center ∈ Q.carrier := by
  simp only [center,carrier,mem_ofPred_eq,Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor
  · linarith
  · exact ⟨by linarith,by linarith,by linarith⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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

theorem DyadicSquare.descendant_subset_take (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : CellPath) (a : ℕ) : (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  have he := Q.descendant_append (p.take a) (p.drop a)
  rw [List.take_append_drop] at he
  rw [he]
  exact (Q.descendant (p.take a)).descendant_subset (Q.descendant_side_pos hQ _) _

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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem finiteMin_le {ι : Type*} {s : Finset ι} (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) : finiteMin s f ≤ f i := by
  rw [finiteMin, dite_eq_left ⟨i, hi⟩]
  exact Finset.inf'_le f hi

theorem le_finiteMin {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ) {c : ℝ} (h : ∀ i ∈ s, c ≤ f i) : c ≤ finiteMin s f := by
  rw [finiteMin, dite_eq_left hs]
  exact Finset.le_inf' hs f h

theorem depthPairs_nonempty {a t Q : ℕ} (hQ : 0 < Q) (hw : a + Q ≤ t) :
    (depthPairs a t Q).Nonempty := by
  refine ⟨(a,a+Q), mem_depthPairs.mpr ?_⟩
  omega

theorem potential_le (A : ℕ → ℝ) {a t Q i j : ℕ}
    (hi : a ≤ i) (hij : i < j) (hjt : j ≤ t) (hgap : i + Q ≤ j) :
    potential A a t Q ≤ A i + A j :=
  finiteMin_le _ (mem_depthPairs.mpr ⟨hi,hij,hjt,hgap⟩)

theorem le_potential (A : ℕ → ℝ) {a t Q : ℕ} (hQ : 0 < Q)
    (hw : a+Q ≤ t) {c : ℝ}
    (h : ∀ i j, a ≤ i → i < j → j ≤ t → i+Q ≤ j → c ≤ A i + A j) :
    c ≤ potential A a t Q := by
  apply le_finiteMin (depthPairs_nonempty hQ hw)
  rintro ⟨i,j⟩ hij
  obtain ⟨hi, hij, hjt, hgap⟩ := mem_depthPairs.mp hij
  exact h i j hi hij hjt hgap

theorem potential_mono (A : ℕ → ℝ) {a b u t Q : ℕ}
    (hQ : 0 < Q) (hw : b+Q ≤ u) (hab : a ≤ b) (hut : u ≤ t) :
    potential A a t Q ≤ potential A b u Q := by
  apply le_potential A hQ hw
  intro i j hbi hij hju hgap
  exact potential_le A (hab.trans hbi) hij (hju.trans hut) hgap

theorem prefix_payment (A : ℕ → ℝ) {a p v t Q i₀ : ℕ}
    (hQ : 0 < Q) (hw : p+Q ≤ v) (hai : a ≤ i₀) (hip : i₀ ≤ p)
    (hvt : v ≤ t) (hcontrolled : ∀ i, p ≤ i → i+Q ≤ v → A p ≤ A i) :
    potential A a t Q + (A p - A i₀) ≤ potential A p v Q := by
  apply le_potential A hQ hw
  intro i j hpi hij hjv hgap
  have hparent := potential_le A hai (by omega : i₀ < j) (by omega : j ≤ t)
    (by omega : i₀+Q ≤ j)
  have hAi := hcontrolled i hpi (by omega)
  linarith

theorem direct_origin_payment (A : ℕ → ℝ) {a p v b u l r L q Q i₀ : ℕ}
    (hq : 0 < q) (hQ : Q = 10*q) (hw : p+Q ≤ v)
    (hai : a ≤ i₀) (hip : i₀ ≤ p) (hlp : l ≤ p) (hpr : p ≤ r)
    (hl : l ≤ b+2*q) (hr : u ≤ r+2*q) (hLu : b+2*L ≤ u)
    (hv : v ≤ a+2*L) (hmin : A i₀ < A p)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a v Q + (A p - A i₀) ≤ potential A p v Q := by
  have hi₀l : i₀ < l := by
    by_contra h
    have := hinner i₀ (by omega) (by omega)
    linarith
  apply prefix_payment A (by omega) hw hai hip (le_refl v)
  intro i hpi hiQ
  apply hinner i (by omega) (by omega)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_Ledger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem intervalMin_attained (A : ℕ → ℝ) {a t : ℕ} (hat : a ≤ t) :
    ∃ i, a ≤ i ∧ i ≤ t ∧ intervalMin A a t = A i := by
  have hn : (Finset.Icc a t).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl,hat⟩⟩
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hn A
  exact ⟨i,(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2,
    by simpa only [intervalMin, finiteMin, dite_eq_left hn] using he⟩

theorem intervalMin_le (A : ℕ → ℝ) {a t i : ℕ} (hai : a ≤ i) (hit : i ≤ t) :
    intervalMin A a t ≤ A i := finiteMin_le A (Finset.mem_Icc.mpr ⟨hai,hit⟩)

theorem height_nonneg (A : ℕ → ℝ) {a p : ℕ} (hap : a ≤ p) :
    0 ≤ height A a p := sub_nonneg.mpr (intervalMin_le A hap le_rfl)

theorem policy_direct_payment (A : ℕ → ℝ) {a p v b u l r L q : ℕ}
    (hq : 0 < q) (hw : p+10*q ≤ v) (hap : a ≤ p)
    (hlp : l ≤ p) (hpr : p ≤ r) (hl : l ≤ b+2*q) (hr : u ≤ r+2*q)
    (hLu : b+2*L ≤ u) (hv : v ≤ a+2*L)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a v (10*q) + height A a p ≤ potential A p v (10*q) := by
  obtain ⟨i,hai,hip,hmin⟩ := intervalMin_attained A hap
  by_cases hcost : 0 < height A a p
  · have hi : A i < A p := by unfold height at hcost; rw [hmin] at hcost; linarith
    simpa only [height, hmin] using
      direct_origin_payment A hq rfl hw hai hip hlp hpr hl hr hLu hv hi hinner
  · have hz : height A a p = 0 := le_antisymm (not_lt.mp hcost) (height_nonneg A hap)
    rw [hz, add_zero]
    exact potential_mono A (by omega) hw hap le_rfl

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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InteriorPolicy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finiteArgmin_spec {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → ℝ) :
    finiteArgmin S f ∈ S ∧ ∀ j ∈ S, f (finiteArgmin S f) ≤ f j := by
  rw [finiteArgmin,dite_eq_left hS]
  have hs := Classical.choose_spec (Finset.exists_mem_eq_inf' hS f)
  refine ⟨hs.1,?_⟩
  intro j hj
  rw [← hs.2]
  exact Finset.inf'_le f hj

theorem policyBlock_nonempty {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    (policyBlock N q k).Nonempty := by
  apply Finset.nonempty_Ico.mpr
  have he : (k+1)*q = k*q+q := by ring
  omega

theorem policyRepresentative_spec (A : ℕ → ℝ) {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    k*q ≤ policyRepresentative A N q k ∧ policyRepresentative A N q k < (k+1)*q ∧
      policyRepresentative A N q k ≤ N ∧
      ∀ n ∈ policyBlock N q k, A (policyRepresentative A N q k) ≤ A n := by
  have hh := finiteArgmin_spec (policyBlock_nonempty hq hk) A
  have hm := Finset.mem_Ico.mp hh.1
  refine ⟨hm.1,lt_of_lt_of_le hm.2 (min_le_left _ _),?_,hh.2⟩
  exact Nat.le_of_lt_succ (lt_of_lt_of_le hm.2 (min_le_right _ _))

theorem policyBlocks_mem {N q a t k : ℕ} (h : k ∈ policyBlocks N q a t) :
    k ≤ N/q ∧ a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1 := by
  obtain ⟨hk,hl,hr⟩ := Finset.mem_filter.mp h
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hk),hl,hr⟩

theorem policy_left_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, k*q ≤ a+2*q := by
  let k := (a+2*q-1)/q
  have hlo := Nat.div_mul_le_self (a+2*q-1) q
  have hhi := Nat.lt_mul_div_succ (a+2*q-1) hq
  have hprod : (k+1)*q = k*q+q := by ring
  change k*q ≤ a+2*q-1 at hlo
  have hceil : a+q ≤ k*q := by
    rw [Nat.mul_comm q] at hhi
    change a+2*q-1 < (k+1)*q at hhi
    omega
  have hend : (k+1)*q ≤ t-q+1 := by omega
  have hkn : k*q ≤ N := by omega
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hceil,hend⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policy_right_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, t-2*q ≤ (k+1)*q-1 := by
  let j := (t-q+1)/q
  have hj : 0 < j := Nat.div_pos (by omega) hq
  have hlo := Nat.div_mul_le_self (t-q+1) q
  have hhi := Nat.lt_mul_div_succ (t-q+1) hq
  change j*q ≤ t-q+1 at hlo
  rw [Nat.mul_comm q] at hhi
  change t-q+1 < (j+1)*q at hhi
  have hmul : (j+1)*q = j*q+q := by ring
  have he : (j-1+1)*q = j*q := by rw [Nat.sub_add_cancel hj]
  have he' : (j-1)*q+q = j*q := by simpa only [Nat.add_mul,one_mul] using he
  have hleft : a+q ≤ (j-1)*q := by omega
  have hkn : (j-1)*q ≤ N := by omega
  refine ⟨j-1,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hleft,by omega⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policyBlocks_nonempty {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    (policyBlocks N q a t).Nonempty := by
  obtain ⟨k,hk,_⟩ := policy_left_block hq ht hwide
  exact ⟨k,hk⟩

theorem policyDepth_minimizes (A : ℕ → ℝ) {N q a t n : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) (hn : n ≤ N)
    (hblock : n/q ∈ policyBlocks N q a t) : A (policyDepth A N q a t) ≤ A n := by
  have hkey := finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))
  have hcell : n ∈ policyBlock N q (n/q) := by
    apply Finset.mem_Ico.mpr
    have hlo := Nat.div_mul_le_self n q
    have hhi := Nat.lt_mul_div_succ n hq
    rw [Nat.mul_comm q] at hhi
    exact ⟨hlo,lt_min hhi (Nat.lt_succ_of_le hn)⟩
  exact (hkey.2 _ hblock).trans
    ((policyRepresentative_spec A hq ((Nat.div_mul_le_self n q).trans hn)).2.2.2 n hcell)

theorem policyDepth_interior (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    a+q ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ t-q := by
  have hkey := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  have hb := policyBlocks_mem hkey
  have hrep := policyRepresentative_spec A hq ((Nat.le_div_iff_mul_le hq).mp hb.1)
  exact ⟨hb.2.1.trans hrep.1,Nat.le_of_lt_succ (hrep.2.1.trans_le hb.2.2)⟩

theorem policy_move_length (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    let p := policyDepth A N q a t
    let l := min (p-a) (t-p)
    q ≤ l ∧ a ≤ p-l ∧ p+l ≤ t := by
  have hh := policyDepth_interior A hq hne
  dsimp only
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PolicyInteriorInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem policy_blocks_order_convex {N q a t j k l : ℕ}
    (hj : j ∈ policyBlocks N q a t) (hl : l ∈ policyBlocks N q a t)
    (hjk : j ≤ k) (hkl : k ≤ l) : k ∈ policyBlocks N q a t := by
  have hj' := policyBlocks_mem hj
  have hl' := policyBlocks_mem hl
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_,?_⟩
  · exact hj'.2.1.trans (Nat.mul_le_mul_right q hjk)
  · exact (Nat.mul_le_mul_right q (Nat.add_le_add_right hkl 1)).trans hl'.2.2

theorem policy_interior_interval (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ l u : ℕ, l ≤ a+2*q ∧ t ≤ u+2*q ∧
      l ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ u ∧
      ∀ n, l ≤ n → n ≤ u → A (policyDepth A N q a t) ≤ A n := by
  let S := policyBlocks N q a t
  have hS : S.Nonempty := policyBlocks_nonempty hq ht hwide
  let j := S.min' hS
  let k := S.max' hS
  have hj : j ∈ S := S.min'_mem hS
  have hk : k ∈ S := S.max'_mem hS
  have hj' := policyBlocks_mem hj
  have hk' := policyBlocks_mem hk
  have hkpos : 0 < (k+1)*q := Nat.mul_pos (by omega) hq
  have huN : (k+1)*q-1 ≤ N := by omega
  obtain ⟨j₀,hj₀,hleft⟩ := policy_left_block hq ht hwide
  obtain ⟨k₀,hk₀,hright⟩ := policy_right_block hq ht hwide
  have hjj₀ : j ≤ j₀ := S.min'_le j₀ hj₀
  have hk₀k : k₀ ≤ k := S.le_max' k₀ hk₀
  have hlower : j*q ≤ a+2*q := (Nat.mul_le_mul_right q hjj₀).trans hleft
  have hupper : t ≤ ((k+1)*q-1)+2*q := by
    have hh := Nat.mul_le_mul_right q (Nat.add_le_add_right hk₀k 1)
    omega
  let key := policyKey A N q a t
  have hkey : key ∈ S := (finiteArgmin_spec hS (fun j => A (policyRepresentative A N q j))).1
  have hkeylo : j ≤ key := S.min'_le key hkey
  have hkeyhi : key ≤ k := S.le_max' key hkey
  have hrep := policyRepresentative_spec A hq
    ((Nat.le_div_iff_mul_le hq).mp (policyBlocks_mem hkey).1)
  have hplo : j*q ≤ policyDepth A N q a t := (Nat.mul_le_mul_right q hkeylo).trans hrep.1
  have hphi : policyDepth A N q a t ≤ (k+1)*q-1 := by
    have hh := hrep.2.1.trans_le (Nat.mul_le_mul_right q (Nat.add_le_add_right hkeyhi 1))
    exact Nat.le_sub_one_of_lt hh
  refine ⟨j*q,(k+1)*q-1,hlower,hupper,hplo,hphi,?_⟩
  intro n hnlo hnhi
  have hnN : n ≤ N := hnhi.trans huN
  have hjn : j ≤ n/q := (Nat.le_div_iff_mul_le hq).mpr hnlo
  have hnk : n/q ≤ k := by
    have hh : n < (k+1)*q := by omega
    have hd := (Nat.div_lt_iff_lt_mul hq).mpr hh
    omega
  exact policyDepth_minimizes A hq hS hnN (policy_blocks_order_convex hj hk hjn hnk)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PolicyDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem originDescriptor_anchor (A : ℕ → ℝ) {N q b u : ℕ} {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) : descriptorAnchor d = policyDepth A N q b u := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    rfl
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d; rfl
    · simp at hd

theorem originDescriptor_length (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) :
    0 < descriptorLength d ∧ b ≤ descriptorAnchor d-descriptorLength d ∧
      descriptorAnchor d+descriptorLength d ≤ u := by
  have hne := policyBlocks_nonempty hq huN hwide
  have hp := policyDepth_interior A hq hne
  have hl := policy_move_length A hq hne
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hd
    have hg := Finset.mem_Ico.mp hg
    dsimp only [descriptorLength,descriptorAnchor] at *
    omega
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d
      dsimp only [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

theorem originDescriptors_card (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) : (originDescriptors A N q b u).card ≤ N+1 := by
  classical
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq huN hwide)
  unfold originDescriptors
  apply (Finset.card_union_le _ _).trans
  have hfirst : ((Finset.Ico (policyDepth A N q b u-min (policyDepth A N q b u-b)
      (u-policyDepth A N q b u)) (policyDepth A N q b u)).image
      (fun g => PolicyDescriptor.parallel g (policyDepth A N q b u))).card ≤ N := by
    apply Finset.card_image_le.trans
    rw [Nat.card_Ico]
    omega
  split_ifs <;> simp only [Finset.card_singleton,Finset.card_empty] <;> omega

theorem policyDescriptorList_card (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) :
    (policyDescriptorList A N q a t).card ≤ (N+1)^3 := by
  classical
  calc
    _ ≤ ∑ z ∈ policyOrigins N q a t, (originDescriptors A N q z.1 z.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ policyOrigins N q a t, (N+1) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hz,_,_,hwide⟩ := Finset.mem_filter.mp hz
      have huN := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
      exact originDescriptors_card A hq huN hwide
    _ = (policyOrigins N q a t).card*(N+1) := by simp
    _ ≤ ((N+1)*(N+1))*(N+1) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans (by simp)
    _ = (N+1)^3 := by ring

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

 theorem spatialAnchorMask_eq_on_child (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d)
    (P : CellPath) (hn : n ≤ P.length) {x y : Plane}
    (hx : x ∈ (Q.descendant P).carrier) (hy : y ∈ (Q.descendant P).carrier) (dir : UnitCircle) :
    spatialAnchorMask Q ρ n G d hd x dir = spatialAnchorMask Q ρ n G d hd y dir := by
  classical
  have hp : (P.take n).length = n := by simp [List.length_take, Nat.min_eq_left hn]
  have hxP := Q.descendant_subset_take hQ P n hx
  have hyP := Q.descendant_subset_take hQ P n hy
  unfold spatialAnchorMask
  apply Finset.sum_congr rfl
  intro c hc
  have hlen : c.length = n := (mem_dyadicPaths n c).mp (Finset.mem_filter.mp hc).1
  by_cases he : c = P.take n
  · subst c; simp [hxP,hyP]
  · have hh := Q.descendants_disjoint hQ (hlen.trans hp.symm) he
    have hxc : x ∉ (Q.descendant c).carrier := fun h => Set.disjoint_left.mp hh h hxP
    have hyc : y ∉ (Q.descendant c).carrier := fun h => Set.disjoint_left.mp hh h hyP
    simp [hxc,hyc]

 theorem descriptorAngleMask_eq_on_child (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (P : CellPath) (hb : descriptorAnchor b ≤ P.length)
    {x y : Plane} (hx : x ∈ (Q.descendant P).carrier) (hy : y ∈ (Q.descendant P).carrier) :
    descriptorAngleMask Q ρ m N lam sig J i b x = descriptorAngleMask Q ρ m N lam sig J i b y := by
  funext θ
  exact spatialAnchorMask_eq_on_child Q hQ ρ _ _ _ _ P hb hx hy _

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

 theorem inheritedMaskProduct_split {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath)
    {x z : Plane} (hx : x ∈ (Q.descendant P).carrier) (hz : z ∈ (Q.descendant P).carrier) :
    inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x) =
      fun θ => inheritedMaskProduct (S.filter fun a => descriptorAnchor (b a) ≤ P.length)
        b k Q ρ m N lam sig J i (fun _ => z) θ *
      inheritedMaskProduct (S.filter fun a => P.length < descriptorAnchor (b a))
        b k Q ρ m N lam sig J i (fun _ => x) θ := by
  classical
  funext θ
  have he : inheritedMaskProduct (S.filter fun a => descriptorAnchor (b a) ≤ P.length)
      b k Q ρ m N lam sig J i (fun _ => x) θ =
      inheritedMaskProduct (S.filter fun a => descriptorAnchor (b a) ≤ P.length)
      b k Q ρ m N lam sig J i (fun _ => z) θ := by
    apply Finset.prod_congr rfl
    intro a ha
    have ha := (Finset.mem_filter.mp ha).2
    rw [descriptorAngleMask_eq_on_child Q hQ ρ m N lam sig J i (b a) P ha hx hz]
  rw [← he]
  unfold inheritedMaskProduct
  symm
  convert Finset.prod_filter_mul_prod_filter_not S (fun a => descriptorAnchor (b a) ≤ P.length)
    (fun a => normalizedMaskFactor (descriptorAngleMask Q ρ m N lam sig J i (b a) x)
      (sourceAngularRadius N sig (descriptorLength (b a))) (k a) θ) using 1
  all_goals try with_reducible_and_instances rfl
  simp

 theorem inheritedMaskProduct_removed_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (z : Plane)
    (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K) (θ : ℝ) :
    ‖inheritedMaskProduct (S.filter fun a => descriptorAnchor (b a) ≤ P.length)
      b k Q ρ m N lam sig J i (fun _ => z) θ‖ ≤ symbolDerivativeConstant K^K := by
  apply inheritedMaskProduct_zero_bound _ _ _ Q hQ _ _ _ _ _ _ _ _ K _ θ
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Nat.zero_le _)).trans hK

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularEnergyDropping
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

 theorem sourceAngularTransform_factor (ρ : Measure Plane) (X : Set Plane)
    (hX : MeasurableSet X) (M : ℝ) (b c : Plane → UnitCircle → ℂ) (a : UnitCircle → ℂ)
    (he : ∀ x ∈ X, ∀ ω, b x ω = a ω * c x ω) (r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ X M b r ω = a ω * sourceAngularTransform ρ X M c r ω := by
  unfold sourceAngularTransform
  have hh : (∫ x in X, Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (ω:Plane) x:ℂ))*b x ω ∂ρ) =
      ∫ x in X, a ω*(Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (ω:Plane) x:ℂ))*c x ω) ∂ρ := by
    apply setIntegral_congr_fun hX
    intro x hx
    dsimp only
    rw [he x hx ω]
    ring
  rw [hh,integral_const_mul]
  simp only [Complex.real_smul]
  ring

 theorem sourceAngularMoment_le_of_enorm (U V : ℝ × UnitCircle → ℂ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (h : ∀ z, ‖U z‖ₑ ≤ C*‖V z‖ₑ) (r : ℝ) :
    sourceAngularMoment U r ≤ C^2 * sourceAngularMoment V r := by
  unfold sourceAngularMoment
  calc
    _ ≤ ∫⁻ ω, (C*‖V (r,ω)‖ₑ)^2 ∂sourceArcLength :=
      lintegral_mono (fun ω => pow_le_pow_left' (h (r,ω)) 2)
    _ = _ := by simp_rw [mul_pow]; exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top hC)

 theorem sourceAngularH_le_of_enorm (a v : ℝ) (Ψ : ℝ → ℝ)
    (U₁ U₂ V₁ V₂ : ℝ × UnitCircle → ℂ) (C₁ C₂ : ℝ≥0∞)
    (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (h₁ : ∀ z, ‖U₁ z‖ₑ ≤ C₁*‖V₁ z‖ₑ) (h₂ : ∀ z, ‖U₂ z‖ₑ ≤ C₂*‖V₂ z‖ₑ) :
    sourceAngularH a v Ψ U₁ U₂ ≤ (C₁^2*C₂^2)*sourceAngularH a v Ψ V₁ V₂ := by
  unfold sourceAngularH
  calc
    _ ≤ ENNReal.ofReal ((2:ℝ)^(2*(v-a))) * ∫⁻ r,
        (C₁^2*sourceAngularMoment V₁ r)*(C₂^2*sourceAngularMoment V₂ r)
          ∂sourceAngularShellMeasure v Ψ := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro r
      exact mul_le_mul' (sourceAngularMoment_le_of_enorm U₁ V₁ C₁ hC₁ h₁ r)
        (sourceAngularMoment_le_of_enorm U₂ V₂ C₂ hC₂ h₂ r)
    _ = _ := by
      simp_rw [show ∀ r, (C₁^2*sourceAngularMoment V₁ r)*(C₂^2*sourceAngularMoment V₂ r) =
        (C₁^2*C₂^2)*(sourceAngularMoment V₁ r*sourceAngularMoment V₂ r) from fun r => by ring]
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top hC₁) (ENNReal.pow_ne_top hC₂))]
      ring

 theorem inherited_transform_drop {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (h : Plane → ℂ)
    {z : Plane} (hz : z ∈ (Q.descendant P).carrier) (M r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ (Q.descendant P).carrier M
      (inheritedCircleSymbol S b k Q ρ m N lam sig J i h) r ω =
      (inheritedMaskProduct (S.filter fun a => descriptorAnchor (b a) ≤ P.length)
        b k Q ρ m N lam sig J i (fun _ => z) (sourceAngle ω):ℂ) *
      sourceAngularTransform ρ (Q.descendant P).carrier M
        (inheritedCircleSymbol (S.filter fun a => P.length < descriptorAnchor (b a))
          b k Q ρ m N lam sig J i h) r ω := by
  apply sourceAngularTransform_factor ρ _ (Q.descendant P).measurable
  intro x hx ω
  unfold inheritedCircleSymbol
  rw [inheritedMaskProduct_split S b k Q hQ ρ m N lam sig J i P hx hz]
  simp only [Complex.ofReal_mul]
  ring

 theorem inherited_transform_drop_enorm {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (h : Plane → ℂ)
    (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K) {z : Plane} (hz : z ∈ (Q.descendant P).carrier)
    (M r : ℝ) (ω : UnitCircle) :
    ‖sourceAngularTransform ρ (Q.descendant P).carrier M
      (inheritedCircleSymbol S b k Q ρ m N lam sig J i h) r ω‖ₑ ≤
      ENNReal.ofReal (symbolDerivativeConstant K^K) *
      ‖sourceAngularTransform ρ (Q.descendant P).carrier M
        (inheritedCircleSymbol (S.filter fun a => P.length < descriptorAnchor (b a))
          b k Q ρ m N lam sig J i h) r ω‖ₑ := by
  rw [inherited_transform_drop S b k Q hQ ρ m N lam sig J i P h hz, enorm_mul]
  apply mul_le_mul_left
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Complex.norm_real] using
    inheritedMaskProduct_removed_bound S b k Q hQ ρ m N lam sig J i P z K hK (sourceAngle ω)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngularDropping
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

 theorem actual_inherited_H_drop
    {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]
    (S₁ : Finset ι₁) (S₂ : Finset ι₂) (b₁ : ι₁ → PolicyDescriptor) (b₂ : ι₂ → PolicyDescriptor)
    (k₁ : ι₁ → ℕ) (k₂ : ι₂ → ℕ) (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (ρ₁ ρ₂ : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P₁ P₂ : CellPath)
    (h₁ h₂ : Plane → ℂ) (K₁ K₂ : ℕ) (hK₁ : ∑ c ∈ S₁, k₁ c ≤ K₁)
    (hK₂ : ∑ c ∈ S₂, k₂ c ≤ K₂) {z₁ z₂ : Plane}
    (hz₁ : z₁ ∈ (Q₁.descendant P₁).carrier) (hz₂ : z₂ ∈ (Q₂.descendant P₂).carrier)
    (M₁ M₂ a v : ℝ) (Ψ : ℝ → ℝ) :
    sourceAngularH a v Ψ
      (fun z => sourceAngularTransform ρ₁ (Q₁.descendant P₁).carrier M₁
        (inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam sig J i h₁) z.1 z.2)
      (fun z => sourceAngularTransform ρ₂ (Q₂.descendant P₂).carrier M₂
        (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam sig J i h₂) z.1 z.2) ≤
    (ENNReal.ofReal (symbolDerivativeConstant K₁^K₁)^2 *
      ENNReal.ofReal (symbolDerivativeConstant K₂^K₂)^2) *
    sourceAngularH a v Ψ
      (fun z => sourceAngularTransform ρ₁ (Q₁.descendant P₁).carrier M₁
        (inheritedCircleSymbol (S₁.filter fun c => P₁.length < descriptorAnchor (b₁ c))
          b₁ k₁ Q₁ ρ₁ m₁ N lam sig J i h₁) z.1 z.2)
      (fun z => sourceAngularTransform ρ₂ (Q₂.descendant P₂).carrier M₂
        (inheritedCircleSymbol (S₂.filter fun c => P₂.length < descriptorAnchor (b₂ c))
          b₂ k₂ Q₂ ρ₂ m₂ N lam sig J i h₂) z.1 z.2) := by
  apply sourceAngularH_le_of_enorm _ _ _ _ _ _ _ _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · intro z
    exact inherited_transform_drop_enorm S₁ b₁ k₁ Q₁ hQ₁ ρ₁ m₁ N lam sig J i P₁ h₁ K₁ hK₁ hz₁ M₁ z.1 z.2
  · intro z
    exact inherited_transform_drop_enorm S₂ b₂ k₂ Q₂ hQ₂ ρ₂ m₂ N lam sig J i P₂ h₂ K₂ hK₂ hz₂ M₂ z.1 z.2

 theorem remaining_symbol_budget {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (a K : ℕ) (hK : ∑ c ∈ S, k c ≤ K) :
    ∑ c ∈ S.filter (fun c => a < descriptorAnchor (b c)), k c ≤ K :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)).trans hK

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
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductOccupiedVertices
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sourceProductVertices_subset (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a) :
    sourceProductVertices Q₁ Q₂ ρ ν A B n ⊆ (dyadicPaths (a+n)) ×ˢ (dyadicPaths (a+n)) := by
  classical
  intro c hc
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hc
  obtain ⟨x,hx,hx'⟩ := Finset.mem_image.mp h1
  obtain ⟨y,hy,hy'⟩ := Finset.mem_image.mp h2
  have hlx := (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hx).1
  have hly := (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hy).1
  rw [Finset.mem_product,← hx',← hy']
  simp [mem_dyadicPaths,hA,hB,hlx,hly]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductEnergyMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal NNReal

theorem finiteEnergyMaximum_nonneg {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞) :
    0 ≤ finiteEnergyMaximum S E := NNReal.coe_nonneg _

theorem le_finiteEnergyMaximum {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞) {i : ι} (hi : i ∈ S) :
    (E i).toReal ≤ finiteEnergyMaximum S E := by
  exact_mod_cast (Finset.le_sup (f := fun i => (E i).toNNReal) hi)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualProductEquation13
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_product_equation13
    {sig c₀ : ℝ} (hsig : 0 < sig) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi)
    (K : ℕ) (lam T : ℝ) (hlam : 0 ≤ lam) {η : ℝ} (hη : 0 < η) {J : ℕ} (hJ : 0 < J) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam mass) →
    ∀ (i : ℕ) (h : Fin 2 → Plane → ℂ), i < J → (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N →
    0 ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ e ∈ S 0, ∀ g : ℕ, d 0 e = .parallel g (a+n) →
    a ≤ g → g ≤ a+n → (g:ℝ)-a ≤ 2*sig*N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) mass N lam sig J i (h l)
    let M := fun _ : Fin 2 => ((2:ℝ)^N)^(-mass (a+n))
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 0) X.carrier
      (((2:ℝ)^N)^(-mass a)) (β 0) z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 1) Y.carrier
      (((2:ℝ)^N)^(-mass a)) (β 1) z.1 z.2
    let Uc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 0) ((Q 0).descendant P).carrier (M 0) (β 0) z.1 z.2
    let Vc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 1) ((Q 1).descendant P).carrier (M 1) (β 1) z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    (sourceAngularH a v Ψ U V).toReal ≤
      ((2:ℝ)^N)^(
        -2*(mass (a+n)-((a:ℝ)+n)/N-(mass a-(a:ℝ)/N))
        +height (fun t : ℕ => mass t-(t:ℝ)/(N:ℝ)) a (a+n)+4000*(lam+sig)+η) *
      finiteEnergyMaximum (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n)
        (fun row => sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)) + ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,hmain⟩ := uniform_actual_product_estimate hsig hc hcap K lam T hlam hη hJ hΨ hpos hs
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass B δ hd i h hi hh hhb a n v hp hu ht hLu hv
    e he g hdesc hag hgp hgap A B' hA hB
  have hh' := hmain N hN S d k hcard hK L hL Q hQ ρ (fun _ => mass) B δ hd
    i h hi hh hhb a n v hp hu ht hLu hv e he g hdesc hag hgp hgap A B' hA hB
  dsimp only at hh' ⊢
  have heq (x : ℝ) : -x-x = -2*x := by ring
  simpa only [heq] using hh'

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualProductEnergyFinite
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

theorem finiteEnergyMaximum_empty {ι : Type*} (E : ι → ℝ≥0∞) :
    finiteEnergyMaximum ∅ E = 0 := by simp [finiteEnergyMaximum]

theorem finiteEnergyMaximum_attained {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (E : ι → ℝ≥0∞) : ∃ i ∈ S, finiteEnergyMaximum S E = (E i).toReal := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup S hS (fun i => (E i).toNNReal)
  refine ⟨i,hi,?_⟩
  exact congrArg (fun x : ℝ≥0 => (x:ℝ)) he

theorem inherited_product_energy_finite
    {ι : Fin 2 → Type} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (K : ℕ) (hK : ∀ l, (∑ t ∈ S l, k l t) ≤ K)
    (Q : Fin 2 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (mass : Fin 2 → ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (X Y : Set Plane) (p v : ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    sourceAngularH p v Ψ
      (fun z => sourceAngularTransform (ρ 0) X M₁ (β 0) z.1 z.2)
      (fun z => sourceAngularTransform (ρ 1) Y M₂ (β 1) z.1 z.2) ≠ ⊤ := by
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  have hb : ∀ (l : Fin 2) (x : Plane) (dir : UnitCircle), ‖β l x dir‖ ≤ symbolDerivativeConstant K^K := by
    intro l x dir
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) dir
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  exact (sourceAngularH_original_four_transform p v hΨ.continuous.measurable hpos hs hW
    (fun t => (le_abs_self _).trans (hw t)) (ρ 0) (ρ 1) X Y hM₁ hM₂ (β 0) (β 1) (hm 0) (hm 1)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K) (hb 0) (hb 1)).1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDroppedMaximum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

theorem finiteEnergyMaximum_le_mul {ι : Type*} (S : Finset ι) (E F : ι → ℝ≥0∞)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i ∈ S, (E i).toReal ≤ c*(F i).toReal) :
    finiteEnergyMaximum S E ≤ c*finiteEnergyMaximum S F := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨i,hi,he⟩ := finiteEnergyMaximum_attained S hs E
    rw [he]
    exact (hb i hi).trans (mul_le_mul_of_nonneg_left (le_finiteEnergyMaximum S F hi) hc)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he,finiteEnergyMaximum_empty]

theorem inherited_product_energy_drop_real
    {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)]
    (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (K : ℕ) (hK : ∀ l, (∑ t ∈ S l, k l t) ≤ K)
    (Q : Fin 2 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (mass : Fin 2 → ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (row : CellPath × CellPath) (p v : ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let E := sourceAngularH p v Ψ
      (fun z => sourceAngularTransform (ρ 0) ((Q 0).descendant row.1).carrier M₁ (β 0) z.1 z.2)
      (fun z => sourceAngularTransform (ρ 1) ((Q 1).descendant row.2).carrier M₂ (β 1) z.1 z.2)
    let F := remainingAngularEnergy S d k Q ρ mass N lam sig J i h M₁ M₂ p v Ψ row
    F ≠ ⊤ ∧ E.toReal ≤ (symbolDerivativeConstant K^K)^4*F.toReal := by
  classical
  let P : Fin 2 → CellPath := ![row.1,row.2]
  let S' := fun l => (S l).filter (fun c => (P l).length < descriptorAnchor (d l c))
  have hb (l : Fin 2) : (∑ t ∈ S' l, k l t) ≤ K :=
    remaining_symbol_budget (S l) (d l) (k l) (P l).length K (hK l)
  have hf := inherited_product_energy_finite S' d k K hb Q hQ ρ mass N lam sig J i h hh hhb
    ((Q 0).descendant row.1).carrier ((Q 1).descendant row.2).carrier p v hM₁ hM₂ hΨ hpos hs
  have hdrop := actual_inherited_H_drop (S 0) (S 1) (d 0) (d 1) (k 0) (k 1) (Q 0) (Q 1)
    (hQ 0) (hQ 1) (ρ 0) (ρ 1) (mass 0) (mass 1) N lam sig J i row.1 row.2 (h 0) (h 1)
    K K (hK 0) (hK 1)
    (((Q 0).descendant row.1).center_mem ((Q 0).descendant_side_pos (hQ 0) row.1))
    (((Q 1).descendant row.2).center_mem ((Q 1).descendant_side_pos (hQ 1) row.2)) M₁ M₂ p v Ψ
  dsimp only
  have hf' : remainingAngularEnergy S d k Q ρ mass N lam sig J i h M₁ M₂ p v Ψ row ≠ ⊤ := hf
  refine ⟨hf',?_⟩
  have hn : 0 ≤ symbolDerivativeConstant K^K := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) hf') hdrop
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hn] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InheritedPolicyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

 theorem remainingPolicyDescriptors_mono (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ} (hap : a ≤ p) :
    remainingPolicyDescriptors A N q a₀ t₀ p ⊆ remainingPolicyDescriptors A N q a₀ t₀ a := by
  intro d hd
  obtain ⟨hd,hp⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hd,hap.trans_lt hp⟩

 theorem remainingPolicyDescriptors_drop (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ} (hap : a ≤ p) :
    (remainingPolicyDescriptors A N q a₀ t₀ a).filter (fun d => p < descriptorAnchor d) =
      remainingPolicyDescriptors A N q a₀ t₀ p := by
  ext d
  simp only [remainingPolicyDescriptors,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,hap.trans_lt h.2⟩,h.2⟩

 theorem remainingPolicyDescriptors_card (A : ℕ → ℝ) {N q a₀ t₀ a : ℕ} (hq : 0 < q) :
    (remainingPolicyDescriptors A N q a₀ t₀ a).card ≤ (N+1)^3 :=
  (Finset.card_filter_le _ _).trans (policyDescriptorList_card A hq)

 theorem reached_anchor_strictly_reduces_list (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ}
    (hap : a ≤ p) {d : PolicyDescriptor}
    (hd : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a) (hp : descriptorAnchor d ≤ p) :
    (remainingPolicyDescriptors A N q a₀ t₀ p).card <
      (remainingPolicyDescriptors A N q a₀ t₀ a).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨remainingPolicyDescriptors_mono A N q a₀ t₀ hap,?_⟩
  intro he
  rw [← he] at hd
  have hh := (Finset.mem_filter.mp hd).2
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStateData
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace AngularStateData

theorem child_budget (d : AngularStateData) {a p K : ℕ} (hap : a ≤ p)
    (k : PolicyDescriptor → ℕ) (hk : ∑ b ∈ d.retainedList a, k b ≤ K) :
    ∑ b ∈ d.retainedList p, k b ≤ K := by
  exact (Finset.sum_le_sum_of_subset (remainingPolicyDescriptors_mono
    d.profile d.N d.q d.a₀ d.t₀ hap)).trans hk

theorem cellEnergy_finite (d : AngularStateData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (S : Finset PolicyDescriptor)
    (k : Fin 2 → PolicyDescriptor → ℕ) (K : ℕ) (hk : ∀ l, ∑ b ∈ S, k l b ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (p : ℕ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) (row : CellPath × CellPath) :
    d.cellEnergy S k h p Ψ row ≠ ⊤ := by
  let : ∀ _l : Fin 2, IsFiniteMeasure d.ρ := fun _ => inferInstance
  exact inherited_product_energy_finite (fun _ : Fin 2 => S) (fun _ => id) k K hk
    (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) (fun _ => d.mass)
    d.N d.lam d.sig d.J d.i h hh hhb
    (d.Q.descendant row.1).carrier (d.Q.descendant row.2).carrier p d.v
    (by positivity) (by positivity) hΨ hpos hs

theorem childMaximum_nonneg (d : AngularStateData)
    (k : Fin 2 → PolicyDescriptor → ℕ) (h : Fin 2 → Plane → ℂ) (p : ℕ) (Ψ : ℝ → ℝ) :
    0 ≤ d.childMaximum k h p Ψ := finiteEnergyMaximum_nonneg _ _

end AngularStateData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStateDropping
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
namespace AngularStateData

theorem child_drop (d : AngularStateData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (p : ℕ) (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (row : CellPath × CellPath) (hr : row ∈ d.children p)
    (k : Fin 2 → PolicyDescriptor → ℕ) (K : ℕ)
    (hk : ∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    d.childEnergy k h p Ψ row ≠ ⊤ ∧
    (d.cellEnergy (d.retainedList d.a) k h p Ψ row).toReal ≤
      (symbolDerivativeConstant K^K)^4*(d.childEnergy k h p Ψ row).toReal := by
  classical
  have hd := sourceProductVertices_subset d.Q d.Q d.ρ d.ρ d.X d.Y d.a (p-d.a) hX hY hr
  have hl := Finset.mem_product.mp hd
  have h1 : row.1.length = p := by
    simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hl.1
  have h2 : row.2.length = p := by
    simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hl.2
  let : ∀ _l : Fin 2, IsFiniteMeasure d.ρ := fun _ => inferInstance
  have hdrop := inherited_product_energy_drop_real (fun _ : Fin 2 => d.retainedList d.a)
    (fun _ => id) k K hk (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) (fun _ => d.mass)
    d.N d.lam d.sig d.J d.i h hh hhb row p d.v
    (by positivity : 0 < ((2:ℝ)^d.N)^(-d.mass p))
    (by positivity : 0 < ((2:ℝ)^d.N)^(-d.mass p)) hΨ hpos hs
  simpa only [remainingAngularEnergy,h1,h2,childEnergy,cellEnergy,retainedList,id_eq,
    remainingPolicyDescriptors_drop d.profile d.N d.q d.a₀ d.t₀ hap] using hdrop

theorem child_maximum_drop (d : AngularStateData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (p : ℕ) (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (k : Fin 2 → PolicyDescriptor → ℕ) (K : ℕ)
    (hk : ∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    finiteEnergyMaximum (d.children p) (d.cellEnergy (d.retainedList d.a) k h p Ψ) ≤
      (symbolDerivativeConstant K^K)^4*d.childMaximum k h p Ψ := by
  apply finiteEnergyMaximum_le_mul _ _ _ (by positivity)
  intro row hr
  exact (d.child_drop hQ p hap hX hY row hr k K hk h hh hhb hΨ hpos hs).2

end AngularStateData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualOuterMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem sourceSmoothingLevels_pos {sig kap : ℝ} (hsig : 0 < sig) (hkap : 0 < kap) :
    0 < sourceSmoothingLevels sig kap := by
  unfold sourceSmoothingLevels
  exact Nat.ceil_pos.mpr (by positivity)

theorem sourcePolicyBlock_pos {N : ℕ} (hN : 0 < N) {kap : ℝ} (hkap : 0 < kap) :
    0 < sourcePolicyBlock N kap := by
  unfold sourcePolicyBlock
  exact Nat.ceil_pos.mpr (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_MinimalDescriptorLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem originDescriptor_length_le_anchor (A : ℕ → ℝ) {N q b u : ℕ}
    {d : PolicyDescriptor} (hd : d ∈ originDescriptors A N q b u) :
    descriptorLength d ≤ descriptorAnchor d := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    exact Nat.sub_le _ _
  · split_ifs at hd with h
    · obtain rfl := Finset.mem_singleton.mp hd
      dsimp [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixPolicyGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem source_policy_block_lower (N : ℕ) (kap : ℝ) :
    kap*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) := Nat.le_ceil _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualDirectBuffer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem uniform_source_ceiling_slack {sig kap : ℝ}
    (hsig : 0 < sig) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap ∧
      10*sig*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) ∧
      sig*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) := by
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (1/sig)
  refine ⟨max 1 N₀,by omega,?_⟩
  intro N hN
  have hNs : 1/sig < (N:ℝ) := h₀.trans_le (Nat.cast_le.mpr (by omega))
  have hsigN : 1 < sig*(N:ℝ) := by
    have := (div_lt_iff₀ hsig).mp hNs
    linarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 10*sig*(N:ℝ) by positivity)
  have hblock := source_policy_block_lower N kap
  have hgapN : 1000*sig*(N:ℝ) ≤ kap*N :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hlt : (⌈10*sig*(N:ℝ)⌉₊:ℝ) < (sourcePolicyBlock N kap:ℝ) := by linarith
  exact ⟨Nat.cast_lt.mp hlt,by linarith,by linarith⟩

theorem direct_buffer_eq_length {N L q a v : ℕ} {sig : ℝ}
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q) (hw : a+100*q < v)
    (hdirect : v-2*sourceFarBuffer N L sig ≤ a) :
    sourceFarBuffer N L sig = L ∧ v ≤ a+2*L ∧ 0 < L := by
  have hv : v ≤ a+2*sourceFarBuffer N L sig := by omega
  have hL : ⌈10*sig*(N:ℝ)⌉₊ ≤ L := by
    by_contra h
    have he : sourceFarBuffer N L sig = ⌈10*sig*(N:ℝ)⌉₊ := max_eq_right (by omega)
    rw [he] at hv
    omega
  have he : sourceFarBuffer N L sig = L := max_eq_left hL
  rw [he] at hv
  exact ⟨he,hv,by omega⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ActualPolicyPayments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem actual_direct_policy_payment (A : ℕ → ℝ) {N q a v a₀ t₀ : ℕ}
    (hq : 0 < q) (hw : a+100*q < v) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a₀ t₀)
    (hap : a < descriptorAnchor d)
    (hdirect : v ≤ a+2*descriptorLength d)
    (hscale : 2*descriptorAnchor d ≤ a+v+2*q) :
    descriptorAnchor d+10*q ≤ v ∧
      potential A a v (10*q)+height A a (descriptorAnchor d) ≤
        potential A (descriptorAnchor d) v (10*q) := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,_,_,hzwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hp := originDescriptor_anchor A hd
  have hlength := originDescriptor_length A hq huN hzwide hd
  have hlengthp := originDescriptor_length_le_anchor A hd
  obtain ⟨l,r,hl,hr,hlp,hpr,hinner⟩ := policy_interior_interval A hq huN hzwide
  rw [← hp] at hlp hpr hinner
  have hwidth : descriptorAnchor d+10*q ≤ v := by omega
  refine ⟨hwidth,policy_direct_payment A hq hwidth hap.le hlp hpr hl hr ?_ hdirect hinner⟩
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DirectPolicyWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem remaining_descriptor_companion (A : ℕ → ℝ) {N q a₀ t₀ a : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a) :
    PolicyDescriptor.parallel (max a (descriptorAnchor d-descriptorLength d))
      (descriptorAnchor d) ∈ remainingPolicyDescriptors A N q a₀ t₀ a := by
  classical
  obtain ⟨hd,hap⟩ := Finset.mem_filter.mp hd
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  have hz' := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz'.1).2)
  have hp := originDescriptor_anchor A hd
  have hl := originDescriptor_length A hq huN hz'.2.2.2 hd
  have hLp := originDescriptor_length_le_anchor A hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ⟨z,hz,?_⟩,hap⟩
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨max a (descriptorAnchor d-descriptorLength d),Finset.mem_Ico.mpr ⟨?_,?_⟩,?_⟩
  · rw [← hp]
    omega
  · omega
  · rw [hp]

theorem actual_direct_policy_witness (A : ℕ → ℝ) {N q a₀ t₀ a v : ℕ} {sig : ℝ}
    (hsig : 0 ≤ sig) (hq : 0 < q) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    (hslack : sig*(N:ℝ) ≤ (q:ℝ)) (hslack10 : 10*sig*(N:ℝ) ≤ (q:ℝ))
    (ht : (t₀:ℝ) ≤ (v:ℝ)+sig*N) (hw : a+100*q < v)
    (hdirect : v-2*sourceFarBuffer N
      ((remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength) sig ≤ a) :
    ∃ d : PolicyDescriptor, DirectPolicyWitness A N q a₀ t₀ a v sig d := by
  classical
  let S := remainingPolicyDescriptors A N q a₀ t₀ a
  have hb := direct_buffer_eq_length hceil hw hdirect
  have hS : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : S.sup descriptorLength = 0 := by rw [he]; rfl
    exact (Nat.ne_of_gt hb.2.2) hz
  obtain ⟨d,hd,hmax⟩ := Finset.exists_mem_eq_sup S hS descriptorLength
  dsimp only [S] at hmax
  have hmax' := hmax.symm
  have hdir : v ≤ a+2*descriptorLength d := by simpa only [hmax] using hb.2.1
  have hmem := Finset.mem_filter.mp hd
  have hap : a < descriptorAnchor d := hmem.2
  obtain ⟨z,hz,hzd⟩ := Finset.mem_biUnion.mp hmem.1
  have hz' := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz'.1).2)
  have hl := originDescriptor_length A hq huN hz'.2.2.2 hzd
  have hLp := originDescriptor_length_le_anchor A hzd
  have hpt : descriptorAnchor d+descriptorLength d ≤ t₀ := hl.2.2.trans hz'.2.2.1
  have hptR : (descriptorAnchor d:ℝ)+(descriptorLength d:ℝ) ≤ (t₀:ℝ) := by exact_mod_cast hpt
  have hsigN : 0 ≤ sig*(N:ℝ) := mul_nonneg hsig (Nat.cast_nonneg _)
  have hdirR : (v:ℝ) ≤ (a:ℝ)+2*(descriptorLength d:ℝ) := by exact_mod_cast hdir
  have hmidR : 2*(descriptorAnchor d:ℝ) ≤ (a:ℝ)+v+2*q := by linarith
  have hmid : 2*descriptorAnchor d ≤ a+v+2*q := by exact_mod_cast hmidR
  have hwidth : descriptorAnchor d+10*q ≤ v := by omega
  have hwidthR : (descriptorAnchor d:ℝ)+10*(q:ℝ) ≤ (v:ℝ) := by exact_mod_cast hwidth
  have hn : ((descriptorAnchor d-a:ℕ):ℝ) = (descriptorAnchor d:ℝ)-a := Nat.cast_sub hap.le
  have hgs : ((descriptorAnchor d-descriptorLength d:ℕ):ℝ) =
      (descriptorAnchor d:ℝ)-descriptorLength d := Nat.cast_sub hLp
  refine ⟨d, {
    mem := hd
    maximal := hmax'
    buffer := ?_
    direct_depth := hdir
    anchor_gt := hap
    anchor_lt := by omega
    width := hwidth
    companion := remaining_descriptor_companion A hq hd
    g_lt := by omega
    g_slack := ?_
    frequency_slack := by linarith
    depth_scale := ?_
    length_scale := ?_
    midpoint := hmid
    shrinks := reached_anchor_strictly_reduces_list A N q a₀ t₀ hap.le hd le_rfl
    payment := (actual_direct_policy_payment A hq hw hmem.1 hap hdir hmid).2 }⟩
  · simpa only [← hmax] using hb.1
  · rw [Nat.cast_max,hgs,sub_le_iff_le_add]
    apply max_le <;> linarith [show 0 ≤ sig*(N:ℝ) by positivity]
  · rw [hn]
    linarith
  · have haR : (a:ℝ) < (descriptorAnchor d:ℝ) := Nat.cast_lt.mpr hap
    linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualDirectGraph
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
namespace AngularStateData

theorem uniform_direct_graph {lam sig eps : ℝ} (hlam : 0 ≤ lam) (hsig : 0 < sig)
    (heps : 0 < eps) (T : ℝ) (K J : ℕ) (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : AngularStateData,
      d.lam = lam → d.sig = sig → d.J = J → N₀ ≤ d.N →
      d.Q.side = 1 → 0 < d.q → d.v ≤ d.N → d.i < d.J →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      ∀ e : PolicyDescriptor, DirectPolicyWitness d.profile d.N d.q d.a₀ d.t₀ d.a d.v d.sig e →
      let p := descriptorAnchor e
      d.energy k h Ψ ≠ ⊤ ∧ (∀ row, d.childEnergy k h p Ψ row ≠ ⊤) ∧
      (∀ l, ∑ b ∈ d.retainedList p, k l b ≤ K) ∧
      (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
        (-2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(lam+sig)+eps) *
          d.childMaximum k h p Ψ + ((2:ℝ)^d.N)^(-T) := by
  obtain ⟨N₁,h₁⟩ := uniform_actual_product_equation13 hsig Real.pi_pos
    (by linarith [Real.pi_pos] : Real.pi ≤ 2*Real.pi)
    K lam T hlam (half_pos heps) hJ hΨ hpos hs
  obtain ⟨N₂,h₂⟩ := fixed_constant_absorbed (half_pos heps) ((symbolDerivativeConstant K^K)^4)
  refine ⟨max N₁ N₂,?_⟩
  intro d hdLam hdSig hdJ hN hQ hq hvN hi hX hY B δ hprof k hk h hh hhb e hw
  subst lam
  subst sig
  subst J
  let := hprof.probability
  have hQp : 0 < d.Q.side := by rw [hQ]; norm_num
  let p := descriptorAnchor e
  have hap : d.a ≤ p := hw.anchor_gt.le
  have hpN : p ≤ d.N := hw.anchor_lt.le.trans hvN
  have heq : d.a+(p-d.a) = p := Nat.add_sub_of_le hap
  have heqR : (d.a:ℝ)+((p-d.a:ℕ):ℝ) = (p:ℝ) := by exact_mod_cast heq
  have hcard (_l : Fin 2) : (d.retainedList d.a).card ≤ (d.N+1)^3+1 :=
    (remainingPolicyDescriptors_card d.profile hq).trans (Nat.le_succ _)
  have hL (_l : Fin 2) (b : PolicyDescriptor) (hb : b ∈ d.retainedList d.a) :
      descriptorLength (id b) ≤ descriptorLength e := by
    rw [hw.maximal]
    exact Finset.le_sup hb
  have hdepth : ((p-d.a:ℕ):ℝ) ≤ (d.v:ℝ)-((d.a:ℝ)+((p-d.a:ℕ):ℝ))+2*d.sig*d.N := by
    rw [heqR]
    exact hw.depth_scale
  have hlength : (descriptorLength e:ℝ) ≤ (d.v:ℝ)-((d.a:ℝ)+((p-d.a:ℕ):ℝ))+2*d.sig*d.N := by
    rw [heqR]
    exact hw.length_scale
  have hv : 0 ≤ (d.v:ℝ)-((d.a:ℝ)+((p-d.a:ℕ):ℝ)) := by
    rw [heqR]
    exact sub_nonneg.mpr (Nat.cast_le.mpr hw.anchor_lt.le)
  have hgap : ((max d.a (p-descriptorLength e):ℕ):ℝ)-d.a ≤ 2*d.sig*d.N := by
    have hg := hw.g_slack
    dsimp only [p] at *
    linarith [show 0 ≤ d.sig*(d.N:ℝ) by positivity]
  have hmain := h₁ d.N ((le_max_left _ _).trans hN)
    (fun _ : Fin 2 => d.retainedList d.a) (fun _ => id) k hcard hk
    (descriptorLength e) hL (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) d.mass B δ
    (fun _ => hprof) d.i h hi hh hhb d.a (p-d.a) d.v (by omega) hv hdepth hlength
    (by have htR : (d.v:ℝ) ≤ d.N := Nat.cast_le.mpr hvN; linarith [show (0:ℝ) ≤ (d.a:ℝ) from Nat.cast_nonneg _])
    (.parallel (max d.a (p-descriptorLength e)) p) hw.companion
    (max d.a (p-descriptorLength e)) (by simp only [id_eq,heq])
    (le_max_left _ _) (by rw [heq]; exact hw.g_lt.le) hgap d.X d.Y hX hY
  have hgraph : d.energy k h Ψ ≠ ⊤ ∧
      (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
        (-2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(d.lam+d.sig)+eps/2) *
          finiteEnergyMaximum (d.children p) (d.cellEnergy (d.retainedList d.a) k h p Ψ)
            + ((2:ℝ)^d.N)^(-T) := by
    dsimp only at hmain
    simp only [heqR,heq] at hmain
    exact hmain
  have hk' (l : Fin 2) := d.child_budget hap (k l) (hk l)
  refine ⟨hgraph.1,fun row => d.cellEnergy_finite hQp (d.retainedList p) k K hk' h hh hhb p hΨ hpos hs row,
    hk',hgraph.2.trans ?_⟩
  have hdrop := d.child_maximum_drop hQp p hap hX hY k K hk h hh hhb hΨ hpos hs
  have hconst := h₂ d.N ((le_max_right _ _).trans hN)
  let E := -2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(d.lam+d.sig)
  have habs : ((2:ℝ)^d.N)^(E+eps/2)*(symbolDerivativeConstant K^K)^4 ≤
      ((2:ℝ)^d.N)^(E+eps) := by
    calc
      _ ≤ ((2:ℝ)^d.N)^(E+eps/2)*((2:ℝ)^d.N)^(eps/2) := by gcongr
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  calc
    _ ≤ ((2:ℝ)^d.N)^(E+eps/2)*((symbolDerivativeConstant K^K)^4*d.childMaximum k h p Ψ)
        + ((2:ℝ)^d.N)^(-T) := by gcongr
    _ = (((2:ℝ)^d.N)^(E+eps/2)*(symbolDerivativeConstant K^K)^4)*d.childMaximum k h p Ψ
        + ((2:ℝ)^d.N)^(-T) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right habs (d.childMaximum_nonneg k h p Ψ)) le_rfl

end AngularStateData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SourceAngularDirect
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem source_angular_direct_oai {lam sig kap eps : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (T : ℝ) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ d : AngularStateData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 →
      d.a₀ ≤ d.a → d.a ≤ d.v → d.v ≤ d.t₀ → d.t₀ ≤ d.N →
      (d.t₀:ℝ) ≤ (d.v:ℝ)+sig*d.N → d.a+100*d.q < d.v → d.i+1 ≤ d.J →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.retainedList d.a, k l b ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      d.v-2*sourceFarBuffer d.N ((d.retainedList d.a).sup descriptorLength) d.sig ≤ d.a →
      ∃ e : PolicyDescriptor,
        DirectPolicyWitness d.profile d.N d.q d.a₀ d.t₀ d.a d.v d.sig e ∧
        let p := descriptorAnchor e
        d.energy k h Ψ ≠ ⊤ ∧ (∀ row, d.childEnergy k h p Ψ row ≠ ⊤) ∧
        (∀ l, ∑ b ∈ d.retainedList p, k l b ≤ K) ∧
        (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^
          (-2*(d.profile p-d.profile d.a)+height d.profile d.a p+4000*(lam+sig)+eps) *
            d.childMaximum k h p Ψ + ((2:ℝ)^d.N)^(-T) := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,h₂⟩ := AngularStateData.uniform_direct_graph hlam hsig heps T K
    (sourceSmoothingLevels sig kap) (sourceSmoothingLevels_pos hsig hkap) hΨ hpos hs
  refine ⟨max N₁ N₂,?_⟩
  intro d hdLam hdSig hdq hdJ hN hQ ha₀ hav hvt htN ht hw hi hX hY B δ hprof k hk h hh hhb hdir
  have hNpos : 0 < d.N := hN₁.trans_le ((le_max_left _ _).trans hN)
  have hq : 0 < d.q := by rw [hdq]; exact sourcePolicyBlock_pos hNpos hkap
  have hslack := h₁ d.N ((le_max_left _ _).trans hN)
  rw [← hdq,← hdSig] at hslack
  have hsig' : 0 < d.sig := hdSig ▸ hsig
  have ht' : (d.t₀:ℝ) ≤ (d.v:ℝ)+d.sig*d.N := by simpa only [hdSig] using ht
  obtain ⟨e,he⟩ := actual_direct_policy_witness d.profile hsig'.le hq hslack.1
    hslack.2.2 hslack.2.1 ht' hw hdir
  refine ⟨e,he,?_⟩
  exact h₂ d hdLam hdSig hdJ ((le_max_right _ _).trans hN) hQ hq (hvt.trans htN)
    (by omega) hX hY B δ hprof k hk h hh hhb e he

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.source_angular_direct_oai := @OAI.PlanarFalconer.source_angular_direct_oai
