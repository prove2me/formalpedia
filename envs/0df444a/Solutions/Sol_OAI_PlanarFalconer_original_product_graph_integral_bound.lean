-- Prove2me | solution 1 for OAI.PlanarFalconer.original_product_graph_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:24:45.526226+00:00
-- url     : https://prove2.me/submissions/516a5b6f-7d13-4df2-afba-134bee0bf9c9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

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

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphActualNonedgeSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem graphOriginalTerm_zero_of_empty_weight_support
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (distance plus : Bool) (axis δ v : ℝ)
    (j k : ℕ) (Ψ : ℝ → ℝ)
    (hS : ¬(tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty) :
    graphOriginalTerm ρ X M b distance plus axis δ v j k Ψ = 0 := by
  have hw (u w : UnitCircle) : graphSourceWeight distance plus axis (angularBinCount δ) j k (u,w) = 0 := by
    by_contra hn
    exact hS ⟨(u,w),subset_closure hn⟩
  simp [graphOriginalTerm,sourceGraphFourTransform,hw]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualProductDegrees
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphOriginalProductSum_supported (I : Finset GraphNonedgeIndex)
    (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare) (M : Fin 4 → ℝ)
    (β : Fin 4 → Plane → UnitCircle → ℂ) (θ v : ℝ) (Ψ : ℝ → ℝ) :
    (∑ e ∈ I, graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M β
      false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ) =
    ∑ e ∈ graphSupportedProductIndices I θ,
      graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M β
        false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hn
  apply graphOriginalTerm_zero_of_empty_weight_support
  intro hs
  exact hn (Finset.mem_filter.mpr ⟨he,hs⟩)

theorem activeProductMatrixNeighbors_eq_supported (I : Finset GraphNonedgeIndex)
    (p j b : ℕ) (θ : ℝ) (plus reverse : Bool) (row : CellPath × CellPath) :
    activeProductMatrixNeighbors I p j b θ plus reverse row =
      productMatrixNeighbors (graphSupportedProductIndices I θ) p j b plus reverse row := by
  classical
  ext c
  cases reverse <;> by_cases hs : (tsupport (graphSourceWeight false plus 0 (angularBinCount θ) j b)).Nonempty <;>
    simp [activeProductMatrixNeighbors,productMatrixNeighbors,graphSupportedProductIndices,productMatrixIndex,hs]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_FinsetSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finset_bipartite_schur {α β : Type*} (A : Finset α) (B : Finset β)
    (G : α → β → Prop) [DecidableRel G] (u : α → ℝ) (v : β → ℝ) (d : ℝ)
    (hrow : ∀ a ∈ A, ((B.filter (G a)).card : ℝ) ≤ d)
    (hcol : ∀ b ∈ B, ((A.filter (fun a => G a b)).card : ℝ) ≤ d) :
    (∑ a ∈ A, ∑ b ∈ B, if G a b then u a*v b else 0) ≤
      d/2*((∑ a ∈ A, u a^2)+(∑ b ∈ B, v b^2)) := by
  have hp (a : α) (b : β) : 2*(if G a b then u a*v b else 0) ≤
      (if G a b then u a^2 else 0)+(if G a b then v b^2 else 0) := by
    split_ifs
    · nlinarith [sq_nonneg (u a-v b)]
    · norm_num
  have hs := Finset.sum_le_sum (s := A) (fun a _ =>
    Finset.sum_le_sum (s := B) (fun b _ => hp a b))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hR : (∑ a ∈ A, ∑ b ∈ B, if G a b then u a^2 else 0) ≤ d*(∑ a ∈ A, u a^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hrow a ha) (sq_nonneg _)
  have hC : (∑ a ∈ A, ∑ b ∈ B, if G a b then v b^2 else 0) ≤ d*(∑ b ∈ B, v b^2) := by
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcol b hb) (sq_nonneg _)
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductMatrixReindex
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable

theorem product_graph_sum_matrix {p m : ℕ} (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ graphNonedgeIndices p m) (j b : ℕ) (plus : Bool)
    {α : Type*} [AddCommMonoid α] (F : GraphNonedgeIndex → α) :
    (∑ e ∈ I.filter (fun e => e.2 = ((j,b),plus)), F e) =
    ∑ row ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
      ∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
        if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0 := by
  classical
  rw [← Finset.sum_product',← Finset.sum_filter]
  apply Finset.sum_bij (fun e _ => ((e.1.1.1,e.1.2.1),(e.1.1.2,e.1.2.2)))
  · intro e he
    obtain ⟨he,hs⟩ := Finset.mem_filter.mp he
    have hq := (Finset.mem_product.mp (hI he)).1
    simp only [graphCellQuadIndices,Finset.product_eq_sprod,Finset.mem_product] at hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hq.1.1,hq.2.1⟩,
      Finset.mem_product.mpr ⟨hq.1.2,hq.2.2⟩⟩,?_⟩
    have hi : productMatrixIndex (e.1.1.1,e.1.2.1) (e.1.1.2,e.1.2.2) j b plus = e := by
      exact Prod.ext rfl hs.symm
    rw [hi]
    exact he
  · intro e he f hf heq
    have hs := (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (Prod.ext (Prod.ext heq.1.1 heq.2.1) (Prod.ext heq.1.2 heq.2.2)) hs
  · intro pair hp
    have hp' := (Finset.mem_filter.mp hp).2
    exact ⟨productMatrixIndex pair.1 pair.2 j b plus,Finset.mem_filter.mpr ⟨hp',rfl⟩,rfl⟩
  · intro e he
    have hs := (Finset.mem_filter.mp he).2
    have hi : productMatrixIndex (e.1.1.1,e.1.2.1) (e.1.1.2,e.1.2.2) j b plus = e :=
      Prod.ext rfl hs.symm
    exact congrArg F hi.symm

theorem product_graph_sum_bins {p m : ℕ} (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ graphNonedgeIndices p m) {α : Type*} [AddCommMonoid α]
    (F : GraphNonedgeIndex → α) :
    (∑ e ∈ I, F e) =
      ∑ j ∈ Finset.range m, ∑ b ∈ Finset.range m, ∑ plus : Bool,
        ∑ row ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
          ∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
            if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0 := by
  classical
  have he : (∑ s ∈ ((Finset.range m) ×ˢ (Finset.range m)) ×ˢ (Finset.univ : Finset Bool),
      ∑ e ∈ I.filter (fun e => e.2 = s), F e) = ∑ e ∈ I, F e := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    exact Finset.sum_eq_single_of_mem e.2 (Finset.mem_product.mp (hI he)).2
      (fun s _ hs => by simp [Ne.symm hs]) |>.trans (by simp)
  rw [← he]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro plus _
  simpa only [Finset.sum_product] using product_graph_sum_matrix I hI j b plus F

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

theorem sourceProductGraphIndices_vertices (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (n m : ℕ) {e : GraphNonedgeIndex}
    (he : e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B) :
    (e.1.1.1,e.1.2.1) ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n ∧
    (e.1.1.2,e.1.2.2) ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  simp only [sourceProductRelativeIndices,Finset.mem_product] at hq
  constructor
  · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,hq.1.1.1,rfl⟩,
      Finset.mem_image.mpr ⟨_,hq.1.2.1,rfl⟩⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,hq.1.1.2,rfl⟩,
      Finset.mem_image.mpr ⟨_,hq.1.2.2,rfl⟩⟩

theorem product_matrix_schur_on (I : Finset GraphNonedgeIndex) (p j b : ℕ) (θ : ℝ)
    (plus : Bool) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (u v : CellPath × CellPath → ℝ) (d : ℝ)
    (hdegree : ∀ (reverse : Bool) (row : CellPath × CellPath),
      ((activeProductMatrixNeighbors I p j b θ plus reverse row).card : ℝ) ≤ d) :
    let H := graphSupportedProductIndices I θ
    (∑ row ∈ C, ∑ col ∈ C, if productMatrixIndex row col j b plus ∈ H then u row*v col else 0) ≤
      d/2*((∑ row ∈ C, u row^2)+(∑ col ∈ C, v col^2)) := by
  classical
  dsimp only
  apply finset_bipartite_schur
  · intro row _
    apply le_trans _ (hdegree false row)
    rw [activeProductMatrixNeighbors_eq_supported]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro col hc
    obtain ⟨hc,hi⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨hC hc,hi⟩
  · intro col _
    apply le_trans _ (hdegree true col)
    rw [activeProductMatrixNeighbors_eq_supported]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro row hr
    obtain ⟨hr,hi⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hC hr,hi⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductOccupiedIntegrand
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem product_matrix_complex_bound_on (I : Finset GraphNonedgeIndex) (p j b : ℕ) (θ : ℝ)
    (plus : Bool) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p)) (U V : CellPath → ℂ) (W : ℂ) (d : ℝ)
    (hdegree : ∀ (reverse : Bool) (row : CellPath × CellPath),
      ((activeProductMatrixNeighbors I p j b θ plus reverse row).card : ℝ) ≤ d) :
    let H := graphSupportedProductIndices I θ
    ‖∑ row ∈ C, ∑ col ∈ C, if productMatrixIndex row col j b plus ∈ H
      then W*(U row.1*conj (U col.1))*(V row.2*conj (V col.2)) else 0‖ ≤
    ‖W‖*d*(∑ row ∈ C, ‖U row.1‖^2*‖V row.2‖^2) := by
  classical
  dsimp only
  let H := graphSupportedProductIndices I θ
  let f := fun row : CellPath × CellPath => ‖U row.1‖*‖V row.2‖
  have hh := product_matrix_schur_on I p j b θ plus C hC f f d hdegree
  dsimp only at hh
  have he : (∑ row ∈ C, ∑ col ∈ C,
      ‖if productMatrixIndex row col j b plus ∈ H
        then W*(U row.1*conj (U col.1))*(V row.2*conj (V col.2)) else 0‖) =
      ‖W‖*(∑ row ∈ C, ∑ col ∈ C, if productMatrixIndex row col j b plus ∈ H
        then f row*f col else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro col _
    split_ifs <;> simp only [norm_mul,Complex.norm_conj,norm_zero,mul_zero,f]
    ring
  calc
    _ ≤ ∑ row ∈ C, ‖∑ col ∈ C, if productMatrixIndex row col j b plus ∈ H
        then W*(U row.1*conj (U col.1))*(V row.2*conj (V col.2)) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ row ∈ C, ∑ col ∈ C, ‖if productMatrixIndex row col j b plus ∈ H
        then W*(U row.1*conj (U col.1))*(V row.2*conj (V col.2)) else 0‖ :=
      Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ = _ := he
    _ ≤ ‖W‖*(d/2*((∑ row ∈ C, f row^2)+(∑ row ∈ C, f row^2))) :=
      mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = _ := by simp only [f,mul_pow]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductOccupiedSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem product_matrix_sum_restrict {p : ℕ} (I : Finset GraphNonedgeIndex)
    (C : Finset (CellPath × CellPath)) (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hvertices : ∀ e ∈ I, (e.1.1.1,e.1.2.1) ∈ C ∧ (e.1.1.2,e.1.2.2) ∈ C)
    (j b : ℕ) (plus : Bool) {α : Type*} [AddCommMonoid α] (F : GraphNonedgeIndex → α) :
    (∑ row ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
      ∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
        if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0) =
    ∑ row ∈ C, ∑ col ∈ C,
      if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0 := by
  classical
  have hcol (row : CellPath × CellPath) :
      (∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
        if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0) =
      ∑ col ∈ C, if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0 := by
    symm
    apply Finset.sum_subset hC
    intro col _ hn
    have hi : productMatrixIndex row col j b plus ∉ I := fun hi => hn (hvertices _ hi).2
    simp [hi]
  simp_rw [hcol]
  symm
  apply Finset.sum_subset hC
  intro row _ hn
  apply Finset.sum_eq_zero
  intro col _
  have hi : productMatrixIndex row col j b plus ∉ I := fun hi => hn (hvertices _ hi).1
  simp [hi]

theorem source_product_graph_sum_occupied (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (a n m : ℕ) (hA : A.length = a) (hB : B.length = a)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
    {α : Type*} [AddCommMonoid α] (F : GraphNonedgeIndex → α) :
    (∑ e ∈ I, F e) =
    ∑ j ∈ Finset.range m, ∑ b ∈ Finset.range m, ∑ plus : Bool,
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          if productMatrixIndex row col j b plus ∈ I then F (productMatrixIndex row col j b plus) else 0 := by
  rw [product_graph_sum_bins I (hI.trans (sourceProductGraphIndices_subset hA hB)) F]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro plus _
  exact product_matrix_sum_restrict I _ (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB)
    (fun e he => sourceProductGraphIndices_vertices Q₁ Q₂ ρ ν A B n m (hI he)) j b plus F

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductWeightSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphProductWeight_nonneg (s : Bool) (m j k : ℕ) (p : UnitCircle × UnitCircle) :
    0 ≤ (graphProductWeight s m j k p).re := by
  have hb := mul_nonneg (circleAngularBin_bounds m j p.1).1 (circleAngularBin_bounds m k p.2).1
  have hs := graphSignPartition_bounds ((p.1:Plane),(p.2:Plane))
  cases s
  · exact mul_nonneg hb hs.2.2.1
  · exact mul_nonneg hb hs.1

theorem graphProductWeight_norm (s : Bool) (m j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphProductWeight s m j k p‖ = (graphProductWeight s m j k p).re := by
  have hp := graphProductWeight_nonneg s m j k p
  unfold graphProductWeight at hp ⊢
  simpa only [Complex.norm_real,Real.norm_eq_abs,Complex.ofReal_re] using abs_of_nonneg hp

theorem graphProductWeight_norm_total {m : ℕ} (hm : 0 < m) (p : UnitCircle × UnitCircle) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ∑ s : Bool, ‖graphProductWeight s m j k p‖) = 1 := by
  have he := congrArg Complex.re (graphProductWeight_total hm p)
  simpa only [Complex.re_sum,Complex.one_re,graphProductWeight_norm] using he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductGraphPointwise
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem product_graph_pointwise_bound
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (A B : CellPath) (a n m : ℕ)
    (hA : A.length = a) (hB : B.length = a) (hm : 0 < m)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
    (θ d : ℝ)
    (hdegree : ∀ j k s reverse row,
      ((activeProductMatrixNeighbors I (a+n) j k θ s reverse row).card : ℝ) ≤ d)
    (U V : CellPath → ℂ) (u w : UnitCircle) :
    ‖∑ e ∈ graphSupportedProductIndices I θ,
      graphProductWeight e.2.2 m e.2.1.1 e.2.1.2 (u,w) *
        (U e.1.1.1*conj (U e.1.1.2))*(V e.1.2.1*conj (V e.1.2.2))‖ ≤
      d * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, ‖U row.1‖^2*‖V row.2‖^2 := by
  classical
  let C := sourceProductVertices Q₁ Q₂ ρ ν A B n
  let H := graphSupportedProductIndices I θ
  let F := fun e : GraphNonedgeIndex => graphProductWeight e.2.2 m e.2.1.1 e.2.1.2 (u,w) *
    (U e.1.1.1*conj (U e.1.1.2))*(V e.1.2.1*conj (V e.1.2.2))
  have hh : H ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B :=
    (Finset.filter_subset _ _).trans hI
  change ‖∑ e ∈ H, F e‖ ≤ _
  rw [source_product_graph_sum_occupied Q₁ Q₂ ρ ν A B a n m hA hB H hh F]
  calc
    _ ≤ ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ∑ s : Bool,
        ‖∑ row ∈ C, ∑ col ∈ C, if productMatrixIndex row col j k s ∈ H
          then F (productMatrixIndex row col j k s) else 0‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ∑ s : Bool,
        ‖graphProductWeight s m j k (u,w)‖*d*(∑ row ∈ C, ‖U row.1‖^2*‖V row.2‖^2) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro s _
      exact product_matrix_complex_bound_on I (a+n) j k θ s C
        (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB)
        U V (graphProductWeight s m j k (u,w)) d (hdegree j k s)
    _ = _ := by
      simp only [← Finset.sum_mul,graphProductWeight_norm_total hm,one_mul,C]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_ProductSchurIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem product_moment_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hbU : ∀ x, ‖U x‖ ≤ C) (hbV : ∀ x, ‖V x‖ ≤ D) :
    Integrable (fun r => sourceRealAngularMoment U r * sourceRealAngularMoment V r) μ := by
  apply Integrable.of_bound
    ((sourceRealAngularMoment_measurable U hU).mul (sourceRealAngularMoment_measurable V hV)).aestronglyMeasurable
    ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ))
  filter_upwards with r
  change ‖sourceRealAngularMoment U r * sourceRealAngularMoment V r‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sourceRealAngularMoment_nonneg U r)
    (sourceRealAngularMoment_nonneg V r))]
  exact mul_le_mul (sourceRealAngularMoment_bound U hbU r) (sourceRealAngularMoment_bound V hbV r)
    (sourceRealAngularMoment_nonneg V r) (by positivity)

theorem circle_pair_schur_bound {ι : Type*} (S : Finset ι)
    (U V : ι → ℝ × UnitCircle → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ x, ‖U i x‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ x, ‖V i x‖ ≤ D i)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) {d : ℝ} (_hd : 0 ≤ d)
    (hb : ∀ r u w, ‖F (r,(u,w))‖ ≤ d * ∑ i ∈ S, ‖U i (r,u)‖^2*‖V i (r,w)‖^2)
    (r : ℝ) :
    ‖∫ u, ∫ w, F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength‖ ≤
      d * ∑ i ∈ S, sourceRealAngularMoment (U i) r * sourceRealAngularMoment (V i) r := by
  have hiU (i : ι) (hi : i ∈ S) := integrable_circle_norm_square (fun u => U i (r,u))
    ((hU i hi).comp (measurable_const.prodMk measurable_id)) (hC i hi) (fun u => hbU i hi (r,u))
  have hiV (i : ι) (hi : i ∈ S) := integrable_circle_norm_square (fun w => V i (r,w))
    ((hV i hi).comp (measurable_const.prodMk measurable_id)) (hD i hi) (fun w => hbV i hi (r,w))
  have inner (u : UnitCircle) :
      ‖∫ w, F (r,(u,w)) ∂sourceArcLength‖ ≤
        d * ∑ i ∈ S, ‖U i (r,u)‖^2 * sourceRealAngularMoment (V i) r := by
    have hi : Integrable (fun w => d * ∑ i ∈ S, ‖U i (r,u)‖^2*‖V i (r,w)‖^2) sourceArcLength :=
      (integrable_finsetSum S (fun i hi => (hiV i hi).const_mul _)).const_mul d
    have he := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall (hb r u))
    simpa only [integral_const_mul,integral_finsetSum S (fun i hi => (hiV i hi).const_mul _),
      sourceRealAngularMoment] using he
  have hi : Integrable (fun u => d * ∑ i ∈ S, ‖U i (r,u)‖^2*sourceRealAngularMoment (V i) r) sourceArcLength :=
    (integrable_finsetSum S (fun i hi => (hiU i hi).mul_const _)).const_mul d
  have he := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall inner)
  simpa only [integral_const_mul,integral_finsetSum S (fun i hi => (hiU i hi).mul_const _),
    integral_mul_const,sourceRealAngularMoment] using he

theorem original_product_schur_integral {ι : Type*} (S : Finset ι)
    (U V : ι → ℝ × UnitCircle → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ x, ‖U i x‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ x, ‖V i x‖ ≤ D i)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) {d : ℝ} (hd : 0 ≤ d)
    (hb : ∀ r u w, ‖F (r,(u,w))‖ ≤ d * ∑ i ∈ S, ‖U i (r,u)‖^2*‖V i (r,w)‖^2)
    (p v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ‖((2:ℝ)^(2*(v-p))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) • F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength)‖ ≤
      d * ∑ i ∈ S, (sourceAngularH p v Ψ (U i) (V i)).toReal := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  have hzero : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  have hi (i : ι) (hi : i ∈ S) := product_moment_integrable (sourceAngularShellMeasure v Ψ)
    (U i) (V i) (hU i hi) (hV i hi) (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)
  have hh := norm_integral_le_of_norm_le
    ((integrable_finsetSum S hi).const_mul d)
    (Filter.Eventually.of_forall (circle_pair_schur_bound S U V hU hV C D hC hD hbU hbV F hd hb))
  have he (i : ι) (hi : i ∈ S) := (sourceAngularH_finite_integral p v Ψ
    (U i) (V i) (hU i hi) (hV i hi) (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)).2
  simp_rw [integral_smul]
  rw [← sourceAngularShellMeasure_integral v hΨ hpos hzero]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-p)))]
  calc
    _ ≤ (2:ℝ)^(2*(v-p)) * (∫ r, d * ∑ i ∈ S,
        sourceRealAngularMoment (U i) r * sourceRealAngularMoment (V i) r ∂sourceAngularShellMeasure v Ψ) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum S hi]
      simp_rw [Finset.sum_congr rfl he]
      rw [← Finset.mul_sum]
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductGraphIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem original_product_graph_integral_bound_oai
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a)
    {θ : ℝ} (hθ : 0 < θ) (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n (angularBinCount θ) A B)
    {d : ℝ} (hd : 0 ≤ d)
    (hdegree : ∀ j k s reverse row,
      ((activeProductMatrixNeighbors I (a+n) j k θ s reverse row).card : ℝ) ≤ d)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ B₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ B₂)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    let U := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform ρ (Q₁.descendant P).carrier M₁ β z.1 z.2
    let V := fun Q : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform ν (Q₂.descendant Q).carrier M₂ γ z.1 z.2
    ‖((2:ℝ)^(2*(v-(a+n)))) •
      ∑ e ∈ I, graphOriginalTerm ![ρ,ρ,ν,ν]
        (fun l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
        ![M₁,M₁,M₂,M₂] ![β,β,γ,γ] false e.2.2 0 θ v e.2.1.1 e.2.1.2 Ψ‖ ≤
      d * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (sourceAngularH (a+n) v Ψ (U row.1) (V row.2)).toReal := by
  classical
  let : ∀ l : Fin 4, IsFiniteMeasure (![ρ,ρ,ν,ν] l) := by
    intro l; fin_cases l <;> dsimp <;> infer_instance
  have hM : ∀ l : Fin 4, 0 < (![M₁,M₁,M₂,M₂] l) := by
    intro l; fin_cases l <;> first | exact hM₁ | exact hM₂
  have hb : ∀ l : Fin 4, Measurable (fun z : Plane × UnitCircle => (![β,β,γ,γ] l) z.1 z.2) := by
    intro l; fin_cases l <;> first | exact hβ | exact hγ
  have hbound : ∀ (l : Fin 4) x u, ‖(![β,β,γ,γ] l) x u‖ ≤ (![B₁,B₁,B₂,B₂] l) := by
    intro l; fin_cases l <;> first | exact hbβ | exact hbγ
  have hB4 : ∀ l : Fin 4, 0 ≤ (![B₁,B₁,B₂,B₂] l) := by
    intro l; fin_cases l <;> first | exact hB₁ | exact hB₂
  let H := graphSupportedProductIndices I θ
  let F := fun z : ℝ × (UnitCircle × UnitCircle) => ∑ e ∈ H,
    sourceGraphFourTransform ![ρ,ρ,ν,ν]
      (fun l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
      ![M₁,M₁,M₂,M₂] ![β,β,γ,γ]
      (graphProductWeight e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2) z.1 z.2.1 z.2.2
  let U := fun P : CellPath => fun z : ℝ × UnitCircle =>
    sourceAngularTransform ρ (Q₁.descendant P).carrier M₁ β z.1 z.2
  let V := fun Q : CellPath => fun z : ℝ × UnitCircle =>
    sourceAngularTransform ν (Q₂.descendant Q).carrier M₂ γ z.1 z.2
  have hpoint (r : ℝ) (u w : UnitCircle) : ‖F (r,(u,w))‖ ≤
      d * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, ‖U row.1 (r,u)‖^2*‖V row.2 (r,w)‖^2 :=
    product_graph_pointwise_bound Q₁ Q₂ ρ ν A B a n (angularBinCount θ) hA hB
      (angularBinCount_pos hθ) I hI θ d hdegree (fun P => U P (r,u)) (fun Q => V Q (r,w)) u w
  have hmain := original_product_schur_integral (sourceProductVertices Q₁ Q₂ ρ ν A B n)
    (fun row => U row.1) (fun row => V row.2)
    (fun row _ => measurable_sourceAngularTransform ρ (Q₁.descendant row.1).carrier M₁ β hβ)
    (fun row _ => measurable_sourceAngularTransform ν (Q₂.descendant row.2).carrier M₂ γ hγ)
    (fun row => B₁*(ρ (Q₁.descendant row.1).carrier).toReal/M₁)
    (fun row => B₂*(ν (Q₂.descendant row.2).carrier).toReal/M₂)
    (fun row _ => by positivity) (fun row _ => by positivity)
    (fun row _ z => sourceAngularTransform_norm_le ρ _ M₁ hM₁ β B₁ (fun x _ => hbβ x) z.1 z.2)
    (fun row _ z => sourceAngularTransform_norm_le ν _ M₂ hM₂ γ B₂ (fun x _ => hbγ x) z.1 z.2)
    F hd hpoint (a+n) v hΨ hpos hs hW hw
  have hsum := sourceGraphFourTransform_original_sum H ![ρ,ρ,ν,ν]
    (fun e l => (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1 l).carrier)
    ![M₁,M₁,M₂,M₂] hM ![β,β,γ,γ]
    (fun e => graphProductWeight e.2.2 (angularBinCount θ) e.2.1.1 e.2.1.2) hb
    (fun e => (graphProductWeight_continuous _ _ _ _).measurable)
    (fun e => graphProductWeight_norm_le _ _ _ _)
    ![B₁,B₁,B₂,B₂] hB4 hbound hΨ hs hW
    (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t) v
  dsimp only [F] at hmain
  rw [hsum] at hmain
  dsimp only
  rw [graphOriginalProductSum_supported]
  simpa only [Finset.smul_sum,graphOriginalTerm,graphSourceWeight,
    Bool.false_eq_true,↓reduceIte,H,U,V] using hmain

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.original_product_graph_integral_bound_oai := @OAI.PlanarFalconer.original_product_graph_integral_bound_oai
