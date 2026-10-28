-- Prove2me | solution 1 for OAI.PlanarFalconer.original_distance_graph_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:24:00.570404+00:00
-- url     : https://prove2.me/submissions/0baabcd6-a167-4e50-83e4-611cebe422ea

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ContDiff

theorem sourceConeCircle_norm_le (axis : ℝ) (dir : UnitCircle) :
    ‖sourceConeCircle axis dir‖ ≤ 1 := by
  simp only [sourceConeCircle, graphConeCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg graphConeBump.nonneg]
  exact graphConeBump.le_one

theorem sourceAngle_comp_on_period {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    sourceAngle (sourceUnitDirection θ) = θ := by
  rw [sourceAngle_sourceUnitDirection]
  exact_mod_cast Complex.arg_cos_add_sin_mul_I hθ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SmoothRotatedCone
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Filter
open scoped ContDiff Topology

theorem periodic_contDiff_of_principal {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi))
    (hf : ∀ θ ∈ Ioc (-Real.pi) Real.pi, ContDiffAt ℝ ∞ f θ) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hr : sourceAngle (sourceUnitDirection θ) ∈ Ioc (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have hh := hf _ hr
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [sourceAngle_sourceUnitDirection, he] at hh
  let c : ℝ := 2*Real.pi*(⌊(Real.pi-θ)/(2*Real.pi)⌋ : ℤ)
  have ht : ContDiffAt ℝ ∞ (fun t : ℝ => t+c) θ := contDiffAt_id.add contDiffAt_const
  have hc : ContDiffAt ℝ ∞ f (θ+c) := by simpa only [c, add_comm] using hh
  have hcomp := hc.comp θ ht
  have heq : (fun t => f (t+c)) = f := by
    funext t
    simpa only [c, mul_comm] using hp.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋ t
  simpa only [Function.comp_def, heq] using hcomp

theorem sourceConeCircle_angular_contDiff :
    ContDiff ℝ ∞ (fun θ => sourceConeCircle 0 (sourceUnitDirection θ)) := by
  let f : ℝ → ℂ := fun θ => sourceConeCircle 0 (sourceUnitDirection θ)
  have hp : Function.Periodic f (2*Real.pi) :=
    fun θ => congrArg (sourceConeCircle 0) (sourceUnitDirection_periodic θ)
  have hlocal {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) : f θ = graphConeCutoff θ := by
    simp only [f, sourceConeCircle, neg_zero, sourceCircleRotate_zero, sourceAngle_comp_on_period hθ]
  have hzero (θ : ℝ) (hc : Real.cos θ < 0) : f θ = 0 := by
    by_contra hn
    have hs : sourceAngle (sourceUnitDirection θ) ∈ Icc (-1/5 : ℝ) (1/5) := by
      apply graphConeCutoff_support
      apply subset_closure
      simpa only [Function.mem_support, f, sourceConeCircle, neg_zero, sourceCircleRotate_zero] using hn
    have hcos : 0 ≤ Real.cos (sourceAngle (sourceUnitDirection θ)) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by have := Real.one_le_pi_div_two; linarith [hs.1])
        (by have := Real.one_le_pi_div_two; linarith [hs.2])
    have he := periodic_sourceAngle (show Function.Periodic Real.cos (2*Real.pi) from Real.cos_periodic) θ
    rw [he] at hcos
    linarith
  apply periodic_contDiff_of_principal hp
  intro θ hθ
  by_cases hlt : θ < Real.pi
  · apply graphConeCutoff_contDiff.contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ.1, hlt⟩] with t ht
    exact hlocal ⟨ht.1, ht.2.le⟩
  · have hθπ : θ = Real.pi := le_antisymm hθ.2 (le_of_not_gt hlt)
    rw [hθπ]
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have hn : {t : ℝ | Real.cos t < 0} ∈ 𝓝 Real.pi :=
      (isOpen_lt Real.continuous_cos continuous_const).mem_nhds (by simp)
    filter_upwards [hn] with t ht
    exact hzero t ht

theorem sourceConeCircle_rotated_contDiff (axis : ℝ) :
    ContDiff ℝ ∞ (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) := by
  have he : (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) =
      fun θ => sourceConeCircle 0 (sourceUnitDirection (θ-axis)) := by
    funext θ
    simp only [sourceConeCircle, sourceCircleRotate_comp, neg_zero,
      sub_eq_add_neg, add_zero]
  rw [he]
  exact sourceConeCircle_angular_contDiff.comp (contDiff_id.sub contDiff_const)

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

theorem continuous_circle_of_direction {E : Type*} [TopologicalSpace E]
    (f : UnitCircle → E) (hf : Continuous (fun θ => f (sourceUnitDirection θ))) :
    Continuous f := by
  let A := Icc (-Real.pi) Real.pi
  let : CompactSpace A := isCompact_iff_compactSpace.mp (show IsCompact A from isCompact_Icc)
  let q : A → UnitCircle := fun θ => sourceUnitDirection θ
  have hq : Continuous q := continuous_sourceUnitDirection.comp continuous_subtype_val
  have hs : Function.Surjective q := by
    intro ω
    exact ⟨⟨sourceAngle ω, (Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩,
      sourceUnitDirection_sourceAngle ω⟩
  exact (hq.isClosedMap.isQuotientMap hq hs).continuous_iff.mpr
    (hf.comp continuous_subtype_val)

theorem sourceConeCircle_continuous (axis : ℝ) : Continuous (sourceConeCircle axis) :=
  continuous_circle_of_direction _ (sourceConeCircle_rotated_contDiff axis).continuous

theorem graphBinWeight_continuous (n j k : ℕ) : Continuous (graphBinWeight n j k) :=
  ((circleAngularBin_continuous n j).comp continuous_fst).mul
    ((circleAngularBin_continuous n k).comp continuous_snd)

theorem graphDistanceWeight_continuous (axis : ℝ) (n j k : ℕ) :
    Continuous (graphDistanceWeight axis n j k) := by
  exact ((Complex.continuous_ofReal.comp (graphBinWeight_continuous n j k)).mul
    ((sourceConeCircle_continuous axis).comp continuous_fst)).mul
      (Complex.continuous_conj.comp ((sourceConeCircle_continuous axis).comp continuous_snd))

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

theorem graphDistanceWeight_norm_le (axis : ℝ) (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphDistanceWeight axis n j k p‖ ≤ 1 := by
  have hb := graphBinWeight_bounds n j k p
  simp only [graphDistanceWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb.1, Complex.norm_conj]
  exact (mul_le_mul (mul_le_mul hb.2 (sourceConeCircle_norm_le axis p.1)
    (norm_nonneg _) zero_le_one) (sourceConeCircle_norm_le axis p.2)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphRotatedWeights
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphRotatedDistanceWeight_continuous (axis : ℝ) (n j k : ℕ) :
    Continuous (graphRotatedDistanceWeight axis n j k) :=
  (graphDistanceWeight_continuous 0 n j k).comp
    (((sourceCircleRotate_isometry (-axis)).continuous.comp continuous_fst).prodMk
      ((sourceCircleRotate_isometry (-axis)).continuous.comp continuous_snd))

theorem graphRotatedDistanceWeight_norm_le (axis : ℝ) (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphRotatedDistanceWeight axis n j k p‖ ≤ 1 := graphDistanceWeight_norm_le 0 n j k _

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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ParentGraphIndices
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

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

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_DistanceSupportedGraph
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphOriginalDistanceSum_supported (I : Finset GraphNonedgeIndex)
    (ρ : Fin 4 → Measure Plane) (Q : Fin 4 → DyadicSquare) (M : Fin 4 → ℝ)
    (β : Fin 4 → Plane → UnitCircle → ℂ) (θ axis v : ℝ) (Ψ : ℝ → ℝ) :
    (∑ e ∈ I, graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M β
      true e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ) =
    ∑ e ∈ graphSupportedDistanceIndices I θ axis,
      graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M β
        true e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hn
  apply graphOriginalTerm_zero_of_empty_weight_support
  intro hs
  exact hn (Finset.mem_filter.mpr ⟨he,hs⟩)

theorem activeDistanceMatrixNeighbors_eq_supported (I : Finset GraphNonedgeIndex)
    (p j b : ℕ) (θ axis : ℝ) (plus reverse : Bool) (row : CellPath × CellPath) :
    activeDistanceMatrixNeighbors I p j b θ axis plus reverse row =
      distanceMatrixNeighbors (graphSupportedDistanceIndices I θ axis) p j b plus reverse row := by
  classical
  ext col
  cases reverse <;> by_cases hs : (tsupport (graphSourceWeight true plus axis (angularBinCount θ) j b)).Nonempty <;>
    simp [activeDistanceMatrixNeighbors,distanceMatrixNeighbors,graphSupportedDistanceIndices,distanceMatrixIndex,hs]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DistanceMatrixSchur
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open scoped ComplexConjugate

theorem distance_matrix_schur_on (I : Finset GraphNonedgeIndex) (p j b : ℕ) (θ axis : ℝ)
    (plus : Bool) (A B : Finset (CellPath × CellPath))
    (hA : A ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hB : B ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (u v : CellPath × CellPath → ℝ) (d : ℝ)
    (hdegree : ∀ reverse row,
      ((activeDistanceMatrixNeighbors I p j b θ axis plus reverse row).card : ℝ) ≤ d) :
    let H := graphSupportedDistanceIndices I θ axis
    (∑ row ∈ A, ∑ col ∈ B, if distanceMatrixIndex row col j b plus ∈ H then u row*v col else 0) ≤
      d/2*((∑ row ∈ A, u row^2)+(∑ col ∈ B, v col^2)) := by
  classical
  dsimp only
  apply finset_bipartite_schur
  · intro row _
    apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hB))).trans
    simpa only [activeDistanceMatrixNeighbors_eq_supported,distanceMatrixNeighbors,Bool.false_eq_true,↓reduceIte]
      using hdegree false row
  · intro col _
    apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hA))).trans
    simpa only [activeDistanceMatrixNeighbors_eq_supported,distanceMatrixNeighbors,↓reduceIte]
      using hdegree true col

theorem distance_matrix_complex_bound_on (I : Finset GraphNonedgeIndex) (p j b : ℕ) (θ axis : ℝ)
    (plus : Bool) (A B : Finset (CellPath × CellPath))
    (hA : A ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hB : B ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (u v : CellPath × CellPath → ℂ) (weight : ℂ) (d : ℝ)
    (hdegree : ∀ reverse row,
      ((activeDistanceMatrixNeighbors I p j b θ axis plus reverse row).card : ℝ) ≤ d) :
    let H := graphSupportedDistanceIndices I θ axis
    ‖∑ row ∈ A, ∑ col ∈ B, if distanceMatrixIndex row col j b plus ∈ H
      then weight*(u row*conj (v col)) else 0‖ ≤
      ‖weight‖*(d/2*((∑ row ∈ A, ‖u row‖^2)+(∑ col ∈ B, ‖v col‖^2))) := by
  classical
  dsimp only
  have hh := distance_matrix_schur_on I p j b θ axis plus A B hA hB
    (fun row => ‖u row‖) (fun col => ‖v col‖) d hdegree
  calc
    _ ≤ ∑ row ∈ A, ∑ col ∈ B, ‖if distanceMatrixIndex row col j b plus ∈ graphSupportedDistanceIndices I θ axis
        then weight*(u row*conj (v col)) else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ = ‖weight‖*(∑ row ∈ A, ∑ col ∈ B,
        if distanceMatrixIndex row col j b plus ∈ graphSupportedDistanceIndices I θ axis
        then ‖u row‖*‖v col‖ else 0) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row _
      apply Finset.sum_congr rfl
      intro col _
      split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (norm_nonneg _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceOccupiedSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sourceParentGraphIndices_vertices (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (N n : ℕ) (sig t : ℝ) {e : GraphNonedgeIndex}
    (he : e ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B) :
    (e.1.1.1,e.1.2.1) ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n ∧
    (e.1.1.2,e.1.2.2) ∈ sourceProductVertices Q₂ Q₁ ν ρ B A n := by
  obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨heP,heQ,_⟩ := sourceParentBinLabels_spec (Finset.mem_product.mp hef).1
  obtain ⟨hfP,hfQ,_⟩ := sourceParentBinLabels_spec (Finset.mem_product.mp hef).2
  constructor
  · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,heP,rfl⟩,
      Finset.mem_image.mpr ⟨_,hfQ,rfl⟩⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨_,heQ,rfl⟩,
      Finset.mem_image.mpr ⟨_,hfP,rfl⟩⟩

theorem sourceParentGraphIndices_sign (X Y : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (N n : ℕ) (sig t : ℝ) {e : GraphNonedgeIndex}
    (he : e ∈ sourceParentGraphIndices N sig t X Y ρ ν n A B) : e.2.2 = true := by
  obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp he
  rfl

theorem sourceProductVertices_swap_sum (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (n : ℕ) {α : Type*} [AddCommMonoid α]
    (F : CellPath → CellPath → α) :
    (∑ col ∈ sourceProductVertices Q₂ Q₁ ν ρ B A n, F col.1 col.2) =
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, F row.2 row.1 := by
  simp only [sourceProductVertices,Finset.sum_product]
  exact Finset.sum_comm

theorem distance_matrix_sum_restrict {p : ℕ} (I : Finset GraphNonedgeIndex)
    (C D : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hD : D ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hvertices : ∀ e ∈ I, (e.1.1.1,e.1.2.1) ∈ C ∧ (e.1.1.2,e.1.2.2) ∈ D)
    (j b : ℕ) (plus : Bool) {α : Type*} [AddCommMonoid α] (F : GraphNonedgeIndex → α) :
    (∑ row ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
      ∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
        if distanceMatrixIndex row col j b plus ∈ I then F (distanceMatrixIndex row col j b plus) else 0) =
    ∑ row ∈ C, ∑ col ∈ D,
      if distanceMatrixIndex row col j b plus ∈ I then F (distanceMatrixIndex row col j b plus) else 0 := by
  classical
  have hcol (row : CellPath × CellPath) :
      (∑ col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p),
        if distanceMatrixIndex row col j b plus ∈ I then F (distanceMatrixIndex row col j b plus) else 0) =
      ∑ col ∈ D, if distanceMatrixIndex row col j b plus ∈ I then F (distanceMatrixIndex row col j b plus) else 0 := by
    symm
    apply Finset.sum_subset hD
    intro col _ hn
    have hi : distanceMatrixIndex row col j b plus ∉ I := fun hi => hn (hvertices _ hi).2
    simp [hi]
  simp_rw [hcol]
  symm
  apply Finset.sum_subset hC
  intro row _ hn
  apply Finset.sum_eq_zero
  intro col _
  have hi : distanceMatrixIndex row col j b plus ∉ I := fun hi => hn (hvertices _ hi).1
  simp [hi]

theorem source_distance_graph_sum_occupied (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (N a n : ℕ) (sig t : ℝ) (hA : A.length = a) (hB : B.length = a)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    {α : Type*} [AddCommMonoid α] (F : GraphNonedgeIndex → α) :
    (∑ e ∈ I, F e) =
    ∑ j ∈ Finset.range (angularBinCount (graphUncappedAngularScale N sig t)),
      ∑ b ∈ Finset.range (angularBinCount (graphUncappedAngularScale N sig t)),
        ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          ∑ col ∈ sourceProductVertices Q₂ Q₁ ν ρ B A n,
            if distanceMatrixIndex row col j b true ∈ I then F (distanceMatrixIndex row col j b true) else 0 := by
  classical
  rw [product_graph_sum_bins I (hI.trans (sourceParentGraphIndices_subset hA hB)) F]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  have hz (row col : CellPath × CellPath) : productMatrixIndex row col j b false ∉ I := by
    intro he
    have hs := sourceParentGraphIndices_sign _ _ _ _ _ _ _ _ _ _ (hI he)
    exact Bool.noConfusion hs
  simp only [Fintype.sum_bool,hz,↓reduceIte,Finset.sum_const_zero,add_zero]
  exact distance_matrix_sum_restrict I _ _
    (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB)
    (sourceProductVertices_subset Q₂ Q₁ ν ρ B A a n hB hA)
    (fun e he => sourceParentGraphIndices_vertices Q₁ Q₂ ρ ν A B N n sig t (hI he)) j b true F

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceWeightSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphDistanceWeight_norm_total {m : ℕ} (hm : 0 < m)
    (axis : ℝ) (p : UnitCircle × UnitCircle) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ‖graphDistanceWeight axis m j k p‖) =
      ‖sourceConeCircle axis p.1‖ * ‖sourceConeCircle axis p.2‖ := by
  simp only [graphDistanceWeight,norm_mul,Complex.norm_conj,Complex.norm_real,
    Real.norm_eq_abs,
    graphBinWeight,abs_of_nonneg (circleAngularBin_bounds _ _ _).1,← Finset.sum_mul,← Finset.mul_sum,circleAngularBin_partition hm,one_mul,mul_one]

theorem graphRotatedDistanceWeight_norm_total_le {m : ℕ} (hm : 0 < m)
    (axis : ℝ) (p : UnitCircle × UnitCircle) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ‖graphRotatedDistanceWeight axis m j k p‖) ≤ 1 := by
  rw [show (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ‖graphRotatedDistanceWeight axis m j k p‖) =
      ‖sourceConeCircle 0 (sourceCircleRotate (-axis) p.1)‖ *
      ‖sourceConeCircle 0 (sourceCircleRotate (-axis) p.2)‖ from graphDistanceWeight_norm_total hm 0 _]
  exact (mul_le_mul (sourceConeCircle_norm_le _ _) (sourceConeCircle_norm_le _ _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_DistanceGraphPointwise
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem distance_graph_pointwise_bound
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (A B : CellPath) (N a n : ℕ)
    (sig t : ℝ) (hA : A.length = a) (hB : B.length = a)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    {θ : ℝ} (hθ : 0 < θ) (hscale : θ = graphUncappedAngularScale N sig t)
    (axis d : ℝ) (hd : 0 ≤ d)
    (hdegree : ∀ j k s reverse row,
      ((activeDistanceMatrixNeighbors I (a+n) j k θ axis s reverse row).card : ℝ) ≤ d)
    (U V : CellPath → UnitCircle → ℂ) (u w : UnitCircle) :
    ‖∑ e ∈ graphSupportedDistanceIndices I θ axis,
      graphRotatedDistanceWeight axis (angularBinCount θ) e.2.1.1 e.2.1.2 (u,w) *
        (U e.1.1.1 u*conj (V e.1.1.2 u))*(V e.1.2.1 w*conj (U e.1.2.2 w))‖ ≤
      d/2 * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (‖U row.1 u‖^2*‖V row.2 w‖^2 + ‖V row.2 u‖^2*‖U row.1 w‖^2) := by
  classical
  let C := sourceProductVertices Q₁ Q₂ ρ ν A B n
  let D := sourceProductVertices Q₂ Q₁ ν ρ B A n
  let H := graphSupportedDistanceIndices I θ axis
  let F := fun e : GraphNonedgeIndex => graphRotatedDistanceWeight axis (angularBinCount θ) e.2.1.1 e.2.1.2 (u,w) *
    (U e.1.1.1 u*conj (V e.1.1.2 u))*(V e.1.2.1 w*conj (U e.1.2.2 w))
  let S := d/2 * ((∑ row ∈ C, ‖U row.1 u‖^2*‖V row.2 w‖^2) +
    (∑ col ∈ D, ‖V col.1 u‖^2*‖U col.2 w‖^2))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hh : H ⊆ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B :=
    (Finset.filter_subset _ _).trans hI
  have hmatrix (j b : ℕ) :
      ‖∑ row ∈ C, ∑ col ∈ D, if distanceMatrixIndex row col j b true ∈ H
        then F (distanceMatrixIndex row col j b true) else 0‖ ≤
        ‖graphRotatedDistanceWeight axis (angularBinCount θ) j b (u,w)‖ * S := by
    have he := distance_matrix_complex_bound_on I (a+n) j b θ axis true C D
      (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB)
      (sourceProductVertices_subset Q₂ Q₁ ν ρ B A a n hB hA)
      (fun row => U row.1 u*V row.2 w) (fun col => V col.1 u*U col.2 w)
      (graphRotatedDistanceWeight axis (angularBinCount θ) j b (u,w)) d (hdegree j b true)
    have hf (row col : CellPath × CellPath) : F (distanceMatrixIndex row col j b true) =
        graphRotatedDistanceWeight axis (angularBinCount θ) j b (u,w) *
          ((U row.1 u*V row.2 w)*conj (V col.1 u*U col.2 w)) := by
      dsimp [F,distanceMatrixIndex]
      rw [map_mul]
      ring
    simpa only [hf,norm_mul,mul_pow,H,S] using he
  change ‖∑ e ∈ H, F e‖ ≤ _
  rw [source_distance_graph_sum_occupied Q₁ Q₂ ρ ν A B N a n sig t hA hB H hh F,← hscale]
  calc
    _ ≤ ∑ j ∈ Finset.range (angularBinCount θ), ∑ b ∈ Finset.range (angularBinCount θ),
        ‖∑ row ∈ C, ∑ col ∈ D, if distanceMatrixIndex row col j b true ∈ H
          then F (distanceMatrixIndex row col j b true) else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ j ∈ Finset.range (angularBinCount θ), ∑ b ∈ Finset.range (angularBinCount θ),
        ‖graphRotatedDistanceWeight axis (angularBinCount θ) j b (u,w)‖*S :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun b _ => hmatrix j b))
    _ ≤ S := by
      simp only [← Finset.sum_mul]
      exact (mul_le_mul_of_nonneg_right
        (graphRotatedDistanceWeight_norm_total_le (angularBinCount_pos hθ) axis (u,w)) hS).trans_eq (one_mul S)
    _ = _ := by
      dsimp [S,C,D]
      rw [sourceProductVertices_swap_sum Q₁ Q₂ ρ ν A B n
        (fun c p => ‖V c u‖^2*‖U p w‖^2),Finset.sum_add_distrib]

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
-- module Solutions.OAIQ038_FA.Falconer_Measures_DistanceSchurIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem original_distance_schur_integral {ι : Type*} (S : Finset ι)
    (U V : ι → ℝ × UnitCircle → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ x, ‖U i x‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ x, ‖V i x‖ ≤ D i)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) {d : ℝ} (hd : 0 ≤ d)
    (hb : ∀ r u w, ‖F (r,(u,w))‖ ≤ d/2 * (∑ i ∈ S, (‖U i (r,u)‖^2*‖V i (r,w)‖^2 + ‖V i (r,u)‖^2*‖U i (r,w)‖^2)))
    (p v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ‖((2:ℝ)^(2*(v-p))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) • F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength)‖ ≤
      d * ∑ i ∈ S, (sourceAngularH p v Ψ (U i) (V i)).toReal := by
  classical
  let E := S ×ˢ (Finset.univ : Finset Bool)
  let U' := fun e : ι × Bool => if e.2 then U e.1 else V e.1
  let V' := fun e : ι × Bool => if e.2 then V e.1 else U e.1
  let C' := fun e : ι × Bool => if e.2 then C e.1 else D e.1
  let D' := fun e : ι × Bool => if e.2 then D e.1 else C e.1
  have hU' : ∀ e ∈ E, Measurable (U' e) := by
    intro ⟨i,b⟩ he
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hU i hi | exact hV i hi
  have hV' : ∀ e ∈ E, Measurable (V' e) := by
    intro ⟨i,b⟩ he
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hU i hi | exact hV i hi
  have hC' : ∀ e ∈ E, 0 ≤ C' e := by
    intro ⟨i,b⟩ he
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hC i hi | exact hD i hi
  have hD' : ∀ e ∈ E, 0 ≤ D' e := by
    intro ⟨i,b⟩ he
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hC i hi | exact hD i hi
  have hbU' : ∀ e ∈ E, ∀ x, ‖U' e x‖ ≤ C' e := by
    intro ⟨i,b⟩ he x
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hbU i hi x | exact hbV i hi x
  have hbV' : ∀ e ∈ E, ∀ x, ‖V' e x‖ ≤ D' e := by
    intro ⟨i,b⟩ he x
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hbU i hi x | exact hbV i hi x
  have hb' : ∀ r u w, ‖F (r,(u,w))‖ ≤
      d/2 * ∑ e ∈ E, ‖U' e (r,u)‖^2*‖V' e (r,w)‖^2 := by
    intro r u w
    simpa [E,U',V',Finset.sum_product,Fintype.sum_bool,add_comm] using hb r u w
  have hh := original_product_schur_integral E U' V' hU' hV' C' D' hC' hD' hbU' hbV'
    F (div_nonneg hd (by norm_num)) hb' p v hΨ hpos hs hW hw
  have hsym (i : ι) : sourceAngularH p v Ψ (V i) (U i) = sourceAngularH p v Ψ (U i) (V i) := by
    unfold sourceAngularH
    simp_rw [mul_comm (sourceAngularMoment (V i) _) (sourceAngularMoment (U i) _)]
  simp [E,U',V',Finset.sum_product,hsym,← two_mul,← Finset.mul_sum] at hh
  have hcanc (x : ℝ) : d/2*(2*x) = d*x := by ring
  rw [hcanc] at hh
  simpa using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_DistanceGraphIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem original_distance_graph_integral_bound_oai
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (N a n : ℕ) (sig t : ℝ) (hA : A.length = a) (hB : B.length = a)
    {θ : ℝ} (hθ : 0 < θ) (hscale : θ = graphUncappedAngularScale N sig t) (axis : ℝ) (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    {d : ℝ} (hd : 0 ≤ d)
    (hdegree : ∀ j k s reverse row,
      ((activeDistanceMatrixNeighbors I (a+n) j k θ axis s reverse row).card : ℝ) ≤ d)
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
      ∑ e ∈ I, graphOriginalTerm ![ρ,ν,ν,ρ]
        (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1 l).carrier)
        ![M₁,M₂,M₂,M₁] ![β,γ,γ,β] true e.2.2 axis θ v e.2.1.1 e.2.1.2 Ψ‖ ≤
      d * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (sourceAngularH (a+n) v Ψ (U row.1) (V row.2)).toReal := by
  classical
  let : ∀ l : Fin 4, IsFiniteMeasure (![ρ,ν,ν,ρ] l) := by
    intro l; fin_cases l <;> dsimp <;> infer_instance
  have hM : ∀ l : Fin 4, 0 < (![M₁,M₂,M₂,M₁] l) := by
    intro l; fin_cases l <;> first | exact hM₁ | exact hM₂
  have hb : ∀ l : Fin 4, Measurable (fun z : Plane × UnitCircle => (![β,γ,γ,β] l) z.1 z.2) := by
    intro l; fin_cases l <;> first | exact hβ | exact hγ
  have hbound : ∀ (l : Fin 4) x u, ‖(![β,γ,γ,β] l) x u‖ ≤ (![B₁,B₂,B₂,B₁] l) := by
    intro l; fin_cases l <;> first | exact hbβ | exact hbγ
  have hB4 : ∀ l : Fin 4, 0 ≤ (![B₁,B₂,B₂,B₁] l) := by
    intro l; fin_cases l <;> first | exact hB₁ | exact hB₂
  let H := graphSupportedDistanceIndices I θ axis
  let F := fun z : ℝ × (UnitCircle × UnitCircle) => ∑ e ∈ H,
    sourceGraphFourTransform ![ρ,ν,ν,ρ]
      (fun l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1 l).carrier)
      ![M₁,M₂,M₂,M₁] ![β,γ,γ,β]
      (graphRotatedDistanceWeight axis (angularBinCount θ) e.2.1.1 e.2.1.2) z.1 z.2.1 z.2.2
  let U := fun P : CellPath => fun z : ℝ × UnitCircle =>
    sourceAngularTransform ρ (Q₁.descendant P).carrier M₁ β z.1 z.2
  let V := fun Q : CellPath => fun z : ℝ × UnitCircle =>
    sourceAngularTransform ν (Q₂.descendant Q).carrier M₂ γ z.1 z.2
  have hpoint (r : ℝ) (u w : UnitCircle) : ‖F (r,(u,w))‖ ≤
      d/2 * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (‖U row.1 (r,u)‖^2*‖V row.2 (r,w)‖^2 + ‖V row.2 (r,u)‖^2*‖U row.1 (r,w)‖^2) :=
    distance_graph_pointwise_bound Q₁ Q₂ ρ ν A B N a n sig t hA hB
      I hI hθ hscale axis d hd hdegree (fun P u => U P (r,u)) (fun Q w => V Q (r,w)) u w
  have hmain := original_distance_schur_integral (sourceProductVertices Q₁ Q₂ ρ ν A B n)
    (fun row => U row.1) (fun row => V row.2)
    (fun row _ => measurable_sourceAngularTransform ρ (Q₁.descendant row.1).carrier M₁ β hβ)
    (fun row _ => measurable_sourceAngularTransform ν (Q₂.descendant row.2).carrier M₂ γ hγ)
    (fun row => B₁*(ρ (Q₁.descendant row.1).carrier).toReal/M₁)
    (fun row => B₂*(ν (Q₂.descendant row.2).carrier).toReal/M₂)
    (fun row _ => by positivity) (fun row _ => by positivity)
    (fun row _ z => sourceAngularTransform_norm_le ρ _ M₁ hM₁ β B₁ (fun x _ => hbβ x) z.1 z.2)
    (fun row _ z => sourceAngularTransform_norm_le ν _ M₂ hM₂ γ B₂ (fun x _ => hbγ x) z.1 z.2)
    F hd hpoint (a+n) v hΨ hpos hs hW hw
  have hsum := sourceGraphFourTransform_original_sum H ![ρ,ν,ν,ρ]
    (fun e l => (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1 l).carrier)
    ![M₁,M₂,M₂,M₁] hM ![β,γ,γ,β]
    (fun e => graphRotatedDistanceWeight axis (angularBinCount θ) e.2.1.1 e.2.1.2) hb
    (fun e => (graphRotatedDistanceWeight_continuous _ _ _ _).measurable)
    (fun e => graphRotatedDistanceWeight_norm_le _ _ _ _)
    ![B₁,B₂,B₂,B₁] hB4 hbound hΨ hs hW
    (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t) v
  dsimp only [F] at hmain
  rw [hsum] at hmain
  dsimp only
  rw [graphOriginalDistanceSum_supported]
  simpa only [Finset.smul_sum,graphOriginalTerm,graphSourceWeight,
    ↓reduceIte,H,U,V] using hmain

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.original_distance_graph_integral_bound_oai := @OAI.PlanarFalconer.original_distance_graph_integral_bound_oai
