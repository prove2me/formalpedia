-- Prove2me | solution 1 for OAI.SubsphereRegression.continuation_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:24:27.039105+00:00
-- url     : https://prove2.me/submissions/affba40d-2cc7-4880-a0fe-930ceb6c02b0

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Streaming.lean:L137-L190
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.continuation_mass_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Theorems.Thm_OAI_SubsphereRegression_continuation_unroll
import Theorems.Thm_OAI_SubsphereRegression_localized_routing_bound
import Theorems.Thm_OAI_SubsphereRegression_measurable_streamRoute

-- ---- from OAI.Probability.Subsphere.Regression.Blocks ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
namespace Learner
end Learner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma projectionLaw_withDensity_apply (μ : Measure E) [SFinite μ] {h : E → ℝ≥0∞}
    (hh : Measurable h) [SFinite (μ.withDensity h)] (m : ℕ)
    {S : Set ((Fin m → E) × (Fin m → ℝ))} (hS : MeasurableSet S) :
    projectionLaw (μ.withDensity h) m S =
      ∫⁻ s, h s * (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (A, fun j => ⟪s,A j⟫)
        ∂Measure.pi (fun _ : Fin m => stdGaussian E)) ∂μ := by
  have hobs : Measurable (fun x : (Fin m → E) × E => (x.1, fun j => ⟪x.2,x.1 j⟫)) := by fun_prop
  have hi : Measurable (fun x : (Fin m → E) × E => S.indicator (fun _ => (1 : ℝ≥0∞))
      (x.1, fun j => ⟪x.2,x.1 j⟫)) :=
    ((measurable_const : Measurable (fun _ => (1 : ℝ≥0∞))).indicator hS).comp hobs
  rw [projectionLaw, Measure.map_apply hobs hS]
  rw [← one_mul (((Measure.pi (fun _ : Fin m => stdGaussian E)).prod (μ.withDensity h)) _),
    ← lintegral_indicator_const (hobs hS) 1]
  change (∫⁻ x : (Fin m → E) × E, S.indicator (fun _ => (1 : ℝ≥0∞))
    (x.1, fun j => ⟪x.2,x.1 j⟫) ∂(Measure.pi (fun _ : Fin m => stdGaussian E)).prod (μ.withDensity h)) = _
  rw [lintegral_prod_symm _ hi.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul μ hh hi.lintegral_prod_left]
  rfl

lemma blockValue_mass_identity (μ : Measure E) [IsFiniteMeasure μ]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {m : ℕ} {h : J → E → ℝ≥0∞} (hh : ∀ j, Measurable (h j))
    (hh1 : ∀ j s, h j s ≤ 1)
    {φ : ((Fin m → E) × (Fin m → ℝ)) → J} (hφ : Measurable φ)
    {S : Set E} (hS : MeasurableSet S) :
    (μ.withDensity (blockValue h φ)) S =
      ∑ j, projectionLaw ((μ.withDensity (h j)).restrict S) m {x | φ x = j} := by
  classical
  let g (j : J) (s : E) (A : Fin m → E) : ℝ≥0∞ :=
    if φ (A, fun k => ⟪s,A k⟫) = j then h j s else 0
  have hg (j : J) : Measurable (Function.uncurry (g j)) := by
    exact Measurable.ite (measurableSet_eq_fun (hφ.comp (by fun_prop)) measurable_const)
      ((hh j).comp measurable_fst) measurable_const
  have hselect (s : E) (A : Fin m → E) : h (φ (A, fun k => ⟪s,A k⟫)) s = ∑ j, g j s A := by
    simp [g]
  have he (j : J) : projectionLaw ((μ.withDensity (h j)).restrict S) m {x | φ x = j} =
      ∫⁻ s in S, ∫⁻ A, g j s A ∂Measure.pi (fun _ : Fin m => stdGaussian E) ∂μ := by
    rw [restrict_withDensity hS]
    let : IsFiniteMeasure ((μ.restrict S).withDensity (h j)) :=
      isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 j)).trans_lt (by simp)))
    rw [projectionLaw_withDensity_apply _ (hh j) _ (measurableSet_eq_fun hφ measurable_const)]
    apply lintegral_congr
    intro s
    rw [← lintegral_const_mul' _ _ (ne_of_lt ((hh1 j s).trans_lt (by simp)))]
    apply lintegral_congr
    intro A
    by_cases hx : φ (A, fun k => ⟪s,A k⟫) = j <;> simp [g, hx]
  rw [withDensity_apply _ hS]
  calc
    _ = ∫⁻ s in S, ∑ j, ∫⁻ A, g j s A ∂Measure.pi (fun _ : Fin m => stdGaussian E) ∂μ := by
      apply lintegral_congr
      intro s
      unfold blockValue
      simp_rw [hselect]
      exact lintegral_finsetSum _ (fun j _ => (hg j).comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      rw [lintegral_finsetSum _ (fun j _ => (hg j).lintegral_prod_right)]
      simp_rw [he]

lemma blockValue_mass_bound (μ : Measure E) [IsFiniteMeasure μ]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {a m n : ℕ} {C : ℝ≥0∞} {h : J → E → ℝ≥0∞}
    (hh : ∀ j, Measurable (h j)) (hh1 : ∀ j s, h j s ≤ 1)
    (hlocal : ∀ j, PolynomialMass (μ.withDensity (h j)) a C)
    (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    {φ : ((Fin m → E) × (Fin m → ℝ)) → J} (hφ : Measurable φ) :
    PolynomialMass (μ.withDensity (blockValue h φ)) a
      ((32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) * C) := by
  let (j : J) : IsFiniteMeasure (μ.withDensity (h j)) :=
    isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 j)).trans_lt (by simp)))
  intro z r hr
  rw [blockValue_mass_identity μ hh hh1 hφ Metric.isClosed_closedBall.measurableSet]
  exact localized_routing_bound (fun j => μ.withDensity (h j)) hlocal hC hCt hd ha hm hn hmargin φ hφ z hr

end SubsphereRegression

end

end OAI

-- ---- from OAI.Probability.Subsphere.Regression.Streaming ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma measurable_select {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {h : J → X → Y} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) :=
  (measurable_from_prod_countable_right (f := fun p : J × X => h p.1 p.2) hh).comp (hφ.prodMk measurable_id)

lemma measurable_continuation {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j)) (n k : ℕ) (j : J) :
    Measurable (continuation δ w n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    exact measurable_select (fun a => (ih (n+1) a).comp measurable_snd)
      ((hδ (n+1) j).comp (by fun_prop))

omit [BorelSpace E] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma continuation_le_one {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : J) (s : E) :
    continuation δ w n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih =>
    refine (lintegral_mono (fun x => ih _ _)).trans ?_
    rw [lintegral_const, one_mul]
    unfold stdGaussian
    exact prob_le_one

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamFactor_ne_top (q : ℕ) : streamFactor (E := E) (J := J) q ≠ ∞ := by
  exact ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma one_le_streamFactor [Nonempty J] {q : ℕ} (hq : 0 < q) :
    1 ≤ streamFactor (E := E) (J := J) q := by
  apply one_le_mul (one_le_pow₀ (by norm_num))
  exact ENNReal.one_le_rpow (by exact_mod_cast Fintype.card_pos (α := J)) (by positivity)

lemma continuation_mass_bound [Nonempty J] (μ : Measure E) [IsFiniteMeasure μ]
    {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (μ.withDensity (w n j)) a C)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    PolynomialMass (μ.withDensity (continuation δ w n k j)) a
      (C * streamFactor (E := E) (J := J) q ^ (k/q+1)) := by
  have hden : ((q-1 : ℕ) : ℝ)+1 = (q : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    ring
  have hq0 : 0 < q := by omega
  have hK1 := one_le_streamFactor (E := E) (J := J) hq0
  have hK0 : streamFactor (E := E) (J := J) q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  have hKt := streamFactor_ne_top (E := E) (J := J) q
  induction k using Nat.strong_induction_on generalizing n j with
  | h k ih =>
    by_cases hk : q ≤ k
    · have hki : k-q < k := by omega
      have hC1 : C * streamFactor (E := E) (J := J) q ^ ((k-q)/q+1) ≠ 0 :=
        mul_ne_zero hC (pow_ne_zero _ hK0)
      have hC1t : C * streamFactor (E := E) (J := J) q ^ ((k-q)/q+1) ≠ ∞ :=
        ENNReal.mul_ne_top hCt (ENNReal.pow_ne_top hKt)
      have hb := blockValue_mass_bound μ
        (fun b => measurable_continuation hδ hw (n+q) (k-q) b)
        (fun b s => continuation_le_one hw1 (n+q) (k-q) b s)
        (fun b => ih (k-q) hki (n+q) b) hC1 hC1t hd ha
        (by omega : q ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+q ≤ a) (measurable_streamRoute hδ n q j)
      have he : continuation δ w n k j =
          blockValue (fun b => continuation δ w (n+q) (k-q) b) (streamRoute δ n q j) := by
        funext s
        simpa [Nat.add_sub_of_le hk] using continuation_unroll hδ n q (k-q) j s
      rw [he]
      have hdiv : k/q = (k-q)/q+1 := by
        conv_lhs => rw [← Nat.add_sub_of_le hk]
        exact Nat.add_div_left _ hq0
      convert hb using 1
      rw [hden, ← streamFactor, hdiv, pow_succ]
      ring
    · have hkm : k ≤ q := by omega
      have hb := blockValue_mass_bound μ
        (fun b => hw (n+k) b) (fun b s => hw1 (n+k) b s) (hlocal (n+k)) hC hCt hd ha
        (by omega : k ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+k ≤ a) (measurable_streamRoute hδ n k j)
      have he : continuation δ w n k j = blockValue (w (n+k)) (streamRoute δ n k j) := by
        funext s
        simpa [continuation] using continuation_unroll hδ n k 0 j s
      rw [he]
      convert hb using 1
      rw [hden, ← streamFactor, Nat.div_eq_of_lt (by omega : k < q)]
      simp [mul_comm]

end StreamAux

namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

end Learner

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

end StreamCaps

section ObservationAC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ObservationAC

end SubsphereRegression
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open InnerProductSpace
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.SubsphereRegression.continuation_mass_bound := @_root_.OAI.SubsphereRegression.continuation_mass_bound
