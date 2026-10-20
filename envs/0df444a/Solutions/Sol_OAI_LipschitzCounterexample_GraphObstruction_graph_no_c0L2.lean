-- Prove2me | solution 1 for OAI.LipschitzCounterexample.GraphObstruction.graph_no_c0L2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:02:36.832488+00:00
-- url     : https://prove2.me/submissions/989961d6-297d-402e-98e0-fbc60c2b1906

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/GraphObstruction.lean:L273-L332
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.GraphObstruction.graph_no_c0L2. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Theorems.Thm_OAI_LipschitzCounterexample_GraphObstruction_no_lower_of_coordinate_null
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_wsc_sumL1

-- ---- from OAI.Analysis.LipschitzEquivalence.Schur ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem WeakNull.map {u : ℕ → E} (hu : WeakNull u) (T : E →L[ℝ] F) :
    WeakNull (fun n => T (u n)) := fun f => hu (f.comp T)

end WeakSequences

end LipschitzCounterexample
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.WeakSums ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uG

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem WeakCauchy.map {u : ℕ → E} (hu : WeakCauchy u) (T : E →L[ℝ] F) :
    WeakCauchy (fun n => T (u n)) := fun f => hu (f.comp T)

variable {G : ℕ → Type uG} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]

end WeakSequences

namespace WeakSequences
open Filter Topology
open scoped NNReal ENNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weakLimit_mem {s : Set E} (hs : Convex ℝ s) (hc : IsClosed s)
    {u : ℕ → E} (hu : ∀ n, u n ∈ s) {x : E}
    (hx : ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) : x ∈ s := by
  by_contra hn
  obtain ⟨f, c, hf, hfx⟩ := geometric_hahn_banach_closed_point hs hc hn
  have hh : f x ≤ c := le_of_tendsto (hx f) (Eventually.of_forall (fun n => (hf _ (hu n)).le))
  exact hfx.not_ge hh

theorem wsc_submodule (hE : WeakSequentiallyComplete E) (p : Submodule ℝ E)
    (hp : IsClosed (p : Set E)) : WeakSequentiallyComplete p := by
  intro u hu
  obtain ⟨x, hx⟩ := hE (fun n => (u n : E)) (hu.map p.subtypeL)
  have hxp : x ∈ p := weakLimit_mem p.convex hp (fun n => (u n).property) hx
  refine ⟨⟨x, hxp⟩, fun f => ?_⟩
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq p f
  simpa only [← hg] using hx g

theorem wsc_equiv (e : E ≃L[ℝ] F) (hF : WeakSequentiallyComplete F) :
    WeakSequentiallyComplete E := by
  intro u hu
  obtain ⟨y, hy⟩ := hF (fun n => e (u n)) (hu.map e.toContinuousLinearMap)
  refine ⟨e.symm y, fun f => ?_⟩
  simpa using hy (f.comp e.symm.toContinuousLinearMap)

open NullSequences

theorem summable_c0_dual (f : ScalarC0 →L[ℝ] ℝ) :
    Summable (fun i => |f (single i 1)|) := by
  classical
  apply summable_of_sum_le (fun _ => abs_nonneg _) (fun s => ?_) (c := ‖f‖)
  let w : ScalarC0 := ∑ i ∈ s, Real.sign (f (single i 1)) • single i 1
  have hw : ‖w‖ ≤ 1 := by
    apply (norm_le zero_le_one).2
    intro i
    change ‖(∑ j ∈ s, Real.sign (f (single j (1 : ℝ))) • single j (1 : ℝ)) i‖ ≤ 1
    rw [NullSequences.sum_apply]
    by_cases hi : i ∈ s
    · simp only [ZeroAtInftyContinuousMap.smul_apply, single_apply]
      rw [Finset.sum_eq_single i]
      · simp only [ite_true, smul_eq_mul, mul_one]
        rcases Real.sign_apply_eq (f (single i 1)) with h | h | h <;> rw [h] <;> norm_num
      · intro j hj hji
        simp [Ne.symm hji]
      · exact fun h => (h hi).elim
    · have hz : ∀ j ∈ s, (Real.sign (f (single j (1 : ℝ))) • single j (1 : ℝ)) i = 0 := by
        intro j hj
        have hij : i ≠ j := fun h => hi (h ▸ hj)
        simp [hij]
      simp only [Finset.sum_eq_zero hz, norm_zero, zero_le_one]
  have hf : f w = ∑ i ∈ s, |f (single i 1)| := by
    simp only [w, map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rcases lt_trichotomy (f (single i 1)) 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · simp [h]
    · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]
  rw [← hf]
  exact (le_abs_self _).trans ((f.le_opNorm w).trans (mul_le_of_le_one_right (norm_nonneg _) hw))

theorem initialOnes_weakCauchy : WeakCauchy initialOnes := by
  intro f
  have hs : Summable (fun i => f (single i 1)) := (summable_c0_dual f).of_abs
  have ht := hs.hasSum.tendsto_sum_nat
  exact (show Tendsto (fun n => f (initialOnes n)) atTop (𝓝 (∑' i, f (single i 1))) from by
    simpa [initialOnes] using ht).cauchySeq

theorem not_wsc_c0 : ¬ WeakSequentiallyComplete ScalarC0 := by
  intro h
  obtain ⟨x, hx⟩ := h initialOnes initialOnes_weakCauchy
  have hones : ∀ i, x i = 1 := by
    intro i
    have hlim : Tendsto (fun n => evalCLM (H := ℝ) i (initialOnes n)) atTop (𝓝 (1 : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop i] with n hn
      change 1 = initialOnes n i
      simp [hn]
    exact tendsto_nhds_unique (hx (evalCLM i)) hlim
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds
    (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) by
      have ht := tendsto_zero x
      have he : (fun n => x n) = (fun _ : ℕ => (1 : ℝ)) := funext hones
      simpa only [he] using ht)
  exact one_ne_zero this

theorem no_c0_of_wsc [CompleteSpace E] (hE : WeakSequentiallyComplete E) (T : ScalarC0 →L[ℝ] E)
    (a : ℝ) (ha : 0 < a) (hT : ∀ x, a * ‖x‖ ≤ ‖T x‖) : False := by
  let K : ℝ≥0 := ⟨a⁻¹, inv_nonneg.mpr ha.le⟩
  have hanti : AntilipschitzWith K T := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    simp only [dist_eq_norm, ← map_sub]
    change ‖x - y‖ ≤ a⁻¹ * ‖T (x-y)‖
    exact (le_inv_mul_iff₀ ha).2 (hT (x-y))
  have hc : IsClosed (Set.range T) := hanti.isClosed_range T.uniformContinuous
  have hw : WeakSequentiallyComplete T.range := wsc_submodule hE T.range hc
  exact not_wsc_c0 (wsc_equiv (T.equivRange hanti.injective hc) hw)

end WeakSequences

end LipschitzCounterexample
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.GraphObstruction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uH uA uB

noncomputable section
namespace LipschitzCounterexample

namespace GraphObstruction
open Filter Topology
open WeakSequences
open scoped ENNReal NNReal
variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem unitVector_weakNull : WeakNull unitVector := by
  intro f
  let x := (InnerProductSpace.toDual ℝ RealL2).symm f
  have hx (i : ℕ) : f (unitVector i) = x i := by
    rw [← InnerProductSpace.toDual_symm_apply]
    change inner ℝ x (lp.single 2 i (1 : ℝ)) = x i
    simp [lp.inner_single_right]
  simp_rw [hx]
  have hs : Summable (fun i => ‖x i‖ ^ 2) := by
    simpa using (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x).summable
  have ht := hs.tendsto_atTop_zero
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht (ε^2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [dist_zero_right, Real.norm_of_nonneg (sq_nonneg _)] at h
  rw [dist_zero_right]
  nlinarith [norm_nonneg (x n)]

open NullSequences

variable {A : Type uA} {B : Type uB} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem exists_small_unit (T : A →L[ℝ] B) (ε : ℝ)
    (hT : ¬ ∀ x, ε * ‖x‖ ≤ ‖T x‖) : ∃ x, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  push Not at hT
  obtain ⟨x, hx⟩ := hT
  have hn : 0 < ‖x‖ := norm_pos_iff.2 (by intro h; simp [h] at hx)
  refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  · rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    apply (inv_mul_lt_iff₀ hn).2
    nlinarith

theorem exists_small_unit_of_coordinate_null (T : RealL2 →L[ℝ] C0 (H := H))
    (hcoord : ∀ i, Tendsto (fun k => T (unitVector k) i) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) : ∃ x, ‖x‖ = 1 ∧ ‖T x‖ < ε :=
  exists_small_unit T ε (no_lower_of_coordinate_null T hcoord ε hε)

theorem diagonal_single (t : ℕ → RealL2) (ht : ∀ n, ‖t n‖ = 1) (n : ℕ) (r : ℝ) :
    diagonal t ht (NullSequences.single n r) = r • c0singleLI n (t n) := by
  apply ZeroAtInftyContinuousMap.ext
  intro i
  change (if i = n then r else 0) • t i = r • (if i = n then t n else 0)
  by_cases h : i = n <;> simp [h]

variable [CompleteSpace A] [CompleteSpace H]

omit [CompleteSpace A] [CompleteSpace H] in
theorem graph_norm (Q : A →L[ℝ] H) (s : WeightedGraph.Space Q) :
    ‖s‖ = max ‖first Q s‖ ‖WeightedGraph.output Q s‖ := rfl

omit [CompleteSpace H] in

theorem graph_no_c0L2 (Q : A →L[ℝ] H) (hA : WeakSequentiallyComplete A)
    (hQ : CompletelyContinuous Q) (S : C0 (H := RealL2) →L[ℝ] WeightedGraph.Space Q)
    (b : ℝ) (hb : 0 < b) (hS : ∀ x, b * ‖x‖ ≤ ‖S x‖) : False := by
  classical
  let J := WeightedGraph.output Q
  let T (n : ℕ) : RealL2 →L[ℝ] C0 (H := H) :=
    J.comp (S.comp (c0singleLI n).toContinuousLinearMap)
  have hcoord (n i : ℕ) : Tendsto (fun k => T n (unitVector k) i) atTop (𝓝 0) := by
    have hw := (unitVector_weakNull.map (c0singleLI n).toContinuousLinearMap).map S
    have h := hQ _ (hw.map (WeightedGraph.coordCLM Q i))
    change Tendsto (fun k => Q (WeightedGraph.coord Q (S (c0singleLI n (unitVector k))) i))
      atTop (𝓝 0) at h
    simpa only [WeightedGraph.map_coord, T, J, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap] using h
  have hchoose (n : ℕ) : ∃ t : RealL2, ‖t‖ = 1 ∧ ‖T n t‖ < (b/2) * WeightedGraph.weight n :=
    exists_small_unit_of_coordinate_null (T n) (hcoord n) _ (mul_pos (half_pos hb) (WeightedGraph.weight_pos n))
  choose t ht hsmall using hchoose
  let R := (diagonal t ht).toContinuousLinearMap
  let L : ScalarC0 →L[ℝ] C0 (H := H) := J.comp (S.comp R)
  have hsingle (n : ℕ) (r : ℝ) : L (NullSequences.single n r) = r • T n (t n) := by
    change J (S (diagonal t ht (NullSequences.single n r))) = _
    rw [diagonal_single, map_smul, map_smul]
    rfl
  have hL (a : ScalarC0) : ‖L a‖ ≤ (b/2) * ‖a‖ := by
    have htrunc (N : ℕ) : ‖L (NullSequences.trunc N a)‖ ≤ (b/2) * ‖a‖ := by
      rw [NullSequences.trunc, map_sum]
      apply (norm_sum_le _ _).trans
      calc
        ∑ n ∈ Finset.range N, ‖L (NullSequences.single n (a n))‖ ≤
            ∑ n ∈ Finset.range N, ((b/2)*‖a‖) * WeightedGraph.weight n := by
          apply Finset.sum_le_sum
          intro n hn
          rw [hsingle, norm_smul]
          calc
            ‖a n‖ * ‖T n (t n)‖ ≤ ‖a‖ * ((b/2)*WeightedGraph.weight n) :=
              mul_le_mul (norm_apply_le a n) (hsmall n).le (norm_nonneg _) (norm_nonneg _)
            _ = _ := by ring
        _ = ((b/2)*‖a‖) * ∑ n ∈ Finset.range N, WeightedGraph.weight n := by rw [Finset.mul_sum]
        _ ≤ ((b/2)*‖a‖) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (half_pos hb).le (norm_nonneg _))
          exact WeightedGraph.hasSum_weight.summable.sum_le_tsum _
            (fun _ _ => WeightedGraph.weight_nonneg _) |>.trans_eq WeightedGraph.hasSum_weight.tsum_eq
        _ = _ := mul_one _
    exact le_of_tendsto ((L.continuous.tendsto a).comp (NullSequences.tendsto_trunc a)).norm
      (Eventually.of_forall htrunc)
  let F := (first Q).comp (S.comp R)
  apply no_c0_of_wsc (wsc_sumL1 (fun _ => hA)) F b hb
  intro a
  have hs := hS (R a)
  have hr : ‖R a‖ = ‖a‖ := (diagonal t ht).norm_map a
  rw [hr, graph_norm] at hs
  have hsmall' := hL a
  change ‖J (S (R a))‖ ≤ (b/2)*‖a‖ at hsmall'
  change b * ‖a‖ ≤ ‖first Q (S (R a))‖
  rcases le_max_iff.1 hs with hf | hg
  · exact hf
  · have hz : ‖a‖ = 0 := by nlinarith [norm_nonneg a]
    simp [hz]

end GraphObstruction

end LipschitzCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.GraphObstruction
open Filter Topology
open WeakSequences
open scoped ENNReal NNReal
open NullSequences


theorem solution.{uH,uA} : type_of% @_root_.OAI.LipschitzCounterexample.GraphObstruction.graph_no_c0L2.{uH,uA} := @_root_.OAI.LipschitzCounterexample.GraphObstruction.graph_no_c0L2.{uH,uA}
