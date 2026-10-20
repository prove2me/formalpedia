-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.radius_escape_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:51:22.975836+00:00
-- url     : https://prove2.me/submissions/51866f46-d269-4865-9717-452b054e6f84

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
universe uM
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]
theorem h50b_test_sub (a b : LipZero M) (μ : Space M) :
    LocalizedLinearization.test a μ - LocalizedLinearization.test b μ =
      LocalizedLinearization.test (a - b) μ := by
  change μ.1 a - μ.1 b = μ.1 (a - b)
  rw [map_sub]

theorem h50b_abs_test_le (a : LipZero M) {K : ℝ≥0} (ha : LipschitzWith K a.1) (μ : Space M) :
    |LocalizedLinearization.test a μ| ≤ K * ‖μ‖ := by
  have h1 : |LocalizedLinearization.test a μ| ≤ ‖a‖ * ‖μ‖ := by
    change |μ.1 a| ≤ ‖a‖ * ‖μ‖
    have := μ.1.le_opNorm a
    rw [Real.norm_eq_abs] at this
    calc |μ.1 a| ≤ ‖μ.1‖ * ‖a‖ := this
      _ = ‖a‖ * ‖μ‖ := by rw [mul_comm]; rfl
  exact h1.trans (mul_le_mul_of_nonneg_right (norm_le_of_lipschitz a ha) (norm_nonneg _))

theorem h50b_test_vanish {K : Set M} (a : LipZero M) (ha : ∀ x ∈ K, a.1 x = 0) {μ : Space M}
    (hμ : μ ∈ supported K) : LocalizedLinearization.test a μ = 0 := by
  have hle : supported K ≤ LinearMap.ker (LocalizedLinearization.test a).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [LocalizedLinearization.test_point]
      exact ha x hx
    · exact (LocalizedLinearization.test a).isClosed_ker
  exact hle hμ

theorem h50b_normalized_lip (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (LocalizedLinearization.normalized f hf).1 :=
  LocalizedLinearization.lipschitz_sub_const f hf (f 0)
theorem h50b_supported_mono {K L : Set M} (h : K ⊆ L) : supported K ≤ supported L :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono h))

theorem h50b_approx_ball (μ : Space M) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, Approximable μ (Metric.closedBall 0 R) ε := by
  classical
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp dense_combinations μ ε hε
  obtain ⟨R, hR⟩ := (a.support.finite_toSet.isBounded).subset_closedBall (0 : M)
  refine ⟨R, Finsupp.linearCombination ℝ point a, ?_, ?_⟩
  · apply Submodule.le_topologicalClosure
    rw [Finsupp.mem_span_image_iff_linearCombination]
    exact ⟨a, (Finsupp.mem_supported ℝ a).mpr hR, rfl⟩
  · rw [← dist_eq_norm]; exact ha

theorem h50b_approx_mono {μ : Space M} {K L : Set M} {ε : ℝ} (h : K ⊆ L)
    (hK : Approximable μ K ε) : Approximable μ L ε := by
  obtain ⟨ν, hν, hd⟩ := hK
  exact ⟨ν, h50b_supported_mono h hν, hd⟩
theorem h50b_clm_ext (S T : Space M →L[ℝ] ℝ) (h : ∀ x, S (point x) = T (point x)) : S = T := by
  have hlin : S.toLinearMap ∘ₗ Finsupp.linearCombination ℝ point =
      T.toLinearMap ∘ₗ Finsupp.linearCombination ℝ point := by
    apply Finsupp.lhom_ext
    intro x c
    simp [h x]
  have := dense_combinations.equalizer S.continuous T.continuous (by
    funext a
    exact LinearMap.congr_fun hlin a)
  exact ContinuousLinearMap.coe_injective (by
    ext μ
    exact congrFun this μ)

theorem h50b_vanishing (K : Set M) (μ : Space M) {ε : ℝ}
    (hfar : ∀ ν : Space M, ν ∈ supported K → ε ≤ ‖μ-ν‖) :
    ∃ f : M → ℝ, LipschitzWith 1 f ∧ f 0 = 0 ∧ (∀ x ∈ K, f x = 0) ∧
      ∀ hf : LipschitzWith 1 f, ε ≤ LocalizedLinearization.test (LocalizedLinearization.normalized f hf) μ := by
  by_cases hε : ε ≤ 0
  · refine ⟨fun _ => 0, (LipschitzWith.const 0).weaken (zero_le_one), rfl, fun _ _ => rfl, fun hf => ?_⟩
    have : LocalizedLinearization.test (LocalizedLinearization.normalized (fun _ : M => (0:ℝ)) hf) μ = 0 := by
      change μ.1 _ = 0
      have : LocalizedLinearization.normalized (fun _ : M => (0:ℝ)) hf = 0 := by
        apply Subtype.ext; funext x; change (0:ℝ) - 0 = 0; ring
      rw [this, map_zero]
    rw [this]; exact hε
  push Not at hε
  set W := supported K with hW
  have : IsClosed (W : Set (Space M)) := Submodule.isClosed_topologicalClosure _
  set q : Space M ⧸ W := Submodule.Quotient.mk μ with hq
  have hqnorm : ε ≤ ‖q‖ := by
    apply le_of_forall_pos_lt_add
    intro δ hδ
    obtain ⟨m, hm, hmn⟩ := Submodule.Quotient.norm_mk_lt q hδ
    have hmem : μ - m ∈ W := by
      have := (Submodule.Quotient.eq W).mp (hm.trans hq)
      rw [← neg_mem_iff, neg_sub]; exact this
    have := hfar _ hmem
    rw [sub_sub_cancel] at this
    linarith
  have hq0 : ‖q‖ ≠ 0 := by
    intro h0; rw [h0] at hqnorm; linarith
  obtain ⟨g, hg1, hgq⟩ := exists_dual_vector ℝ q hq0
  set T : Space M →L[ℝ] ℝ := g.comp W.mkQL with hT
  have hTn : ‖T‖₊ ≤ 1 := by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    calc ‖T x‖ = ‖g (W.mkQL x)‖ := rfl
      _ ≤ ‖g‖ * ‖W.mkQL x‖ := g.le_opNorm _
      _ ≤ 1 * ‖x‖ := by rw [hg1]; exact mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le W x) zero_le_one
  have hlip : LipschitzWith 1 (fun x => T (point x)) := (dual_point_lipschitz T).weaken hTn
  refine ⟨fun x => T (point x), hlip, by simp, ?_, fun hf => ?_⟩
  · intro x hx
    change g (W.mkQL (point x)) = 0
    have : W.mkQL (point x) = 0 := by
      change Submodule.Quotient.mk (point x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x, hx, rfl⟩)
    rw [this, map_zero]
  · have : LocalizedLinearization.test (LocalizedLinearization.normalized _ hf) = T := by
      apply h50b_clm_ext
      intro x
      rw [LocalizedLinearization.test_point]
      change T (point x) - T (point 0) = T (point x)
      simp
    rw [this]
    change ε ≤ g q
    rw [hgq]; exact hqnorm

theorem h50b_pairing_diff {K : Set M} (h0 : (0 : M) ∈ K)
    (f g : M → ℝ) {C D : ℝ≥0} (hf : LipschitzWith C f) (hg : LipschitzWith D g)
    (he : ∀ x ∈ K, f x = g x) (μ ν : Space M) (hν : ν ∈ supported K) :
    |LocalizedLinearization.test (LocalizedLinearization.normalized f hf) μ -
      LocalizedLinearization.test (LocalizedLinearization.normalized g hg) μ| ≤ (C+D)*‖μ-ν‖ := by
  set a := LocalizedLinearization.normalized f hf - LocalizedLinearization.normalized g hg with ha
  have hvan : ∀ x ∈ K, a.1 x = 0 := by
    intro x hx
    change (f x - f 0) - (g x - g 0) = 0
    rw [he x hx, he 0 h0]; ring
  have hlip : LipschitzWith (C + D) a.1 :=
    (h50b_normalized_lip f hf).sub (h50b_normalized_lip g hg)
  have h1 := h50b_test_vanish a hvan hν
  rw [h50b_test_sub, ← ha]
  have : LocalizedLinearization.test a μ = LocalizedLinearization.test a (μ - ν) := by
    rw [map_sub, h1, sub_zero]
  rw [this]
  have := h50b_abs_test_le a hlip (μ - ν)
  simpa using this

theorem h50b_cutoff_one {S : ℝ} (hS : 0 < S) {sN : ℝ≥0} (hsN : (sN : ℝ) = 2 * S) {x : M}
    (hx : dist x 0 ≤ S) : LocalizedLinearization.cutoff (0 : M) sN x = 1 := by
  unfold LocalizedLinearization.cutoff
  have : 1 ≤ 2 - 2 / (sN : ℝ) * dist x 0 := by
    rw [hsN]
    have : 2 / (2 * S) * dist x 0 ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]; linarith
    linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem solution {μ : ℕ → Space M} {ε : ℝ} (hε : 0 < ε)
    (hfail : ∀ R : ℝ, 0 < R → ∃ i, ¬ Approximable (μ i) (Metric.closedBall 0 R) ε)
    (p : ℕ) (r : ℝ) : ∃ i : ℕ, ∃ s : ℝ, ∃ g : M → ℝ,
      p < i ∧ r < s ∧ LipschitzWith 3 g ∧ g 0 = 0 ∧
      (∀ x, dist x 0 ≤ r → g x = 0) ∧ (∀ x, s ≤ dist x 0 → g x = 0) ∧
      ∀ hg : LipschitzWith 3 g, ε/2 < |test (normalized g hg) (μ i)| := by
  choose Ri hRi using fun i => h50b_approx_ball (μ i) hε
  set R := |r| + 1 + ∑ i ∈ Finset.range (p+1), |Ri i| with hRdef
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (p+1), |Ri i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hRpos : 0 < R := by linarith [abs_nonneg r]
  have hrR : r ≤ R := by linarith [le_abs_self r]
  obtain ⟨i, hi⟩ := hfail R hRpos
  have hpi : p < i := by
    by_contra hle
    push Not at hle
    apply hi
    apply h50b_approx_mono _ (hRi i)
    apply Metric.closedBall_subset_closedBall
    have h1 : |Ri i| ≤ ∑ j ∈ Finset.range (p+1), |Ri j| :=
      Finset.single_le_sum (f := fun j => |Ri j|) (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
    linarith [le_abs_self (Ri i), abs_nonneg r]
  have hfar : ∀ ν : Space M, ν ∈ supported (Metric.closedBall 0 R) → ε ≤ ‖μ i - ν‖ := by
    intro ν hν
    by_contra hlt
    push Not at hlt
    exact hi ⟨ν, hν, hlt⟩
  obtain ⟨f, hf1, hf0, hfK, hftest⟩ := h50b_vanishing _ (μ i) hfar
  obtain ⟨R', ν, hν, hνd⟩ := h50b_approx_ball (μ i) (show 0 < ε / 16 by positivity)
  set S := |R'| + |r| + 1 with hSdef
  have hSpos : 0 < S := by positivity
  set sN : ℝ≥0 := ⟨2 * S, by positivity⟩ with hsNdef
  have hsN : (sN : ℝ) = 2 * S := rfl
  have hsNpos : 0 < sN := by rw [← NNReal.coe_pos, hsN]; positivity
  set g : M → ℝ := fun x => f x * LocalizedLinearization.cutoff (0 : M) sN x with hgdef
  have hglip : LipschitzWith 3 g := by
    have := LocalizedLinearization.cutoff_product_lipschitz (0 : M) hsNpos f hf1 hf0
    simpa using this
  refine ⟨i, 2 * S, g, hpi, by linarith [le_abs_self r, abs_nonneg R'], hglip, by simp [hgdef, hf0], ?_, ?_, ?_⟩
  · intro x hx
    simp only [hgdef]
    rw [hfK x (Metric.mem_closedBall.mpr (le_trans hx hrR)), zero_mul]
  · intro x hx
    simp only [hgdef]
    rw [LocalizedLinearization.cutoff_zero (0 : M) hsNpos (by rw [hsN]; exact hx), mul_zero]
  · intro hg
    have heq : ∀ x ∈ Metric.closedBall (0 : M) S, f x = g x := by
      intro x hx
      simp only [hgdef]
      rw [h50b_cutoff_one hSpos hsN (Metric.mem_closedBall.mp hx), mul_one]
    have hν' : ν ∈ supported (Metric.closedBall (0 : M) S) :=
      h50b_supported_mono (Metric.closedBall_subset_closedBall (by linarith [le_abs_self R', abs_nonneg r])) hν
    have hd := h50b_pairing_diff (Metric.mem_closedBall_self hSpos.le) f g hf1 hg heq (μ i) ν hν'
    have h1 := hftest hf1
    have h2 := abs_le.mp hd
    push_cast at h2
    rw [lt_abs]
    left
    nlinarith

