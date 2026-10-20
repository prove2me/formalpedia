-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.supported_intersection_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:49:26.605781+00:00
-- url     : https://prove2.me/submissions/fb13250f-6030-4852-ac49-200e1875de7a

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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports

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

theorem h50b_clip_lip (δ a b : ℝ) : |clip δ a - clip δ b| ≤ 2 * |a - b| := by
  unfold clip
  have h1 := abs_max_sub_max_le_abs (a - δ) (b - δ) 0
  rw [sub_sub_sub_cancel_right] at h1
  have h2 := abs_min_sub_min_le_max (a + δ) 0 (b + δ) 0
  rw [add_sub_add_right_eq_sub, sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h2
  calc |max (a - δ) 0 + min (a + δ) 0 - (max (b - δ) 0 + min (b + δ) 0)|
      = |(max (a - δ) 0 - max (b - δ) 0) + (min (a + δ) 0 - min (b + δ) 0)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * |a - b| := by linarith

theorem h50b_clip_small {δ t : ℝ} (ht : |t| ≤ δ) : clip δ t = 0 := by
  unfold clip
  rw [abs_le] at ht
  rw [max_eq_right (by linarith), min_eq_right (by linarith)]; ring

theorem h50b_clip_close {δ t : ℝ} (hδ : 0 ≤ δ) : |t - clip δ t| ≤ δ := by
  unfold clip
  rw [abs_le]
  constructor <;> (simp only [max_def, min_def]; split_ifs <;> linarith)

theorem h50b_test_comb (k : LipZero M) (a : M →₀ ℝ) :
    LocalizedLinearization.test k (Finsupp.linearCombination ℝ point a) = a.sum (fun x c => c * k.1 x) := by
  rw [Finsupp.linearCombination_apply, map_finsuppSum]
  simp [LocalizedLinearization.test_point]

theorem solution (K : ℕ → Set M)
    (huniform : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ x ∈ K N,
      ∃ y ∈ ⋂ n, K n, dist x y < ε) (μ : Space M)
    (hμ : ∀ n, μ ∈ supported (K n)) : μ ∈ supported (⋂ n, K n) := by
  classical
  set L := ⋂ n, K n with hL
  by_contra hμL
  have hcl : IsClosed (supported L : Set (Space M)) := Submodule.isClosed_topologicalClosure _
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl μ hμL
  have hfar : ∀ ν : Space M, ν ∈ supported L → η ≤ ‖μ - ν‖ := by
    intro ν hν
    by_contra hlt
    push Not at hlt
    exact hball (by rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hlt) hν
  obtain ⟨f, hf1, hf0, hfL, hftest⟩ := h50b_vanishing L μ hfar
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp dense_combinations μ (η / 8) (by positivity)
  set m := Finsupp.linearCombination ℝ point a with hm
  set s := a.sum (fun _ c => |c|) with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set δ := η / (8 * (s + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := huniform δ hδpos
  set g : M → ℝ := fun x => clip δ (f x) with hg
  have hglip : LipschitzWith 2 g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have := h50b_clip_lip δ (f x) (f y)
    have h2 := hf1.dist_le_mul x y
    rw [Real.dist_eq] at h2
    push_cast at h2 ⊢
    linarith
  have hfx : ∀ x, |f x| ≤ dist x 0 := by
    intro x; have := hf1.dist_le_mul x 0; rw [Real.dist_eq, hf0, sub_zero] at this; simpa using this
  have hg0 : g 0 = 0 := by simp only [hg, hf0]; exact h50b_clip_small (by simp [hδpos.le])
  have hgK : ∀ x ∈ K N, (LocalizedLinearization.normalized g hglip).1 x = 0 := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hN x hx
    change g x - g 0 = 0
    rw [hg0, sub_zero]
    apply h50b_clip_small
    have := hf1.dist_le_mul x y
    rw [Real.dist_eq, hfL y hy, sub_zero] at this
    push_cast at this
    linarith
  have htg : LocalizedLinearization.test (LocalizedLinearization.normalized g hglip) μ = 0 :=
    h50b_test_vanish _ hgK (hμ N)
  set k := LocalizedLinearization.normalized f hf1 - LocalizedLinearization.normalized g hglip with hk
  have hklip : LipschitzWith (1 + 2) k.1 := (h50b_normalized_lip f hf1).sub (h50b_normalized_lip g hglip)
  have hkval : ∀ x, |k.1 x| ≤ δ := by
    intro x
    change |(f x - f 0) - (g x - g 0)| ≤ δ
    rw [hf0, hg0, sub_zero, sub_zero]
    exact h50b_clip_close hδpos.le
  have hkμ : LocalizedLinearization.test k μ = LocalizedLinearization.test (LocalizedLinearization.normalized f hf1) μ := by
    rw [hk, ← h50b_test_sub, htg, sub_zero]
  have hkm : |LocalizedLinearization.test k m| ≤ s * δ := by
    rw [hm, h50b_test_comb]
    unfold Finsupp.sum
    calc |∑ x ∈ a.support, a x * k.1 x| ≤ ∑ x ∈ a.support, |a x * k.1 x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ a.support, |a x| * δ := Finset.sum_le_sum (fun x _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hkval x) (abs_nonneg _))
      _ = s * δ := by rw [hs, Finsupp.sum, Finset.sum_mul]
  have hsd : s * δ < η / 8 := by
    rw [hδ, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hkd : |LocalizedLinearization.test k (μ - m)| ≤ (1 + 2 : ℝ≥0) * ‖μ - m‖ := h50b_abs_test_le k hklip _
  have hμm : ‖μ - m‖ < η / 8 := by rw [← dist_eq_norm]; exact ha
  have hsplit : LocalizedLinearization.test k μ = LocalizedLinearization.test k (μ - m) + LocalizedLinearization.test k m := by
    rw [map_sub]; ring
  have hge := hftest hf1
  rw [← hkμ, hsplit] at hge
  have := abs_le.mp hkd
  have := abs_le.mp hkm
  push_cast at *
  nlinarith [norm_nonneg (μ - m)]

