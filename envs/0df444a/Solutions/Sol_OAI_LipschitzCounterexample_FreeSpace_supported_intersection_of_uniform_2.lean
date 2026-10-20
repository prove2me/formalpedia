-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.supported_intersection_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:58:20.268807+00:00
-- url     : https://prove2.me/submissions/911c3a3c-5a27-483f-9ce7-3ed3dbf17c9c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompactSupports.lean:L178-L208
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.supported_intersection_of_uniform. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_exists_vanishing_test

-- ---- from OAI.Analysis.LipschitzEquivalence.Localization ----
namespace OAI

universe uM uV

noncomputable section
namespace LipschitzCounterexample

namespace LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem norm_test_apply_le (f : FreeSpace.LipZero M) (μ : FreeSpace.Space M) :
    ‖test f μ‖ ≤ ‖f‖ * ‖μ‖ := by
  change ‖μ.1 f‖ ≤ ‖f‖ * ‖μ.1‖
  simpa only [mul_comm] using μ.1.le_opNorm f

theorem norm_normalized_le (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) :
    ‖normalized f hf‖ ≤ C := FreeSpace.norm_le_of_lipschitz _ (by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [normalized, Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y)

end LocalizedLinearization

end LipschitzCounterexample
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.SeparableCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uI uE uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]
end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace Topology
variable {E : ℕ → Type uE} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]

end LipschitzCounterexample.HilbertSlots

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set CoordinateSpaces

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.FreeSpace
open scoped Topology NNReal
open Filter Set
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem supported_isClosed (K : Set M) : IsClosed (supported K : Set (Space M)) :=
  Submodule.isClosed_topologicalClosure _

theorem supported_le_ker {K : Set M} (T : Space M →L[ℝ] ℝ)
    (hT : ∀ x ∈ K, T (point x) = 0) : supported K ≤ T.ker := by
  apply Submodule.topologicalClosure_minimal _ _ T.isClosed_ker
  apply Submodule.span_le.mpr
  rintro _ ⟨x,hx,rfl⟩
  exact hT x hx

end LipschitzCounterexample.FreeSpace

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.CoordinateSpaces

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.SupportedDuality ----
namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem exists_finite_approx (μ : Space M) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : M →₀ ℝ, ‖μ - Finsupp.linearCombination ℝ point a‖ < ε := by
  obtain ⟨a,ha⟩ := dense_combinations.exists_dist_lt μ hε
  exact ⟨a,by simpa only [dist_eq_norm] using ha⟩

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.LocalizedLinearization
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.CompactSupports ----
namespace OAI

universe uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped Topology
open Filter Set
variable {M : Type uM} [MetricSpace M]

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem test_tendsto_of_pointwise {f : ℕ → M → ℝ} {g : M → ℝ} {C D : ℝ≥0}
    (hf : ∀ n, LipschitzWith C (f n)) (hg : LipschitzWith D g)
    (hpoint : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) (μ : Space M) :
    Tendsto (fun n => test (normalized (f n) (hf n)) μ) atTop (𝓝 (test (normalized g hg) μ)) := by
  have hfinite (a : M →₀ ℝ) :
      Tendsto (fun n => test (normalized (f n) (hf n)) (Finsupp.linearCombination ℝ point a))
        atTop (𝓝 (test (normalized g hg) (Finsupp.linearCombination ℝ point a))) := by
    simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,test_point,smul_eq_mul]
    change Tendsto (fun n => ∑ x ∈ a.support, a x*(f n x-f n 0))
      atTop (𝓝 (∑ x ∈ a.support, a x*(g x-g 0)))
    apply tendsto_finsetSum
    intro x _
    exact tendsto_const_nhds.mul ((hpoint x).sub (hpoint 0))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨a,ha⟩ := exists_finite_approx μ (show 0 < ε/(2*((C : ℝ)+D+1)) by positivity)
  let ν := Finsupp.linearCombination ℝ point a
  have hsmall : ((C : ℝ)+D)*‖μ-ν‖ < ε/2 := by
    have hh := (lt_div_iff₀ (show (0 : ℝ) < 2*((C : ℝ)+D+1) by positivity)).mp ha
    have hn := norm_nonneg (μ-ν)
    change ‖μ-ν‖*(2*((C : ℝ)+D+1)) < ε at hh
    nlinarith
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hfinite a) (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have h₁ : dist (test (normalized (f n) (hf n)) μ) (test (normalized (f n) (hf n)) ν) ≤ C*‖μ-ν‖ := by
    rw [dist_eq_norm,← map_sub]
    exact (norm_test_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_normalized_le _ _) (norm_nonneg _))
  have h₃ : dist (test (normalized g hg) ν) (test (normalized g hg) μ) ≤ D*‖μ-ν‖ := by
    rw [dist_comm,dist_eq_norm,← map_sub]
    exact (norm_test_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_normalized_le _ _) (norm_nonneg _))
  have ht := dist_triangle (test (normalized (f n) (hf n)) μ)
    (test (normalized (f n) (hf n)) ν) (test (normalized g hg) μ)
  have ht' := dist_triangle (test (normalized (f n) (hf n)) ν)
    (test (normalized g hg) ν) (test (normalized g hg) μ)
  have hm := hN n hn
  change dist (test (normalized (f n) (hf n)) ν) (test (normalized g hg) ν) < ε/2 at hm
  linarith

theorem mem_supported_of_annihilating {K : Set M} (μ : Space M)
    (h : ∀ f : M → ℝ, ∀ hf : LipschitzWith 1 f, f 0 = 0 →
      (∀ x ∈ K, f x = 0) → test (normalized f hf) μ = 0) : μ ∈ supported K := by
  let S := supported K
  let : IsClosed (S : Set (Space M)) := supported_isClosed K
  by_contra hμ
  have hne : S.mkQL μ ≠ 0 := by
    intro hz
    apply hμ
    exact (Submodule.Quotient.mk_eq_zero S).mp hz
  have hp : 0 < ‖S.mkQL μ‖ := norm_pos_iff.mpr hne
  have hfar : ∀ ν : Space M, ν ∈ S → ‖S.mkQL μ‖ ≤ ‖μ-ν‖ := by
    intro ν hν
    have hz : S.mkQL ν = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hν
    have he : S.mkQL (μ-ν) = S.mkQL μ := by rw [map_sub,hz,sub_zero]
    rw [← he]
    exact Submodule.Quotient.norm_mk_le S (μ-ν)
  obtain ⟨f,hf,hf0,hfK,hlarge⟩ := exists_vanishing_test K μ hfar
  have hz := h f hf hf0 hfK
  have hl := hlarge hf
  rw [hz] at hl
  exact (not_le_of_gt hp) hl

theorem clip_lipschitz (ε : ℝ) : LipschitzWith 2 (clip ε) := by
  have h₁ := (lipschitz_sub_const (fun t : ℝ => t) LipschitzWith.id ε).max_const 0
  have h₂ : LipschitzWith 1 (fun t : ℝ => min (t+ε) 0) := by
    simpa only [sub_neg_eq_add] using
      (lipschitz_sub_const (fun t : ℝ => t) LipschitzWith.id (-ε)).min_const 0
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (h₁.add h₂).dist_le_mul x y
  simpa only [clip,NNReal.coe_add,NNReal.coe_one,one_add_one_eq_two] using h

theorem clip_zero {ε t : ℝ} (ht : |t| ≤ ε) : clip ε t = 0 := by
  have ht' := abs_le.mp ht
  simp only [clip,max_eq_right (by linarith : t-ε ≤ 0),min_eq_right (by linarith : 0 ≤ t+ε),add_zero]

theorem clip_tendsto {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => clip (ε n) t) atTop (𝓝 t) := by
  have h : Tendsto (fun n => max (t-ε n) 0+min (t+ε n) 0) atTop
      (𝓝 (max (t-0) 0+min (t+0) 0)) :=
    ((tendsto_const_nhds.sub hε).max tendsto_const_nhds).add
      ((tendsto_const_nhds.add hε).min tendsto_const_nhds)
  change Tendsto (fun n => clip (ε n) t) atTop (𝓝 (max (t-0) 0+min (t+0) 0)) at h
  simpa only [sub_zero,add_zero,max_add_min] using h

theorem supported_intersection_of_uniform (K : ℕ → Set M)
    (huniform : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ x ∈ K N,
      ∃ y ∈ ⋂ n, K n, dist x y < ε) (μ : Space M)
    (hμ : ∀ n, μ ∈ supported (K n)) : μ ∈ supported (⋂ n, K n) := by
  classical
  apply mem_supported_of_annihilating μ
  intro f hf hf0 hfK
  let ε : ℕ → ℝ := fun n => (1/2 : ℝ)^n
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  choose N hN using fun n => huniform (ε n) (hε n)
  let fs : ℕ → M → ℝ := fun n x => clip (ε n) (f x)
  have hfs (n : ℕ) : LipschitzWith 2 (fs n) := by
    simpa only [mul_one,Function.comp_def] using (clip_lipschitz (ε n)).comp hf
  have hfs0 (n : ℕ) : fs n 0 = 0 := by
    exact clip_zero (by rw [hf0,abs_zero]; exact (hε n).le)
  have hzero (n : ℕ) : test (normalized (fs n) (hfs n)) μ = 0 := by
    apply supported_le_ker (K := K (N n)) (test (normalized (fs n) (hfs n))) ?_ (hμ (N n))
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hN n x hx
    have hfx : |f x| ≤ ε n := by
      have h := hf.dist_le_mul x y
      rw [hfK y hy,dist_zero_right,Real.norm_eq_abs,NNReal.coe_one,one_mul] at h
      exact h.trans hxy.le
    change fs n x-fs n 0 = 0
    rw [hfs0]
    exact sub_eq_zero.mpr (clip_zero hfx)
  have hlim := test_tendsto_of_pointwise hfs hf (fun x => clip_tendsto hεlim (f x)) μ
  have he : (fun n => test (normalized (fs n) (hfs n)) μ) = fun _ => 0 := funext hzero
  rw [he] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

end LipschitzCounterexample.FreeSpace

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped NNReal Topology
open Filter Set LocalizedLinearization


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.supported_intersection_of_uniform.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.supported_intersection_of_uniform.{uM}
