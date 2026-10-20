-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.bounded_cauchy_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:15:06.101806+00:00
-- url     : https://prove2.me/submissions/d2e03c53-6586-4b93-b419-ca243b5a4235

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CauchyApproximation.lean:L112-L129
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.bounded_cauchy_approx. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_uniform_radius_approx_cauchy
import Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_lipschitz_effective_smul

-- ---- from OAI.Analysis.LipschitzEquivalence.FreeSpace ----
namespace OAI

universe uM uF

noncomputable section
namespace LipschitzCounterexample

namespace FreeSpace

open scoped NNReal ENNReal

variable (M : Type uM) [MetricSpace M] [Zero M]

variable {M}

section Linearization
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (D : M → F) {K : ℝ≥0} (hD : LipschitzWith K D) (h0 : D 0 = 0)

include hD h0

variable [CompleteSpace F]

theorem norm_linearize_le : ‖linearize D‖ ≤ K :=
  LinearMap.opNorm_extendOfNorm_le dense_combinations K.coe_nonneg
    (norm_combination_le D hD h0)

end Linearization

end FreeSpace

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

open NullSequences

end WeakSequences

end LipschitzCounterexample
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.Localization ----
namespace OAI

universe uM uV

noncomputable section
namespace LipschitzCounterexample

namespace LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

omit [Zero M] in
theorem cutoff_one (z : M) {s : ℝ≥0} (hs : 0 < s) {x : M} (hx : dist x z ≤ s / 2) :
    cutoff z s x = 1 := by
  have hs' : 0 < (s : ℝ) := hs
  have hmul : (2 / (s : ℝ)) * dist x z ≤ 1 := by
    calc
      _ ≤ (2 / (s : ℝ)) * ((s : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      _ = 1 := by field_simp
  unfold cutoff
  rw [min_eq_left (by linarith)]
  norm_num

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

theorem point_mem_supported {K : Set M} {x : M} (hx : x ∈ K) : point x ∈ supported K :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x,hx,rfl⟩)

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

theorem combination_mem_supported (a : M →₀ ℝ) {K : Set M}
    (ha : ∀ x ∈ a.support, x ∈ K) : Finsupp.linearCombination ℝ point a ∈ supported K := by
  rw [Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ (fun x hx => Submodule.smul_mem _ _ (point_mem_supported (ha x hx)))

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.LocalizedLinearization
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.Multipliers ----
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

theorem multiplier_lipschitz (φ : M → ℝ) {A B R : ℝ≥0}
    (hφ : LipschitzWith B φ) (hA : ∀ x, |φ x| ≤ A)
    (hR : ∀ x, φ x ≠ 0 → dist x 0 ≤ R) :
    LipschitzWith (A+B*R) (fun x => φ x • point x) := by
  simpa only [mul_one] using lipschitz_effective_smul point φ isometry_point.lipschitz hφ hA
    (fun x hx => by
      have he : ‖point x‖ = dist x 0 := by simpa only [point_zero,dist_zero_right] using isometry_point.dist_eq x 0
      rw [he]
      exact hR x hx)

theorem multiplier_point (φ : M → ℝ) {A B R : ℝ≥0}
    (hφ : LipschitzWith B φ) (hA : ∀ x, |φ x| ≤ A)
    (hR : ∀ x, φ x ≠ 0 → dist x 0 ≤ R) (x : M) :
    multiplier φ (point x) = φ x • point x :=
  linearize_point _ (multiplier_lipschitz φ hφ hA hR) (by simp) x

theorem norm_multiplier_le (φ : M → ℝ) {A B R : ℝ≥0}
    (hφ : LipschitzWith B φ) (hA : ∀ x, |φ x| ≤ A)
    (hR : ∀ x, φ x ≠ 0 → dist x 0 ≤ R) :
    ‖multiplier φ‖ ≤ A+B*R :=
  norm_linearize_le _ (multiplier_lipschitz φ hφ hA hR) (by simp)

theorem supported_map {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Space M →L[ℝ] E) (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    {K : Set M} (hT : ∀ x ∈ K, T (point x) ∈ S) :
    ∀ μ ∈ supported K, T μ ∈ S := by
  have hsub : supported K ≤ S.comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal _ _ (hS.preimage T.continuous)
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact hT x hx
  exact fun μ hμ => hsub hμ

theorem supported_univ : supported (Set.univ : Set M) = ⊤ := by
  apply top_unique
  intro μ _
  have hd := dense_combinations μ
  have hs : Set.range (Finsupp.linearCombination ℝ (point : M → Space M)) ⊆
      (↑(supported (M := M) Set.univ) : Set (Space M)) := by
    rintro _ ⟨a,rfl⟩
    exact combination_mem_supported a (by simp)
  exact (supported_isClosed Set.univ).closure_subset (closure_mono hs hd)

theorem multiplier_supported (φ : M → ℝ) {A B R : ℝ≥0}
    (hφ : LipschitzWith B φ) (hA : ∀ x, |φ x| ≤ A)
    (hR : ∀ x, φ x ≠ 0 → dist x 0 ≤ R) {K S : Set M}
    (hS : ∀ x ∈ K, φ x ≠ 0 → x ∈ S) {μ : Space M} (hμ : μ ∈ supported K) :
    multiplier φ μ ∈ supported S := by
  apply supported_map (multiplier φ) (supported S) (supported_isClosed S) (K := K) ?_ μ hμ
  intro x hx
  rw [multiplier_point φ hφ hA hR]
  by_cases hz : φ x = 0
  · simp [hz]
  · exact Submodule.smul_mem _ _ (point_mem_supported (hS x hx hz))

theorem multiplier_identity_on (φ : M → ℝ) {A B R : ℝ≥0}
    (hφ : LipschitzWith B φ) (hA : ∀ x, |φ x| ≤ A)
    (hR : ∀ x, φ x ≠ 0 → dist x 0 ≤ R) {K : Set M}
    (hK : ∀ x ∈ K, φ x = 1) {μ : Space M} (hμ : μ ∈ supported K) :
    multiplier φ μ = μ := by
  have hker : supported K ≤ (multiplier φ-ContinuousLinearMap.id ℝ (Space M)).ker := by
    apply Submodule.topologicalClosure_minimal _ _ (ContinuousLinearMap.isClosed_ker _)
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change multiplier φ (point x)-point x = 0
    rw [multiplier_point φ hφ hA hR,hK x hx,one_smul,sub_self]
  exact sub_eq_zero.mp (hker hμ)

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

end LipschitzCounterexample.FreeSpace

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.FiniteMultipliers ----
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

theorem norm_sub_apply_le_of_agree {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T U : Space M →L[ℝ] E) (μ ν : Space M) (he : T ν = U ν) :
    ‖T μ-U μ‖ ≤ (‖T‖+‖U‖)*‖μ-ν‖ := by
  have hid : T μ-U μ = T (μ-ν)-U (μ-ν) := by
    rw [map_sub,map_sub,he]
    abel
  rw [hid,add_mul]
  exact (_root_.norm_sub_le _ _).trans (add_le_add (T.le_opNorm _) (U.le_opNorm _))

theorem outerRadius_pos (R : ℝ≥0) : 0 < outerRadius R := by dsimp [outerRadius]; positivity

theorem cutoff_abs_le_one (R : ℝ≥0) (x : M) : |cutoff 0 (outerRadius R) x| ≤ (1 : ℝ≥0) := by
  rw [abs_of_nonneg (cutoff_nonneg _ _ _)]
  exact cutoff_le_one _ _ _

theorem cutoff_radius_bound (R : ℝ≥0) (x : M) (hx : cutoff 0 (outerRadius R) x ≠ 0) :
    dist x 0 ≤ outerRadius R := by
  by_contra h
  exact hx (cutoff_zero 0 (outerRadius_pos R) (le_of_lt (lt_of_not_ge h)))

theorem norm_radialMultiplier_le (R : ℝ≥0) : ‖radialMultiplier (M := M) R‖ ≤ 3 := by
  have h := norm_multiplier_le _ (cutoff_lipschitz (0 : M) (outerRadius R))
    (cutoff_abs_le_one R) (cutoff_radius_bound R)
  have hs : (outerRadius R : ℝ) ≠ 0 := ne_of_gt (outerRadius_pos R)
  change ‖radialMultiplier (M := M) R‖ ≤ (1 : ℝ)+((2 : ℝ)/(outerRadius R))*(outerRadius R) at h
  rw [div_mul_cancel₀ _ hs] at h
  norm_num at h
  exact h

theorem radialMultiplier_identity (R : ℝ≥0) {μ : Space M}
    (hμ : μ ∈ supported (Metric.closedBall 0 (R : ℝ))) : radialMultiplier R μ = μ := by
  apply multiplier_identity_on _ (cutoff_lipschitz _ _) (cutoff_abs_le_one R) (cutoff_radius_bound R) ?_ hμ
  intro x hx
  apply cutoff_one 0 (outerRadius_pos R)
  change dist x 0 ≤ (R : ℝ) at hx
  dsimp [outerRadius]
  linarith

theorem radialMultiplier_supported (R : ℝ≥0) (μ : Space M) :
    radialMultiplier R μ ∈ supported (Metric.closedBall 0 (outerRadius R : ℝ)) := by
  apply multiplier_supported _ (cutoff_lipschitz _ _) (cutoff_abs_le_one R) (cutoff_radius_bound R)
    (K := Set.univ) (fun x _ hx => cutoff_radius_bound R x hx)
  rw [supported_univ]
  trivial

end LipschitzCounterexample.FreeSpace

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.CauchyApproximation ----
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
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem bounded_cauchy_approx {μ : ℕ → Space M} (hw : WeakSequences.WeakCauchy μ)
    {ε : ℝ} (hε : 0 < ε) : ∃ R : ℝ≥0, ∃ v : ℕ → Space M,
      WeakSequences.WeakCauchy v ∧ (∀ i, v i ∈ supported (Metric.closedBall 0 (R : ℝ))) ∧
      ∀ i, ‖μ i-v i‖ < ε := by
  obtain ⟨r,hr,happrox⟩ := uniform_radius_approx_cauchy hw (show 0 < ε/8 by positivity)
  let R : ℝ≥0 := ⟨r,hr.le⟩
  let T : Space M →L[ℝ] Space M := radialMultiplier R
  refine ⟨outerRadius R,(fun i => T (μ i)),hw.map T,fun i => radialMultiplier_supported R (μ i),?_⟩
  intro i
  obtain ⟨ν,hν,herr⟩ := happrox i
  have he : (ContinuousLinearMap.id ℝ (Space M)) ν = T ν := (radialMultiplier_identity R hν).symm
  have hbound := norm_sub_apply_le_of_agree (ContinuousLinearMap.id ℝ (Space M)) T (μ i) ν he
  have hT := norm_radialMultiplier_le (M := M) R
  have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Space M)
  have hn := norm_nonneg (μ i-ν)
  change ‖μ i-T (μ i)‖ ≤ _ at hbound
  have hc : ‖ContinuousLinearMap.id ℝ (Space M)‖+‖T‖ ≤ 4 := by dsimp [T]; linarith
  exact (hbound.trans (mul_le_mul_of_nonneg_right hc hn)).trans_lt (by linarith)

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


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.bounded_cauchy_approx.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.bounded_cauchy_approx.{uM}
