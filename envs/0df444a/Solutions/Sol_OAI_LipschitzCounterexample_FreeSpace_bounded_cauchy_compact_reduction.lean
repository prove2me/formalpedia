-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.bounded_cauchy_compact_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:18:38.450738+00:00
-- url     : https://prove2.me/submissions/f2c7d2c3-7ad9-43d8-a65b-63099a8a961e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CauchyReduction.lean:L60-L128
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.bounded_cauchy_compact_reduction. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_nested_finite_cover_uniform
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_supported_intersection_of_uniform
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_uniform_finite_neighborhood_approx_cauchy
import Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_lipschitz_effective_smul
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_weakCauchy_of_uniform_approx

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

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.LocalizedLinearization
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem setCutoff_lipschitz (K : Set M) (r : ℝ≥0) :
    LipschitzWith (2/r) (setCutoff K r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact ((cutoff_lipschitz (0 : ℝ) r).dist_le_mul (Metric.infDist x K) (Metric.infDist y K)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [one_mul,NNReal.coe_one] using
      (Metric.lipschitz_infDist_pt K).dist_le_mul x y) (by positivity))

theorem setCutoff_nonneg (K : Set M) (r : ℝ≥0) (x : M) : 0 ≤ setCutoff K r x :=
  cutoff_nonneg _ _ _

theorem setCutoff_le_one (K : Set M) (r : ℝ≥0) (x : M) : setCutoff K r x ≤ 1 :=
  cutoff_le_one _ _ _

theorem setCutoff_one {K : Set M} {r : ℝ≥0} (hr : 0 < r) {x : M}
    (hx : Metric.infDist x K ≤ r/2) : setCutoff K r x = 1 := by
  apply cutoff_one _ hr
  simpa only [dist_zero_right,Real.norm_of_nonneg Metric.infDist_nonneg] using hx

theorem setCutoff_zero {K : Set M} {r : ℝ≥0} (hr : 0 < r) {x : M}
    (hx : (r : ℝ) ≤ Metric.infDist x K) : setCutoff K r x = 0 := by
  apply cutoff_zero _ hr
  simpa only [dist_zero_right,Real.norm_of_nonneg Metric.infDist_nonneg] using hx

theorem setCutoff_nonzero {K : Set M} {r : ℝ≥0} (hr : 0 < r) {x : M}
    (hx : setCutoff K r x ≠ 0) : Metric.infDist x K < r := by
  by_contra h
  exact hx (setCutoff_zero hr (le_of_not_gt h))

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

theorem supported_mono {K S : Set M} (h : K ⊆ S) : supported K ≤ supported S :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono h))

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

theorem maps_agree_of_points {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T U : Space M →L[ℝ] E) {K : Set M} (he : ∀ x ∈ K, T (point x) = U (point x))
    {μ : Space M} (hμ : μ ∈ supported K) : T μ = U μ := by
  have hk : supported K ≤ (T-U).ker := by
    apply Submodule.topologicalClosure_minimal _ _ (ContinuousLinearMap.isClosed_ker _)
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change T (point x)-U (point x) = 0
    exact sub_eq_zero.mpr (he x hx)
  exact sub_eq_zero.mp (hk hμ)

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

theorem radialMultiplier_point (R : ℝ≥0) (x : M) :
    radialMultiplier R (point x) = cutoff 0 (outerRadius R) x • point x :=
  multiplier_point _ (cutoff_lipschitz _ _) (cutoff_abs_le_one R) (cutoff_radius_bound R) x

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

theorem finiteCutoff_lipschitz (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) :
    LipschitzWith (finiteCutoffLip R δ) (finiteCutoff R A δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := lipschitz_effective_smul (cutoff (0 : M) (outerRadius R)) (setCutoff (A : Set M) (2*δ))
      (cutoff_lipschitz _ _) (setCutoff_lipschitz _ _) (A := 1) (P := 1)
      (fun x => by rw [abs_of_nonneg (setCutoff_nonneg _ _ _)]; exact setCutoff_le_one _ _ _)
      (fun x _ => cutoff_abs_le_one R x)
  simpa only [finiteCutoffLip,finiteCutoff,one_mul,mul_one,smul_eq_mul] using h.dist_le_mul x y

theorem finiteCutoff_abs_le_one (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) (x : M) :
    |finiteCutoff R A δ x| ≤ (1 : ℝ≥0) := by
  rw [finiteCutoff,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _)
    (by rw [abs_of_nonneg (setCutoff_nonneg _ _ _)]; exact setCutoff_le_one _ _ _)).trans
      (cutoff_abs_le_one R x)

theorem finiteCutoff_radius_bound (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) (x : M)
    (hx : finiteCutoff R A δ x ≠ 0) : dist x 0 ≤ outerRadius R :=
  cutoff_radius_bound R x (fun h => hx (by simp [finiteCutoff,h]))

theorem finiteMultiplier_point (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) (x : M) :
    finiteMultiplier R A δ (point x) = finiteCutoff R A δ x • point x :=
  multiplier_point _ (finiteCutoff_lipschitz R A δ) (finiteCutoff_abs_le_one R A δ)
    (finiteCutoff_radius_bound R A δ) x

theorem norm_finiteMultiplier_le (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) :
    ‖finiteMultiplier R A δ‖ ≤ finiteMultiplierBound R δ :=
  norm_multiplier_le _ (finiteCutoff_lipschitz R A δ) (finiteCutoff_abs_le_one R A δ)
    (finiteCutoff_radius_bound R A δ)

theorem finiteMultiplier_agree (R : ℝ≥0) (A : Finset M) {δ : ℝ≥0} (hδ : 0 < δ)
    {ν : Space M} (hν : ν ∈ supported (Near A δ)) :
    finiteMultiplier R A δ ν = radialMultiplier R ν := by
  apply maps_agree_of_points _ _ ?_ hν
  rintro x ⟨a,ha,hxa⟩
  rw [finiteMultiplier_point,radialMultiplier_point]
  have hdist : Metric.infDist x (A : Set M) ≤ ((2*δ : ℝ≥0) : ℝ)/2 := by
    have h := (Metric.infDist_le_dist_of_mem ha).trans hxa
    simpa using h
  have hone := setCutoff_one (show 0 < 2*δ by positivity) hdist
  simp [finiteCutoff,hone]

theorem finiteMultiplier_support (R : ℝ≥0) (A : Finset M) (hA : (0 : M) ∈ A)
    {δ : ℝ≥0} (hδ : 0 < δ) {K : Set M} {μ : Space M} (hμ : μ ∈ supported K) :
    finiteMultiplier R A δ μ ∈ supported (K ∩ Near A (2*δ)) := by
  apply multiplier_supported _ (finiteCutoff_lipschitz R A δ) (finiteCutoff_abs_le_one R A δ)
    (finiteCutoff_radius_bound R A δ) ?_ hμ
  intro x hx hφ
  constructor
  · exact hx
  · have hnz : setCutoff (A : Set M) (2*δ) x ≠ 0 := fun h => hφ (by simp [finiteCutoff,h])
    obtain ⟨a,ha,hxa⟩ := (Metric.infDist_lt_iff (show (A : Set M).Nonempty from ⟨0,hA⟩)).mp
      (setCutoff_nonzero (show 0 < 2*δ by positivity) hnz)
    exact ⟨a,ha,hxa.le⟩

theorem finiteMultiplier_error (R : ℝ≥0) (A : Finset M) {δ : ℝ≥0} (hδ : 0 < δ)
    {μ ν : Space M} (hμ : μ ∈ supported (Metric.closedBall 0 (R : ℝ)))
    (hν : ν ∈ supported (Near A δ)) :
    ‖μ-finiteMultiplier R A δ μ‖ ≤ (3+finiteMultiplierBound R δ)*‖μ-ν‖ := by
  have h := norm_sub_apply_le_of_agree (radialMultiplier R) (finiteMultiplier R A δ) μ ν
    (finiteMultiplier_agree R A hδ hν).symm
  rw [radialMultiplier_identity R hμ] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (add_le_add (norm_radialMultiplier_le R) (norm_finiteMultiplier_le R A δ)) (norm_nonneg _))

end LipschitzCounterexample.FreeSpace

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

theorem near_isClosed (A : Finset M) (δ : ℝ) : IsClosed (Near A δ) := by
  have he : Near A δ = ⋃ a ∈ A, Metric.closedBall a δ := by
    ext x
    simp only [Near,Set.mem_ofPred_eq,Set.mem_iUnion,Metric.mem_closedBall]
    constructor <;> rintro ⟨a,ha,h⟩ <;> exact ⟨a,ha,h⟩
  rw [he]
  exact isClosed_biUnion_finset (fun _ _ => Metric.isClosed_closedBall)

theorem nested_finite_cover_compact [CompleteSpace M] (K : ℕ → Set M)
    (hc : ∀ n, IsClosed (K n)) (A : ℕ → Finset M) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (hcover : ∀ n, K (n+1) ⊆ Near (A n) (r n)) :
    IsCompact (⋂ n, K n) := by
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨?_,(isClosed_iInter hc).isComplete⟩
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hr ε hε
  have hrN : r N < ε := (le_abs_self _).trans_lt (by simpa only [dist_zero_right,Real.norm_eq_abs] using hN N le_rfl)
  refine ⟨(A N : Set M),(A N).finite_toSet,?_⟩
  intro x hx
  obtain ⟨a,ha,hxa⟩ := hcover N (Set.mem_iInter.mp hx (N+1))
  exact Set.mem_iUnion₂.mpr ⟨a,ha,hxa.trans_lt hrN⟩

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

end LipschitzCounterexample.FreeSpace

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.CauchyReduction ----
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

theorem cauchy_localization_step {R : ℝ≥0} (W : CauchyLocalizationState (M := M) R)
    {δ : ℝ≥0} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∃ V : CauchyLocalizationState (M := M) R, V.set ⊆ W.set ∧
      (∃ A : Finset M, V.set ⊆ Near A (2*δ)) ∧
      ∀ i, dist (W.seq i) (V.seq i) < η := by
  have hsupp (i : ℕ) : W.seq i ∈ supported (Metric.closedBall 0 (R : ℝ)) :=
    supported_mono W.bounded (W.support i)
  let C : ℝ := 4+finiteMultiplierBound R δ
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨A,hA,happrox⟩ := uniform_finite_neighborhood_approx_cauchy W.weak hsupp hδ (div_pos hη hC)
  let V : CauchyLocalizationState (M := M) R := {
    seq := fun i => finiteMultiplier R A δ (W.seq i)
    weak := W.weak.map (finiteMultiplier R A δ)
    set := W.set ∩ Near A (2*δ)
    closed := W.closed.inter (near_isClosed A _)
    zero_mem := ⟨W.zero_mem,0,hA,by simp⟩
    bounded := fun _ hx => W.bounded hx.1
    support := fun i => finiteMultiplier_support R A hA hδ (W.support i) }
  refine ⟨V,Set.inter_subset_left,⟨A,Set.inter_subset_right⟩,?_⟩
  intro i
  obtain ⟨ν,hν,herr⟩ := happrox i
  have h := finiteMultiplier_error R A hδ (hsupp i) hν
  have hmul := (mul_lt_mul_of_pos_left herr hC)
  rw [mul_div_cancel₀ _ (ne_of_gt hC)] at hmul
  change dist (W.seq i) (finiteMultiplier R A δ (W.seq i)) < η
  rw [dist_eq_norm]
  have hh : (3+(finiteMultiplierBound R δ : ℝ))*‖W.seq i-ν‖ ≤ C*‖W.seq i-ν‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    dsimp [C]; linarith
  exact (h.trans hh).trans_lt hmul

theorem bounded_cauchy_compact_reduction [CompleteSpace M] {R : ℝ≥0} {μ : ℕ → Space M}
    (hw : WeakSequences.WeakCauchy μ)
    (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {τ : ℝ} (hτ : 0 < τ) : ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
      ∃ ν : ℕ → Space M, WeakSequences.WeakCauchy ν ∧
        (∀ i, ν i ∈ supported K) ∧ ∀ i, ‖μ i-ν i‖ < τ := by
  classical
  let δ : ℕ → ℝ≥0 := fun n => (1/2)^n
  let η : ℕ → ℝ := fun n => (τ/4)*(1/2)^n
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hη (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  choose next hsub hcover herr using fun n (W : CauchyLocalizationState (M := M) R) =>
    cauchy_localization_step W (hδ n) (hη n)
  let start : CauchyLocalizationState (M := M) R := {
    seq := μ
    weak := hw
    set := Metric.closedBall 0 (R : ℝ)
    closed := Metric.isClosed_closedBall
    zero_mem := by simp
    bounded := Set.Subset.rfl
    support := hsupp }
  let W : ℕ → CauchyLocalizationState (M := M) R := fun n =>
    Nat.rec start (fun n V => next n V) n
  have hsucc (n : ℕ) : W (n+1) = next n (W n) := rfl
  let K : ℕ → Set M := fun n => (W n).set
  have hanti : Antitone K := by
    apply antitone_nat_of_succ_le
    intro n
    exact hsub n (W n)
  choose A hA using fun n => hcover n (W n)
  have hcov (n : ℕ) : K (n+1) ⊆ Near (A n) (2*(δ n : ℝ)) := hA n
  have hr : Tendsto (fun n => 2*(δ n : ℝ)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => (1/2 : ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [δ] using hlim.const_mul 2
  have hc (n : ℕ) : IsClosed (K n) := (W n).closed
  have hcompact := nested_finite_cover_compact K hc A _ hr hcov
  have huniform := fun (ε : ℝ) (hε : 0 < ε) =>
    nested_finite_cover_uniform K hc hanti A _ hr hcov hε
  have hstep (i n : ℕ) : dist ((W n).seq i) ((W (n+1)).seq i) ≤ (τ/4)*(1/2)^n :=
    (herr n (W n) i).le
  choose ν hν using fun i => cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1/2) (τ/4) (by norm_num) (hstep i))
  have hdist (i n : ℕ) : ‖(W n).seq i-ν i‖ ≤ (τ/2)*(1/2)^n := by
    have hh := dist_le_of_le_geometric_of_tendsto (1/2) (τ/4) (by norm_num)
      (hstep i) (hν i) n
    rw [dist_eq_norm] at hh
    convert hh using 1; ring
  have hwν : WeakSequences.WeakCauchy ν := by
    apply WeakSequences.weakCauchy_of_uniform_approx
    intro ε hε
    have hlim : Tendsto (fun n => (τ/2)*(1/2 : ℝ)^n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1)).const_mul (τ/2)
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
    refine ⟨(W N).seq,(W N).weak,fun i => ?_⟩
    rw [norm_sub_rev]
    exact (hdist i N).trans_lt (hN N le_rfl)
  refine ⟨⋂ n, K n,hcompact,Set.mem_iInter.mpr (fun n => (W n).zero_mem),
    ν,hwν,fun i => ?_,fun i => ?_⟩
  · apply supported_intersection_of_uniform K huniform
    intro n
    apply (supported_isClosed (K n)).mem_of_tendsto (hν i)
    filter_upwards [eventually_ge_atTop n] with m hm
    exact supported_mono (hanti hm) ((W m).support i)
  · have hh := hdist i 0
    change ‖μ i-ν i‖ ≤ _ at hh
    simp only [pow_zero,mul_one] at hh
    exact hh.trans_lt (by linarith)

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.FreeSpace
open Filter Topology
variable {M : Type uM} [MetricSpace M] [Zero M] [CompleteSpace M]

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


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.bounded_cauchy_compact_reduction.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.bounded_cauchy_compact_reduction.{uM}
