-- Prove2me | solution 2 for OAI.LipschitzCounterexample.FreeSpace.finite_escape_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:51:06.042997+00:00
-- url     : https://prove2.me/submissions/6410cf8b-c8df-4fd7-884f-0ec096144877

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/FiniteReduction.lean:L60-L138
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.FreeSpace.finite_escape_step. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_exists_vanishing_test
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_pairing_difference_le
import Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_lipschitz_effective_smul

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

theorem point_mem_supported {K : Set M} {x : M} (hx : x ∈ K) : point x ∈ supported K :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x,hx,rfl⟩)

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

theorem combination_mem_supported (a : M →₀ ℝ) {K : Set M}
    (ha : ∀ x ∈ a.support, x ∈ K) : Finsupp.linearCombination ℝ point a ∈ supported K := by
  rw [Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ (fun x hx => Submodule.smul_mem _ _ (point_mem_supported (ha x hx)))

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

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem supported_mono {K S : Set M} (h : K ⊆ S) : supported K ≤ supported S :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono h))

theorem Approximable.mono {μ : Space M} {K S : Set M} {ε : ℝ}
    (h : Approximable μ K ε) (hKS : K ⊆ S) : Approximable μ S ε := by
  obtain ⟨ν,hν,hn⟩ := h
  exact ⟨ν,supported_mono hKS hν,hn⟩

theorem test_eq_of_agree {K : Set M} (h0 : (0 : M) ∈ K)
    (f g : M → ℝ) {C D : ℝ≥0} (hf : LipschitzWith C f) (hg : LipschitzWith D g)
    (he : ∀ x ∈ K, f x = g x) {ν : Space M} (hν : ν ∈ supported K) :
    test (normalized f hf) ν = test (normalized g hg) ν := by
  have hker : supported K ≤ (test (normalized f hf)-test (normalized g hg)).ker := by
    apply supported_le_ker
    intro x hx
    change (f x-f 0)-(g x-g 0) = 0
    rw [he x hx,he 0 h0,sub_self]
  exact sub_eq_zero.mp (hker hν)

end LipschitzCounterexample.FreeSpace

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.FiniteReduction ----
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

omit [Zero M] in
theorem near_mono {A B : Finset M} (h : A ⊆ B) (δ : ℝ) : Near A δ ⊆ Near B δ := by
  rintro x ⟨a,ha,hxa⟩
  exact ⟨a,h ha,hxa⟩

omit [Zero M] in
theorem subset_near (A : Finset M) {δ : ℝ} (hδ : 0 ≤ δ) : (A : Set M) ⊆ Near A δ := by
  intro x hx
  exact ⟨x,hx,by simpa using hδ⟩

theorem prefix_finite_approx (μ : ℕ → Space M) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset M, (0 : M) ∈ A ∧ ∀ i < N, Approximable (μ i) (A : Set M) ε := by
  classical
  induction N with
  | zero => exact ⟨{0},by simp,by simp⟩
  | succ N ih =>
    obtain ⟨A,hA,hN⟩ := ih
    obtain ⟨a,ha⟩ := exists_finite_approx (μ N) hε
    refine ⟨A ∪ a.support,Finset.mem_union_left _ hA,?_⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · exact (hN i hi).mono (by intro x hx; exact Finset.mem_union_left _ hx)
    · exact ⟨Finsupp.linearCombination ℝ point a,
        combination_mem_supported a (fun x hx => Finset.mem_union_right _ hx),ha⟩

theorem cutoff_product_bound (f : M → ℝ) {C s : ℝ≥0} (hf : LipschitzWith C f)
    (hf0 : f 0 = 0) (hs : 0 < s) (x : M) : |f x * cutoff 0 s x| ≤ C*s := by
  have hfval : |f x| ≤ C*dist x 0 := by simpa [Real.dist_eq,hf0] using hf.dist_le_mul x 0
  rw [abs_mul,abs_of_nonneg (cutoff_nonneg 0 s x)]
  by_cases hz : cutoff 0 s x = 0
  · rw [hz,mul_zero]; positivity
  · have hx : dist x 0 < s := by
      by_contra h
      exact hz (cutoff_zero 0 hs (le_of_not_gt h))
    exact (mul_le_of_le_one_right (abs_nonneg _) (cutoff_le_one _ _ _)).trans
      (hfval.trans (mul_le_mul_of_nonneg_left hx.le C.coe_nonneg))

theorem finite_escape_step {μ : ℕ → Space M} {ε : ℝ} (hε : 0 < ε)
    {R : ℝ≥0} (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hfail : ∀ A : Finset M, (0 : M) ∈ A → ∃ i, ¬ Approximable (μ i) (Near A δ) ε)
    (p : ℕ) (A : Finset M) : ∃ i : ℕ, ∃ B : Finset M, ∃ g : M → ℝ,
      p < i ∧ (0 : M) ∈ B ∧
      LipschitzWith (3+(2/δ)*(2*R+2)) g ∧ g 0 = 0 ∧
      (∀ x ∈ Near A δ, g x = 0) ∧ (∀ x, g x ≠ 0 → x ∈ Near B δ) ∧
      ∀ hg : LipschitzWith (3+(2/δ)*(2*R+2)) g, ε/2 < |test (normalized g hg) (μ i)| := by
  classical
  obtain ⟨P,hP,hprefix⟩ := prefix_finite_approx μ hε (p+1)
  obtain ⟨i,hi⟩ := hfail (A ∪ P) (Finset.mem_union_right _ hP)
  have hip : p < i := by
    by_contra h
    apply hi
    exact ((hprefix i (Nat.lt_succ_of_le (le_of_not_gt h))).mono
      (by intro x hx; exact Finset.mem_union_right _ hx)).mono
        (subset_near _ (show (0 : ℝ) ≤ δ from δ.coe_nonneg))
  have hfar : ∀ ν : Space M, ν ∈ supported (Near (A ∪ P) δ) → ε ≤ ‖μ i-ν‖ := by
    intro ν hν
    exact le_of_not_gt (fun h => hi ⟨ν,hν,h⟩)
  obtain ⟨f,hf,hf0,hfA,hlarge⟩ := exists_vanishing_test (Near (A ∪ P) δ) (μ i) hfar
  let s : ℝ≥0 := 2*R+2
  have hs : 0 < s := by dsimp [s]; positivity
  let f' : M → ℝ := fun x => f x * cutoff 0 s x
  have hf' : LipschitzWith 3 f' := by
    simpa only [mul_one] using cutoff_product_lipschitz 0 hs f hf hf0
  have hf'0 : f' 0 = 0 := by simp [f',hf0]
  have hf'bound (x : M) : |f' x| ≤ s := by
    simpa only [NNReal.coe_one,one_mul] using cutoff_product_bound f hf hf0 hs x
  have hfeq : test (normalized f hf) (μ i) = test (normalized f' hf') (μ i) := by
    apply test_eq_of_agree (by simp) f f' hf hf' ?_ (hsupp i)
    intro x hx
    have hdist : dist x 0 ≤ (s : ℝ)/2 := by
      change dist x 0 ≤ (↑(2*R+2 : ℝ≥0))/2
      push_cast
      change dist x 0 ≤ (R : ℝ) at hx
      linarith
    simp [f',cutoff_one 0 hs hdist]
  let C : ℝ≥0 := 3+(2/δ)*s
  have hC : 0 < (3+C : ℝ≥0) := by dsimp [C]; positivity
  obtain ⟨a,ha⟩ := exists_finite_approx (μ i) (show 0 < ε/(8*(3+C : ℝ≥0)) by positivity)
  let B : Finset M := insert 0 a.support
  let g : M → ℝ := fun x => setCutoff (B : Set M) δ x * f' x
  have hg : LipschitzWith C g := by
    simpa only [one_mul,smul_eq_mul] using
      lipschitz_effective_smul f' (setCutoff (B : Set M) δ) hf' (setCutoff_lipschitz _ _)
        (A := 1) (P := s)
        (fun x => by rw [abs_of_nonneg (setCutoff_nonneg _ _ _)]; exact setCutoff_le_one _ _ _)
        (fun x _ => hf'bound x)
  refine ⟨i,B,g,hip,by simp [B],hg,by simp [g,hf'0],?_,?_,?_⟩
  · intro x hx
    have hz := hfA x (near_mono Finset.subset_union_left _ hx)
    simp [g,f',hz]
  · intro x hx
    have hcut : setCutoff (B : Set M) δ x ≠ 0 := fun h => hx (by simp [g,h])
    obtain ⟨y,hy,hxy⟩ := (Metric.infDist_lt_iff (show (B : Set M).Nonempty from
      ⟨0,by simp [B]⟩)).mp (setCutoff_nonzero hδ hcut)
    exact ⟨y,hy,hxy.le⟩
  · intro hg'
    have he (x : M) (hx : x ∈ (B : Set M)) : f' x = g x := by
      have hdist : Metric.infDist x (B : Set M) ≤ (δ : ℝ)/2 := by
        rw [Metric.infDist_zero_of_mem hx]
        positivity
      simp [g,setCutoff_one hδ hdist]
    have hdiff := pairing_difference_le (show (0 : M) ∈ (B : Set M) from by simp [B])
      f' g hf' hg' he (μ i) (Finsupp.linearCombination ℝ point a)
      (combination_mem_supported a (fun x hx => Finset.mem_insert_of_mem hx))
    have hl := hlarge hf
    rw [hfeq] at hl
    have heps : (3+C : ℝ≥0)*‖μ i-Finsupp.linearCombination ℝ point a‖ < ε/8 := by
      have hh := (lt_div_iff₀ (show (0 : ℝ) < 8*(3+C : ℝ≥0) by positivity)).mp ha
      push_cast at hh ⊢
      nlinarith
    have habs := le_abs_self (test (normalized f' hf') (μ i)-test (normalized g hg') (μ i))
    have habsg := le_abs_self (test (normalized g hg') (μ i))
    change |test (normalized f' hf') (μ i)-test (normalized g hg') (μ i)| ≤
      (3+C : ℝ≥0)*‖μ i-Finsupp.linearCombination ℝ point a‖ at hdiff
    linarith

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


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.FreeSpace.finite_escape_step.{uM} := @_root_.OAI.LipschitzCounterexample.FreeSpace.finite_escape_step.{uM}
