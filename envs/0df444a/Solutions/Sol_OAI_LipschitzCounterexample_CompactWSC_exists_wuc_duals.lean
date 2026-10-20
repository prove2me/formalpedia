-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.exists_wuc_duals
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:16:58.477487+00:00
-- url     : https://prove2.me/submissions/a173e385-926b-44ba-b23b-a6ae1bdf9fa0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/WUCDuals.lean:L73-L94
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.exists_wuc_duals. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BlockSelection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothMultiplier
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_DetectingSequence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCFunctions
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCDuals
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_wuc_functions

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

-- ---- from OAI.Analysis.LipschitzEquivalence.SmoothRows ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSpace
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSpace
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSubtypeSpaceMemSubmoduleRealSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSubtypeSpaceMemSubmoduleSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeSpaceMemSubmoduleSupported
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealContinuousLinearMapIdSubtypeSpaceMemSubmoduleSupported
theorem dual_molecular {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (a : MolecularData H) (T : Space H →L[ℝ] ℝ) :
    T a.vector = molPair a (fun p => T (point p)) := by
  simp only [MolecularData.vector,map_sum,map_smul,map_sub,smul_eq_mul,molPair,LinearMap.coe_mk,AddHom.coe_mk]

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.WUCDuals ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSpace_1
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSpace_1
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSubtypeSpaceMemSubmoduleRealSupported_1
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSubtypeSpaceMemSubmoduleSupported_1
theorem dual_bound_on_support {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {K : Set H} (h0 : (0:H) ∈ K)
    (T : Space H →L[ℝ] ℝ) (f : H → ℝ) {L : ℝ≥0} (hf : LipschitzOnWith L f K)
    (hT : ∀ x ∈ K, T (point x) = f x-f 0) (u : Space H) (hu : u ∈ supported K) :
    |T u| ≤ L*‖u‖ := by
  obtain ⟨g,hg,hfg⟩ := hf.extend_real
  let G := test (normalized g hg)
  have hk : supported K ≤ (T-G).ker := by
    apply supported_le_ker
    intro x hx
    change T (point x)-G (point x) = 0
    have he : G (point x) = g x-g 0 := test_point (normalized g hg) x
    rw [hT x hx,he,hfg hx,hfg h0,sub_self]
  have he : T u = G u := sub_eq_zero.mp (hk hu)
  rw [he,← Real.norm_eq_abs]
  exact (norm_test_apply_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_normalized_le g hg) (norm_nonneg u))

theorem smooth_wuc_duals {K : Set H} (h0 : (0:H) ∈ K)
    (w : ℕ → Smooth H) (hw0 : ∀ i, (w i).val 0 = 0)
    (hLip : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) →
      LipschitzOnWith 2 (fun x => ∑ i ∈ Finset.range n, c i*(w i).val x) K) :
    ∃ T : ℕ → Space H →L[ℝ] ℝ,
      (∀ i, ‖T i‖ ≤ 2) ∧
      (∀ i x, x ∈ K → T i (point x) = (w i).val x) ∧
      ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ u : Space H, u ∈ supported K →
        |∑ i ∈ Finset.range n, c i*T i u| ≤ 2*‖u‖ := by
  classical
  have hsingle (i : ℕ) : LipschitzOnWith 2 (w i).val K := by
    have hc (j : ℕ) : |(if j=i then 1 else 0:ℝ)| ≤ 1 := by split_ifs <;> norm_num
    have h := hLip (i+1) (fun j => if j=i then 1 else 0) hc
    have he (x : H) : (∑ j ∈ Finset.range (i+1), (if j=i then 1 else 0:ℝ)*(w j).val x) = (w i).val x := by simp
    simpa only [he] using h
  have hex (i : ℕ) := (hsingle i).extend_real
  choose g hg hfg using hex
  let T := fun i => test (normalized (g i) (hg i))
  have hT (i : ℕ) (x : H) (hx : x ∈ K) : T i (point x) = (w i).val x := by
    change test (normalized (g i) (hg i)) (point x) = _
    rw [test_point]
    change g i x-g i 0 = _
    rw [← hfg i hx,← hfg i h0,hw0 i,sub_zero]
  refine ⟨T,fun i => ?_,hT,?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ) ≤ 2)
    intro u
    exact (norm_test_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_normalized_le (g i) (hg i)) (norm_nonneg u))
  · intro n c hc u hu
    let S : Space H →L[ℝ] ℝ := ∑ i ∈ Finset.range n, c i • T i
    have hp : ∀ x ∈ K, S (point x) =
        (∑ i ∈ Finset.range n, c i*(w i).val x)-(∑ i ∈ Finset.range n, c i*(w i).val 0) := by
      intro x hx
      simp only [S,sum_apply,smul_apply,smul_eq_mul,hT _ x hx,hw0,mul_zero,Finset.sum_const_zero,sub_zero]
    have hb := dual_bound_on_support h0 S _ (hLip n c hc) hp u hu
    simpa only [S,sum_apply,smul_apply,smul_eq_mul,NNReal.coe_ofNat] using hb

theorem exists_wuc_duals {K Q : Set H} (h0 : (0:H) ∈ K)
    (hQ : IsCompact Q) (hQc : Convex ℝ Q) (hKQ : K ⊆ Q)
    {C ρ α : ℝ} {μ : ℕ → Space H} (hC : 0 ≤ C) (hα : 0 < α)
    (hRich : (triangularRows K C ρ α μ).Rich) :
    ∃ (T : ℕ → Space H →L[ℝ] ℝ) (a : ℕ → RowItem K C ρ μ),
      (∀ i, ‖T i‖ ≤ 2) ∧ (∀ i, α/2 ≤ T i (a i).a.vector) ∧
      ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ u : Space H, u ∈ supported K →
        |∑ i ∈ Finset.range n, c i*T i u| ≤ 2*‖u‖ := by
  obtain ⟨w,a,hw0,hwdiag,hwLip⟩ := exists_wuc_functions hQ hQc hKQ hC hα hRich
  obtain ⟨T,hT,hpoint,hWUC⟩ := smooth_wuc_duals h0 w hw0
    (fun n c hc => (hwLip n c hc).mono hKQ)
  refine ⟨T,a,hT,fun i => ?_,hWUC⟩
  have he : T i (a i).a.vector = smoothPair (a i).a (w i) := by
    rw [dual_molecular]
    change (∑ j, (a i).a.coeff j*(_-_)) = ∑ j, (a i).a.coeff j*(_-_)
    apply Finset.sum_congr rfl
    intro j _
    change (a i).a.coeff j*(T i (point ((a i).a.p j))-T i (point ((a i).a.q j))) =
      (a i).a.coeff j*((w i).val ((a i).a.p j)-(w i).val ((a i).a.q j))
    rw [hpoint i _ ((a i).support j).1,hpoint i _ ((a i).support j).2]
  rw [he]
  exact hwdiag i

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSpace_1
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSpace_1
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSubtypeSpaceMemSubmoduleRealSupported_1
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSubtypeSpaceMemSubmoduleSupported_1


theorem solution.{uH} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_wuc_duals.{uH} := @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_wuc_duals.{uH}
