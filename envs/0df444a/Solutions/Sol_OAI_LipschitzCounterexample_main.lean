-- Prove2me | solution 1 for OAI.LipschitzCounterexample.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:19:27.013885+00:00
-- url     : https://prove2.me/submissions/aca60d91-4536-4d12-a9b2-e693780ea7fd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/Main.lean:L8-L9
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.LipschitzCounterexample.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_LipschitzCounterexample_main) verbatim and is proved by it.
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCOperator
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactHilbertWSC
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_wuc_duals
import Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_triangularRows_rich
import Theorems.Thm_OAI_LipschitzCounterexample_Criterion_assemble
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_hasCompactReduction
import Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_wsc_of_compact_supported
import Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_completely_continuous_of_compact_reduction
import Theorems.Thm_OAI_LipschitzCounterexample_SeparatingStages_D_local_orthogonality
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_nonconvergent_biddual_gap
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_schur_cauchy
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_uniform_tails_of_cauchy

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

theorem WeakCauchy.bounded {u : ℕ → E} (hu : WeakCauchy u) :
    ∃ C : ℝ, ∀ n, ‖u n‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun n => NormedSpace.inclusionInDoubleDual ℝ E (u n))
    (fun f => by
      obtain ⟨C, hC⟩ := (hu f).isBounded_range.exists_norm_le
      exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩)
  refine ⟨C, fun n => ?_⟩
  have h := (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map (u n)
  exact h ▸ hC n

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

-- ---- from OAI.Analysis.LipschitzEquivalence.HilbertBijection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace
open HilbertSlots RadialBudget SlowAngles RotatingStages

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter

theorem h_lipschitz : LipschitzWith (26/25) h :=
  lipschitzWith_iff_norm_sub_le.mpr (fun x y => (h_bounds x y).2)

theorem h_symm_lipschitz : LipschitzWith (25/24) h.symm := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  have hb := (h_bounds (h.symm x) (h.symm y)).1
  rw [h.apply_symm_apply,h.apply_symm_apply] at hb
  norm_num only [NNReal.coe_div,NNReal.coe_ofNat]
  linarith

theorem q_norm : ‖q‖ ≤ (51/25 : ℝ) :=
  FreeSpace.norm_linearize_le D D_lipschitz D_zero

end LipschitzCounterexample.SeparatingStages

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

end LipschitzCounterexample.FreeSpace

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

end LipschitzCounterexample.CoordinateSpaces

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.LinearizationContinuity ----
namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.SeparatingStages
open LocalGeometry LocalizedLinearization

theorem D_localOrthogonality : LocalOrthogonality D := by
  intro I _ x hx
  obtain ⟨r,hr,l,S,hS,_,hD⟩ := D_local_orthogonality x hx
  refine ⟨r,hr,l,S,hS,fun i y hy => ?_⟩
  have he : CoordinateSpaces.tail l (D y) = HilbertSlots.tailCLM l (D y) := by
    apply lp.ext
    funext n
    apply PiLp.ext
    intro a
    rw [CoordinateSpaces.tail_coord,HilbertSlots.tailCLM_coord]
    split_ifs <;> rfl
  rw [he]
  exact hD i y hy

theorem q_completelyContinuous : WeakSequences.CompletelyContinuous q :=
  completely_continuous_of_compact_reduction FreeSpace.hasCompactReduction D
    D_lipschitz D_zero D_localOrthogonality

theorem main_of_free_wsc
    (hW : WeakSequences.WeakSequentiallyComplete (FreeSpace.Space M)) : MainClaim :=
  Criterion.assemble q h (fun x => q_point x) h_zero h_lipschitz h_symm_lipschitz q_norm hW
    q_completelyContinuous

end LipschitzCounterexample.SeparatingStages

end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.WUCOperator ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample.WeakSequences
open scoped BigOperators NNReal ENNReal Topology
open Filter
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniform_small_of_wuc (T : ℕ → E →L[ℝ] ℝ)
    (hT : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ x : E,
      |∑ i ∈ Finset.range n, c i*T i x| ≤ 2*‖x‖)
    {u : ℕ → E} (hu : WeakCauchy u) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ j ≥ N, ∀ k, |T j (u k)| < ε := by
  let S := wucOperator T hT
  obtain ⟨N,hN⟩ := uniform_tails_of_cauchy (fun k => S (u k))
    (schur_cauchy (hu.map S)) ε hε
  refine ⟨N,fun j hj k => ?_⟩
  have hcoord := lp.norm_apply_le_norm (by norm_num : (1:ℝ≥0∞) ≠ 0)
    (tailL1 N (S (u k))) j
  simp only [tailL1_apply,ite_eq_left hj,Real.norm_eq_abs] at hcoord
  exact hcoord.trans_lt (hN k)

end LipschitzCounterexample.WeakSequences
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.CompactHilbertWSC ----
namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSpace_2
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSpace_2
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSubtypeSpaceMemSubmoduleRealSupported_2
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSubtypeSpaceMemSubmoduleSupported_2
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeSpaceMemSubmoduleSupported_1
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealContinuousLinearMapIdSubtypeSpaceMemSubmoduleSupported_1
theorem compact_supported_wsc (K : Set H) (hK : IsCompact K) (h0 : (0:H) ∈ K) :
    WeakSequences.WeakSequentiallyComplete (supported K) := by
  intro u hu
  by_contra hno
  let : CompleteSpace (supported K) := (supported_isClosed K).completeSpace_coe
  obtain ⟨φ,d,hd,hφ,hfar⟩ := WeakSequences.nonconvergent_biddual_gap hu hno
  obtain ⟨B,hB⟩ := hu.bounded
  let C := max B 1
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have huC (n : ℕ) : ‖u n‖ ≤ C := (hB n).trans (le_max_left _ _)
  let α := d/32
  let ρ := α/16
  have hα : 0 < α := div_pos hd (by norm_num)
  have hρ : 0 < ρ := div_pos hα (by norm_num)
  have hρα : ρ ≤ α/4 := by dsimp [ρ]; linarith
  have hαd : 32*α ≤ d := by dsimp [α]; linarith
  have hRich := triangularRows_rich h0 u φ hφ hd hC hρ hα hρα hαd huC hfar
  let Q := closure (convexHull ℝ K)
  have hQ : IsCompact Q := (hK.totallyBounded.convexHull.closure).isCompact_of_isClosed isClosed_closure
  have hQc : Convex ℝ Q := (convex_convexHull ℝ K).closure
  have hKQ : K ⊆ Q := (subset_convexHull ℝ K).trans subset_closure
  obtain ⟨T,a,hT,hdiag,hWUC⟩ := exists_wuc_duals h0 hQ hQc hKQ hC.le hα hRich
  let S : ℕ → supported K →L[ℝ] ℝ := fun i => (T i).comp (supported K).subtypeL
  have hS : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ x : supported K,
      |∑ i ∈ Finset.range n, c i*S i x| ≤ 2*‖x‖ :=
    fun n c hc x => hWUC n c hc x.val x.property
  obtain ⟨N,hN⟩ := WeakSequences.uniform_small_of_wuc S hS hu (show 0<α/4 by positivity)
  obtain ⟨k,hk⟩ := (a N).close
  have hclose : |T N (u k)-T N (a N).a.vector| < 2*ρ := by
    rw [← map_sub,← Real.norm_eq_abs]
    exact ((T N).le_opNorm _).trans_lt (by nlinarith [hT N,norm_nonneg (T N),norm_nonneg ((u k : Space H)-(a N).a.vector)])
  have hsmall : |T N (u k)| < α/4 := hN N le_rfl k
  have hlarge := hdiag N
  have hl := (abs_lt.mp hclose).1
  have hs := (abs_lt.mp hsmall).2
  dsimp [ρ] at hl
  linarith

theorem hilbert_free_wsc : WeakSequences.WeakSequentiallyComplete (Space H) :=
  FreeSpace.wsc_of_compact_supported compact_supported_wsc

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.Main ----
namespace OAI

noncomputable section
namespace LipschitzCounterexample

theorem main : MainClaim :=
  SeparatingStages.main_of_free_wsc CompactWSC.hilbert_free_wsc

end LipschitzCounterexample

end

end OAI

-- ---- mission target ----
open OAI OAI.LipschitzCounterexample
universe uE uF

namespace OAI
namespace LipschitzCounterexample
theorem _root_.solution : MainClaim := by
  first
    | exact OAI.LipschitzCounterexample.main
    | (apply OAI.LipschitzCounterexample.main <;> assumption)
    | (intros; apply OAI.LipschitzCounterexample.main <;> assumption)
end LipschitzCounterexample
end OAI
