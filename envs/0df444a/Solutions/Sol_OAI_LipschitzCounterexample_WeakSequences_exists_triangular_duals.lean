-- Prove2me | solution 1 for OAI.LipschitzCounterexample.WeakSequences.exists_triangular_duals
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:42:20.890786+00:00
-- url     : https://prove2.me/submissions/d302a185-4fc8-4b9a-b653-67f61579eda7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/TriangularDuals.lean:L13-L57
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.WeakSequences.exists_triangular_duals. The node keeps its source
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
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_bidual_separate_finite

-- ---- from OAI.Analysis.LipschitzEquivalence.TriangularDuals ----
namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample.WeakSequences
open scoped Topology BigOperators
open Filter Set
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_triangular_duals {u : ℕ → E} {φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ}
    (hφ : ∀ f, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f)))
    {d : ℝ} (hd : 0 < d)
    (hfar : ∀ x : E, d ≤ ‖φ-NormedSpace.inclusionInDoubleDual ℝ E x‖) (N : ℕ) :
    ∃ (f : Fin N → E →L[ℝ] ℝ) (v : Fin N → ℕ),
      (∀ j, ‖f j‖ = 1 ∧ d/2 < φ (f j)) ∧
      (∀ i j, j ≤ i → d/4 < f j (u (v i))) ∧
      (∀ i j, i < j → f j (u (v i)) = 0) := by
  classical
  induction N with
  | zero => exact ⟨Fin.elim0,Fin.elim0,by simp,by simp,by simp⟩
  | succ N ih =>
    obtain ⟨f,v,hf,hhigh,hlow⟩ := ih
    obtain ⟨g,hgnorm,hgzero,hgφ⟩ := bidual_separate_finite φ hd hfar (fun i => u (v i))
    let F : Fin (N+1) → E →L[ℝ] ℝ := Fin.snoc f g
    have hF (j : Fin (N+1)) : ‖F j‖ = 1 ∧ d/2 < φ (F j) := by
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa [F] using And.intro hgnorm hgφ
      · simpa [F] using hf i
    have hev (j : Fin (N+1)) : ∀ᶠ k in atTop, d/4 < F j (u k) :=
      (tendsto_order.1 (hφ (F j))).1 _ (by linarith [(hF j).2])
    have hall : ∀ᶠ k in atTop, ∀ j : Fin (N+1), d/4 < F j (u k) :=
      Filter.eventually_all.mpr hev
    obtain ⟨k,hk⟩ := hall.exists
    refine ⟨F,Fin.snoc v k,hF,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro j _
        simpa using hk j
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h
          simp at h
        · intro h
          simpa [F] using hhigh i j (by simpa using h)
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro j h
        exact False.elim (not_lt_of_ge (Fin.le_last j) h)
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _
          simpa [F] using hgzero i
        · intro h
          simpa [F] using hlow i j (by simpa using h)

end LipschitzCounterexample.WeakSequences
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
open scoped Topology BigOperators
open Filter Set


theorem solution.{uE} : type_of% @_root_.OAI.LipschitzCounterexample.WeakSequences.exists_triangular_duals.{uE} := @_root_.OAI.LipschitzCounterexample.WeakSequences.exists_triangular_duals.{uE}
