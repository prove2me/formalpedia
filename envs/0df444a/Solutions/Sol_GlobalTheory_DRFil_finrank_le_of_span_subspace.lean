-- Prove2me | solution 1 for GlobalTheory.DRFil.finrank_le_of_span_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:15.688542+00:00
-- url     : https://prove2.me/submissions/0ad30bd8-d324-4570-af21-686d493d5d61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankMulLeFinrankDdROfSpans
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DRFil.actVdR_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
namespace GlobalTheory.DRFil
theorem _root_.solution {K F M : Type} [Field K] [CommRing F] [Nontrivial F] [Algebra K F]
    [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M] (D : Submodule K M)
    [FiniteDimensional K D] (h : Submodule.span F (D : Set M) = ⊤) :
    finrank F M ≤ finrank K D := by
  classical
  let bD := Module.finBasis K D
  let s : Finset M := Finset.univ.image fun i => ((bD i : D) : M)
  have hs : Submodule.span F (s : Set M) = ⊤ := by
    rw [eq_top_iff, ← h, Submodule.span_le]
    intro x hx
    have hx' := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hx'
    rw [← hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul F]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [s]))
  calc finrank F M = finrank F (⊤ : Submodule F M) := (finrank_top F M).symm
    _ = finrank F (Submodule.span F (s : Set M)) := by rw [hs]
    _ ≤ s.card := finrank_span_finset_le_card s
    _ ≤ (Finset.univ : Finset (Fin (finrank K D))).card := Finset.card_image_le
    _ = finrank K D := by simp
end GlobalTheory.DRFil
