-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.mapsInto_colMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:09:08.45677+00:00
-- url     : https://prove2.me/submissions/536c513a-6f79-48e9-82f5-6bffb9f823e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_chainLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [Fintype n] [DecidableEq n]
namespace GlobalTheory.RootEx.UnfoldShape
namespace _root_.GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution {ϖ : 𝒪[k]} {L' : Submodule 𝒪[k] (n' → k)}
    {Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)} {y : Fin c → (n ⊕ Fin c → k)}
    (hy : ∀ i, (ϖ : k) ^ (i.val + 2) • y i ∈ Λ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.MapsInto (_root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.chainLat ϖ (c + 1) L') Λ := by
  intro v hv
  obtain ⟨-, ha⟩ := _root_.GlobalTheory.RootEx.UnfoldShape.mem_chainLat.1 hv
  choose a ha using ha
  have hsum : _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y *ᵥ v = ∑ i : Fin c, a i.succ • ((ϖ : k) ^ (i.val + 2) • y i) := by
    funext r
    simp only [Matrix.mulVec, dotProduct, _root_.GlobalTheory.RootEx.UnfoldShape.colMat, Matrix.of_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Subring.smul_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i.succ, Fin.val_succ]
    ring
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hy i)
end _root_.GlobalTheory.RootEx.UnfoldShape
end GlobalTheory.RootEx.UnfoldShape
