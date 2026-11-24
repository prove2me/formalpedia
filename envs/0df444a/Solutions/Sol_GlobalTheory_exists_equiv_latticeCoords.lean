-- Prove2me | solution 1 for GlobalTheory.exists_equiv_latticeCoords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:57.568242+00:00
-- url     : https://prove2.me/submissions/4ec2cc41-69a9-44d5-bc12-bb9f4c3f923e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DbarSolveComplexTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (n : ℕ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)),
      (∀ ν : Fin n → ℤ, T (fun k => (ν k : ℝ)) ∈ Λ) ∧
      ∀ l : Λ, ∃ ν : Fin n → ℤ, T.symm l = fun k => (ν k : ℝ) := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  let b0 := Module.finBasis ℤ Λ
  let b := b0.ofZLatticeBasis ℝ Λ
  refine ⟨_, b.equivFunL.symm, ?_, ?_⟩
  · intro ν
    have : b.equivFunL.symm (fun k => (ν k : ℝ)) = ∑ k, (ν k : ℝ) • b k :=
      b.equivFun_symm_apply _
    rw [this]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    refine Submodule.smul_mem _ _ ?_
    simp [b]
  · intro l
    refine ⟨fun k => b0.repr l k, ?_⟩
    funext k
    have := Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b0 l k
    simpa [b] using this
end GlobalTheory
