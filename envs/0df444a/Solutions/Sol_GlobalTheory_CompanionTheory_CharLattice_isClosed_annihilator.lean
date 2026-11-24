-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharLattice.isClosed_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:22:51.292238+00:00
-- url     : https://prove2.me/submissions/943066cb-d2b7-4b33-b517-3f86e2b204ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CharacterAnnihilatorIntegerLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharLattice
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CharLattice
theorem _root_.solution (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (b : k) :
    IsClosed (annihilator ψ n b : Set (Fin n → k)) := by
  have e : (annihilator ψ n b : Set (Fin n → k)) =
      ⋂ (t : Fin n → k) (_ : ∀ j, t j ∈ 𝒪[k]), {x | ψ (b * (t ⬝ᵥ x)) = 1} := by
    ext x
    simp only [Set.mem_iInter]
    rfl
  rw [e]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_eq (hψ.comp (continuous_const.mul (continuous_const.dotProduct continuous_id)))
      continuous_const
end GlobalTheory.CompanionTheory.CharLattice
