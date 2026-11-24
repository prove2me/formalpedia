-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.card_eq_of_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:51:58.955934+00:00
-- url     : https://prove2.me/submissions/1d2904f0-2757-4e4a-82cf-733e6ee24586

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.HenselStep
namespace GlobalTheory.CompanionTheory.UnrDens.HenselStep
theorem _root_.solution {W A B : Type*} (a : W → A) (b : W → B) (ha : Function.Surjective a)
    (hb : Function.Surjective b) (hab : ∀ w w', a w = a w' ↔ b w = b w') :
    Nat.card A = Nat.card B := by
  refine Nat.card_congr (Equiv.ofBijective (fun y => b (Function.surjInv ha y)) ⟨?_, ?_⟩)
  · intro y y' h
    have := (hab _ _).2 h
    simpa [Function.surjInv_eq] using this
  · intro z
    obtain ⟨w, rfl⟩ := hb z
    exact ⟨a w, (hab _ _).1 (Function.surjInv_eq ha _)⟩
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
