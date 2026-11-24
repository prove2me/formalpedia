-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.card_of_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:51:59.721204+00:00
-- url     : https://prove2.me/submissions/2a69c4c2-f039-4b59-92a1-60565c476288

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
theorem _root_.solution {α β : Type*} [Finite α] [Finite β] (f : α → β) (c : ℕ)
    (h : ∀ b, Nat.card {a // f a = b} = c) : Nat.card α = Nat.card β * c := by
  classical
  haveI := Fintype.ofFinite β
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]
  simp [h, Nat.card_eq_fintype_card, mul_comm]
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
