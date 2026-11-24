-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpMain.card_ne_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:24.781018+00:00
-- url     : https://prove2.me/submissions/5e146e56-9c3a-4420-b15c-f6efe240f5dd

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardAffineHyperplaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardTwoAffineHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFunctionalsVanishingSubspaceStatement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumHyperplanesComplementFlags

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpMain
variable {k : Type} [Field k] [Fintype k] {n : ℕ} {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
  {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {red : Γ →* GL (Fin (n + 1)) k} {ρ : Γ →* Module.End ℂ V} {t : Module.End ℂ V}
  {v : Submodule k (Fin (n + 1) → k) → V}
namespace GlobalTheory.CompanionTheory.GapOpMain
theorem _root_.solution (M : Submodule k (Fin (n + 1) → k)) :
    (((Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ M)).card : ℕ) : ℂ) =
      (Fintype.card k : ℂ) ^ Module.finrank k M - 1 := by
  have h1 : Finset.univ.filter (fun x : Fin (n + 1) → k => x ≠ 0 ∧ x ∈ M) =
      (Finset.univ.filter (fun x : Fin (n + 1) → k => x ∈ M)).erase 0 := by
    ext x
    simp
  have h2 : (Finset.univ.filter (fun x : Fin (n + 1) → k => x ∈ M)).card =
      Fintype.card k ^ Module.finrank k M := by
    rw [← Fintype.card_subtype, ← Module.card_eq_pow_finrank]
  rw [h1, Finset.card_erase_of_mem (by simp), h2, Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos),
    Nat.cast_pow, Nat.cast_one]
end GlobalTheory.CompanionTheory.GapOpMain
