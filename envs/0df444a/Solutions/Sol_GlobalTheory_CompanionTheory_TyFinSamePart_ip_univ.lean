-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSamePart.ip_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:50:31.630223+00:00
-- url     : https://prove2.me/submissions/acde2d57-2bf1-48e5-a47d-41967305d89e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSamePart
namespace GlobalTheory.CompanionTheory.TyFinSamePart
theorem _root_.solution {Γ : Type} [Group Γ] [Fintype Γ] (a c : Γ → ℂ) :
    ip Set.univ a c = (Fintype.card Γ : ℂ)⁻¹ * ∑ g, a g⁻¹ * c g := by
  simp [ip, Set.ncard_univ, Nat.card_eq_fintype_card]
end GlobalTheory.CompanionTheory.TyFinSamePart
