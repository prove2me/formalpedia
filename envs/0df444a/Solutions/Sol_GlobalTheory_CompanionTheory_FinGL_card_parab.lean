-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.card_parab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:36.639309+00:00
-- url     : https://prove2.me/submissions/9ae2eaeb-6d3e-4eab-83ef-6d0f810a7638

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_parabCoord_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_parabCoord_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGL
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
namespace GlobalTheory.CompanionTheory.FinGL
theorem _root_.solution : Nat.card (parab K b) =
    Fintype.card K ^ Fintype.card {p : ι × ι // b p.1 < b p.2} *
      ∏ c, Nat.card (GL {i // b i = c} K) := by
  rw [Nat.card_eq_of_bijective _ ⟨parabCoord_injective K b, parabCoord_surjective K b⟩,
    Nat.card_prod, Nat.card_fun, Nat.card_pi, Nat.card_eq_fintype_card (α := K),
    Nat.card_eq_fintype_card (α := {p : ι × ι // b p.1 < b p.2})]
end GlobalTheory.CompanionTheory.FinGL
