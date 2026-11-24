-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.card_swap_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:26.472175+00:00
-- url     : https://prove2.me/submissions/cc73d03f-f274-4bf5-809c-d2521f2a5904

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup

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
theorem _root_.solution :
    Fintype.card {p : ι × ι // b p.2 < b p.1} = Fintype.card {p : ι × ι // b p.1 < b p.2} :=
  Fintype.card_congr
    { toFun := fun p => ⟨p.1.swap, p.2⟩
      invFun := fun p => ⟨p.1.swap, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end GlobalTheory.CompanionTheory.FinGL
