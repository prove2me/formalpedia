-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.card_same_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:24.297801+00:00
-- url     : https://prove2.me/submissions/077cff75-3f96-45ac-b368-f7d7f0d0fb88

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
    Fintype.card {p : ι × ι // b p.1 = b p.2} =
      ∑ c, Fintype.card {i // b i = c} * Fintype.card {i // b i = c} := by
  simp only [← Fintype.card_prod]
  rw [← Fintype.card_sigma]
  refine Fintype.card_congr
    { toFun := fun p => ⟨b p.1.2, ⟨p.1.1, p.2⟩, ⟨p.1.2, rfl⟩⟩
      invFun := fun x => ⟨(x.2.1.1, x.2.2.1), x.2.1.2.trans x.2.2.2.symm⟩
      left_inv := fun _ => rfl
      right_inv := ?_ }
  rintro ⟨c, ⟨i, hi⟩, ⟨j, hj⟩⟩
  subst hj
  rfl
end GlobalTheory.CompanionTheory.FinGL
