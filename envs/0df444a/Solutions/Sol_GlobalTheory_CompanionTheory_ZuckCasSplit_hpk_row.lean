-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:31:36.413413+00:00
-- url     : https://prove2.me/submissions/8eb47037-b90a-4542-bb6d-3bb37b88483b

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckCasSplit
open Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk)
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckCasSplit
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    ∃ (j₀ : Fin (2 * r + k + 1)) (s : ℂ), s * s = 1 ∧ (∀ j, Formalism.QuantumDeterminants.Hpk k r i j = if j = j₀ then s else 0) ∧
      ∀ j, Formalism.QuantumDeterminants.Hpk k r j₀ j = if j = i then s else 0 := by
  have hi := i.2
  by_cases h : r ≤ i.1 ∧ i.1 ≤ r + k
  · refine ⟨i, if i.1 = r + k then -1 else 1, by split_ifs <;> simp, fun j => ?_, fun j => ?_⟩ <;>
    · have hj := j.2
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
  · refine ⟨⟨2 * r + k - i.1, by omega⟩, 1, by simp, fun j => ?_, fun j => ?_⟩ <;>
    · have hj := j.2
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
end GlobalTheory.CompanionTheory.ZuckCasSplit
