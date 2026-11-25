-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsZetaValues.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:13.635407+00:00
-- url     : https://prove2.me/submissions/571c6281-9cd9-4ec0-a7b8-472fd7aa1bab

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ZetaValueIdeals
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZetaValueIdeals_IsClassZeta_eqOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
namespace IsZetaValues
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {z z' : ClassGroup (𝓞 F) → ℚ} (h : IsZetaValues k z)
    (h' : IsZetaValues k z') : z = z' := by
  funext C
  obtain ⟨Z, hZ, e⟩ := h C
  obtain ⟨Z', hZ', e'⟩ := h' C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simpa using this
  have := hZ.eqOn hZ' hne
  rw [e, e'] at this
  exact_mod_cast this
end IsZetaValues
end GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
