-- Prove2me | solution 1 for GordanGenProof.gcone_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:30.246676+00:00
-- url     : https://prove2.me/submissions/340f4e52-e1d9-4f3c-9bf3-b9f75c36b94d

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset
namespace GordanGenProof
theorem _root_.solution {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℚ) (X : Set (Fin n → ℚ))
    (h0 : (0 : Fin n → ℚ) ∈ X) (hadd : ∀ x ∈ X, ∀ y ∈ X, x + y ∈ X)
    (hsmul : ∀ r : ℚ, 0 ≤ r → ∀ x ∈ X, r • x ∈ X) (hf : ∀ i ∈ s, f i ∈ X) :
    gcone s f ⊆ X := by
  rintro x ⟨c, hc, rfl⟩
  exact Finset.sum_induction _ (· ∈ X) (fun a b ha hb => hadd a ha b hb) h0
    (fun i hi => hsmul _ (hc i hi) _ (hf i hi))
end GordanGenProof
