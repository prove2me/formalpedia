-- Prove2me | solution 1 for GlobalTheory.RegBound.piece_extIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:14:07.628799+00:00
-- url     : https://prove2.me/submissions/e0757db9-ed05-4a89-bf6e-9a78a622370e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_contr_comp
import Theorems.Thm_GlobalTheory_RegBound_eq_of_contr
import Theorems.Thm_GlobalTheory_RegBound_contr_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.RegBound
theorem _root_.solution (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    piece (extIdeal L I) e = extSub L (piece I e) := by
  ext F
  refine ⟨fun hF φ => ⟨contr_isHomogeneous φ hF.1, hF.2 φ⟩, fun hF => ⟨?_, fun φ => (hF φ).2⟩⟩
  have : F = homogeneousComponent e F := eq_of_contr (K := K) fun φ => by
    rw [contr_comp, homogeneousComponent_eq_self (hF φ).1]
  rw [this]
  exact homogeneousComponent_isHomogeneous _ _
end GlobalTheory.RegBound
