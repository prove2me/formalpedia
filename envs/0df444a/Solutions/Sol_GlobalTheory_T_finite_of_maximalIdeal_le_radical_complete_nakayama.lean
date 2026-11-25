-- Prove2me | solution 1 for GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:24:29.566543+00:00
-- url     : https://prove2.me/submissions/67ef6cb6-194e-438c-b880-834dff3bd63e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfMaximalIdealLeRadicalCompleteNakayama
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfMaximalIdealLeRadicalCompleteNakayamaStatement
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B R : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ → maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite → ψ.Finite := by
  first | exact @GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical | exact GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical | (intros; apply GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical <;> assumption)
end _root_.GlobalTheory.T
