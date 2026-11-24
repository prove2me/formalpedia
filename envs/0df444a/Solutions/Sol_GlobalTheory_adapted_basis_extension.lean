-- Prove2me | solution 1 for GlobalTheory.adapted_basis_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:08.869376+00:00
-- url     : https://prove2.me/submissions/5ced5f1b-f020-46f0-a16f-bb7f99561996

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLinearIndependentRatBasisAdaptedSubspace
import Theorems.Thm_GlobalTheory_AdaptedFamilyIwasawaDecomposition_exists_adapted_family


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)) (hIL : I ≤ L)
    (hg : Module.finrank ℚ L = g) :
    ∃ rk : ℕ, rk ≤ g ∧ ∃ ε : Fin g → Fin r → ℚ, LinearIndependent ℚ ε ∧ (∀ i, ε i ∈ L) ∧
      (∀ i : Fin g, i.val < rk → ε i ∈ I) ∧
        ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i | i.val < rk}) := by
  first
  | exact @_root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family
  | exact _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family
  | (apply _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family ..)
end GlobalTheory
