-- Prove2me | solution 1 for GlobalTheory.T.exists_hensel_root_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:19:36.749224+00:00
-- url     : https://prove2.me/submissions/2564a1cd-74b1-4a7b-a1c8-07711e811ea8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHenselRootResidue
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHenselRootResidueStatement
import Theorems.Thm_GlobalTheory_exists_root_lift_of_residue_map


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
theorem _root_.solution : ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (φ : A →+* R) (α : A →+* V) (σ : ResidueField R →+* ResidueField V), (∀ a, σ (residue R (φ a)) = residue V (α a)) → ∀ (θ : R) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → IsUnit ((q.derivative.map φ).eval θ) → ∃ η : V, (q.map α).eval η = 0 ∧ residue V η = σ (residue R θ) := by
  first | exact @GlobalTheory.exists_root_lift_of_residue_map | exact GlobalTheory.exists_root_lift_of_residue_map | (intros; apply GlobalTheory.exists_root_lift_of_residue_map <;> assumption)
end _root_.GlobalTheory.T
