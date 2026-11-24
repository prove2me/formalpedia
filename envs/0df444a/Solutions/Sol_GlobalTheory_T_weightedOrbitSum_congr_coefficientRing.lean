-- Prove2me | solution 1 for GlobalTheory.T.weightedOrbitSum_congr_coefficientRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:20:12.780981+00:00
-- url     : https://prove2.me/submissions/3456a6d9-70fb-46b9-9dfb-a27bd73fcdc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeightedOrbitSumCongrCoefficientRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeightedOrbitSumCongrCoefficientRingStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_orbSum_congr_coe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A] [Algebra O' A] (G : Subgroup Aˣ) (X : Set (Submodule O A)) (X' : Set (Submodule O' A)), (∀ L ∈ X, ∃ L' ∈ X', (L' : Set A) = L) → (∀ L' ∈ X', ∃ L ∈ X, (L : Set A) = L') → intUnits O A ⊓ G = intUnits O' A ⊓ G → orbSum O' G X' (fun _ => 1) = orbSum O G X (fun _ => 1) := by
  first | exact @GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe | exact GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe | (intros; apply GlobalTheory.UnitLemma.Orbit.orbSum_congr_coe <;> assumption)
end _root_.GlobalTheory.T
