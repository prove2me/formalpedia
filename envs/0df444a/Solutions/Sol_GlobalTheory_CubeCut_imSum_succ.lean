-- Prove2me | solution 1 for GlobalTheory.CubeCut.imSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:39.819372+00:00
-- url     : https://prove2.me/submissions/95335b0c-94db-4965-9035-57223af8fb98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory GlobalTheory
open GlobalTheory
open GlobalTheory.CubeCut
variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]
variable {g : ℕ} {A B : Cube.{0} I K} (φ : Fin g → (A ⟶ B))
omit [LinearOrder I]
namespace GlobalTheory.CubeCut
theorem _root_.solution (i : Fin g) (s : Finset I) :
    imSum φ (i + 1) s = imSum φ i s ⊔ LinearMap.range ((φ i).app s).hom := by
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    by_cases h : (j : ℕ) < i
    · exact le_sup_of_le_left (le_iSup_of_le j (le_iSup_of_le h le_rfl))
    · have hji : j = i := Fin.ext (by omega)
      subst hji
      exact le_sup_right
  · exact sup_le (iSup₂_le fun j hj => le_iSup_of_le j (le_iSup_of_le (by omega) le_rfl))
      (le_iSup_of_le i (le_iSup_of_le (by omega) le_rfl))
end GlobalTheory.CubeCut
