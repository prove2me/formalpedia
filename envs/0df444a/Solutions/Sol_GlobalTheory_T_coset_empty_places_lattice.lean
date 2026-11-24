-- Prove2me | solution 1 for GlobalTheory.T.coset_empty_places_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:34.986551+00:00
-- url     : https://prove2.me/submissions/a94e31bc-3ae3-4670-ae63-a3e3d129e198

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetEmptyPlacesLattice
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetEmptyPlacesLatticeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_cosetOff_empty_eq_latCoset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (I : Ideal (𝓞 F)) (x0 : ι → F), cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | exact GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | (intros; apply GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset <;> assumption)
end _root_.GlobalTheory.T
