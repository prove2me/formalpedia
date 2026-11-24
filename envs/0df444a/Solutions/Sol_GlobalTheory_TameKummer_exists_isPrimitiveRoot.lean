-- Prove2me | solution 1 for GlobalTheory.TameKummer.exists_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:39:52.338799+00:00
-- url     : https://prove2.me/submissions/f48b4509-cf15-43b7-bcb6-bc18637ad1b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Theorems.Thm_GlobalTheory_TameKummer_exists_pow_eq_of_residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TameKummer
open IsLocalRing Polynomial
namespace GlobalTheory.TameKummer
theorem _root_.solution {R : Type*} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] {n : ℕ} (hn : IsUnit (n : R)) :
    ∃ v : R, IsPrimitiveRoot v n := by
  have : NeZero (n : ResidueField R) := ⟨by simpa using (hn.map (residue R)).ne_zero⟩
  obtain ⟨c, hc⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField R) n
  obtain ⟨v, hv, hvc⟩ := exists_pow_eq_of_residue hn isUnit_one c (by simpa using hc.pow_eq_one)
  refine ⟨v, hv, fun d hd => hc.dvd_of_pow_eq_one d ?_⟩
  rw [← hvc, ← map_pow, hd, map_one]
end GlobalTheory.TameKummer
