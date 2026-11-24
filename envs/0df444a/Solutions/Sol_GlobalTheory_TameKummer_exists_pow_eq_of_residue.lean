-- Prove2me | solution 1 for GlobalTheory.TameKummer.exists_pow_eq_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:34.341778+00:00
-- url     : https://prove2.me/submissions/853c7b4c-4b3d-45cf-b2aa-b8fc44c3ac20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree

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
theorem _root_.solution {R : Type*} [CommRing R] [HenselianLocalRing R] {n : ℕ}
    (hn : IsUnit (n : R)) {u : R} (hu : IsUnit u) (c : ResidueField R)
    (hc : c ^ n = residue R u) : ∃ v : R, v ^ n = u ∧ residue R v = c := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨a, rfl⟩ := residue_surjective c
  have ha : IsUnit a := by
    have : IsUnit (residue R a ^ n) := hc ▸ hu.map _
    exact (isUnit_map_iff (residue R) a).1 ((isUnit_pow_iff hn0).1 this)
  obtain ⟨v, hv, hva⟩ := HenselianLocalRing.is_henselian (X ^ n - C u : R[X])
    (monic_X_pow_sub_C u hn0) a
    (by rw [← residue_eq_zero_iff]; simp [hc])
    (by simpa [derivative_X_pow] using hn.mul (ha.pow _))
  refine ⟨v, ?_, ?_⟩
  · simpa [sub_eq_zero] using hv
  · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hva
    exact hva
end GlobalTheory.TameKummer
