-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.vanish_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:43.494138+00:00
-- url     : https://prove2.me/submissions/b076f041-70d9-43aa-80b8-d10ea6a89964

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp
import Theorems.Thm_GlobalTheory_SS_Smoothening_unit_or_dvd
import Theorems.Thm_GlobalTheory_SS_Smoothening_exists_lift
import Theorems.Thm_GlobalTheory_SS_Dil_exists_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R K B C : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution (π : R) (E : Pts R B)
    (hE : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R') (f : B) (b : Localization.Away f) :
    b ∈ (vanish π E).map (algebraMap B (Localization.Away f)) ↔
      ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : Localization.Away f →ₐ[R] R'),
        E R' (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f))) → algebraMap R R' π ∣ a b := by
  constructor
  · intro hb
    have : (vanish π E).map (algebraMap B (Localization.Away f)) ≤
        vanish π (fun R' _ _ a => E R' (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f)))) :=
      Ideal.map_le_iff_le_comap.2 fun x hx R' _ _ a ha => hx R' _ ha
    exact this hb
  · intro hb
    obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj f b
    have h1 : x * f ∈ vanish π E := by
      intro R' _ _ a ha
      rw [map_mul]
      rcases unit_or_dvd (hE R' a ha) (a f) with h | h
      · obtain ⟨a', rfl⟩ := exists_lift f a h
        refine Dvd.dvd.mul_right ?_ _
        show _ ∣ a' (algebraMap B _ x)
        rw [← hx, map_mul]
        exact (hb R' a' ha).mul_right _
      · exact h.mul_left _
    have h2 := Ideal.mem_map_of_mem (algebraMap B (Localization.Away f)) h1
    rw [map_mul, ← hx, _root_.mul_assoc, ← pow_succ] at h2
    exact (Ideal.mul_unit_mem_iff_mem _ ((IsLocalization.Away.algebraMap_isUnit f).pow _)).1 h2
end GlobalTheory.SS.Smoothening
