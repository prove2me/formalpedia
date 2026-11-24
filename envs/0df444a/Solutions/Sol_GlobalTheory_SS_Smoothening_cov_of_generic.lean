-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.cov_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:38:57.807855+00:00
-- url     : https://prove2.me/submissions/1f209421-27ec-4ca0-b853-4f266d55b126

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
import Theorems.Thm_GlobalTheory_SS_Smoothening_Cov_empty
import Theorems.Thm_GlobalTheory_SS_Smoothening_Cov_union
import Theorems.Thm_GlobalTheory_SS_Smoothening_unit_or_dvd

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
theorem _root_.solution [IsNoetherianRing B] (π : R) (Q : Pts R B)
    (hQ : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Q R' a → Unr π R')
    (H : ∀ E : Pts R B, (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Q R' a) →
      (∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R') (a : B →ₐ[R] R'), E R' a) →
      ∃ f, f ∉ vanish π E ∧ Cov K (fun R' _ _ a => E R' a ∧ IsUnit (a f) : Pts R B)) : Cov K Q := by
  suffices h : ∀ (I : Ideal B) (E : Pts R B),
      (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Q R' a) → vanish π E = I → Cov K E from
    h _ Q (fun _ _ _ _ h => h) rfl
  intro I
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    rintro E hE rfl
    by_cases hne : ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R') (a : B →ₐ[R] R'), E R' a
    · obtain ⟨f, hf, hc⟩ := H E hE hne
      let E' : Pts R B := fun R' _ _ a => E R' a ∧ algebraMap R R' π ∣ a f
      have h' : Cov K E' := by
        refine ih (vanish π E') (lt_of_le_of_ne (fun b hb R' _ _ a ha => hb R' a ha.1) fun e => hf ?_) E'
          (fun R' _ _ a ha => hE R' a ha.1) rfl
        rw [e]; exact fun R' _ _ a ha => ha.2
      exact hc.union h' fun R' _ _ a ha =>
        (unit_or_dvd (hQ R' a (hE R' a ha)) (a f)).imp (fun h => ⟨ha, h⟩) fun h => ⟨ha, h⟩
    · exact Cov.empty fun R' _ _ a ha => hne ⟨R', _, _, a, ha⟩
end GlobalTheory.SS.Smoothening
