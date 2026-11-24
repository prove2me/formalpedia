-- Prove2me | solution 1 for GlobalTheory.T.unramified_ideal_locus_characterization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:52.219025+00:00
-- url     : https://prove2.me/submissions/9594e0a6-4119-4d55-825e-ce7cc3dc82f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Theorems.Thm_GlobalTheory_SS_dilatation_lowers_defect


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B] (E : ∀ (R' : Type) [CommRing R'] [Algebra R R'], (B →ₐ[R] R') → Prop), (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R') → ∀ (I : Ideal B), (∀ b, b ∈ I ↔ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → algebraMap R R' π ∣ a b) → ∀ (k : Type) [Field k] [Algebra R k] [Algebra k (B ⧸ I)] [IsScalarTower R k (B ⧸ I)], Function.Surjective (algebraMap R k) → Algebra.Smooth k (B ⧸ I) → Module.Free (B ⧸ I) (TensorProduct B (B ⧸ I) (KaehlerDifferential R B)) → ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'), Algebra.FiniteType R B' ∧ Module.Flat R B' ∧ Function.Injective φ ∧ (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R') (c : ℕ), E R' a → Defect a π (c + 1) → ∃ a' : B' →ₐ[R] R', a'.comp φ = a ∧ Defect a' π c := by
  first | exact @GlobalTheory.SS.dilatation_lowers_defect | exact GlobalTheory.SS.dilatation_lowers_defect | (intros; apply GlobalTheory.SS.dilatation_lowers_defect <;> assumption)
end _root_.GlobalTheory.T
