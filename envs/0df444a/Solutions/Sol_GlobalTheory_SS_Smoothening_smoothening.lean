-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.smoothening
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:26.297801+00:00
-- url     : https://prove2.me/submissions/eb56abe6-6193-4d70-8df6-8dc0062ae876

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
import Theorems.Thm_GlobalTheory_SS_Smoothening_cov_zero
import Theorems.Thm_GlobalTheory_SS_Smoothening_cov_succ
import Theorems.Thm_GlobalTheory_T_exists_defect_bound_of_smooth_away


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
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → PerfectField (IsLocalRing.ResidueField R) → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ (n : ℕ) (C : Fin n → Type) (_ : ∀ i, CommRing (C i)) (_ : ∀ i, Algebra R (C i)) (φ : ∀ i, B →ₐ[R] C i), (∀ i, Algebra.Smooth R (C i) ∧ IsOpenImmersion (spMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i)).toRingHom)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Unr π R' → ∃ (i : Fin n) (a' : C i →ₐ[R] R'), a'.comp (φ i) = a := by
  intro R K _ _ _ _ _ _ π hπ hk B _ _ _ _ hB
  have H : ∀ (c : ℕ) (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B],
      Algebra.Smooth R (Localization.Away (algebraMap R B π)) →
      Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π c : Pts R B) := by
    intro c
    induction c with
    | zero => exact cov_zero K hπ
    | succ c ih => exact cov_succ K hπ hk c ih
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_defect_bound_of_smooth_away R π hπ B hB
  obtain ⟨l, p, q⟩ := H c B hB
  refine ⟨l.length, fun i => (l.get i).1, inferInstance, inferInstance, fun i => (l.get i).2,
    fun i => p _ (List.get_mem l i), fun R' _ _ a hu => ?_⟩
  obtain ⟨x, hx, r⟩ := q R' a ⟨hu, by haveI := hu.1; exact hc R' a⟩
  obtain ⟨i, rfl⟩ := List.get_of_mem hx
  exact ⟨i, r⟩
end GlobalTheory.SS.Smoothening
