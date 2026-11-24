-- Prove2me | solution 1 for GlobalTheory.SS.Ord.exists_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:36:13.68758+00:00
-- url     : https://prove2.me/submissions/a9685ba3-c741-45e7-9337-32e28d6be815

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Theorems.Thm_GlobalTheory_SS_Ord_exists_pow_mul_mem
import Theorems.Thm_GlobalTheory_SS_Ord_j_cst
import Theorems.Thm_GlobalTheory_SS_Ord_exists_pow_mul_eq

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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.Ord
theorem _root_.solution (hπ : Irreducible π) (M : Model R A) (D : I → VF A) {U : M.Y.left.Opens}
    (hU : IsAffineOpen U) : ∃ n : ℤ, ∀ t : I → Γ(M.Y.left, U), ∃ s : Γ(M.Y.left, U),
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s := by
  have := M.smooth
  have hf : (cst M U).FiniteType := (M.Y.hom.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2)
  obtain ⟨N, hN⟩ := exists_pow_mul_mem (cst M U) hf (M.j.app U).hom (cst M U π) (fun i => (D i).D _)
    (fun i => (D i).leibniz _) (fun i r => by rw [j_cst]; exact (D i).const _ _) (exists_pow_mul_eq hπ M hU)
  choose s hs using hN
  refine ⟨-((N * Fintype.card I : ℕ) : ℤ), fun t => ⟨(Matrix.of fun i j => s i (t j)).det, ?_⟩⟩
  have hp : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  have e : (M.j.app U).hom (Matrix.of fun i j => s i (t j)).det =
      ((M.j.app U).hom (cst M U π) ^ N) ^ Fintype.card I *
        jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) := by
    rw [jac, ← Matrix.det_smul, RingHom.map_det]
    congr 1
    ext i j
    exact hs i (t j)
  rw [e, j_cst, ← pow_mul, ← map_pow, ← _root_.mul_assoc, ← map_mul, zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ hp), map_one, _root_.one_mul]
end GlobalTheory.SS.Ord
