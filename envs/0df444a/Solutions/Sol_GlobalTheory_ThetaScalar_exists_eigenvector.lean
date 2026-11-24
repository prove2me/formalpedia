-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.exists_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:32:54.371802+00:00
-- url     : https://prove2.me/submissions/bd48a1eb-2814-4320-a63c-b0e2f1de3063

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaScalar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaScalar
theorem _root_.solution {R F M : Type} [CommRing R] [Field F] [IsAlgClosed F] (e : R ≃+* F) [AddCommGroup M]
    [Module R M] (h : 0 < Module.finrank R M) (Φ : M →ₗ[R] M) : ∃ (a : R) (v : M), v ≠ 0 ∧ Φ v = a • v := by
  letI : Field R := (e.toMulEquiv.isField (Field.toIsField F)).toField
  haveI : IsAlgClosed R := IsAlgClosed.of_ringEquiv F R e.symm
  haveI : Module.Finite R M := Module.finite_of_finrank_pos h
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos h
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (K := R) (V := M) Φ
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  exact ⟨a, v, hv.2, hv.apply_eq_smul⟩
end GlobalTheory.ThetaScalar
