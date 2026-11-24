-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.exists_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:33:06.098408+00:00
-- url     : https://prove2.me/submissions/10134646-e06b-42d5-9db8-1004a4237b19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution {K R M : Type} [Field K] [IsAlgClosed K] [CommRing R] (e : K ≃+* R) [AddCommGroup M]
    [Module R M] (hM : Module.finrank R M ≠ 0) (f : M →ₗ[R] M) : ∃ (a : R) (v : M), v ≠ 0 ∧ f v = a • v := by
  letI : Field R := (e.symm.isField (Field.toIsField K)).toField
  haveI : IsAlgClosed R := IsAlgClosed.of_ringEquiv K R e
  haveI : Module.Finite R M := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hM)
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (R := R) (Nat.pos_of_ne_zero hM)
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (K := R) f
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  exact ⟨a, v, hv.2, hv.apply_eq_smul⟩
end GlobalTheory.TorsionFixedAut
