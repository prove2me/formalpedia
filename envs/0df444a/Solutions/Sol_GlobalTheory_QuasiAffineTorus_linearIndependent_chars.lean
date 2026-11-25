-- Prove2me | solution 1 for GlobalTheory.QuasiAffineTorus.linearIndependent_chars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:46:38.743257+00:00
-- url     : https://prove2.me/submissions/08a6c71d-3c04-4ccf-b700-08a4777d94d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.restrictPoints_val
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.QuasiAffineTorus
variable {k : Type} [Field k] [IsAlgClosed k] {X : Type} [AddCommGroup X]
namespace GlobalTheory.QuasiAffineTorus
theorem _root_.solution [Module.Free ℤ X] :
    LinearIndependent k fun (χ : X) (t : Multiplicative X →* kˣ) =>
      (t (Multiplicative.ofAdd χ) : k) := by
  let v : X → ((Multiplicative X →* kˣ) →* k) := fun χ =>
    (Units.coeHom k).comp (MonoidHom.eval (Multiplicative.ofAdd χ))
  refine (linearIndependent_monoidHom (Multiplicative X →* kˣ) k).comp v fun χ ψ h => ?_
  let b := Module.Free.chooseBasis ℤ X
  refine b.ext_elem fun j => ?_
  classical
  by_contra hne
  obtain ⟨z, hz, hz0⟩ : ∃ z : k, z ^ (b.repr χ j - b.repr ψ j).natAbs ≠ 1 ∧ z ≠ 0 := by
    have hn : 0 < (b.repr χ j - b.repr ψ j).natAbs := Int.natAbs_pos.2 (sub_ne_zero.2 hne)
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
      (insert (0 : k) (Polynomial.nthRoots (b.repr χ j - b.repr ψ j).natAbs (1 : k)).toFinset)
    simp only [Finset.mem_insert, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn, not_or] at hz
    exact ⟨z, hz.2, hz.1⟩
  let t : Multiplicative X →* kˣ :=
    (zpowersHom kˣ (Units.mk0 z hz0)).comp (AddMonoidHom.toMultiplicative (b.coord j).toAddMonoidHom)
  have h1 : t (Multiplicative.ofAdd χ) = t (Multiplicative.ofAdd ψ) :=
    Units.ext (DFunLike.congr_fun h t)
  have h2 : Units.mk0 z hz0 ^ (b.repr χ j - b.repr ψ j) = 1 := by
    rw [zpow_sub, mul_inv_eq_one]
    exact h1
  have h3 := congrArg Units.val (pow_natAbs_eq_one.2 h2)
  exact hz (by simpa using h3)
end GlobalTheory.QuasiAffineTorus
