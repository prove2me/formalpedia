-- Prove2me | solution 1 for GlobalTheory.QuasiAffineTorus.exists_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:46:37.467408+00:00
-- url     : https://prove2.me/submissions/4285eb72-3582-4aef-a001-548f2459fae8

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
theorem _root_.solution (M : AddSubgroup X) (φ : M →+ Additive kˣ) :
    ∃ t : Multiplicative X →* kˣ, ∀ m : M, t (Multiplicative.ofAdd (m : X)) = (φ m).toMul := by
  letI : RootableBy kˣ ℕ := rootableByOfPowLeftSurj _ _ fun {n} hn u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : k) (Nat.pos_of_ne_zero hn)
    have h0 : z ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [← hz, zero_pow hn])
    exact ⟨Units.mk0 z h0, Units.ext (by simpa using hz)⟩
  letI : RootableBy kˣ ℤ := Group.rootableByIntOfRootableByNat _
  letI : DivisibleBy (Additive kˣ) ℤ :=
    { div := fun a n => Additive.ofMul (RootableBy.root a.toMul n)
      div_zero := fun a => congrArg Additive.ofMul (RootableBy.root_zero a.toMul)
      div_cancel := fun a hn => congrArg Additive.ofMul (RootableBy.root_cancel a.toMul hn) }
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive kˣ)).extension_property_addMonoidHom
    M.subtype M.subtype_injective φ
  exact ⟨AddMonoidHom.toMultiplicativeLeft h, fun m => congrArg Additive.toMul (DFunLike.congr_fun hh m)⟩
end GlobalTheory.QuasiAffineTorus
