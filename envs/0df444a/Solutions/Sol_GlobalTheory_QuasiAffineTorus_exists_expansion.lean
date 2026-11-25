-- Prove2me | solution 1 for GlobalTheory.QuasiAffineTorus.exists_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:19:47.08591+00:00
-- url     : https://prove2.me/submissions/456896b7-e6e9-4208-8907-7217799789fc

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
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_ev_comp
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_ev_torusPt
import Theorems.Thm_GlobalTheory_TorusTrivial_isAffine_and_bijective
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.QuasiAffineTorus
open RationalPoint
variable {k : Type} [Field k] {X : Type} [AddCommGroup X]
namespace GlobalTheory.QuasiAffineTorus
theorem _root_.solution {U : Over (Sp k)} [IsAffine U.left]
    (F : Γ((splitTorus (Sp k) X ⊗ U).left, ⊤)) :
    ∃ (S : Finset X) (a : X → Γ(U.left, ⊤)), ∀ (u : 𝟙_ (Over (Sp k)) ⟶ U)
      (t : Multiplicative X →* kˣ), ev (lift (torusPt k X t) u) F =
        ∑ χ ∈ S, (t (Multiplicative.ofAdd χ) : k) * ev u (a χ) := by
  have : IsIso (lift (fst (splitTorus (Sp k) X) U) (snd _ U)) := by
    rw [lift_fst_snd]; infer_instance
  let c := splitTorusPointsEquiv (Sp k) X _ (fst (splitTorus (Sp k) X) U)
  let ψ : AddMonoidAlgebra Γ(U.left, ⊤) X →+* Γ((splitTorus (Sp k) X ⊗ U).left, ⊤) :=
    AddMonoidAlgebra.liftNCRingHom (snd (splitTorus (Sp k) X) U).left.appTop.hom
      ((Units.coeHom _).comp c) (fun _ _ => Commute.all _ _)
  have hψ : ∀ χ a, ψ (AddMonoidAlgebra.single χ a) =
      (snd (splitTorus (Sp k) X) U).left.appTop.hom a *
        (fst (splitTorus (Sp k) X) U).left.appTop.hom (charUnit (Sp k) X χ).val := fun χ a => by
    rw [← splitTorusPointsEquiv_val]
    exact AddMonoidAlgebra.liftNC_single _ _ χ a
  obtain ⟨-, h⟩ := TorusTrivial.isAffine_and_bijective (fst (splitTorus (Sp k) X) U) (snd _ U)
    (Iso.refl Γ(U.left, ⊤)) ψ (fun a => by
      refine (AddMonoidAlgebra.liftNC_single _ _ 0 a).trans ?_
      exact (congrArg (_ * ·) (((Units.coeHom _).comp c).map_one)).trans (_root_.mul_one _))
    (fun χ => by rw [hψ, map_one, _root_.one_mul])
  obtain ⟨p, rfl⟩ := h.2 F
  refine ⟨p.coeff.support, p.coeff, fun u t => ?_⟩
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  rw [Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [hψ, map_mul, ← ev_comp, ← ev_comp, lift_fst, lift_snd, ev_torusPt, mul_comm]
end GlobalTheory.QuasiAffineTorus
