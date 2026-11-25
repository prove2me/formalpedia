-- Prove2me | solution 1 for GlobalTheory.existsUnique_linear_lift_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:53:44.194219+00:00
-- url     : https://prove2.me/submissions/f9db7b4f-310e-4f7a-bc5a-dd243f7e4751

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibres
import Theorems.Thm_GlobalTheory_UniformLift_map_zero_eq_one
import Theorems.Thm_GlobalTheory_UniformLift_existsUnique_linearMap_lift_of_germ
import Theorems.Thm_GlobalTheory_UniformLift_fibPt_fst
import Theorems.Thm_GlobalTheory_UniformLift_fibPt_snd
import Theorems.Thm_GlobalTheory_UniformLift_fibPt_injective
import Theorems.Thm_GlobalTheory_LocalLift_exists_local_lift
import Theorems.Thm_GlobalTheory_T_isHolTo_fibPt_and_comp_fibre
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_isDerivAt0_fibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open UniformLift
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X X' : Scheme.{0}) (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (y : Sp ℂ ⟶ X) (y' : Sp ℂ ⟶ X') (g g' : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (e' : (Fin g' → ℂ) → (Over.mk y' ⟶ G')) (ψ : pullback G.hom y ⟶ pullback G'.hom y') (ψp : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G')), Smooth G'.hom → (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) → IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) → ((∀ w, ∃! v : epsPt y' ⟶ G', IsDerivAt0 (fun z => (e' z).left) w v.left) ∧ ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) → DiscreteTopology {z // e' z = 1} → ψ ≫ pullback.snd _ _ = pullback.snd _ _ → (∀ x, fibPt G x ≫ ψ = fibPt G' (ψp x)) → ∃! h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), ∀ z, e' (h z) = ψp (e z) := by
  intro X X' G G' _ _ y y' g g' e e' ψ ψp hsm he he' hol hol' hder hdisc hψ hψp
  have hsm' : Smooth (pullback.snd G'.hom y') := inferInstance
  have hd := isDerivAt0_fibre X' G' y' g' e' _ _ _ (fun z => fibPt G' (e' z)) (IsPullback.of_hasPullback G'.hom y')
    (fun z => ⟨fibPt_fst _ _, fibPt_snd _ _⟩) hol' hder
  obtain ⟨k, k0, hka, hk⟩ := LocalLift.exists_local_lift _ (pullback.snd G'.hom y') g g'
    (fun z => fibPt G (e z) ≫ ψ) (fun z => fibPt G' (e' z)) hsm'
    (fun z => by rw [Category.assoc, hψ, fibPt_snd]) (fun z => fibPt_snd _ _)
    ((T.isHolTo_fibPt_and_comp_fibre X G y g e hol).2 _ ψ) (T.isHolTo_fibPt_and_comp_fibre X' G' y' g' e' hol').1 hd
    (by simp only [hψp, map_zero_eq_one e he, map_zero_eq_one e' he', map_one])
  exact existsUnique_linearMap_lift_of_germ
    (ex := toAddHom (fun z => ψp (e z)) fun z w => by rw [he, map_mul]) (ex' := toAddHom e' he')
    ⟨hdisc⟩ hka.differentiableAt k0 (hk.mono fun z hz => fibPt_injective G' (hz.trans (hψp _)))
end GlobalTheory
