-- Prove2me | solution 1 for GlobalTheory.isRegularLocalRing_and_ringKrullDim_eq_of_polAV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:49:14.773803+00:00
-- url     : https://prove2.me/submissions/55cd70b6-2370-4ca0-b6b1-65f56e83459a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularLocalRingAndRingKrullDimEqOfPolAV
import Theorems.Thm_GlobalTheory_forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_GlobalTheory_isRegularRing_of_smooth
import Theorems.Thm_GlobalTheory_trdeg_eq_of_smoothOfRelativeDimension
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_IsCM_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_height_eq_of_isMaximal_of_trdeg_eq_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t₀ : Spec (CommRingCat.of R) ⟶ P.A.left) (m : Ideal R) [m.IsMaximal] (O : Type) [CommRing O] [Algebra R O] [IsLocalization.AtPrime O m], IsOpenImmersion t₀ → IsRegularLocalRing O ∧ ringKrullDim O = P.g := by
  intro K _ _ P R _ t₀ m hm O _ _ _ ht
  have hab := P.isAb
  have hd := P.smoothDim
  have hsm : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  have hgi : GeometricallyIntegral P.A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hsm hab.geomConnected
  have hint : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have hnt : Nontrivial R := ⟨⟨0, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).2 (h ▸ m.zero_mem))⟩⟩
  let φ : CommRingCat.of K ⟶ CommRingCat.of R := Spec.preimage (t₀ ≫ P.A.hom)
  have hφ : t₀ ≫ P.A.hom = Spec.map φ := (Spec.map_preimage _).symm
  let _ : Algebra K R := φ.hom.toAlgebra
  have hφ' : t₀ ≫ P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap K R)) := hφ
  have htr : Algebra.trdeg K R = P.g :=
    trdeg_eq_of_smoothOfRelativeDimension K P.A.left P.A.hom P.g hd R t₀ ht hφ'
  have : IsIntegral (Spec (CommRingCat.of R)) := isIntegral_of_isOpenImmersion t₀
  have : IsDomain R := (affine_isIntegral_iff (CommRingCat.of R)).1 inferInstance
  have hs : Smooth (Spec.map φ) := hφ ▸ inferInstance
  have hs' : Algebra.Smooth K R := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
  have hreg : IsRegularRing R := isRegularRing_of_smooth K R
  have hh := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field P.g htr m
  refine ⟨?_, ?_⟩
  · have := isRegularRing_iff.mp hreg m
    exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv m.primeCompl
      (Localization.AtPrime m) O).toRingEquiv
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height m O, hh]
    rfl
end GlobalTheory
