-- Prove2me | solution 1 for GlobalTheory.ExpUniq.sec_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:37.752793+00:00
-- url     : https://prove2.me/submissions/6ce2ef9e-5f59-4cae-915b-1716cc6314d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
import Theorems.Thm_GlobalTheory_ThickeningDetermines_eq_zero_of_secIdeal_eq_bot
import Theorems.Thm_GlobalTheory_ThickeningDetermines_secIdeal_le_ker
import Theorems.Thm_GlobalTheory_grpObj_geometricallyIntegral_of_smooth
import Theorems.Thm_GlobalTheory_isIso_of_isClosedImmersion_of_thickenings
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ExpUniq
namespace GlobalTheory.ExpUniq
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (W : Type) [CommRing W] [IsNoetherianRing W] [Algebra R W]
    (hI : I.map (algebraMap R W) ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom]
    [GeometricallyConnected H.hom] (N : LB (TA R W ⊗ H).left) (hN : N.IsLB) (s : LB.Sec N)
    (hs : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (TA R W ⊗ H).left) (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))),
      (r ≫ (snd (TA R W) H).left) ≫ H.hom = a ≫ thick R I e → ∀ (z : Z) j, r z ∈ N.U j → gs r z _ (s.f j) = 0) (j : N.ι) :
    s.f j = 0 := by
  let φ := algebraMap R W
  let H₀ : Over (Spec (CommRingCat.of W)) := Over.mk (pullback.fst (TA R W).hom H.hom)
  have := grpObj_geometricallyIntegral_of_smooth _ H
  have : Smooth H₀.hom := inferInstanceAs (Smooth (pullback.fst (TA R W).hom H.hom))
  have : GeometricallyIntegral H₀.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.fst (TA R W).hom H.hom))
  refine ThickeningDetermines.eq_zero_of_secIdeal_eq_bot hN s ?_ j
  have key := isIso_of_isClosedImmersion_of_thickenings W _ hI H₀
    (Over.homMk (pullback.lift (𝟙 _) ((TA R W).hom ≫ η[H].left) (by
      rw [Category.assoc, Over.w η[H]]; simp)) (pullback.lift_fst _ _ _)) (fun p ↦ inferInstance)
    _ (ThickeningDetermines.secIdeal hN s).subschemeι fun n ↦ by
      have : IsClosedImmersion (thick _ (I.map φ) n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG (I.map φ) n H₀).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H₀.hom (thick _ (I.map φ) n)))
      let r : (thickObj _ (I.map φ) n H₀).left ⟶ (TA R W ⊗ H).left := (fstG (I.map φ) n H₀).left
      have : QuasiCompact r := this
      have h0 : ∀ j, (r.app _).hom (s.f j) = 0 := fun j ↦ fn_ext fun z hz => by
        have hz' : (𝟙 (thickObj _ (I.map φ) n H₀).left : _ ⟶ _) z ∈ r ⁻¹ᵁ N.U j := hz
        rw [gs_pull _ r z _ hz', Category.id_comp, gs_eq _ z _ hz', map_zero, map_zero]
        refine hs n _ r (pullback.snd H₀.hom (thick _ (I.map φ) n) ≫
            Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map φ) ^ (n + 1)) φ
            (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)))) ?_ z j hz
        have e₁ : (snd (TA R W) H).left ≫ H.hom = H₀.hom ≫ (TA R W).hom := pullback.condition.symm
        have e₂ : r ≫ H₀.hom = pullback.snd H₀.hom (thick _ (I.map φ) n) ≫ thick _ (I.map φ) n := pullback.condition
        rw [Category.assoc, e₁, ← Category.assoc, e₂, Category.assoc, Category.assoc, ← Spec.map_comp]
        exact congrArg _ (Spec.map_comp _ _).symm
      exact ⟨IsClosedImmersion.lift _ r (by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact ThickeningDetermines.secIdeal_le_ker hN s _ h0), IsClosedImmersion.lift_fac _ _ _⟩
  rw [← Scheme.IdealSheafData.ker_subschemeι (ThickeningDetermines.secIdeal hN s)]
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.1 key
end GlobalTheory.ExpUniq
