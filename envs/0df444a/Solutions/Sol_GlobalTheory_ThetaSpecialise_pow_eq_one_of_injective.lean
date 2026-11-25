-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.pow_eq_one_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:04.755248+00:00
-- url     : https://prove2.me/submissions/d5d906df-3d01-4019-93d5-55a450125f87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution {S₀ : Scheme.{0}} {G : Over S₀} [GrpObj G] [IsSeparated G.hom] {S F : Type}
    [CommRing S] [IsDomain S] [CommRing F] {g : S →+* F} (hg : Function.Injective g)
    {t₀ : Spec (CommRingCat.of S) ⟶ S₀} {t : Spec (CommRingCat.of F) ⟶ S₀} (ρ : Over.mk t ⟶ Over.mk t₀)
    (hρ : ρ.left = Spec.map (CommRingCat.ofHom g)) (x : Over.mk t₀ ⟶ G) {k : ℕ} (h : (ρ ≫ x) ^ k = 1) :
    x ^ k = 1 := by
  have hdom : IsDominant (Spec.map (CommRingCat.ofHom g)) := by
    rw [isDominant_iff]
    have hd : DenseRange (PrimeSpectrum.comap g) := by
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
      intro a ha
      rw [RingHom.mem_ker] at ha
      have ha0 : a = 0 := hg (by rw [ha, map_zero])
      rw [ha0]
      exact zero_mem _
    exact hd
  have e : ρ ≫ x ^ k = ρ ≫ 1 := by rw [MonObj.comp_pow, h, MonObj.comp_one]
  have : IsReduced (Over.mk t₀).left := show IsReduced (Spec (CommRingCat.of S)) from inferInstance
  apply Over.OverMorphism.ext
  have e' := congrArg (fun m => m.left) e
  simp only [Over.comp_left, hρ] at e'
  exact ext_of_isDominant_of_isSeparated G.hom (by simp only [Over.w]) (Spec.map (CommRingCat.ofHom g)) e'
end GlobalTheory.ThetaSpecialise
