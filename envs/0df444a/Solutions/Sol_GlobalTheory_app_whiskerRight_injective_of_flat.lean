-- Prove2me | solution 1 for GlobalTheory.app_whiskerRight_injective_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:23:18.590711+00:00
-- url     : https://prove2.me/submissions/90c6c567-b709-4f36-8b5f-7c62013cc2cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AppWhiskerRightInjectiveOfFlat

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (φ : T' ⟶ T), Function.Injective φ.left.appTop.hom → ∀ U : (T ⊗ B).left.Opens, Function.Injective ((φ ▷ B).left.app U).hom := by
  intro S B T T' _ _ _ φ hφ U
  have hd : IsSchemeTheoreticallyDominant φ.left := by
    refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
    rw [Scheme.Hom.ker_apply]
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot]
    exact hφ
  have pb : IsPullback (pullback.fst T'.hom B.hom) (φ ▷ B).left φ.left (pullback.fst T.hom B.hom) := by
    refine (IsPullback.of_right (h₁₁ := (φ ▷ B).left) (v₁₁ := pullback.fst T'.hom B.hom)
      (h₂₁ := φ.left) (v₁₂ := pullback.fst T.hom B.hom) ?_ (Over.whiskerRight_left_fst φ)
      (IsPullback.of_hasPullback T.hom B.hom).flip).flip
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom B.hom).flip
  have : IsSchemeTheoreticallyDominant (φ ▷ B).left := .of_isPullback pb
  have : QuasiCompact (φ ▷ B).left := MorphismProperty.of_isPullback pb inferInstance
  exact (φ ▷ B).left.app_injective U
end GlobalTheory
