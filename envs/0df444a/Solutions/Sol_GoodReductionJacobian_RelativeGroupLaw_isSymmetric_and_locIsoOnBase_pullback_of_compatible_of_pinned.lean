-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isSymmetric_and_locIsoOnBase_pullback_of_compatible_of_pinned
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/841eda7c-28a7-5be1-ab72-2458e2fa981e

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isSymmetric_and_locIsoOnBase_pullback_of_compatible_of_pinned

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    (X Y : Type) [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y]
    (φ : X →+* Y) (hφ : φ.comp (algebraMap S X) = algebraMap S Y)
    (LX : RelativeGroupLaw X (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))))
    (hLX : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of X))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))))),
        (LX.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (LY : RelativeGroupLaw Y (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))))
    (hLY : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of Y))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))),
        (LY.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S Y)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (ρ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
    (hρ₁ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
    (hρ₂ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ≫ Spec.map (CommRingCat.ofHom φ))
    (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))).Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback ρ).obj 𝓜) ∧
    (IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) LX 𝓜 →
      IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) LY ((Scheme.Modules.pullback ρ).obj 𝓜)) ∧
    (LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))))).obj 𝓛)
        (𝓜 ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) LX)).obj 𝓜) →
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))).obj 𝓛)
        ((Scheme.Modules.pullback ρ).obj 𝓜 ⊗
          (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) LY)).obj ((Scheme.Modules.pullback ρ).obj 𝓜))) := by

  have hneg := GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible L X Y φ hφ LX LY hLX hLY ρ hρ₁ hρ₂
  have EY := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))

  have ofIso : ∀ {M M' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))).Modules} (_ : M ≅ M'),
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) M M' :=
    fun e _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

  have base : ∀ {M M' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))).Modules},
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) M M' →
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
          ((Scheme.Modules.pullback ρ).obj M) ((Scheme.Modules.pullback ρ).obj M') :=
    fun h => AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) ρ (Spec.map (CommRingCat.ofHom φ)) hρ₂ h

  have eNeg : (Scheme.Modules.pullback ρ).obj
      ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) LX)).obj 𝓜) ≅
      (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) LY)).obj
        ((Scheme.Modules.pullback ρ).obj 𝓜) :=
    (Scheme.Modules.pullbackComp ρ _).app 𝓜 ≪≫ (Scheme.Modules.pullbackCongr hneg).app 𝓜 ≪≫
      ((Scheme.Modules.pullbackComp _ ρ).app 𝓜).symm

  have eL : (Scheme.Modules.pullback ρ).obj
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))))).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))).obj 𝓛 :=
    (Scheme.Modules.pullbackComp ρ _).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hρ₁).app 𝓛
  refine ⟨h𝓜.pullback ρ, fun hs => ?_, fun hl => ?_⟩
  · exact EY.trans (ofIso eNeg.symm) (base hs)
  · refine EY.trans (EY.trans (ofIso eL.symm) (base hl)) (ofIso ?_)
    exact Scheme.Modules.pullbackTensorObjIso ρ _ _ ≪≫ whiskerLeftIso _ eNeg

end S_GoodReductionJacobian_RelativeGroupLaw_isSymmetric_and_locIsoOnBase_pullback_of_compatible_of_pinned
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isSymmetric_and_locIsoOnBase_pullback_of_compatible_of_pinned (solution)
