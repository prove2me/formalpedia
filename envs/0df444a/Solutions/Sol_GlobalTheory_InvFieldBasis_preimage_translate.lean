-- Prove2me | solution 1 for GlobalTheory.InvFieldBasis.preimage_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:39:38.003813+00:00
-- url     : https://prove2.me/submissions/2db499d1-bb94-47e8-bd97-48baa8a10c7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PreimageTranslate
import Theorems.Thm_GlobalTheory_ConstThickening_structure_dualNumber
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)
noncomputable section
open GlobalTheory GlobalTheory.InvFieldBasis
variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C]
namespace GlobalTheory.InvFieldBasis
theorem _root_.solution {v : epsR K ⟶ G} (hv : IsTangent v) (W : G.left.Opens) :
    ((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ W = (snd (epsR K) G).left ⁻¹ᵁ W := by
  have e0w : Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (epsR K).hom = (𝟙_ (Over (Sp K))).hom := by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  let e0 : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom) e0w
  have hev : e0 ≫ v = η := Over.OverMorphism.ext hv
  let J : G ⟶ epsR K ⊗ G := lift (toUnit G ≫ e0) (𝟙 G)
  have hJ1 : J ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G) = 𝟙 G := by
    rw [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd, Category.assoc, hev]
    exact _root_.one_mul (𝟙 G)
  have hJ2 : J ≫ snd (epsR K) G = 𝟙 G := lift_snd _ _
  have hpb : IsPullback (snd (epsR K) G).left (fst (epsR K) G).left G.hom (epsR K).hom :=
    (IsPullback.of_hasPullback (epsR K).hom G.hom).flip
  have hs := GlobalTheory.ConstThickening.structure_dualNumber K G.left (epsR K ⊗ G).left G.hom (fst (epsR K) G).left
    (snd (epsR K) G).left J.left hpb
    (by simpa using congrArg (fun f => f.left) hJ2)
    (by simp [J, e0]; exact pullback.lift_fst _ _ _)
  have hc : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens), f ⁻¹ᵁ (g ⁻¹ᵁ U) = (f ≫ g) ⁻¹ᵁ U :=
    fun _ _ _ => rfl
  have h3 : J.left ⁻¹ᵁ (((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ W) =
      J.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ W) := by
    rw [hc, hc, ← Over.comp_left, ← Over.comp_left, hJ1, hJ2]
  rw [← hs.1 (((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ W), h3, hs.1]
end GlobalTheory.InvFieldBasis
