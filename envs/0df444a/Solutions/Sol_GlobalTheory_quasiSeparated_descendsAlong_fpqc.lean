-- Prove2me | solution 1 for GlobalTheory.quasiSeparated_descendsAlong_fpqc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:10.820105+00:00
-- url     : https://prove2.me/submissions/2e9271a2-77de-4759-9f4b-a8ec2173e1b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
universe u
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    MorphismProperty.DescendsAlong (@QuasiSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : IsZariskiLocalAtTarget (@QuasiSeparated : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ (@Surjective ⊓ @Flat) ?_ ?_
  · rintro X Y f ⟨hl, hs⟩
    exact ⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hl⟩
  · intro R S Y φ g hφ hfst
    obtain ⟨hs, -⟩ := hφ
    have : QuasiSeparated (pullback.fst (Spec.map φ) g) := hfst
    have : QuasiSeparatedSpace ↥(Limits.pullback (Spec.map φ) g) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst (Spec.map φ) g)
    have hsnd : Surjective (pullback.snd (Spec.map φ) g) :=
      MorphismProperty.pullback_snd _ _ hs
    have : QuasiCompact (pullback.snd (Spec.map φ) g) :=
      MorphismProperty.pullback_snd _ _ (inferInstanceAs (QuasiCompact (Spec.map φ)))
    show QuasiSeparated g
    rw [quasiSeparated_iff_quasiSeparatedSpace]
    refine ⟨fun U V hU hUc hV hVc => ?_⟩
    set s := pullback.snd (Spec.map φ) g
    have hpre : ∀ W : Set Y, IsOpen W → IsCompact W → IsCompact (s ⁻¹' W) :=
      fun W hW hWc => (quasiCompact_iff s).1 ‹_› W hW hWc
    have : U ∩ V = s '' (s ⁻¹' U ∩ s ⁻¹' V) := by
      rw [← Set.preimage_inter, Set.image_preimage_eq _ hsnd.surj]
    rw [this]
    exact (QuasiSeparatedSpace.inter_isCompact _ _ (hU.preimage s.continuous) (hpre U hU hUc)
      (hV.preimage s.continuous) (hpre V hV hVc)).image s.continuous
end _root_.GlobalTheory
end GlobalTheory
