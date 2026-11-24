-- Prove2me | solution 1 for GlobalTheory.AbLocusPull.isProper_restrict_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:26.988804+00:00
-- url     : https://prove2.me/submissions/59b8b41e-c73c-42f4-9eb3-90bced180c41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLocusPull
theorem _root_.solution {S S' X' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {t : S' ⟶ S} {F : X' ⟶ X}
    (h : IsPullback F p' p t) (U : S.Opens) [IsProper (p ∣_ U)] : IsProper (p' ∣_ (t ⁻¹ᵁ U)) := by
  have e0 : F ⁻¹ᵁ (p ⁻¹ᵁ U) = p' ⁻¹ᵁ (t ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
  have hUY : p' ⁻¹ᵁ (t ⁻¹ᵁ U) = F ⁻¹ᵁ (p ⁻¹ᵁ U) ⊓ p' ⁻¹ᵁ (t ⁻¹ᵁ U) := by rw [e0, inf_idem]
  have sq := Scheme.Hom.isPullback_resLE h (le_refl (t ⁻¹ᵁ U)) (le_refl (p ⁻¹ᵁ U)) hUY
  have hp : IsProper (p.resLE U (p ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  have hq := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) sq hp
  rwa [Scheme.Hom.resLE_eq_morphismRestrict] at hq
end GlobalTheory.AbLocusPull
