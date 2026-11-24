-- Prove2me | solution 1 for GlobalTheory.ToSplit.cover_tensorHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:33:03.622147+00:00
-- url     : https://prove2.me/submissions/6febfa8e-4f50-4112-83d7-9bc543b60849

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension

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
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk
omit hk [IsMonHom q] [GrpObj G] [GrpObj B]
namespace GlobalTheory.ToSplit
theorem _root_.solution : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
    (q ⊗ₘ q).left := by
  have h₁ : IsPullback (fst G G) (q ▷ G) q (fst B G) := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => lift c.fst (c.snd ≫ snd _ _))
      (fun c => by simp) (fun c => ?_) (fun c m h₁ h₂ => ?_)⟩⟩
    · ext <;> simp [c.condition]
    · ext <;> simp [← h₁, ← h₂]
  have h₂ : IsPullback (snd B G) (B ◁ q) q (snd B B) := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => lift (c.snd ≫ fst _ _) c.fst)
      (fun c => by simp) (fun c => ?_) (fun c m h₁ h₂ => ?_)⟩⟩
    · ext <;> simp [c.condition]
    · ext <;> simp [← h₁, ← h₂]
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q.left :=
    ⟨⟨‹_›, ‹_›⟩, ‹_›⟩
  obtain ⟨⟨_, _⟩, _⟩ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
    (q ▷ G).left := ⟨⟨MorphismProperty.of_isPullback (h₁.map (Over.forget S)) hq.1.1,
      MorphismProperty.of_isPullback (h₁.map (Over.forget S)) hq.1.2⟩,
      MorphismProperty.of_isPullback (h₁.map (Over.forget S)) hq.2⟩
  obtain ⟨⟨_, _⟩, _⟩ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
    (B ◁ q).left := ⟨⟨MorphismProperty.of_isPullback (h₂.map (Over.forget S)) hq.1.1,
      MorphismProperty.of_isPullback (h₂.map (Over.forget S)) hq.1.2⟩,
      MorphismProperty.of_isPullback (h₂.map (Over.forget S)) hq.2⟩
  rw [MonoidalCategory.tensorHom_def, Over.comp_left]
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
end GlobalTheory.ToSplit
