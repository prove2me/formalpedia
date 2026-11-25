-- Prove2me | solution 1 for GlobalTheory.SS.TorusSlice.isOpenImmersion_sweep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:48:02.058313+00:00
-- url     : https://prove2.me/submissions/71981564-2f2c-4acc-804e-7f57cad05d11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits
import Theorems.Thm_GlobalTheory_SS_TorusSlice_isOpenImmersion_of_flat_cover
import Theorems.Thm_GlobalTheory_SS_TorusSlice_isPullback_whiskerLeft
import Theorems.Thm_GlobalTheory_SS_TorusSlice_isPullback_sweep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.TorusSlice
variable {S : Scheme.{0}}
namespace GlobalTheory.SS.TorusSlice
theorem _root_.solution {T G Y Y₁ : Over S} [GrpObj T] [GrpObj G] (i : T ⟶ G) [IsMonHom i] (j : Y ⟶ G)
    (σ : Y ⟶ T) (hσ : Equivar i j σ) (e : Y₁ ⟶ Y) (he : IsPullback e (toUnit Y₁) σ η[T])
    [Flat T.hom] [LocallyOfFinitePresentation T.hom] [QuasiCompact T.hom] [IsOpenImmersion j.left] [QuasiCompact j.left] :
    IsOpenImmersion ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)).left := by
  have hj : Mono j := Over.mono_of_mono_left j
  let m : T ⊗ Y ⟶ G := (fst T Y ≫ i) * (snd T Y ≫ j)
  have em : m.left = (T ◁ j).left ≫ (shearIso i).hom.left ≫ (snd T G).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp [m, shearIso, MonObj.comp_mul]
  have hw := (isPullback_whiskerLeft T j).map (Over.forget S)
  have : IsOpenImmersion (T ◁ j).left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hw.flip ‹_›
  have : QuasiCompact (T ◁ j).left := MorphismProperty.of_isPullback (P := @QuasiCompact) hw.flip ‹_›
  have : IsIso (shearIso i).hom.left := inferInstanceAs (IsIso ((Over.forget S).map (shearIso i).hom))
  have : Flat (snd T G).left := inferInstanceAs (Flat (pullback.snd T.hom G.hom))
  have : QuasiCompact (snd T G).left := inferInstanceAs (QuasiCompact (pullback.snd T.hom G.hom))
  have : LocallyOfFinitePresentation (snd T G).left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd T.hom G.hom))
  have : Flat m.left := by rw [em]; infer_instance
  have : QuasiCompact m.left := by rw [em]; infer_instance
  have : LocallyOfFinitePresentation m.left := by rw [em]; infer_instance
  have hW := IsPullback.of_hasPullback (((snd T Y ≫ σ)⁻¹ ≫ i) * (snd T Y ≫ j)) j
  obtain ⟨q, H⟩ := isPullback_sweep i j σ hσ e he _ _ hW
  have hp := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hW.map (Over.forget S)).flip ‹_›
  refine @isOpenImmersion_of_flat_cover _ _ _ _ _ _ _ m.left (H.map (Over.forget S)) hp _ _ _ ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨(T ◁ e).left x, ?_⟩
  have : T ◁ e ≫ m = (fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j) := by simp [m, MonObj.comp_mul]
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, this]
end GlobalTheory.SS.TorusSlice
