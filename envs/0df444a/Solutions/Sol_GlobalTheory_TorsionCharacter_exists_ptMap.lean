-- Prove2me | solution 1 for GlobalTheory.TorsionCharacter.exists_ptMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:21.94385+00:00
-- url     : https://prove2.me/submissions/4ce8e18e-8599-4397-b3cf-c2c8f50b6781

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitsZpowSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCharacter
variable {O : Type} [CommRing O]
namespace GlobalTheory.TorsionCharacter
theorem _root_.solution {A R : Type} [CommRing A] [Algebra O A] [CommRing R] [Algebra O R]
    (c : specO O R ⟶ specO O A) : ∃ φ : A →ₐ[O] R, c = ptMap φ := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of R) c.left
  have w := Over.w c
  change c.left ≫ Spec.map _ = Spec.map _ at w
  rw [← hψ, ← Spec.map_comp] at w
  have w' := congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  exact ⟨⟨ψ.hom, fun r => RingHom.congr_fun w' r⟩, Over.OverMorphism.ext hψ.symm⟩
end GlobalTheory.TorsionCharacter
