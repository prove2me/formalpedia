-- Prove2me | solution 1 for GlobalTheory.TorsionCharacter.exists_finite_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:43.921688+00:00
-- url     : https://prove2.me/submissions/4c5ba040-bf03-4d2b-882f-6033fbdb7aeb

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
theorem _root_.solution [IsLocalRing O] (Z : Over (Spec (CommRingCat.of O))) [IsFinite Z.hom] [Flat Z.hom] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A), Module.Finite O A ∧ Module.Free O A ∧
      Nonempty (specO O A ≅ Z) := by
  haveI : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let g : CommRingCat.of O ⟶ Γ(Z.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ Z.hom.appTop
  letI : Algebra O Γ(Z.left, ⊤) := g.hom.toAlgebra
  have hw : Z.left.isoSpec.inv ≫ Z.hom = Spec.map g := by
    rw [Iso.inv_comp_eq, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]
  haveI h1 : IsFinite (Spec.map g) := hw ▸ inferInstance
  haveI h2 : Flat (Spec.map g) := hw ▸ inferInstance
  have h3 : g.hom.Finite := (IsFinite.SpecMap_iff g).1 h1
  have h4 : g.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h2
  haveI : Module.Finite O Γ(Z.left, ⊤) := h3
  haveI : Module.Flat O Γ(Z.left, ⊤) := h4
  exact ⟨Γ(Z.left, ⊤), inferInstance, inferInstance, inferInstance, Module.free_of_flat_of_isLocalRing,
    ⟨Over.isoMk Z.left.isoSpec.symm hw⟩⟩
end GlobalTheory.TorsionCharacter
