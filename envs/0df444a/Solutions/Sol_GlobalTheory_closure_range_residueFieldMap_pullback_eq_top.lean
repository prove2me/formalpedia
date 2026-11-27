-- Prove2me | solution 1 for GlobalTheory.closure_range_residueFieldMap_pullback_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:27.933743+00:00
-- url     : https://prove2.me/submissions/ad85093c-811c-4ae4-9c9d-e172f708656c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullbackResidueFieldsGenerate
import Theorems.Thm_GlobalTheory_subfield_eq_top_of_fromSpecResidueField_factors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory
open CategoryTheory Limits AlgebraicGeometry
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (X Y S : Scheme.{0}) (f : X ⟶ S) (g : Y ⟶ S)
    (t : ↑(pullback f g)) :
    Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom) = ⊤ := by
  set L := Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom)
  let ι : CommRingCat.of L ⟶ (pullback f g).residueField t := CommRingCat.ofHom L.subtype
  let cx : X.residueField (pullback.fst f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.fst f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  let cy : Y.residueField (pullback.snd f g t) ⟶ CommRingCat.of L := CommRingCat.ofHom
    (((pullback.snd f g).residueFieldMap t).hom.codRestrict L
      fun a => Subfield.subset_closure (Or.inr ⟨a, rfl⟩))
  have hcx : cx ≫ ι = (pullback.fst f g).residueFieldMap t := rfl
  have hcy : cy ≫ ι = (pullback.snd f g).residueFieldMap t := rfl
  have hι : Mono ι := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  have e : f (pullback.fst f g t) = g (pullback.snd f g t) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have key : f.residueFieldMap (pullback.fst f g t) ≫ cx =
      (S.residueFieldCongr e).hom ≫ g.residueFieldMap (pullback.snd f g t) ≫ cy := by
    rw [← cancel_mono ι]
    simp only [Category.assoc, hcx, hcy]
    rw [← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp]
    exact Scheme.Hom.residueFieldMap_congr pullback.condition t
  have hab : (Spec.map cx ≫ X.fromSpecResidueField (pullback.fst f g t)) ≫ f =
      (Spec.map cy ≫ Y.fromSpecResidueField (pullback.snd f g t)) ≫ g := by
    rw [Category.assoc, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, key, Spec.map_comp_assoc, Spec.map_comp_assoc,
      Scheme.residueFieldCongr_fromSpecResidueField]
    rw [Spec.map_comp_assoc]
  have hm : Spec.map (CommRingCat.ofHom L.subtype) ≫ pullback.lift _ _ hab =
      (pullback f g).fromSpecResidueField t := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
    · rw [Category.assoc, pullback.lift_snd, ← Spec.map_comp_assoc]
      exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t
  exact _root_.GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ t L _ hm
end _root_.GlobalTheory
end GlobalTheory
