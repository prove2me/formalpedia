-- Prove2me | solution 1 for GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:28.148797+00:00
-- url     : https://prove2.me/submissions/3016a867-39aa-4680-be31-be8304271c48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullbackResidueFieldsGenerate

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
theorem _root_.solution (Z : Scheme.{0}) (t : Z)
    (K : Subfield (Z.residueField t)) (m : Spec (CommRingCat.of K) ⟶ Z)
    (hm : Spec.map (CommRingCat.ofHom K.subtype) ≫ m = Z.fromSpecResidueField t) : K = ⊤ := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective m
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hm
  have hx : x = t := by
    have h := congr($hm (IsLocalRing.closedPoint _))
    have e₁ := Scheme.fromSpecResidueField_apply x
      (Spec.map φ (Spec.map (CommRingCat.ofHom K.subtype) (IsLocalRing.closedPoint _)))
    have e₂ := Scheme.fromSpecResidueField_apply t (IsLocalRing.closedPoint _)
    exact e₁.symm.trans (h.trans e₂)
  subst hx
  rw [← Category.assoc, ← Spec.map_comp] at hm
  have hφ : φ ≫ CommRingCat.ofHom K.subtype = 𝟙 _ := by
    rw [← Spec.map_inj, Spec.map_id, ← cancel_mono (Z.fromSpecResidueField x), hm]
    exact (Category.id_comp _).symm
  rw [eq_top_iff]
  intro y _
  have hy : K.subtype (φ.hom y) = y := congr($hφ y)
  rw [← hy]
  exact (φ.hom y).2
end _root_.GlobalTheory
end GlobalTheory
