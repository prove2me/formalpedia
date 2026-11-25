-- Prove2me | solution 1 for GlobalTheory.sharp_family_relations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:31:41.227661+00:00
-- url     : https://prove2.me/submissions/61f094fa-4e31-460b-8d4a-056513bb6109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
import Theorems.Thm_GlobalTheory_SharpFamRel_push_mul
import Theorems.Thm_GlobalTheory_SharpFamRel_push_comp
import Theorems.Thm_GlobalTheory_SharpFamRel_push_id
import Theorems.Thm_GlobalTheory_SharpFamRel_push_end
import Theorems.Thm_GlobalTheory_SharpFamRel_transfer_end
import Theorems.Thm_GlobalTheory_SharpFamRel_transfer_pt
import Theorems.Thm_GlobalTheory_SharpFamRel_rel_of_isSharp
import Theorems.Thm_GlobalTheory_SharpRel_push_comp
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory
open SharpFamRel
namespace GlobalTheory
theorem _root_.solution : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j' j'', a j'' = a j * a j' → t.act j'' = t.act j' ≫ t.act j) ∧ (∀ j j' j'', a j'' = a j + a j' → t.act j'' = t.act j * t.act j') ∧ (∀ j, a j = 1 → t.act j = 𝟙 t.A) ∧ ∀ j i, t.pt i ≫ t.act j = (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod := by
  intro h g W J a bas k o _ b em S _ s t hD
  refine ⟨fun j j' j'' hm => ?_, fun j j' j'' hm => ?_, fun j hj => ?_, fun j i => ?_⟩
  · refine transfer_end (F := fun t => t.act j'') (G := fun t => t.act j' ≫ t.act j) ?_ ?_
      (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).1 j j' j'' hm) t hD
    · intro _ _ _ _ t' t _ _ hp hact
      exact push_end hp (hact j'')
    · intro _ _ _ _ t' t _ _ hp hact
      refine push_end hp ?_
      simp only [Over.comp_left, Category.assoc, hact j]
      rw [← Category.assoc, hact j', Category.assoc]
  · refine transfer_end (F := fun t => t.act j'') (G := fun t => t.act j * t.act j') ?_ ?_
      (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).2.1 j j' j'' hm) t hD
    · intro _ _ _ _ t' t _ _ hp hact
      exact push_end hp (hact j'')
    · intro _ _ _ _ t' t _ _ hp hact
      exact push_mul hp (selfMap hp) (push_end hp (hact j)) (push_end hp (hact j'))
  · refine transfer_end (F := fun t => t.act j) (G := fun t => 𝟙 t.A) ?_ ?_
      (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).2.2.1 j hj) t hD
    · intro _ _ _ _ t' t _ _ hp hact
      exact push_end hp (hact j)
    · intro _ _ _ _ t' t _ _ hp _
      exact push_id hp
  · refine transfer_pt (F := fun t => t.pt i ≫ t.act j)
      (G := fun t => (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod) ?_ ?_
      (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).2.2.2 j i) t hD
    · intro _ _ _ _ t' t f _ hp hpt hact
      exact push_comp hp (baseMap f) (Over.OverMorphism.ext (hpt i)) (hact j)
    · intro _ S' _ _ t' t f _ hp hpt _
      let e : (Out.baseOver S' ⟶ t'.A) →* (Over.mk ((Out.baseOver S').hom ≫ f) ⟶ t.A) :=
        MonoidHom.mk' (pushPt hp.1.w) fun x y => Over.OverMorphism.ext (hp.2 _ x y _ _ rfl rfl).symm
      let e2 : (Out.baseOver _ ⟶ t.A) →* (Over.mk ((Out.baseOver S').hom ≫ f) ⟶ t.A) :=
        MonoidHom.mk' (baseMap f ≫ ·) (MonObj.comp_mul _)
      change e _ = e2 _
      rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      congr 1
      refine congrArg List.ofFn (funext fun i' => ?_)
      simp only [Function.comp_apply, map_zpow]
      congr 1
      exact Over.OverMorphism.ext (hpt i')
end GlobalTheory
