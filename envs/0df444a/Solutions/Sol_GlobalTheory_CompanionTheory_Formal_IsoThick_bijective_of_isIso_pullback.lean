-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Formal.IsoThick.bijective_of_isIso_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:14.930527+00:00
-- url     : https://prove2.me/submissions/942e7ab8-79bc-49cb-832b-2f497cc46b2c

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_TowerLemmas_FormalTowerLemmas_Imports
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsoOfThickenings
import Theorems.Thm_GlobalTheory_Published_FormalAlgebraisation_Morphisms_hom_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Formal GlobalTheory.CompanionTheory.Formal.IsoThick
open TensorProduct
namespace GlobalTheory.CompanionTheory.Formal.IsoThick
theorem _root_.solution {R A B T : Type} [CommRing R] [CommRing A] [CommRing B]
    [CommRing T] [Algebra R A] [Algebra R B] [Algebra R T] (φ : A →ₐ[R] B)
    (m : pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    (hm1 : m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hm2 : m ≫ pullback.snd _ _ = pullback.snd _ _) (h : IsIso m) :
    Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id R T)) := by
  have e1 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] T)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] T)) ≫
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have e2 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) :
        T →+* A ⊗[R] T)) =
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : T →ₐ[R] B ⊗[R] T) :
        T →+* B ⊗[R] T)) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp
  have key : m = (pullbackSpecIso R B T).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) ≫
        (pullbackSpecIso R A T).inv := by
    apply pullback.hom_ext
    · rw [hm1, Category.assoc, Category.assoc, pullbackSpecIso_inv_fst, e1, ← Category.assoc,
        pullbackSpecIso_hom_fst]
    · rw [hm2, Category.assoc, Category.assoc, pullbackSpecIso_inv_snd, e2, pullbackSpecIso_hom_snd]
  have h2 : IsIso (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) =
        (pullbackSpecIso R B T).inv ≫ m ≫ (pullbackSpecIso R A T).hom := by
      rw [key]; simp
    rw [this]
    infer_instance
  rw [isIso_SpecMap_iff] at h2
  exact h2
end GlobalTheory.CompanionTheory.Formal.IsoThick
