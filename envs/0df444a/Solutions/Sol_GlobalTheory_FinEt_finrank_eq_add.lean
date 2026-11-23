-- Prove2me | solution 1 for GlobalTheory.FinEt.finrank_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:20.936829+00:00
-- url     : https://prove2.me/submissions/3c4bf20e-9504-4146-b56f-d38c9a845d63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isIso_coprodDesc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
theorem _root_.solution {U V X S : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i]
    [IsOpenImmersion j] (h : Set.range j = (Set.range i)ᶜ) (p : X ⟶ S) [IsFinite p] [Flat p]
    (s : S) : p.finrank s = (i ≫ p).finrank s + (j ≫ p).finrank s := by
  have hi : IsClosedImmersion i := .of_isPreimmersion _ (by
    rw [← isOpen_compl_iff, ← h]; exact j.isOpenEmbedding.isOpen_range)
  have hj : IsClosedImmersion j := .of_isPreimmersion _ (by
    rw [h, isClosed_compl_iff]; exact i.isOpenEmbedding.isOpen_range)
  wlog hS : ∃ R, S = Spec R generalizing U V X S
  · obtain ⟨R, g, _, s, rfl⟩ := S.exists_Spec_apply_eq s
    have H := IsPullback.of_hasPullback p g
    have Hi := IsPullback.of_hasPullback i (pullback.fst p g)
    have Hj := IsPullback.of_hasPullback j (pullback.fst p g)
    rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ H,
      ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (Hi.paste_vert H),
      ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (Hj.paste_vert H)]
    refine this _ _ ?_ _ _ inferInstance inferInstance ⟨_, rfl⟩
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, h, Set.preimage_compl]
  obtain ⟨R, rfl⟩ := hS
  wlog hU : ∃ A, U = Spec A generalizing U
  · have _ : IsAffine U := isAffine_of_isAffineHom (i ≫ p)
    rw [← Scheme.Hom.finrank_comp_left_of_isIso U.isoSpec.inv (i ≫ p), ← Category.assoc]
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    rw [h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      U.isoSpec.inv.surjective.range_eq, Set.image_univ]
  obtain ⟨A, rfl⟩ := hU
  wlog hV : ∃ B, V = Spec B generalizing V
  · have _ : IsAffine V := isAffine_of_isAffineHom (j ≫ p)
    rw [← Scheme.Hom.finrank_comp_left_of_isIso V.isoSpec.inv (j ≫ p), ← Category.assoc]
    refine this _ inferInstance ?_ ⟨_, rfl⟩
    rw [← h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      V.isoSpec.inv.surjective.range_eq, Set.image_univ]
  obtain ⟨B, rfl⟩ := hV
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (j ≫ p)
  have hφ1 : φ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  have hφ2 : φ.hom.Flat := by rw [← Flat.SpecMap_iff, hφ]; infer_instance
  have hψ1 : ψ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hψ]; infer_instance
  have hψ2 : ψ.hom.Flat := by rw [← Flat.SpecMap_iff, hψ]; infer_instance
  have hiso := isIso_coprodDesc i j h
  algebraize [φ.hom, ψ.hom]
  have e : coprod.desc i j ≫ p =
      coprodSpec A B ≫ Spec.map (CommRingCat.ofHom (algebraMap R (A × B))) := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, ← hφ, coprodSpec_inl_assoc, ← Spec.map_comp]; rfl
    · rw [coprod.inr_desc_assoc, ← hψ, coprodSpec_inr_assoc, ← Spec.map_comp]; rfl
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (A × B)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (A × B)))) := by
    rw [← (IsIso.inv_comp_eq _).mpr e]
    infer_instance
  have : Module.Flat R (A × B) := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hfl)
  rw [← Scheme.Hom.finrank_comp_left_of_isIso (coprod.desc i j) p, e,
    Scheme.Hom.finrank_comp_left_of_isIso, ← hφ, ← hψ]
  have e1 := Scheme.Hom.finrank_SpecMap_algebraMap R (A × B) s
  have e2 := Scheme.Hom.finrank_SpecMap_algebraMap R A s
  have e3 := Scheme.Hom.finrank_SpecMap_algebraMap R B s
  rw [Module.rankAtStalk_prod] at e1
  exact e1.trans (congrArg₂ (· + ·) e2.symm e3.symm)
end GlobalTheory.FinEt
