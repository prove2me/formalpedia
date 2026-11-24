-- Prove2me | solution 1 for GlobalTheory.GlueClosed.exists_glue_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:09:31.0186+00:00
-- url     : https://prove2.me/submissions/dabc72c4-4956-42e5-80fa-fa4a57991155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueClosedImmersionsOpenCover
import Theorems.Thm_GlobalTheory_GlueClosed_exists_glue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GlueClosed
namespace GlobalTheory.GlueClosed
theorem _root_.solution : ∀ (X : Scheme.{0}) (ι : Type) (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X), (∀ i, IsOpenImmersion (m i)) → (∀ x : X, ∃ i, x ∈ Set.range (m i)) → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i j : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (g' : Y ⟶ Xi j), g ≫ m i = g' ≫ m j → ((∃ z : Y ⟶ A i, z ≫ a i = g) ↔ (∃ z : Y ⟶ A j, z ≫ a j = g'))) → ∃ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b ∧ ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), ((∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) := by
  intro X ι Xi m hm hcov A a ha hcomp
  let S : Set X.Opens := {U | ∃ i, U ≤ (m i).opensRange}
  have hS : ∀ x : X, ∃ U ∈ S, x ∈ U := fun x ↦ by
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨(m i).opensRange, ⟨i, le_rfl⟩, hi⟩
  have hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S := fun U ⟨i, hi⟩ V _ ↦ ⟨i, inf_le_left.trans hi⟩
  have hl : ∀ (U : X.Opens) (i : ι), U ≤ (m i).opensRange →
      ∃ l : U.toScheme ⟶ Xi i, l ≫ m i = U.ι := fun U i h ↦
    ⟨IsOpenImmersion.lift (m i) U.ι (by rw [Scheme.Opens.range_ι]; exact h),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose l hl using hl
  have hC : ∀ U : S, ∃ (C : Scheme.{0}) (c : C ⟶ U.1.toScheme), IsClosedImmersion c ∧
      ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (h : Y ⟶ U.1.toScheme), h ≫ U.1.ι = g ≫ m i →
        ((∃ z : Y ⟶ C, z ≫ c = h) ↔ ∃ z : Y ⟶ A i, z ≫ a i = g) := by
    rintro ⟨U, j, hj⟩
    refine ⟨pullback (a j) (l U j hj), pullback.snd _ _, inferInstance, fun i Y g h hg ↦ ?_⟩
    rw [← hcomp j i Y (h ≫ l U j hj) g (by rw [Category.assoc, hl, hg])]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z ≫ pullback.fst _ _, by simp [pullback.condition]⟩
    · rintro ⟨z, hz⟩
      exact ⟨pullback.lift z h hz, pullback.lift_snd _ _ _⟩
  choose C c hc hCa using hC
  obtain ⟨B, b, e, he⟩ := exists_glue S hS hinf C c (by
    intro U V h Y g
    obtain ⟨i, hi⟩ := V.2
    rw [hCa U i Y (g ≫ l U.1 i (h.trans hi)) g (by rw [Category.assoc, hl]),
      hCa V i Y (g ≫ l U.1 i (h.trans hi)) (g ≫ X.homOfLE h)
        (by rw [Category.assoc, Category.assoc, hl, X.homOfLE_ι])])
  refine ⟨B, b, ?_, fun i Y g ↦ ?_⟩
  · apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (coverOfSet S hS)
    intro U
    have := hc U
    change IsClosedImmersion (pullback.snd b U.1.ι)
    rw [← (he U).flip.isoPullback_inv_snd]
    infer_instance
  · let U : S := ⟨(m i).opensRange, i, le_rfl⟩
    have hh : (g ≫ (m i).isoOpensRange.hom) ≫ U.1.ι = g ≫ m i := by simp [U]
    rw [← hCa U i Y g _ hh]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(he U).lift _ z (hh.trans hz.symm), (he U).lift_fst _ _ _⟩
    · rintro ⟨z, hz⟩
      exact ⟨z ≫ e U, by rw [Category.assoc, ← (he U).w, ← Category.assoc, hz, hh]⟩
end GlobalTheory.GlueClosed
