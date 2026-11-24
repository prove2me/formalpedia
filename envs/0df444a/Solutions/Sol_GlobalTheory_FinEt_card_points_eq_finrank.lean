-- Prove2me | solution 1 for GlobalTheory.FinEt.card_points_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:45:14.891539+00:00
-- url     : https://prove2.me/submissions/51ae4973-c27f-44a0-9cb6-2c36b9ad41fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_iff
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_of_isSepClosed

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
theorem _root_.solution {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p] [Etale p]
    {k : Type u} [Field k] [IsSepClosed k] (t : Spec (.of k) ⟶ S) (z : Spec (.of k)) :
    Finite {x : Spec (.of k) ⟶ X // x ≫ p = t} ∧
      Nat.card {x : Spec (.of k) ⟶ X // x ≫ p = t} = p.finrank (t z) := by
  obtain ⟨s, hs, ho, hx⟩ :=
    (isSplitOfRank_iff _ _).mp (isSplitOfRank_of_isSepClosed (pullback.snd p t) z)
  rw [← Scheme.Hom.finrank_pullback_snd]
  let F : Fin ((pullback.snd p t).finrank z) → {x : Spec (.of k) ⟶ X // x ≫ p = t} :=
    fun i ↦ ⟨s i ≫ pullback.fst p t, by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]⟩
  have hF : Function.Bijective F := by
    constructor
    · intro i j hij
      have : s i = s j := pullback.hom_ext congr(($hij).1) (by rw [hs, hs])
      exact (hx (s i z)).unique ⟨z, rfl⟩ ⟨z, by rw [this]⟩
    · rintro ⟨x, hxp⟩
      let y : Spec (.of k) ⟶ pullback p t := pullback.lift x (𝟙 _) (by simp [hxp])
      obtain ⟨i, hi⟩ := (hx (y z)).exists
      have hr : Set.range y ⊆ Set.range (s i) := by
        rintro _ ⟨w, rfl⟩
        rwa [Subsingleton.elim w z]
      have h1 := IsOpenImmersion.lift_fac (s i) y hr
      have h2 : IsOpenImmersion.lift (s i) y hr = 𝟙 _ := by
        have := h1 =≫ pullback.snd p t
        rwa [Category.assoc, hs, Category.comp_id, pullback.lift_snd] at this
      rw [h2, Category.id_comp] at h1
      refine ⟨i, Subtype.ext ?_⟩
      simp [F, h1, y]
  exact ⟨.of_surjective F hF.2, by rw [← Nat.card_eq_of_bijective F hF, Nat.card_fin]⟩
end GlobalTheory.FinEt
