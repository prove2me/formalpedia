-- Prove2me | solution 1 for GlobalTheory.FinEt.isIso_iff_bijective_algClosed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:20.639067+00:00
-- url     : https://prove2.me/submissions/5f33b486-8497-4de2-96a7-54982997b36d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_exists_algClosed_point

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
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f] :
    IsIso f ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k],
      Function.Bijective fun x : Spec (.of k) ⟶ X ↦ x ≫ f := by
  constructor
  · intro _ k _ _
    exact ⟨fun a b h ↦ (cancel_mono f).mp h, fun y ↦ ⟨y ≫ inv f, by simp⟩⟩
  intro h
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨k, _, _, a, ha⟩ := exists_algClosed_point Y y
    obtain ⟨b, rfl⟩ := (h k).2 a
    obtain ⟨z⟩ : Nonempty (Spec (.of k)) := inferInstance
    refine ⟨b z, ?_⟩
    rw [← Set.mem_singleton_iff, ← ha, ← Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hdiag : IsIso (pullback.diagonal f) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [eq_top_iff]
    intro z _
    obtain ⟨k, _, _, a, ha⟩ := exists_algClosed_point _ z
    have e : a ≫ pullback.fst f f = a ≫ pullback.snd f f :=
      (h k).1 (by simp [pullback.condition])
    have e' : a = (a ≫ pullback.fst f f) ≫ pullback.diagonal f := by
      apply pullback.hom_ext <;> simp [e]
    have : z ∈ Set.range a := by simp [ha]
    obtain ⟨w, rfl⟩ := this
    refine ⟨(a ≫ pullback.fst f f) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← e']
  have hsnd : IsIso (pullback.snd f f) :=
    IsIso.of_isIso_fac_left (pullback.diagonal_snd f)
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  funext y
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← Scheme.Hom.finrank_pullback_snd, Scheme.Hom.finrank_eq_one_of_isIso]
  rfl
end GlobalTheory.FinEt
