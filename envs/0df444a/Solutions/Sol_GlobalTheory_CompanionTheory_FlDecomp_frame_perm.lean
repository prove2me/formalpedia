-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.frame_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:04:54.174542+00:00
-- url     : https://prove2.me/submissions/f850c3a1-1c6b-44e2-a53e-da40a5f94013

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_frame_form
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_permMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
variable {s : L →+* L} {δ : L} {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution {δ : L} (hδ : δ ≠ 0) {h : V → V → L} (hh : IsHerm s h) {l : ℕ}
    {e f : Fin l → V} {W : Submodule L V} (hF : IsFrame h δ e f W) (σ : Equiv.Perm (Fin l)) :
    ∃ P : V ≃ₗ[L] V, IsIso h P ∧ (∀ i, P (e i) = e (σ i)) ∧ (∀ i, P (f i) = f (σ i)) ∧ ∀ w ∈ W, P w = w := by
  have hinv : ∀ τ : Equiv.Perm (Fin l), permMap hh δ e f τ ∘ₗ permMap hh δ e f τ.symm = LinearMap.id := by
    intro τ
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
    rw [LinearMap.comp_apply, permMap_apply hδ hh hF _ a b hw, permMap_apply hδ hh hF _ _ _ hw]
    simp
  let P : V ≃ₗ[L] V := LinearEquiv.ofLinear (permMap hh δ e f σ) (permMap hh δ e f σ.symm) (hinv σ)
    (by simpa using hinv σ.symm)
  have hP : ∀ x, P x = permMap hh δ e f σ x := fun _ => rfl
  have he : ∀ j, e j = ∑ i, (Pi.single j (1 : L) : Fin l → L) i • e i + ∑ i, (0 : Fin l → L) i • f i + 0 := fun j => by
    simp [Pi.single_apply, ite_smul]
  have hf : ∀ j, f j = ∑ i, (0 : Fin l → L) i • e i + ∑ i, (Pi.single j (1 : L) : Fin l → L) i • f i + 0 := fun j => by
    simp [Pi.single_apply, ite_smul]
  have hw0 : ∀ w, w = ∑ i, (0 : Fin l → L) i • e i + ∑ i, (0 : Fin l → L) i • f i + w := fun w => by simp
  refine ⟨P, fun x y => ?_, fun i => ?_, fun i => ?_, fun w hw => ?_⟩
  · obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
    obtain ⟨a', b', w', hw', rfl⟩ := hF.2.2.2.2.2 y
    rw [hP, hP, permMap_apply hδ hh hF _ _ _ hw, permMap_apply hδ hh hF _ _ _ hw', frame_form hh hF _ _ _ _ hw' hw,
      frame_form hh hF _ _ _ _ hw' hw,
      Equiv.sum_comp σ.symm (fun j => a' j * s (b j * δ)), Equiv.sum_comp σ.symm (fun j => b' j * s (a j * s δ))]
  · rw [hP, he i, permMap_apply hδ hh hF _ _ _ W.zero_mem]
    simp [Pi.single_apply, ite_smul, Equiv.symm_apply_eq]
  · rw [hP, hf i, permMap_apply hδ hh hF _ _ _ W.zero_mem]
    simp [Pi.single_apply, ite_smul, Equiv.symm_apply_eq]
  · rw [hP]
    conv_lhs => rw [hw0 w]
    rw [permMap_apply hδ hh hF _ _ _ hw]
    simp
end GlobalTheory.CompanionTheory.FlDecomp
