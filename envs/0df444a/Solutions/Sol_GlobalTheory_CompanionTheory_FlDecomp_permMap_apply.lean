-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.permMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:31:35.959165+00:00
-- url     : https://prove2.me/submissions/15ead7ef-ffb2-4a3b-bdff-976f85c04dce

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_hl_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_form_e
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_form_f

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
theorem _root_.solution (hδ : δ ≠ 0) (hh : IsHerm s h) (hF : IsFrame h δ e f W) (τ : Equiv.Perm (Fin l))
    (a b : Fin l → L) {w : V} (hw : w ∈ W) :
    permMap hh δ e f τ (∑ j, a j • e j + ∑ j, b j • f j + w) =
      ∑ j, a (τ.symm j) • e j + ∑ j, b (τ.symm j) • f j + w := by
  have hsδ : s δ ≠ 0 := (map_ne_zero s).2 hδ
  have he : ∑ j, a (τ.symm j) • e j = ∑ i, a i • e (τ i) :=
    (Equiv.sum_comp τ (fun j => a (τ.symm j) • e j)).symm.trans (by simp)
  have hf : ∑ j, b (τ.symm j) • f j = ∑ i, b i • f (τ i) :=
    (Equiv.sum_comp τ (fun j => b (τ.symm j) • f j)).symm.trans (by simp)
  rw [he, hf]
  simp only [permMap, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, hl_apply, form_e hh hF a b hw, form_f hh hF a b hw, smul_eq_mul]
  have c1 : ∀ i, (s δ)⁻¹ * (a i * s δ) = a i := fun i => by field_simp
  have c2 : ∀ i, δ⁻¹ * (b i * δ) = b i := fun i => by field_simp
  simp only [c1, c2, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel
end GlobalTheory.CompanionTheory.FlDecomp
