-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.frame_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:29.226788+00:00
-- url     : https://prove2.me/submissions/5ca07489-26bd-448c-b917-f2b09742f583

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_hl_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_form_e
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_form_f
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_form_w

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
theorem _root_.solution (hh : IsHerm s h) (hF : IsFrame h δ e f W) (a b a' b' : Fin l → L) {w w' : V} (hw : w ∈ W)
    (hw' : w' ∈ W) :
    h (∑ j, a' j • e j + ∑ j, b' j • f j + w') (∑ j, a j • e j + ∑ j, b j • f j + w) =
      ∑ j, a j * s (b' j * δ) + ∑ j, b j * s (a' j * s δ) + s (h w w') := by
  set y := ∑ j, a' j • e j + ∑ j, b' j • f j + w' with hy
  have h1 : ∀ j, h y (e j) = s (b' j * δ) := fun j => by
    rw [hh.2.2.1 (e j) y, hy, form_e hh hF a' b' hw' j]
  have h2 : ∀ j, h y (f j) = s (a' j * s δ) := fun j => by
    rw [hh.2.2.1 (f j) y, hy, form_f hh hF a' b' hw' j]
  have h3 : h y w = s (h w w') := by
    rw [hh.2.2.1 w y, hy, form_w hh hF a' b' hw' hw]
  change hl hh y _ = _
  simp only [map_add, map_sum, map_smul, smul_eq_mul, hl_apply, h1, h2, h3]
end GlobalTheory.CompanionTheory.FlDecomp
