-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.form_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:23.334448+00:00
-- url     : https://prove2.me/submissions/d972281b-94c5-4b8c-aaa0-c2ea6bcda9e4

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_hl_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_h_fe

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
theorem _root_.solution (hh : IsHerm s h) (hF : IsFrame h δ e f W) (a b : Fin l → L) {w : V} (hw : w ∈ W) (i : Fin l) :
    h (f i) (∑ j, a j • e j + ∑ j, b j • f j + w) = a i * s δ := by
  change hl hh (f i) _ = _
  simp only [map_add, map_sum, map_smul, smul_eq_mul, hl_apply, h_fe hh hF, hF.2.1, (hF.2.2.2.1 w hw i).2]
  simp
end GlobalTheory.CompanionTheory.FlDecomp
