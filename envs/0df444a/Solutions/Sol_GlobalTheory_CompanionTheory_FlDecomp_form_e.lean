-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.form_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:41.179792+00:00
-- url     : https://prove2.me/submissions/efb42843-ece9-449d-9988-cb57acad7c6f

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_hl_apply

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
    h (e i) (∑ j, a j • e j + ∑ j, b j • f j + w) = b i * δ := by
  change hl hh (e i) _ = _
  simp only [map_add, map_sum, map_smul, smul_eq_mul, hl_apply, hF.1, hF.2.2.1, (hF.2.2.2.1 w hw i).1]
  simp
end GlobalTheory.CompanionTheory.FlDecomp
