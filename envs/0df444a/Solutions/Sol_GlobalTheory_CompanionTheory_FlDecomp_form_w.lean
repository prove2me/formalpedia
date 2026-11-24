-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.form_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:31:25.826395+00:00
-- url     : https://prove2.me/submissions/93d82b37-913e-4a22-b9b3-32e4d5f4ab8a

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
theorem _root_.solution (hh : IsHerm s h) (hF : IsFrame h δ e f W) (a b : Fin l → L) {w v : V} (hw : w ∈ W) (hv : v ∈ W) :
    h v (∑ j, a j • e j + ∑ j, b j • f j + w) = h v w := by
  have h1 : ∀ j, h v (e j) = 0 := fun j => by
    rw [hh.2.2.1 (e j) v, (hF.2.2.2.1 v hv j).1, map_zero]
  have h2 : ∀ j, h v (f j) = 0 := fun j => by
    rw [hh.2.2.1 (f j) v, (hF.2.2.2.1 v hv j).2, map_zero]
  change hl hh v _ = _
  simp only [map_add, map_sum, map_smul, smul_eq_mul, hl_apply, h1, h2]
  simp
end GlobalTheory.CompanionTheory.FlDecomp
