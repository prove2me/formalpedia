-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.tor_w
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:42.655831+00:00
-- url     : https://prove2.me/submissions/3066c631-8a93-495c-9d44-600bedd7772a

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_pair_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.FrameTorus.pair_apply

set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrameTorus
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
variable {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
namespace GlobalTheory.CompanionTheory.FrameTorus
theorem _root_.solution (hH : IsHerm s h) (hF : IsFrame h δ e f W) (u : Fin l → L) {w : V} (hw : w ∈ W) :
    tor hH δ e f u w = w := by
  rw [tor_apply]
  simp [(hF.2.2.2.1 w hw _).1, (hF.2.2.2.1 w hw _).2]
end GlobalTheory.CompanionTheory.FrameTorus
