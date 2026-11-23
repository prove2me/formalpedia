-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.tor_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:43.031367+00:00
-- url     : https://prove2.me/submissions/692d24fa-4b3b-4835-a3da-a1b31e3f7a05

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_pair_apply
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
namespace GlobalTheory.CompanionTheory.FrameTorus
theorem _root_.solution {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V)
    (u : Fin l → L) (x : V) :
    tor hH δ e f u x = x + (∑ i, ((u i - 1) * (s δ)⁻¹) • (h (f i) x • e i)) +
      ∑ i, (((s (u i))⁻¹ - 1) * δ⁻¹) • (h (e i) x • f i) := by
  simp [tor, LinearMap.add_apply, LinearMap.sum_apply]
end GlobalTheory.CompanionTheory.FrameTorus
