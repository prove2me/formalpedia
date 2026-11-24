-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.tor_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:54:02.821054+00:00
-- url     : https://prove2.me/submissions/bb9940ac-7d25-45d4-9ea2-f38a9305c33b

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_gens_induction
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_pair_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_smul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_iso_gens
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
theorem _root_.solution (hs : ∀ x, s (s x) = x) (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0)
    (u : Fin l → L) (hu : ∀ i, u i ≠ 0) (x y : V) :
    h (tor hH δ e f u x) (tor hH δ e f u y) = h x y := by
  have hz : ∀ z, h z 0 = 0 := fun z => by simpa using hH.2.1 0 z 0
  have hz' : ∀ z, h 0 z = 0 := fun z => by simpa using smul_left hH 0 0 z
  have step : ∀ g ∈ gens e f W, ∀ y, h (tor hH δ e f u g) (tor hH δ e f u y) = h g y := by
    intro g hg
    refine gens_induction hF (fun y hy => tor_iso_gens hs hH hF hδ u hu hg hy) ?_ ?_ ?_
    · simp [hz]
    · intro y y' hy hy'
      simp only [map_add, hH.1, hy, hy']
    · intro a y hy
      simp only [map_smul, hH.2.1, hy]
  refine gens_induction hF (P := fun x => ∀ y, h (tor hH δ e f u x) (tor hH δ e f u y) = h x y)
    step ?_ ?_ ?_ x y
  · simp [hz']
  · intro x x' hx hx' y
    rw [map_add, add_left hH, hx, hx', add_left hH]
  · intro a x hx y
    simp only [map_smul, smul_left hH, hx]
end GlobalTheory.CompanionTheory.FrameTorus
