-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.tor_iso_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:35:53.707366+00:00
-- url     : https://prove2.me/submissions/91330143-3702-4c26-9a26-b3a8c04734c4

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_pair_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_smul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_pair_fe
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_e
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_f
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_tor_w
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
    (u : Fin l → L) (hu : ∀ i, u i ≠ 0) {x y : V} (hx : x ∈ gens e f W) (hy : y ∈ gens e f W) :
    h (tor hH δ e f u x) (tor hH δ e f u y) = h x y := by
  have hsu : ∀ i, s (u i) ≠ 0 := fun i => (map_ne_zero s).2 (hu i)
  have hwe : ∀ {w : V}, w ∈ W → ∀ i, h w (e i) = 0 := fun hw i => by
    rw [hH.2.2.1 (e i) _, (hF.2.2.2.1 _ hw i).1, map_zero]
  have hwf : ∀ {w : V}, w ∈ W → ∀ i, h w (f i) = 0 := fun hw i => by
    rw [hH.2.2.1 (f i) _, (hF.2.2.2.1 _ hw i).2, map_zero]
  rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | hx <;> rcases hy with (⟨j, rfl⟩ | ⟨j, rfl⟩) | hy
  · simp [tor_e hH hF hδ, smul_left hH, hH.2.1, hF.1]
  · rw [tor_e hH hF hδ, tor_f hH hF hδ, smul_left hH, hH.2.1, hF.2.2.1]
    by_cases hij : i = j
    · subst hij
      simp [hsu i]
    · simp [hij]
  · rw [tor_e hH hF hδ, tor_w hH hF u hy, smul_left hH, (hF.2.2.2.1 _ hy i).1, mul_zero]
  · rw [tor_f hH hF hδ, tor_e hH hF hδ, smul_left hH, hH.2.1, pair_fe hH hF]
    by_cases hij : i = j
    · subst hij
      simp [hs, hu i]
    · simp [hij]
  · simp [tor_f hH hF hδ, smul_left hH, hH.2.1, hF.2.1]
  · rw [tor_f hH hF hδ, tor_w hH hF u hy, smul_left hH, (hF.2.2.2.1 _ hy i).2, mul_zero]
  · rw [tor_w hH hF u hx, tor_e hH hF hδ, hH.2.1, hwe hx, mul_zero]
  · rw [tor_w hH hF u hx, tor_f hH hF hδ, hH.2.1, hwf hx, mul_zero]
  · rw [tor_w hH hF u hx, tor_w hH hF u hy]
end GlobalTheory.CompanionTheory.FrameTorus
