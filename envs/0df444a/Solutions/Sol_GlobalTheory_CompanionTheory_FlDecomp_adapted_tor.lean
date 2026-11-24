-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.adapted_tor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:54.425004+00:00
-- url     : https://prove2.me/submissions/bcf6e0a1-56a8-4b98-81d3-92824071ef9a

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_mem_pull

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
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution {s : L →+* L} (hs : IsInv s) {h : V → V → L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
    {u : Fin l → L} {Λ : AddSubgroup V} {t : V ≃ₗ[L] V} (hu : ∀ i, u i ≠ 0) (ht : IsTor s e f W u t)
    (hA : IsAdapted h e f W u Λ) : IsAdapted h e f W (fun _ => 1) (pull t Λ) := by
  intro a b w hw
  rw [mem_pull]
  have : t (∑ i, a i • e i + ∑ i, b i • f i + w) =
      ∑ i, (a i * u i) • e i + ∑ i, (b i * (s (u i))⁻¹) • f i + w := by
    simp [map_add, map_sum, ht.1, ht.2.1, ht.2.2 w hw, smul_smul]
  rw [this, hA _ _ w hw]
  have hn : ∀ i, ‖s (u i)‖ = ‖u i‖ := fun i => hs.2.1 _
  have hp : ∀ i, 0 < ‖u i‖ := fun i => norm_pos_iff.2 (hu i)
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) Iff.rfl)
  · rw [norm_mul, norm_one]
    exact ⟨fun H => le_of_mul_le_mul_right (by simpa using H) (hp i), fun H => by simpa using mul_le_mul_of_nonneg_right H (hp i).le⟩
  · rw [norm_mul, norm_inv, hn, norm_one]
    have := inv_pos.2 (hp i)
    exact ⟨fun H => le_of_mul_le_mul_right (by simpa using H) this, fun H => by simpa using mul_le_mul_of_nonneg_right H this.le⟩
end GlobalTheory.CompanionTheory.FlDecomp
