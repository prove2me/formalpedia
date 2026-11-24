-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:38:20.537058+00:00
-- url     : https://prove2.me/submissions/446bfb5a-474f-48b4-982a-73ab593f4eff

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupNormalInMaximalCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_Normal_entry_le_one
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_Normal_entry_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.Normal
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
namespace GlobalTheory.CompanionTheory.CartGL.Normal
theorem _root_.solution (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1) (c x : GL (Fin n) L)
    (hc : c ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (hx : x ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) :
    c * x * c⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
  have hC : ∀ i j, ‖((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 :=
    entry_le_one fun i j => (hc i j).1
  have hD : ∀ i j, ‖(((c⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 :=
    entry_le_one fun i j => (hc i j).2
  have hCD : ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((c⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  intro i j
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact entry_conj h0 hC hD hCD (fun i j => (hx i j).1) i j
  · have e : (c * x * c⁻¹)⁻¹ = c * x⁻¹ * c⁻¹ := by group
    rw [e, Units.val_mul, Units.val_mul]
    exact entry_conj h0 hC hD hCD (fun i j => (hx i j).2) i j
end GlobalTheory.CompanionTheory.CartGL.Normal
