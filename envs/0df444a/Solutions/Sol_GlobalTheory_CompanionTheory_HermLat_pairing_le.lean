-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermLat.pairing_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:31.388813+00:00
-- url     : https://prove2.me/submissions/6bb6392d-a273-4ee3-a984-4ddfc657377b

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_smul_mem_of_isLat
import Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_herm_add_add
import Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_norm_sub_le_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermLat
theorem _root_.solution (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hL : IsLat L Λ) (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ‖h x y‖ ≤ ‖δ‖ := by
  refine (hδ.2.1 _).1 fun t ht => ?_
  have hty : t • y ∈ Λ := smul_mem_of_isLat hL ht hy
  have e := herm_add_add hh x (t • y)
  have e' : h x y * t + s (h x y * t) =
      h (x + t • y) (x + t • y) - h x x - h (t • y) (t • y) := by
    rw [e, hh.2.1 t x y, mul_comm t]
    ring
  rw [e']
  exact norm_sub_le_of_le (norm_sub_le_of_le (hint _ (Λ.add_mem hx hty)) (hint _ hx)) (hint _ hty)
end GlobalTheory.CompanionTheory.HermLat
