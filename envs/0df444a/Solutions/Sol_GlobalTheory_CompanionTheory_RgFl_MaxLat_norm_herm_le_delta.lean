-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.MaxLat.norm_herm_le_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:25:19.155739+00:00
-- url     : https://prove2.me/submissions/fafab1d3-808d-4c40-88b0-fe591afe63c2

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_herm_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_norm_sub_le_max_of_ultrametric_field

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.MaxLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.RgFl.MaxLat
theorem _root_.solution {s : L →+* L} {δ : L} {h : V → V → L} (hδ : IsDelta s δ)
    (hh : IsHerm s h) {M : AddSubgroup V} (hO : ∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ M, a • x ∈ M)
    (hM : ∀ x ∈ M, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ M) (hy : y ∈ M) : ‖h x y‖ ≤ ‖δ‖ := by
  refine (hδ.2.1 (h x y)).1 fun t ht => ?_
  have hy' : t • y ∈ M := hO t ht y hy
  have e1 : h x (t • y) = h x y * t := by rw [hh.2.1, mul_comm]
  have e2 : h (t • y) x = s (h x y * t) := by rw [hh.2.2.1 x (t • y), e1]
  have e3 : h (x + t • y) (x + t • y)
      = h x x + (h x y * t + s (h x y * t)) + h (t • y) (t • y) := by
    rw [herm_add_left hh, hh.1, hh.1, e1, e2]; ring
  have e4 : h x y * t + s (h x y * t)
      = h (x + t • y) (x + t • y) - h x x - h (t • y) (t • y) := by
    rw [e3]; ring
  rw [e4]
  exact (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le
    ((norm_sub_le_max_of_ultrametric_field _ _).trans
      (max_le (hM _ (M.add_mem hx hy')) (hM _ hx))) (hM _ hy'))
end GlobalTheory.CompanionTheory.RgFl.MaxLat
