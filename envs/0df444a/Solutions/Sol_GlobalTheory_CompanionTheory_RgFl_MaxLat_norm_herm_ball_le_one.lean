-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.MaxLat.norm_herm_ball_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:08:34.485333+00:00
-- url     : https://prove2.me/submissions/1c08e0d5-2181-4dd4-a699-b73483ac5614

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_herm_eq_sum

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
theorem _root_.solution {s : L →+* L} {h : V → V → L} (hs : IsInv s) (hh : IsHerm s h)
    {m : ℕ} (b : Module.Basis (Fin m) L V) (hb : ∀ i j, ‖h (b i) (b j)‖ ≤ 1) {x : V}
    (hx : x ∈ ball b) : ‖h x x‖ ≤ 1 := by
  have h1 : ∀ j, ‖h (b j) x‖ ≤ 1 := fun j => by
    rw [herm_eq_sum hh b]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hx i) (norm_nonneg _) (hb j i)
  rw [herm_eq_sum hh b]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  rw [norm_mul, hh.2.2.1 (b j) x, hs.2.1]
  exact mul_le_one₀ (hx j) (norm_nonneg _) (h1 j)
end GlobalTheory.CompanionTheory.RgFl.MaxLat
