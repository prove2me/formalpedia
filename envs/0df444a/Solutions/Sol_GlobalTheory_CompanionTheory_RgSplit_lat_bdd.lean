-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.lat_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:59.795088+00:00
-- url     : https://prove2.me/submissions/e75007e8-173c-4987-b785-f8973c905d55

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_smul_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_absorb

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgSplit
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution {V' : Type} [AddCommGroup V'] [Module L V'] {Λ : AddSubgroup V}
    {Λ₀ : AddSubgroup V'} (hΛ : IsLat L Λ) (hΛ₀ : IsLat L Λ₀) (P : V →ₗ[L] V') :
    ∃ c : L, c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ ∀ x ∈ Λ, c • P x ∈ Λ₀ := by
  obtain ⟨m, b, hb⟩ := hΛ
  obtain ⟨c, hc0, hc1, hc⟩ := lat_absorb hΛ₀ (fun i => P (b i))
  refine ⟨c, hc0, hc1, fun x hx => ?_⟩
  have hx' := (hb x).1 hx
  have key : c • P x = ∑ i, b.repr x i • (c • P (b i)) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [key]
  exact AddSubgroup.sum_mem _ fun i _ => lat_smul_mem hΛ₀ (hx' i) (hc i)
end GlobalTheory.CompanionTheory.RgSplit
