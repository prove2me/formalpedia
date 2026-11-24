-- Prove2me | solution 1 for GlobalTheory.mvPowerSeries_mem_map_C_of_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:23:48.83422+00:00
-- url     : https://prove2.me/submissions/3a8ae0be-2e2c-46b1-86a0-eeea1fa05952

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesMemMapCOfCoeffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {σ R : Type} [CommRing R] (I : Ideal R)
    (hI : I.FG) (g : MvPowerSeries σ R) (hg : ∀ n, MvPowerSeries.coeff n g ∈ I) :
    g ∈ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) I := by
  classical
  obtain ⟨s, rfl⟩ := hI
  have h : ∀ n, ∃ c : R → R, ∑ a ∈ s, c a * a = MvPowerSeries.coeff n g := by
    intro n
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 (hg n)
    exact ⟨c, by simpa [smul_eq_mul] using hc⟩
  choose c hc using h
  let G : R → MvPowerSeries σ R := fun a n => c n a
  have : g = ∑ a ∈ s, G a * MvPowerSeries.C a := by
    ext n
    rw [map_sum, ← hc n]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPowerSeries.coeff_mul_C]
    rfl
  rw [this]
  refine Ideal.sum_mem _ fun a ha => Ideal.mul_mem_left _ _ ?_
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ha)
end GlobalTheory
