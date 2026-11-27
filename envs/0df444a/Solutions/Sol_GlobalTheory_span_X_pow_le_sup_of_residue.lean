-- Prove2me | solution 1 for GlobalTheory.span_X_pow_le_sup_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:40:53.44181+00:00
-- url     : https://prove2.me/submissions/2fb7ff3b-8e49-4a9d-9597-2c0518a72225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesMemMapCOfCoeffMem
import Theorems.Thm_GlobalTheory_mvPowerSeries_map_surjective
import Theorems.Thm_GlobalTheory_mvPowerSeries_mem_map_C_of_coeff_mem

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
theorem _root_.solution :
    ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] (σ ι : Type) [Finite σ] (f : ι → MvPowerSeries σ T) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (f j)) → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ T)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : T →+* MvPowerSeries σ T) (maximalIdeal T) := by
  intro T _ _ _ σ ι _ f M h
  set φ : MvPowerSeries σ T →+* MvPowerSeries σ (ResidueField T) :=
    MvPowerSeries.map (residue T) with hφ
  have hs : Function.Surjective φ := mvPowerSeries_map_surjective _ residue_surjective
  have h1 : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField T))) =
      Ideal.map φ (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ T))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    ext1 i
    simp [hφ]
  have h2 : Ideal.span (Set.range fun j => φ (f j)) = Ideal.map φ (Ideal.span (Set.range f)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [h1, h2, ← Ideal.map_pow, Ideal.map_le_iff_le_comap,
    Ideal.comap_map_of_surjective φ hs] at h
  refine h.trans (sup_le_sup_left ?_ _)
  intro g hg
  refine mvPowerSeries_mem_map_C_of_coeff_mem _ (IsNoetherian.noetherian _) g fun n => ?_
  have h0 : φ g = 0 := by simpa using hg
  rw [← residue_eq_zero_iff]
  have := congrArg (MvPowerSeries.coeff n) h0
  simpa [hφ] using this
end GlobalTheory
