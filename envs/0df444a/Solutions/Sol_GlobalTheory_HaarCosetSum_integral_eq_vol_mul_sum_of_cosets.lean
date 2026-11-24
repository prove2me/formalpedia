-- Prove2me | solution 1 for GlobalTheory.HaarCosetSum.integral_eq_vol_mul_sum_of_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:14.886624+00:00
-- url     : https://prove2.me/submissions/222d3252-deb1-4b8a-a062-a5d2d379046b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarIntegralOverCosetRepresentatives

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open scoped Pointwise
open GlobalTheory GlobalTheory.HaarCosetSum
namespace GlobalTheory.HaarCosetSum
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (K : Subgroup (GL (Fin a) k)),
    IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) → ∀ F : GL (Fin a) k → ℂ,
    (∀ g x, x ∈ K → F (g * x) = F g) → ∀ R : Finset (GL (Fin a) k),
    (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') → (∀ g, F g ≠ 0 → ∃ r ∈ R, r⁻¹ * g ∈ K) →
    ∫ g, F g ∂(haarVol (KO k (Fin a))) = ((haarVol (KO k (Fin a))).real (K : Set (GL (Fin a) k)) : ℂ) * ∑ r ∈ R, F r := by
  intro k _ _ _ _ _ _ a K hKo hKle F hF R hR hsupp
  set μ := haarVol (KO k (Fin a)) with hμ
  have hKm : MeasurableSet (K : Set (GL (Fin a) k)) := hKo.measurableSet

  have hval : ∀ r g, r⁻¹ * g ∈ K → F g = F r := by
    intro r g h
    have := hF r (r⁻¹ * g) h
    rwa [mul_inv_cancel_left] at this

  have hpt : ∀ g, F g = ∑ r ∈ R, ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r) g) := by
    intro g
    by_cases hg : F g = 0
    · rw [hg]
      refine (Finset.sum_eq_zero fun r _ => ?_).symm
      by_cases hm : g ∈ r • (K : Set (GL (Fin a) k))
      · rw [Set.indicator_of_mem hm, ← hval r g ((mem_leftCoset_iff r).1 hm), hg]
      · rw [Set.indicator_of_notMem hm]
    · obtain ⟨r₀, hr₀, hg₀⟩ := hsupp g hg
      rw [Finset.sum_eq_single r₀]
      · rw [Set.indicator_of_mem ((mem_leftCoset_iff r₀).2 hg₀), hval r₀ g hg₀]
      · intro r hr hne
        rw [Set.indicator_of_notMem]
        intro hm
        have h1 : r⁻¹ * g ∈ K := (mem_leftCoset_iff r).1 hm
        have h2 : r⁻¹ * r₀ ∈ K := by
          have := K.mul_mem h1 (K.inv_mem hg₀)
          simpa [mul_assoc] using this
        exact hne (hR r hr r₀ hr₀ h2)
      · intro h; exact absurd hr₀ h
  have hfin : μ (K : Set (GL (Fin a) k)) ≠ ⊤ :=
    ((measure_mono hKle).trans_lt isCompact_KO.measure_lt_top).ne
  have hcos : ∀ r : GL (Fin a) k, μ (r • (K : Set (GL (Fin a) k))) = μ K := fun r => measure_smul μ r _
  have hint : ∀ r ∈ R, Integrable ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r)) μ := by
    intro r _
    rw [integrable_indicator_iff (hKm.const_smul r)]
    exact integrableOn_const (by rw [hcos]; exact hfin)
  calc ∫ g, F g ∂μ = ∫ g, ∑ r ∈ R, ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r) g) ∂μ := by
          congr 1; funext g; exact hpt g
    _ = ∑ r ∈ R, ∫ g, ((r • (K : Set (GL (Fin a) k))).indicator (fun _ => F r) g) ∂μ :=
          integral_finset_sum R hint
    _ = ∑ r ∈ R, (μ.real (K : Set (GL (Fin a) k)) : ℂ) * F r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [integral_indicator_const _ (hKm.const_smul r), Measure.real, hcos, ← Measure.real,
            Complex.real_smul]
    _ = _ := by rw [Finset.mul_sum]
end GlobalTheory.HaarCosetSum
