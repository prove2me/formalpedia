-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:55:14.447605+00:00
-- url     : https://prove2.me/submissions/b0d67932-d6cd-4549-87fa-1d24f9b794fc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SummableOneDivAbsNormSq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmall
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Primes_summable_one_div_absNorm_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV
namespace GlobalTheory.CompanionTheory.Mass.MeanV
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (C : ℝ), 0 ≤ C → ∀ η : ℝ, 0 < η →
      ∃ T₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ T, T₀ ⊆ T →
        ∀ U : Finset (HeightOneSpectrum (𝓞 F)),
          ∑ D ∈ U.powerset with ¬ D ⊆ T,
            ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ≤ η := by
  intro F _ _ C hC η hη
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => 2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2
    with ha_def
  have ha0 : ∀ v, 0 ≤ a v := fun v => by
    simp only [ha_def]
    positivity
  have hsum : Summable a := by
    refine ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left (2 * C)).congr fun v => ?_
    simp only [ha_def, mul_one_div]

  set S := ∑' v, a v with hS
  have hexpS : 0 < Real.exp S := Real.exp_pos S
  have hq : 0 < η / Real.exp S := div_pos hη hexpS
  set ε := Real.log (1 + η / Real.exp S) with hε_def
  have hε : 0 < ε := Real.log_pos (by linarith)
  have hexpε : Real.exp ε = 1 + η / Real.exp S := Real.exp_log (by linarith)
  obtain ⟨T₀, hT₀⟩ := hsum.vanishing (Iio_mem_nhds hε)
  refine ⟨T₀, fun T hT U => ?_⟩

  have hsplit := Finset.sum_filter_add_sum_filter_not U.powerset (fun D => D ⊆ T)
    (fun D => ∏ v ∈ D, a v)
  have hin : U.powerset.filter (fun D => D ⊆ T) = (U ∩ T).powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
  rw [hin, ← Finset.prod_one_add, ← Finset.prod_one_add] at hsplit
  have hUT := Finset.prod_inter_mul_prod_sdiff U T (fun v => 1 + a v)
  have key : ∑ D ∈ U.powerset with ¬ D ⊆ T, ∏ v ∈ D, a v
      = (∏ v ∈ U ∩ T, (1 + a v)) * ((∏ v ∈ U \ T, (1 + a v)) - 1) := by
    rw [mul_sub, mul_one, hUT]
    linarith
  rw [key]
  have hA : ∏ v ∈ U ∩ T, (1 + a v) ≤ Real.exp S :=
    (Real.prod_one_add_le_exp_sum _ ha0).trans
      (Real.exp_le_exp.mpr (hsum.sum_le_tsum _ (fun v _ => ha0 v)))
  have hB1 : 1 ≤ ∏ v ∈ U \ T, (1 + a v) := by
    have := Finset.prod_le_prod (s := U \ T) (f := fun _ => (1 : ℝ)) (g := fun v => 1 + a v)
      (fun _ _ => zero_le_one) (fun v _ => by linarith [ha0 v])
    simpa using this

  have hdisj : Disjoint (U \ T) T₀ :=
    Finset.disjoint_left.mpr fun v hv hv0 => (Finset.mem_sdiff.mp hv).2 (hT hv0)
  have htail : ∑ v ∈ U \ T, a v < ε := hT₀ _ hdisj
  have hB : ∏ v ∈ U \ T, (1 + a v) ≤ 1 + η / Real.exp S := by
    rw [← hexpε]
    exact (Real.prod_one_add_le_exp_sum _ ha0).trans (Real.exp_le_exp.mpr htail.le)
  calc (∏ v ∈ U ∩ T, (1 + a v)) * ((∏ v ∈ U \ T, (1 + a v)) - 1)
      ≤ Real.exp S * (η / Real.exp S) :=
        mul_le_mul hA (by linarith) (by linarith) hexpS.le
    _ = η := by field_simp
end GlobalTheory.CompanionTheory.Mass.MeanV
