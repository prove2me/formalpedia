-- Prove2me | solution 1 for GlobalTheory.IwasawaShape.exists_lintegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:14:11.174844+00:00
-- url     : https://prove2.me/submissions/b59ec9ad-a877-418c-8653-12069f0c7fd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMapMulRightEqSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLintegralEqOfMeasurable
import Theorems.Thm_GlobalTheory_IwasawaShape_exists_lintegral_eq_of_measurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.IwasawaShape
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.IwasawaShape
theorem _root_.solution (N M K : Subgroup G) (hN : IsClosed (N : Set G))
    (hM : IsClosed (M : Set G)) (hK : IsCompact (K : Set G)) (hnorm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N)
    (huniq : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1) (hdec : ∀ g, ∃ u ∈ N, ∃ m ∈ M, ∃ k ∈ K, g = u * m * k)
    (μ μN μM μK : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (hμ : μ ≠ 0)
    [IsFiniteMeasureOnCompacts μN] [IsFiniteMeasureOnCompacts μM] [IsProbabilityMeasure μK]
    (hN0 : μN ≠ 0) (hM0 : μM ≠ 0)
    (h1 : μN (N : Set G)ᶜ = 0) (h2 : μM (M : Set G)ᶜ = 0)
    (iN : ∀ s ∈ N, μN.map (fun g => s * g) = μN) (iM : ∀ s ∈ M, μM.map (fun g => s * g) = μM)
    (iK : ∀ s ∈ K, μK.map (fun g => s * g) = μK) (δ : G → ENNReal)
    (hmod : ∀ m ∈ M, μN.map (fun u => m * u * m⁻¹) = δ m • μN) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂μ = c * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN := by
  obtain ⟨i, hi⟩ : ∃ i, μN (compactCovering G i) ≠ 0 := by
    by_contra h
    push Not at h
    exact hN0 (Measure.measure_univ_eq_zero.1 (by rw [← iUnion_compactCovering]; exact measure_iUnion_null h))
  have hC := isCompact_compactCovering G i
  generalize compactCovering G i = C at hi hC
  set δ' : G → ENNReal := fun m => μN ((fun u => m * u * m⁻¹) ⁻¹' C) / μN C with hδ'
  have hm' : Measurable δ' := by
    refine Measurable.div_const ?_ _
    exact measurable_measure_prodMk_left (s := (fun z : G × G => z.1 * z.2 * z.1⁻¹) ⁻¹' C)
      ((measurable_mul.mul measurable_fst.inv) hC.measurableSet)
  have he : ∀ m ∈ M, δ' m = δ m := by
    intro m hm
    simp only [hδ']
    rw [← Measure.map_apply ((measurable_const_mul m).mul_const _) hC.measurableSet, hmod m hm,
      Measure.smul_apply, smul_eq_mul, mul_div_assoc, ENNReal.div_self hi hC.measure_lt_top.ne, mul_one]
  obtain ⟨c, hc0, hc1, hc⟩ := exists_lintegral_eq_of_measurable N M K hN hM hK hnorm huniq hdec μ μN μM μK hμ
    C hC hi hM0 h1 h2 iN iM iK δ' hm' (fun m hm => by rw [he m hm, hmod m hm])
  refine ⟨c, hc0, hc1, fun φ hφ => ?_⟩
  rw [hc φ hφ]
  congr 1
  refine lintegral_congr fun u => lintegral_congr_ae ?_
  filter_upwards [mem_ae_iff.2 h2] with m hm
  rw [he m hm]
end GlobalTheory.IwasawaShape
