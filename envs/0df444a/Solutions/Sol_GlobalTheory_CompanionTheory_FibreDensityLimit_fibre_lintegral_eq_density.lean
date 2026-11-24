-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FibreDensityLimit.fibre_lintegral_eq_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:03:32.375073+00:00
-- url     : https://prove2.me/submissions/4f2746a7-f461-4cd4-bc09-cdc0adea355f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationInjectiveOpenMap
import Theorems.Thm_GlobalTheory_CompanionTheory_FibreDensityLimit_ofReal_le_of_forall_compact
import Theorems.Thm_GlobalTheory_CompanionTheory_FibreDensityLimit_exists_cutoffs
import Theorems.Thm_GlobalTheory_CompanionTheory_FibreDensityLimit_lintegral_slice_test

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibreDensityLimit
open Set
namespace GlobalTheory.CompanionTheory.FibreDensityLimit
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U : Set V) (fib : X → Measure V), IsOpen U → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ φ : V → ℝ, Continuous φ → (∀ v, 0 ≤ φ v) → ∀ D : X → ℝ, Continuous D → (∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (φ v) ∂μ = ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν) → (∀ ε : ℝ, 0 < ε → ∃ K : Set V, IsCompact K ∧ K ⊆ U ∧ ∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A) ∩ Kᶜ, ENNReal.ofReal (φ v) ∂μ ≤ ENNReal.ofReal ε * ν A) → ∀ s₀ : X, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s₀) = ENNReal.ofReal (D s₀) := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ f g ι hι hgc hfg U fib hUo h φ hφ hφ0 D hD hDA hK s0
  have hg : Measurable g := hgc.measurable
  have hUm : MeasurableSet U := hUo.measurableSet
  have htest : ∀ ψ : V → ℝ, Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∀ v, 0 ≤ ψ v) → (∀ v, ψ v ≤ φ v) →
      ENNReal.ofReal (∫ v, ψ v ∂(fib s0)) ≤ ENNReal.ofReal (D s0) := by
    intro ψ hψ hψc hψU hψ0 hψφ
    have hcont : Continuous fun s => ∫ v, ψ v ∂(fib s) :=
      continuousOn_univ.mp (h.2.2 ψ hψ hψc hψU).2
    have hcmp : ∀ A : Set X, IsCompact A →
        ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v ∂(fib s)) ∂ν ≤
          ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν + ENNReal.ofReal 0 * ν A := by
      intro A hA
      rw [ENNReal.ofReal_zero, zero_mul, add_zero,
        ← lintegral_slice_test h hUm hι hg hfg hψ hψc hψU hψ0 hA.measurableSet,
        ← hDA A hA.measurableSet]
      exact lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hψφ v)
    simpa using ofReal_le_of_forall_compact ν hcont hD 0 hcmp s0
  have hae : ∀ᵐ v ∂(fib s0), v ∈ f ⁻¹' {ι s0} ∩ U := (MeasureTheory.mem_ae_iff).mpr (h.1 s0)
  have hint : ∀ θ : V → ℝ, Continuous θ → HasCompactSupport θ → tsupport θ ⊆ U → (∀ v, 0 ≤ θ v) →
      ENNReal.ofReal (∫ v, θ v ∂(fib s0)) = ∫⁻ v, ENNReal.ofReal (θ v) ∂(fib s0) :=
    fun θ hθ hθc hθU hθ0 => ofReal_integral_eq_lintegral_ofReal
      ((h.2.2 θ hθ hθc hθU).1 s0 (Set.mem_univ _)) (Filter.Eventually.of_forall hθ0)
  obtain ⟨χ, hχc, hχs, hχU, hχb, hχm, hχ1⟩ := exists_cutoffs hUo
  have hψn : ∀ n, ∫⁻ v, ENNReal.ofReal (χ n v * φ v) ∂(fib s0) ≤ ENNReal.ofReal (D s0) := by
    intro n
    have hc : Continuous fun v => χ n v * φ v := (hχc n).mul hφ
    have hs : HasCompactSupport fun v => χ n v * φ v := (hχs n).mul_right
    have hsU : tsupport (fun v => χ n v * φ v) ⊆ U := tsupport_mul_subset_left.trans (hχU n)
    have h0 : ∀ v, 0 ≤ χ n v * φ v := fun v => mul_nonneg (hχb n v).1 (hφ0 v)
    rw [← hint _ hc hs hsU h0]
    exact htest _ hc hs hsU h0 fun v => mul_le_of_le_one_left (hφ0 v) (hχb n v).2
  have hX : ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s0) ≤ ENNReal.ofReal (D s0) := by
    have heq : ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s0) =
        ∫⁻ v, ⨆ n, ENNReal.ofReal (χ n v * φ v) ∂(fib s0) := by
      refine lintegral_congr_ae (hae.mono fun v hv => ?_)
      obtain ⟨n, hn⟩ := hχ1 v hv.2
      refine le_antisymm (le_iSup_of_le n (by rw [hn, one_mul])) (iSup_le fun m => ?_)
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hφ0 v) (hχb m v).2)
    rw [heq, lintegral_iSup (f := fun n v => ENNReal.ofReal (χ n v * φ v)) (fun n => ENNReal.measurable_ofReal.comp ((hχc n).mul hφ).measurable)
      (fun m n hmn v => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hχm v hmn) (hφ0 v)))]
    exact iSup_le hψn
  refine le_antisymm hX (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
  obtain ⟨K, hKc, hKU, hKε⟩ := hK ε (NNReal.coe_pos.mpr hε)
  obtain ⟨L, -, hLc, hKL, hLU⟩ := exists_compact_closed_between hKc hUo hKU
  obtain ⟨ψ, hψ1, hψ0', hψs, hψb⟩ := exists_continuous_one_zero_of_isCompact hKc
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)
  have hψU : tsupport ψ ⊆ U := by
    refine (closure_minimal ?_ hLc).trans hLU
    intro v hv
    by_contra hvL
    exact hv (hψ0' (fun hi => hvL (interior_subset hi)))
  have hc : Continuous fun v => ψ v * φ v := ψ.continuous.mul hφ
  have hs : HasCompactSupport fun v => ψ v * φ v := hψs.mul_right
  have hsU : tsupport (fun v => ψ v * φ v) ⊆ U := tsupport_mul_subset_left.trans hψU
  have h0 : ∀ v, 0 ≤ ψ v * φ v := fun v => mul_nonneg (hψb v).1 (hφ0 v)
  have hcont : Continuous fun s => ∫ v, ψ v * φ v ∂(fib s) :=
    continuousOn_univ.mp (h.2.2 _ hc hs hsU).2
  have hcmp : ∀ A : Set X, IsCompact A →
      ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν ≤
        ∫⁻ s in A, ENNReal.ofReal (∫ v, ψ v * φ v ∂(fib s)) ∂ν + ENNReal.ofReal ε * ν A := by
    intro A hA
    have hAm := hA.measurableSet
    rw [← hDA A hAm, ← lintegral_slice_test h hUm hι hg hfg hc hs hsU h0 hAm]
    calc ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (φ v) ∂μ
        ≤ ∫⁻ v in f ⁻¹' (ι '' A), (ENNReal.ofReal (ψ v * φ v) +
            Kᶜ.indicator (fun v => ENNReal.ofReal (φ v)) v) ∂μ := by
          refine lintegral_mono fun v => ?_
          by_cases hv : v ∈ K
          · rw [Set.indicator_of_notMem (show v ∉ Kᶜ from fun h' => h' hv), add_zero, hψ1 hv, Pi.one_apply, one_mul]
          · rw [Set.indicator_of_mem hv]
            exact le_add_self
      _ = ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v * φ v) ∂μ +
            ∫⁻ v in f ⁻¹' (ι '' A) ∩ Kᶜ, ENNReal.ofReal (φ v) ∂μ := by
          rw [lintegral_add_left (f := fun v => ENNReal.ofReal (ψ v * φ v))
              (ENNReal.measurable_ofReal.comp hc.measurable),
            setLIntegral_indicator hKc.measurableSet.compl, Set.inter_comm]
      _ ≤ ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (ψ v * φ v) ∂μ + ENNReal.ofReal ε * ν A := by
          gcongr
          exact hKε A hAm
  have hmain := ofReal_le_of_forall_compact ν hD hcont ε hcmp s0
  rw [hint _ hc hs hsU h0, ENNReal.ofReal_coe_nnreal] at hmain
  refine hmain.trans (add_le_add ?_ le_rfl)
  exact lintegral_mono fun v => ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hφ0 v) (hψb v).2)
end GlobalTheory.CompanionTheory.FibreDensityLimit
