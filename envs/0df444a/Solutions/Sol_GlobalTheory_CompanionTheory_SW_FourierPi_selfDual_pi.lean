-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.selfDual_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:37.585024+00:00
-- url     : https://prove2.me/submissions/a9193e18-d9df-4290-8d50-d42b1a4ed063

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_dual_facts
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_continuous_psi_dot
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_box_formula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_mean_close

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FourierPi
namespace GlobalTheory.CompanionTheory.SW.FourierPi
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ψ : R → ℂ), Continuous ψ → (∀ x y, ψ (x + y) = ψ x * ψ y) → (∀ x, ‖ψ x‖ = 1) → ∀ lam : Measure R, SelfDual lam (fun s t => ψ (s * t)) → (∃ L : AddSubgroup R, IsCompact (L : Set R) ∧ IsOpen (L : Set R)) → (∀ L : AddSubgroup R, IsCompact (L : Set R) → IsOpen (L : Set R) → IsCompact {t | ∀ s ∈ L, ψ (s * t) = 1}) → (∀ K : Set R, IsCompact K → ∃ L : AddSubgroup R, IsCompact (L : Set R) ∧ IsOpen (L : Set R) ∧ K ⊆ L) → (∀ U ∈ 𝓝 (0 : R), ∃ L : AddSubgroup R, IsCompact (L : Set R) ∧ IsOpen (L : Set R) ∧ (L : Set R) ⊆ U) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => lam) (fun x y => ψ (x ⬝ᵥ y)) := by
  intro R _ _ _ _ _ _ _ _ ψ hc ha hn lam hsd _ hC hK hU ι _
  haveI := hsd.1
  refine ⟨inferInstance, ?_⟩
  intro Φ Φc Φs hint z
  change Integrable (fun y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂(Measure.pi fun _ : ι => lam))
    (Measure.pi fun _ : ι => lam) at hint
  change ∫ y, (∫ x, Φ x * ψ (x ⬝ᵥ y) ∂(Measure.pi fun _ : ι => lam)) * ψ (y ⬝ᵥ z)
    ∂(Measure.pi fun _ : ι => lam) = Φ (-z)
  have hi : Integrable Φ (Measure.pi fun _ : ι => lam) := Φc.integrable_of_hasCompactSupport Φs
  have hPc : ∀ L : AddSubgroup R, IsCompact (L : Set R) → IsOpen (L : Set R) →
      IsCompact (ann ha hn L : Set R) := hC
  obtain ⟨U, hUb⟩ := (𝓝 (0 : R)).exists_antitone_basis
  choose L hLc hLo hLU using fun n => hU (U n) (hUb.mem n)
  have hLs : ∀ S ∈ 𝓝 (0 : R), ∀ᶠ n in Filter.atTop, (L n : Set R) ⊆ S := by
    intro S hS
    obtain ⟨N, -, hN⟩ := hUb.1.mem_iff.1 hS
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact (hLU n).trans ((hUb.2 hn).trans hN)
  have hD := fun n => dual_facts hc ha hn lam hsd (L n) (hLc n) (hLo n) (hPc _ (hLc n) (hLo n))
  have hex : ∀ t : R, ∀ᶠ n in Filter.atTop, t ∈ ann ha hn (L n) := by
    intro t
    obtain ⟨M, hMc, hMo, hMt⟩ := hK {t} isCompact_singleton
    have hMo' := (dual_facts hc ha hn lam hsd M hMc hMo (hPc _ hMc hMo)).2.2
    have hnb : (ann ha hn M : Set R) ∈ 𝓝 (0 : R) :=
      hMo'.mem_nhds (ann ha hn M).zero_mem
    filter_upwards [hLs _ hnb] with n hn s hs
    have := hn hs t (hMt rfl)
    rwa [mul_comm] at this
  set f : (ι → R) → ℂ := fun y =>
    (∫ x, Φ x * ψ (x ⬝ᵥ y) ∂(Measure.pi fun _ : ι => lam)) * ψ (y ⬝ᵥ z) with hf
  have hbm : ∀ n, MeasurableSet (box ι (ann ha hn (L n) : Set R)) := fun n =>
    MeasurableSet.univ_pi fun _ => (hPc _ (hLc n) (hLo n)).isClosed.measurableSet
  have fm : AEStronglyMeasurable f (Measure.pi fun _ : ι => lam) :=
    hint.aestronglyMeasurable.mul
      (continuous_psi_dot hc continuous_id continuous_const).aestronglyMeasurable
  have lim1 : Filter.Tendsto (fun n => ∫ y in box ι (ann ha hn (L n) : Set R), f y
      ∂(Measure.pi fun _ : ι => lam)) Filter.atTop
      (𝓝 (∫ y, f y ∂(Measure.pi fun _ : ι => lam))) := by
    simp_rw [← integral_indicator (hbm _)]
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖∫ x, Φ x * ψ (x ⬝ᵥ y) ∂(Measure.pi fun _ : ι => lam)‖) ?_ hint.norm ?_ ?_
    · exact fun n => fm.indicator (hbm n)
    · refine fun n => Filter.Eventually.of_forall fun y => ?_
      refine (norm_indicator_le_norm_self _ _).trans ?_
      simp [hf, hn]
    · refine Filter.Eventually.of_forall fun y => ?_
      refine tendsto_const_nhds.congr' ?_
      have : ∀ᶠ n in Filter.atTop, ∀ i, y i ∈ ann ha hn (L n) :=
        Filter.eventually_all.2 fun i => hex (y i)
      filter_upwards [this] with n hn'
      rw [Set.indicator_of_mem (show y ∈ box ι (ann ha hn (L n) : Set R) from fun i _ => hn' i)]
  have lim2 : Filter.Tendsto (fun n => ∫ y in box ι (ann ha hn (L n) : Set R), f y
      ∂(Measure.pi fun _ : ι => lam)) Filter.atTop (𝓝 (Φ (-z))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hcont : ContinuousAt (fun u : ι → R => Φ (u - z)) 0 := by fun_prop
    have hS : ∀ᶠ u in 𝓝 (0 : ι → R), ‖Φ (u - z) - Φ (-z)‖ < ε / 2 := by
      have := (Metric.tendsto_nhds.1 hcont.tendsto) (ε / 2) (half_pos hε)
      simpa [dist_eq_norm] using this
    have hS' := hS
    rw [Filter.Eventually, nhds_pi, Filter.mem_pi'] at hS'
    obtain ⟨I, t, ht, hIt⟩ := hS'
    have hall : ∀ᶠ n in Filter.atTop, ∀ i, (L n : Set R) ⊆ t i :=
      Filter.eventually_all.2 fun i => hLs _ (ht i)
    filter_upwards [hall] with n hn'
    obtain ⟨d1, -, -⟩ := hD n
    have hbf := box_formula hc ha hn lam (L n) (ann ha hn (L n)) (hLo n).measurableSet
      (hPc _ (hLc n) (hLo n)).isClosed.measurableSet (hPc _ (hLc n) (hLo n)).measure_lt_top
      (fun s hs t ht => ht s hs) (hD n).2.1 Φ Φc hi z
    rw [hf, hbf, dist_eq_norm]
    have hsub : HasCompactSupport fun u : ι → R => Φ (u - z) :=
      Φs.comp_homeomorph (Homeomorph.subRight z)
    have hint2 : Integrable (fun u : ι → R => Φ (u - z)) (Measure.pi fun _ : ι => lam) :=
      (Φc.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport hsub
    refine lt_of_le_of_lt (mean_close lam (L n : Set R) (hLo n).measurableSet
      (hLc n).measure_lt_top _ measureReal_nonneg d1 _ hint2.integrableOn (Φ (-z)) (ε / 2) ?_)
      (half_lt_self hε)
    intro u hu
    refine le_of_lt (hIt fun i _ => hn' i (hu i (Set.mem_univ i)))
  exact tendsto_nhds_unique lim1 lim2
end GlobalTheory.CompanionTheory.SW.FourierPi
