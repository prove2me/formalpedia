-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:31.526596+00:00
-- url     : https://prove2.me/submissions/10c9a607-cc6d-47e5-b980-903715d43f3f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFibrationVolume
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatticeUnimod_unimodular_of_isFundamentalDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PeriodisedMean
namespace GlobalTheory.CompanionTheory.SW.PeriodisedMean
theorem _root_.solution : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ : Subgroup N) [Countable Γ] (𝓕N : Set N), IsFundamentalDomain Γ 𝓕N ν → ν 𝓕N < ⊤ → ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (dA : Measure V) [dA.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (D : Set V), IsAddFundamentalDomain Λ D dA → dA D = 1 → ∀ l : N → V, Continuous l → (∀ x y, l (x * y) = l x + l y) → Function.Surjective l → (∀ γ ∈ Γ, l γ ∈ Λ) → ∀ f : V → ℝ≥0∞, Measurable f → ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν = ν 𝓕N * ∫⁻ x, f x ∂dA := by
  intro N _ _ _ _ _ _ _ _ ν _ Γ _ 𝓕N h𝓕 hfin V _ _ _ _ _ _ _ _ dA _ Λ _ D hD hD1 l hlc hlmul hlsurj hlΓ f hf
  obtain ⟨-, hR, -⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain N Γ ν 𝓕N h𝓕 hfin
  have hlm : Measurable l := hlc.measurable

  set Ft : V → ℝ≥0∞ := fun x => ∑' a : Λ, f ((a : V) + x) with hFt
  have hFtm : Measurable Ft :=
    Measurable.tsum fun a => hf.comp (measurable_const.add measurable_id)
  have hper : ∀ b ∈ Λ, ∀ x, Ft (x + b) = Ft x := by
    intro b hb x
    simp only [hFt]
    rw [← (Equiv.addRight (⟨b, hb⟩ : Λ)).tsum_eq (fun a : Λ => f ((a : V) + x))]
    refine tsum_congr fun a => ?_
    simp only [Equiv.coe_addRight, AddSubgroup.coe_add]
    congr 1
    abel
  set h : N → ℝ≥0∞ := fun m => Ft (l m⁻¹) with hh
  have hinv : ∀ γ ∈ Γ, ∀ m, h (γ * m) = h m := by
    intro γ hγ m
    simp only [hh]
    rw [mul_inv_rev, hlmul]
    exact hper _ (hlΓ _ (Γ.inv_mem hγ)) _

  have hshift : ∀ n₀ : N, ∫⁻ m in 𝓕N, h (m * n₀) ∂ν = ∫⁻ m in 𝓕N, h m ∂ν := by
    intro n₀
    have hF : IsFundamentalDomain Γ ((· * n₀⁻¹) ⁻¹' 𝓕N) ν :=
      h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right ν n₀⁻¹) (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hmp : MeasurePreserving (· * n₀) ν ν := measurePreserving_mul_right ν n₀
    have hemb : MeasurableEmbedding (· * n₀ : N → N) :=
      (MeasurableEquiv.mulRight n₀).measurableEmbedding
    have e1 := hmp.setLIntegral_comp_preimage_emb hemb h ((· * n₀⁻¹) ⁻¹' 𝓕N)
    have e2 : (· * n₀ : N → N) ⁻¹' ((· * n₀⁻¹) ⁻¹' 𝓕N) = 𝓕N := by
      ext x; simp
    rw [e2] at e1
    rw [e1]
    exact hF.setLIntegral_eq h𝓕 h (fun γ x => hinv γ γ.2 x)

  have hT : ∀ x, ∫⁻ m in 𝓕N, Ft (x + l m⁻¹) ∂ν = ∫⁻ m in 𝓕N, h m ∂ν := by
    intro x
    obtain ⟨y, rfl⟩ := hlsurj x
    rw [← hshift y⁻¹]
    refine lintegral_congr fun m => ?_
    simp only [hh]
    rw [mul_inv_rev, inv_inv, hlmul]

  have hfold : ∀ c : V, ∫⁻ x in D, Ft (x + c) ∂dA = ∫⁻ x, f x ∂dA := by
    intro c
    have e0 : ∫⁻ x, f (x + c) ∂dA = ∫⁻ x, f x ∂dA := lintegral_add_right_eq_self f c
    have e3 : ∫⁻ x in D, ∑' a : Λ, f ((a +ᵥ x) + c) ∂dA
        = ∑' a : Λ, ∫⁻ x in D, f ((a +ᵥ x) + c) ∂dA :=
      lintegral_tsum fun a => (hf.comp ((measurable_const_vadd a).add_const c)).aemeasurable
    rw [← e0, hD.lintegral_eq_tsum'' (fun x => f (x + c)), ← e3]
    refine lintegral_congr fun x => ?_
    simp only [hFt]
    refine tsum_congr fun a => ?_
    simp [AddSubgroup.vadd_def, vadd_eq_add, add_assoc]
  have hswapm : Measurable (Function.uncurry fun (x : V) (m : N) => Ft (x + l m⁻¹)) :=
    hFtm.comp (measurable_fst.add (hlm.comp measurable_snd.inv))
  calc ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν
      = ∫⁻ m in 𝓕N, h m ∂ν := rfl
    _ = ∫⁻ _x in D, (∫⁻ m in 𝓕N, h m ∂ν) ∂dA := by
        rw [setLIntegral_const, hD1, mul_one]
    _ = ∫⁻ x in D, ∫⁻ m in 𝓕N, Ft (x + l m⁻¹) ∂ν ∂dA :=
        lintegral_congr fun x => (hT x).symm
    _ = ∫⁻ m in 𝓕N, ∫⁻ x in D, Ft (x + l m⁻¹) ∂dA ∂ν :=
        lintegral_lintegral_swap hswapm.aemeasurable
    _ = ∫⁻ _m in 𝓕N, (∫⁻ x, f x ∂dA) ∂ν := lintegral_congr fun m => hfold _
    _ = ν 𝓕N * ∫⁻ x, f x ∂dA := by
        rw [setLIntegral_const, mul_comm]
end GlobalTheory.CompanionTheory.SW.PeriodisedMean
