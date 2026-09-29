-- Prove2me | solution 1 for MarkovChainCLT.setIntegral_next_coord_eq
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T23:11:19.053497+00:00
-- url     : https://prove2.me/submissions/e9faf579-d213-4ea4-80fe-e08386d550b2

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Theorems.Thm_MarkovChainCLT_chainMeasure_past_inter_future
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 1000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam]
    (h : X → ℝ) (hh : Measurable h) (B : ℝ) (hB : ∀ x, |h x| ≤ B) (k : ℕ)
    (A₀ : Set (Π _i : Finset.Iic k, X)) (hA₀ : MeasurableSet A₀) :
    ∫ ω in (frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀), h (ω (k + 1))
        ∂(chainMeasure P lam)
      = ∫ ω in (frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀),
          (∫ y, h y ∂(P (ω k))) ∂(chainMeasure P lam) := by
  classical
  -- the coordinate `0` marginal of a chain is its initial law
  have hcoord0 : ∀ (mu : Measure X), IsProbabilityMeasure mu →
      (chainMeasure P mu).map (fun ω : ℕ → X => ω 0) = mu := by
    intro mu hmu
    have hK : (BanditAlgorithm.markovChainKernel P).map (fun ω : ℕ → X => ω 0)
        = Kernel.id := by
      have hmap : (Kernel.traj (BanditAlgorithm.markovChainStep P) 0).map
          (frestrictLe (π := fun _ : ℕ => X) 0) = Kernel.id := by
        rw [Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
      ext x A hA
      rw [Kernel.map_apply' _ (measurable_pi_apply 0) _ hA,
        BanditAlgorithm.markovChainKernel, Kernel.comap_apply]
      have h1 : (fun ω : ℕ → X => ω 0) ⁻¹' A
          = (frestrictLe (π := fun _ : ℕ => X) 0) ⁻¹'
            ((fun u : Π _i : Finset.Iic 0, X => u ⟨0, Finset.mem_Iic.2 le_rfl⟩) ⁻¹' A) := rfl
      have hmeas : Measurable (fun u : Π _i : Finset.Iic 0, X =>
          u ⟨0, Finset.mem_Iic.2 le_rfl⟩) := measurable_pi_apply _
      rw [h1, ← Measure.map_apply (by fun_prop) (hA.preimage hmeas),
        ← Kernel.map_apply _ (by fun_prop), hmap, Kernel.id_apply,
        Measure.dirac_apply' _ (hA.preimage hmeas), Kernel.id_apply,
        Measure.dirac_apply' _ hA]
      rfl
    rw [chainMeasure, Measure.map_comp _ _ (by fun_prop), hK]
    simp
  set ν : Measure (ℕ → X) := chainMeasure P lam with hν
  set S : Set (ℕ → X) := frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀ with hS
  have hSm : MeasurableSet S := hA₀.preimage (measurable_frestrictLe k)
  set ρ : Measure (ℕ → X) := ν.restrict S with hρ
  haveI : IsFiniteMeasure ρ := by
    rw [hρ]
    infer_instance
  set μ₂ : Measure X := ρ.map (fun ω : ℕ → X => ω k) with hμ₂
  haveI : IsFiniteMeasure μ₂ := by
    constructor
    have huniv : μ₂ Set.univ = ρ Set.univ := by
      rw [hμ₂, Measure.map_apply (measurable_pi_apply k) MeasurableSet.univ]
      rfl
    rw [huniv]
    exact measure_lt_top ρ Set.univ
  -- the joint law: the next coordinate is distributed as `P` applied to the current one
  have hkey : ρ.map (fun ω : ℕ → X => ω (k + 1)) = P ∘ₘ μ₂ := by
    ext E hE
    have hE1 : MeasurableSet {ω : ℕ → X | ω 0 ∈ E} := hE.preimage (measurable_pi_apply 0)
    have hmain := chainMeasure_past_inter_future P lam k 1 A₀ hA₀ {ω : ℕ → X | ω 0 ∈ E} hE1
    -- left-hand sides agree
    have hsetEq : ((fun (ω : ℕ → X) (l : ℕ) => ω (k + 1 + l)) ⁻¹' {ω : ℕ → X | ω 0 ∈ E})
        = (fun ω : ℕ → X => ω (k + 1)) ⁻¹' E := by
      ext ω
      simp
    have hL : ρ.map (fun ω : ℕ → X => ω (k + 1)) E
        = ν (S ∩ ((fun (ω : ℕ → X) (l : ℕ) => ω (k + 1 + l)) ⁻¹' {ω : ℕ → X | ω 0 ∈ E})) := by
      rw [hsetEq, hρ, Measure.map_apply (measurable_pi_apply (k + 1)) hE,
        Measure.restrict_apply (hE.preimage (measurable_pi_apply (k + 1))), Set.inter_comm]
    -- right-hand sides agree
    have hR : (P ∘ₘ μ₂) E
        = ∫⁻ u in A₀, ((BanditAlgorithm.markovChainKernel P)
            ∘ₘ (iterKernel P 1 (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) {ω : ℕ → X | ω 0 ∈ E}
            ∂(ν.map (frestrictLe (π := fun _ : ℕ => X) k)) := by
      have hone : ∀ x : X, ((BanditAlgorithm.markovChainKernel P)
          ∘ₘ (iterKernel P 1 x)) {ω : ℕ → X | ω 0 ∈ E} = P x E := by
        intro x
        have hiter : iterKernel P 1 x = P x := by
          rw [show (1 : ℕ) = 0 + 1 from rfl, iterKernel_succ, iterKernel_zero, Kernel.comp_id]
        rw [hiter]
        have h2 := hcoord0 (P x) inferInstance
        calc ((BanditAlgorithm.markovChainKernel P) ∘ₘ (P x)) {ω : ℕ → X | ω 0 ∈ E}
            = (chainMeasure P (P x)) ((fun ω : ℕ → X => ω 0) ⁻¹' E) := rfl
          _ = ((chainMeasure P (P x)).map (fun ω : ℕ → X => ω 0)) E := by
              rw [Measure.map_apply (measurable_pi_apply 0) hE]
          _ = P x E := by rw [h2]
      have hLHS : (P ∘ₘ μ₂) E = ∫⁻ ω in S, P (ω k) E ∂ν := by
        rw [Measure.bind_apply hE (Kernel.aemeasurable _), hμ₂,
          lintegral_map (Kernel.measurable_coe P hE) (measurable_pi_apply k), hρ]
      have hRHS : (∫⁻ u in A₀, P (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) E
            ∂(ν.map (frestrictLe (π := fun _ : ℕ => X) k)))
          = ∫⁻ ω in S, P (ω k) E ∂ν := by
        have hm2 : Measurable (fun u : Π _i : Finset.Iic k, X =>
            P (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) E) :=
          (Kernel.measurable_coe P hE).comp
            (measurable_pi_apply (⟨k, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic k))
        rw [setLIntegral_map hA₀ hm2 (measurable_frestrictLe k)]
        rfl
      simp only [hone]
      rw [hLHS, hRHS]
    rw [hL, hR, ← hmain]
  -- turn the measure identity into the integral identity
  have hhs : StronglyMeasurable h := hh.stronglyMeasurable
  have hint1 : ∫ ω in S, h (ω (k + 1)) ∂ν = ∫ y, h y ∂(ρ.map (fun ω : ℕ → X => ω (k + 1))) := by
    rw [integral_map (measurable_pi_apply (k + 1)).aemeasurable hhs.aestronglyMeasurable]
  have hint2 : ∫ ω in S, (∫ y, h y ∂(P (ω k))) ∂ν = ∫ x, (∫ y, h y ∂(P x)) ∂μ₂ := by
    rw [hμ₂, integral_map (measurable_pi_apply k).aemeasurable
      (hhs.integral_kernel (κ := P)).aestronglyMeasurable]
  have hint3 : ∫ y, h y ∂(P ∘ₘ μ₂) = ∫ x, (∫ y, h y ∂(P x)) ∂μ₂ := by
    haveI : IsFiniteMeasure (P ∘ₘ μ₂) := by
      constructor
      rw [Measure.comp_apply_univ]
      exact measure_lt_top μ₂ Set.univ
    have hcomp : P ∘ₘ μ₂ = (P ∘ₖ Kernel.const Unit μ₂) () :=
      Measure.comp_eq_comp_const_apply
    have hintg : Integrable h ((P ∘ₖ Kernel.const Unit μ₂) ()) := by
      rw [← hcomp]
      exact ⟨hhs.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := B) (ae_of_all _ (fun y => by simpa using hB y))⟩
    rw [hcomp, Kernel.integral_comp hintg]
    simp
  rw [hint1, hkey, hint3, hint2]
