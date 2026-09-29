-- Prove2me | solution 1 for MarkovChainCLT.alpha_mixing_le_tv_rate
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:29:02.126341+00:00
-- url     : https://prove2.me/submissions/88453546-5ef2-47b4-8242-8b00b209e075

import Theorems.Thm_MarkovChainCLT_chainMeasure_past_inter_future
import Theorems.Thm_MarkovChainCLT_processSigma_Ici_eq_comap_shift
import Theorems.Thm_MarkovChainCLT_processSigma_Iic_eq_comap_restrict
import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_chainMeasure
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure

open Filter Finset Function MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π)
    (M : X → ℝ) (hM0 : ∀ x, 0 ≤ M x) (hM : Integrable M π)
    (γ : ℕ → ℝ) (hγ0 : ∀ n, 0 ≤ γ n) (hrate : ErgodicWithRate P π M γ) :
    ∀ n : ℕ, 1 ≤ n →
      alphaMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n
        ≤ γ n * ∫ x, M x ∂π := by
  intro n hn
  have hinv : Kernel.Invariant P π := hP.1
  have hC0 : 0 ≤ γ n * ∫ x, M x ∂π :=
    mul_nonneg (hγ0 n) (integral_nonneg hM0)
  set μ := chainMeasure P π with hμ
  set K := BanditAlgorithm.markovChainKernel P with hK
  refine Real.sSup_le ?_ hC0
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  rw [MarkovChainCLT.processSigma_Iic_eq_comap_restrict] at hA
  rw [MarkovChainCLT.processSigma_Ici_eq_comap_shift] at hB
  obtain ⟨A₀, hA₀, rfl⟩ := hA
  obtain ⟨B₀, hB₀, rfl⟩ := hB
  have hfr : (fun (ω : ℕ → X) => fun i : Finset.Iic k => ω i.1)
      = frestrictLe (π := fun _ : ℕ => X) k := rfl
  have hsh : Measurable (fun (ω : ℕ → X) => fun l => ω (k + n + l)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  set lamk := μ.map (frestrictLe (π := fun _ : ℕ => X) k) with hlamk
  haveI : IsProbabilityMeasure lamk := by
    rw [hlamk]; exact Measure.isProbabilityMeasure_map (measurable_frestrictLe k).aemeasurable
  set g : X → ℝ := fun y => ((K y) B₀).toReal with hg
  have hgm : Measurable g := (Kernel.measurable_coe K hB₀).ennreal_toReal
  have hg0 : ∀ y, 0 ≤ g y := fun y => ENNReal.toReal_nonneg
  have hg1 : ∀ y, g y ≤ 1 := by
    intro y; rw [hg]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa using prob_le_one
  have hbindReal : ∀ (ν : Measure X), IsProbabilityMeasure ν →
      ((K ∘ₘ ν) B₀).toReal = ∫ y, g y ∂ν := by
    intro ν hν
    haveI := hν
    rw [Measure.bind_apply hB₀ (Kernel.aemeasurable _)]
    refine (integral_toReal (Kernel.measurable_coe K hB₀).aemeasurable ?_).symm
    filter_upwards with y; exact measure_lt_top _ _
  have hstat : μ ((fun (ω : ℕ → X) => fun l => ω (k + n + l)) ⁻¹' B₀) = μ B₀ := by
    have hconv : (fun (ω : ℕ → X) => fun l => ω (k + n + l))
        = (fun (ω : ℕ → X) => fun l => ω (l + (k + n))) := by
      funext ω; funext l; rw [Nat.add_comm]
    rw [← Measure.map_apply hsh hB₀, hconv]
    have hs := MarkovChainCLT.isStrictlyStationary_chainMeasure P π hinv (k + n)
    simp only at hs
    rw [hs]
    have hid : (fun (ω : ℕ → X) => fun l => ω l) = id := rfl
    rw [hid, Measure.map_id]
  rw [hfr, hstat,
    MarkovChainCLT.chainMeasure_past_inter_future P π k n A₀ hA₀ B₀ hB₀,
    show μ (frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀) = lamk A₀ from
      (Measure.map_apply (measurable_frestrictLe k) hA₀).symm]
  set F : (Π _i : Finset.Iic k, X) → ℝ≥0∞ :=
    fun u => (K ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀ with hF
  have hFm : Measurable F := by
    have h1 : Measurable (fun x : X => (K ∘ₘ (iterKernel P n x)) B₀) := by
      have he : (fun x : X => (K ∘ₘ (iterKernel P n x)) B₀)
          = fun x : X => ((K ∘ₖ (iterKernel P n)) x) B₀ := by
        funext x; rw [Kernel.comp_apply]
      rw [he]; exact Kernel.measurable_coe _ hB₀
    exact h1.comp (measurable_pi_apply _)
  have hFlt : ∀ u, F u < ∞ := fun u => measure_lt_top _ _
  have hFcond : ∀ u, (F u).toReal
      = ∫ y, g y ∂(iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩)) :=
    fun u => hbindReal _ inferInstance
  have hmB : (μ B₀).toReal = ∫ y, g y ∂π := by
    rw [hμ, chainMeasure, ← hK]; exact hbindReal π inferInstance
  have hToReal : (∫⁻ u in A₀, F u ∂lamk).toReal = ∫ u in A₀, (F u).toReal ∂lamk :=
    (integral_toReal hFm.aemeasurable (Filter.Eventually.of_forall hFlt)).symm
  rw [hToReal]
  -- the k-th coordinate has law π
  have hev : Measurable (fun u : Π _i : Finset.Iic k, X => u ⟨k, Finset.mem_Iic.2 le_rfl⟩) :=
    measurable_pi_apply _
  have hcoord : lamk.map (fun u : Π _i : Finset.Iic k, X => u ⟨k, Finset.mem_Iic.2 le_rfl⟩)
      = π := by
    rw [hlamk, Measure.map_map hev (measurable_frestrictLe k)]
    have hcomp : (fun u : Π _i : Finset.Iic k, X => u ⟨k, Finset.mem_Iic.2 le_rfl⟩)
        ∘ (frestrictLe (π := fun _ : ℕ => X) k) = fun ω : ℕ → X => ω k := rfl
    rw [hcomp, hμ]
    exact MarkovChainCLT.map_coord_chainMeasure P π hinv k
  -- pointwise bound on `A₀`, with an `x`-dependent constant
  set m := (μ B₀).toReal with hm
  have hbd : ∀ u, |(F u).toReal - m| ≤ M (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) * γ n := by
    intro u
    rw [hFcond u, hmB]
    exact le_trans (MarkovChainCLT.abs_integral_sub_le_tvDist _ π g hgm hg0 hg1)
      (hrate _ n hn)
  -- integrability
  have hFint : Integrable (fun u => (F u).toReal) lamk := by
    refine ⟨hFm.ennreal_toReal.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (1:ℝ)).mono ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, abs_of_nonneg ENNReal.toReal_nonneg, hFcond u]
    calc ∫ y, g y ∂(iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))
        ≤ ∫ _y, (1:ℝ) ∂(iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩)) := by
          refine integral_mono ⟨hgm.aestronglyMeasurable, ?_⟩ (integrable_const 1) hg1
          refine (hasFiniteIntegral_const (1:ℝ)).mono ?_
          filter_upwards with y
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, abs_of_nonneg (hg0 y)]
          exact hg1 y
      _ = 1 := by simp
  have hMint : Integrable (fun u : Π _i : Finset.Iic k, X =>
      M (u ⟨k, Finset.mem_Iic.2 le_rfl⟩)) lamk := by
    rw [← hcoord] at hM
    exact (integrable_map_measure hM.1 hev.aemeasurable).mp hM
  have hMval : (∫ u, M (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) ∂lamk) = ∫ x, M x ∂π := by
    rw [← hcoord, integral_map hev.aemeasurable]
    rw [hcoord]
    exact hM.1
  -- the covariance bound
  have hcent : (∫ u in A₀, (F u).toReal ∂lamk) - (lamk A₀).toReal * m
      = ∫ u in A₀, ((F u).toReal - m) ∂lamk := by
    rw [integral_sub hFint.integrableOn (integrable_const m).restrict, integral_const,
      smul_eq_mul]
    congr 2
    simp [Measure.real]
  have hle : |∫ u in A₀, ((F u).toReal - m) ∂lamk| ≤ γ n * ∫ x, M x ∂π := by
    have h1 : |∫ u in A₀, ((F u).toReal - m) ∂lamk| ≤ ∫ u in A₀, |(F u).toReal - m| ∂lamk := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := lamk.restrict A₀) (f := fun u => (F u).toReal - m)
    have h2 : (∫ u in A₀, |(F u).toReal - m| ∂lamk)
        ≤ ∫ u in A₀, (M (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) * γ n) ∂lamk := by
      refine integral_mono ((hFint.sub (integrable_const m)).abs.integrableOn)
        ((hMint.mul_const (γ n)).integrableOn) (fun u => hbd u)
    have h3 : (∫ u in A₀, (M (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) * γ n) ∂lamk)
        ≤ ∫ u, (M (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) * γ n) ∂lamk := by
      refine integral_mono_measure (Measure.restrict_le_self)
        (Filter.Eventually.of_forall (fun u => mul_nonneg (hM0 _) (hγ0 n)))
        (hMint.mul_const (γ n))
    have h4 : (∫ u, (M (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) * γ n) ∂lamk)
        = γ n * ∫ x, M x ∂π := by
      rw [integral_mul_const, hMval]; ring
    linarith [h1, h2, h3, h4.le, h4.ge]
  rw [← hcent] at hle
  exact hle
