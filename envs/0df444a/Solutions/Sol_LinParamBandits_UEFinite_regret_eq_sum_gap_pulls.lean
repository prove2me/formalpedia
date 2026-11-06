-- Prove2me | solution 1 for LinParamBandits.UEFinite.regret_eq_sum_gap_pulls
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:25:36.706695+00:00
-- url     : https://prove2.me/submissions/1202a01f-0c69-4bc1-a709-4508e29e55d4

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy

open MeasureTheory ProbabilityTheory

namespace UEFinRegretEqAux

open LinParamBandits.UEFinite

variable {r : ℕ}

/-- The one-step extension map of `histMeasure` is measurable. -/
lemma measurable_step (ψ : LinParamBandits.UEGeneral.Policy r) (z : LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    Measurable (fun p : LinParamBandits.LowerBound.History r n × ℝ =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
        (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have ha : Measurable (fun p : LinParamBandits.LowerBound.History r n × ℝ => ψ.act n p.1) :=
      (ψ.measurable_act n).comp measurable_fst
    refine ha.prodMk ?_
    exact (Measurable.inner ha measurable_const).add measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

lemma isProb_histMeasure (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : LinParamBandits.UEGeneral.Policy r) :
    ∀ n, IsProbabilityMeasure (LinParamBandits.UEGeneral.histMeasure ν z ψ n)
  | 0 => by
      simp only [LinParamBandits.UEGeneral.histMeasure]; infer_instance
  | n + 1 => by
      have := isProb_histMeasure ν z ψ n
      simp only [LinParamBandits.UEGeneral.histMeasure]
      exact Measure.isProbabilityMeasure_map (measurable_step ψ z n).aemeasurable

lemma measurableSet_armsIn (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite) (n : ℕ) :
    MeasurableSet {h : LinParamBandits.LowerBound.History r n | ∀ s, (h s).1 ∈ 𝒰} := by
  have : {h : LinParamBandits.LowerBound.History r n | ∀ s, (h s).1 ∈ 𝒰} =
      ⋂ s, (fun h : LinParamBandits.LowerBound.History r n => (h s).1) ⁻¹' 𝒰 := by
    ext h; simp
  rw [this]
  exact MeasurableSet.iInter fun s =>
    (measurable_fst.comp (measurable_pi_apply s)) h𝒰fin.measurableSet

lemma ae_armsIn (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ)
    (z : LinParamBandits.LowerBound.Vec r) (ψ : LinParamBandits.UEGeneral.Policy r)
    (hact : ∀ t h, ψ.act t h ∈ 𝒰) :
    ∀ n, ∀ᵐ h ∂(LinParamBandits.UEGeneral.histMeasure ν z ψ n), ∀ s, (h s).1 ∈ 𝒰
  | 0 => Filter.Eventually.of_forall (fun h s => Fin.elim0 s)
  | n + 1 => by
      have ih := ae_armsIn 𝒰 h𝒰fin ν z ψ hact n
      simp only [LinParamBandits.UEGeneral.histMeasure]
      rw [ae_map_iff (measurable_step ψ z n).aemeasurable (measurableSet_armsIn 𝒰 h𝒰fin (n + 1))]
      have hms : MeasurableSet {p : LinParamBandits.LowerBound.History r n × ℝ | ∀ s, (p.1 s).1 ∈ 𝒰} :=
        measurable_fst (measurableSet_armsIn 𝒰 h𝒰fin n)
      have h2 : ∀ᵐ p ∂((LinParamBandits.UEGeneral.histMeasure ν z ψ n) ⊗ₘ
          (ν.comap (ψ.act n) (ψ.measurable_act n))), ∀ s, (p.1 s).1 ∈ 𝒰 := by
        apply Measure.ae_compProd_of_ae_ae hms
        filter_upwards [ih] with h hh
        exact Filter.Eventually.of_forall (fun _ => hh)
      filter_upwards [h2] with p hp
      intro s
      refine Fin.lastCases ?_ (fun j => ?_) s
      · simp only [Fin.snoc_last]; exact hact n p.1
      · simp only [Fin.snoc_castSucc]; exact hp j

lemma measurable_pullCount (u : LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    Measurable (fun h : LinParamBandits.LowerBound.History r n => (pullCount u h : ℝ)) := by
  classical
  have : (fun h : LinParamBandits.LowerBound.History r n => (pullCount u h : ℝ)) =
      fun h => ∑ s, (if (h s).1 = u then (1 : ℝ) else 0) := by
    funext h
    simp only [pullCount]
    rw [Finset.sum_boole]
  rw [this]
  refine Finset.measurable_sum _ (fun s _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_fst.comp (measurable_pi_apply s)) (measurableSet_singleton u)

lemma pullCount_le (u : LinParamBandits.LowerBound.Vec r) {n : ℕ}
    (h : LinParamBandits.LowerBound.History r n) : pullCount u h ≤ n := by
  classical
  simp only [pullCount]
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma bestValue_ge (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite)
    (u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (z : LinParamBandits.LowerBound.Vec r) :
    inner ℝ u z ≤ LinParamBandits.UEGeneral.bestValue 𝒰 z :=
  le_csSup (h𝒰fin.image _).bddAbove ⟨u, hu, rfl⟩

/-- Pointwise identity: `∑_u Δ^u N^u(h) = ∑_s Δ^{U_s}`. -/
lemma sum_gap_pull (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite)
    (z : LinParamBandits.LowerBound.Vec r) {n : ℕ} (h : LinParamBandits.LowerBound.History r n)
    (hh : ∀ s, (h s).1 ∈ 𝒰) :
    ∑ u ∈ h𝒰fin.toFinset, gap 𝒰 u z * (pullCount u h : ℝ) =
      n * LinParamBandits.UEGeneral.bestValue 𝒰 z - ∑ s, inner ℝ (h s).1 z := by
  classical
  have h1 : ∀ u, gap 𝒰 u z * (pullCount u h : ℝ) =
      ∑ s ∈ Finset.univ.filter (fun s => (h s).1 = u), gap 𝒰 (h s).1 z := by
    intro u
    rw [Finset.sum_congr rfl (g := fun _ => gap 𝒰 u z)]
    · simp only [Finset.sum_const, nsmul_eq_mul, pullCount]
      rw [mul_comm]

    · intro s hs
      simp only [Finset.mem_filter] at hs
      rw [hs.2]
  simp_rw [h1]
  rw [Finset.sum_fiberwise_of_maps_to (g := fun s => (h s).1) (fun s _ => by simpa using hh s)]
  simp only [gap, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end UEFinRegretEqAux

open UEFinRegretEqAux in
theorem solution
    (σ₀ ū lam₀ : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (r : ℕ) (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite) (h𝒰ne : 𝒰.Nonempty)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (hν : IsMarkovKernel ν) (hnoise : LinParamBandits.UEFinite.NoiseAssumption 𝒰 ν σ₀)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (harms : LinParamBandits.UEFinite.ArmAssumption 𝒰 b ū lam₀)
    (ψ : LinParamBandits.UEGeneral.Policy r) (hψ : LinParamBandits.UEFinite.IsUE 𝒰 b σ₀ ū lam₀ ψ)
    (T : ℕ) (z : LinParamBandits.LowerBound.Vec r) :
    LinParamBandits.UEFinite.Regret 𝒰 ν ψ z T =
      ∑ u ∈ h𝒰fin.toFinset, LinParamBandits.UEFinite.gap 𝒰 u z * ∫ h, (LinParamBandits.UEFinite.pullCount u h : ℝ) ∂(LinParamBandits.UEGeneral.histMeasure ν z ψ T) := by
  set μ := LinParamBandits.UEGeneral.histMeasure ν z ψ T with hμ
  have : IsProbabilityMeasure μ := isProb_histMeasure ν z ψ T
  have hint : ∀ u, Integrable (fun h : LinParamBandits.LowerBound.History r T =>
      (LinParamBandits.UEFinite.pullCount u h : ℝ)) μ := by
    intro u
    refine Integrable.of_bound (measurable_pullCount u T).aestronglyMeasurable (T : ℝ) ?_
    refine Filter.Eventually.of_forall (fun h => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact_mod_cast pullCount_le u h
  have hG : Integrable (fun h : LinParamBandits.LowerBound.History r T =>
      ∑ u ∈ h𝒰fin.toFinset, LinParamBandits.UEFinite.gap 𝒰 u z *
        (LinParamBandits.UEFinite.pullCount u h : ℝ)) μ :=
    integrable_finsetSum _ (fun u _ => (hint u).const_mul _)
  have hRHS : ∑ u ∈ h𝒰fin.toFinset, LinParamBandits.UEFinite.gap 𝒰 u z *
      ∫ h, (LinParamBandits.UEFinite.pullCount u h : ℝ) ∂μ =
      ∫ h, ∑ u ∈ h𝒰fin.toFinset, LinParamBandits.UEFinite.gap 𝒰 u z *
        (LinParamBandits.UEFinite.pullCount u h : ℝ) ∂μ := by
    rw [integral_finsetSum _ (fun u _ => (hint u).const_mul _)]
    simp_rw [integral_const_mul]
  have hae := ae_armsIn 𝒰 h𝒰fin ν z ψ hψ.1 T
  have hEq : (fun h : LinParamBandits.LowerBound.History r T => ∑ s, inner ℝ (h s).1 z) =ᵐ[μ]
      fun h => (T : ℝ) * LinParamBandits.UEGeneral.bestValue 𝒰 z -
        ∑ u ∈ h𝒰fin.toFinset, LinParamBandits.UEFinite.gap 𝒰 u z *
          (LinParamBandits.UEFinite.pullCount u h : ℝ) := by
    filter_upwards [hae] with h hh
    rw [sum_gap_pull 𝒰 h𝒰fin z h hh]
    ring
  rw [hRHS]
  unfold LinParamBandits.UEFinite.Regret
  rw [← hμ, integral_congr_ae hEq, integral_sub (integrable_const _) hG, integral_const]
  simp
