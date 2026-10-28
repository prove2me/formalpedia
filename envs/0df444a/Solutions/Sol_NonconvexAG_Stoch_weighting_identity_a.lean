-- Prove2me | solution 1 for NonconvexAG.Stoch.weighting_identity_a
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T03:53:11.325751+00:00
-- url     : https://prove2.me/submissions/b541bfb5-dd9a-4e5c-a393-765649f5f125

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_Smooth_AGRun
import Definitions.Def_NonconvexAG_Stoch_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace Aux_NAGSwa
open NonconvexAG.Stoch GhadimiLan.RSG

lemma path_meas {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n)
    (hG : Measurable (Function.uncurry G)) (α β lam : ℕ → ℝ) (x0 : E n) :
    ∀ k, Measurable (fun s : ℕ → Ξ => rsagPath G α β lam x0 s k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have h1 : Measurable (fun s : ℕ → Ξ => (rsagPath G α β lam x0 s k).1) := ih.fst
    have h2 : Measurable (fun s : ℕ → Ξ => (rsagPath G α β lam x0 s k).2) := ih.snd
    have hlin : Continuous (fun p : E n × E n => (1 - α (k + 1)) • p.1 + α (k + 1) • p.2) := by
      fun_prop
    have hmd : Measurable (fun s : ℕ → Ξ => (1 - α (k + 1)) • (rsagPath G α β lam x0 s k).2 +
        α (k + 1) • (rsagPath G α β lam x0 s k).1) :=
      hlin.measurable.comp (h2.prodMk h1)
    have hGk : Measurable (fun s : ℕ → Ξ => G ((1 - α (k + 1)) • (rsagPath G α β lam x0 s k).2 +
        α (k + 1) • (rsagPath G α β lam x0 s k).1) (s (k + 1))) :=
      hG.comp (hmd.prodMk (measurable_pi_apply (k + 1)))
    have hsub1 : Continuous (fun p : E n × E n => p.1 - lam (k + 1) • p.2) := by fun_prop
    have hsub2 : Continuous (fun p : E n × E n => p.1 - β (k + 1) • p.2) := by fun_prop
    exact (hsub1.measurable.comp (h1.prodMk hGk)).prodMk (hsub2.measurable.comp (hmd.prodMk hGk))

end Aux_NAGSwa

open NonconvexAG.Stoch GhadimiLan.RSG Aux_NAGSwa in
theorem solution {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (α β lam : ℕ → ℝ) (hstep : RSAGStepsizes α β lam) (x0 : E n)
    (N : ℕ) (hN : 1 ≤ N) (hC : ∀ k ∈ Finset.Icc 1 N, 0 < NonconvexAG.Smooth.C LΨ α β lam N k)
    (R : Ω → ℕ) (hR : IsOutputIndex μ R N (pmfA LΨ α β lam N))
    (hRind : IndepFun R (fun ω k => ξ k ω) μ)
    (hint : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2) μ) :
    Integrable (fun ω => ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2) μ ∧
    ∫ ω, ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2 ∂μ =
      (∑ k ∈ Finset.Icc 1 N,
          lam k * NonconvexAG.Smooth.C LΨ α β lam N k * ∫ ω, ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 ∂μ) /
        ∑ k ∈ Finset.Icc 1 N, lam k * NonconvexAG.Smooth.C LΨ α β lam N k := by
  obtain ⟨hRm, hRrange, hRlaw⟩ := hR
  -- g is continuous
  have hgc : Continuous g := by
    have : LipschitzWith ⟨LΨ, hL.le⟩ g := LipschitzWith.of_dist_le_mul (fun x y => by
      rw [dist_eq_norm, dist_eq_norm]; exact hΨ.2.2 x y)
    exact this.continuous
  set Fk : ℕ → (ℕ → Ξ) → ℝ := fun k s =>
    ‖g ((1 - α k) • (rsagPath G α β lam x0 s (k - 1)).2 +
      α k • (rsagPath G α β lam x0 s (k - 1)).1)‖ ^ 2 with hFkdef
  have hFk : ∀ k, Measurable (Fk k) := by
    intro k
    have hp := path_meas G hG α β lam x0 (k - 1)
    have hc : Continuous (fun p : E n × E n => ‖g ((1 - α k) • p.1 + α k • p.2)‖ ^ 2) := by
      fun_prop
    have hm := hc.measurable.comp (hp.snd.prodMk hp.fst)
    exact hm
  set f : ℕ → Ω → ℝ := fun k ω => ‖g (xmdSeq G α β lam x0 ξ k ω)‖ ^ 2 with hfdef
  have hfk : ∀ k, f k = Fk k ∘ (fun ω j => ξ j ω) := fun k => rfl
  have hdecomp : (fun ω => ‖g (xmdSeq G α β lam x0 ξ (R ω) ω)‖ ^ 2) =
      fun ω => ∑ k ∈ Finset.Icc 1 N, (R ⁻¹' {k}).indicator (f k) ω := by
    funext ω
    rw [Finset.sum_eq_single_of_mem (R ω) (hRrange ω)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro b _ hb
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact fun h => hb h.symm
  have hmeasS : ∀ k, MeasurableSet (R ⁻¹' {k}) := fun k => hRm (measurableSet_singleton k)
  refine ⟨?_, ?_⟩
  · rw [hdecomp]
    exact integrable_finset_sum _ (fun k hk => (hint k hk).indicator (hmeasS k))
  -- positivity of weights
  have hpos : ∀ k ∈ Finset.Icc 1 N, 0 < lam k * NonconvexAG.Smooth.C LΨ α β lam N k := by
    intro k hk
    exact mul_pos (hstep.2.2.2 k (Finset.mem_Icc.1 hk).1) (hC k hk)
  have hSpos : 0 < ∑ k ∈ Finset.Icc 1 N, lam k * NonconvexAG.Smooth.C LΨ α β lam N k :=
    Finset.sum_pos hpos ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hN⟩⟩
  have hpmf_nn : ∀ k ∈ Finset.Icc 1 N, 0 ≤ pmfA LΨ α β lam N k := by
    intro k hk
    unfold pmfA
    exact div_nonneg (hpos k hk).le hSpos.le
  -- integral of each term
  have hterm : ∀ k ∈ Finset.Icc 1 N, ∫ ω, (R ⁻¹' {k}).indicator (f k) ω ∂μ =
      pmfA LΨ α β lam N k * ∫ ω, f k ω ∂μ := by
    intro k hk
    have hind : (R ⁻¹' {k}).indicator (f k) =
        fun ω => (({k} : Set ℕ).indicator (fun _ => (1 : ℝ)) (R ω)) * f k ω := by
      funext ω
      by_cases h : R ω = k
      · rw [Set.indicator_of_mem (by simp [h]), Set.indicator_of_mem (by simp [h]), one_mul]
      · rw [Set.indicator_of_notMem (by simp [h]), Set.indicator_of_notMem (by simp [h]),
          zero_mul]
    have hφ : Measurable (({k} : Set ℕ).indicator (fun _ => (1 : ℝ))) :=
      measurable_const.indicator (measurableSet_singleton k)
    have hindep := hRind.comp hφ (hFk k)
    have hX : AEStronglyMeasurable (({k} : Set ℕ).indicator (fun _ => (1 : ℝ)) ∘ R) μ :=
      (hφ.comp hRm).aestronglyMeasurable
    have hY : AEStronglyMeasurable (Fk k ∘ fun ω j => ξ j ω) μ := (hint k hk).aestronglyMeasurable
    have hXint : ∫ ω, (({k} : Set ℕ).indicator (fun _ => (1 : ℝ)) ∘ R) ω ∂μ =
        pmfA LΨ α β lam N k := by
      have : (({k} : Set ℕ).indicator (fun _ => (1 : ℝ)) ∘ R) =
          (R ⁻¹' {k}).indicator (fun _ => (1 : ℝ)) := by
        funext ω
        simp only [Function.comp, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
      rw [this, integral_indicator_const _ (hmeasS k), smul_eq_mul, mul_one, measureReal_def]
      have hl := hRlaw k hk
      rw [show R ⁻¹' {k} = {ω | R ω = k} by ext; simp, hl,
        ENNReal.toReal_ofReal (hpmf_nn k hk)]
    rw [hind]
    calc ∫ ω, ({k} : Set ℕ).indicator (fun _ => (1 : ℝ)) (R ω) * f k ω ∂μ
        = ∫ ω, (({k} : Set ℕ).indicator (fun _ => (1 : ℝ)) ∘ R) ω *
            (Fk k ∘ fun ω j => ξ j ω) ω ∂μ := rfl
      _ = (∫ ω, (({k} : Set ℕ).indicator (fun _ => (1 : ℝ)) ∘ R) ω ∂μ) *
            ∫ ω, (Fk k ∘ fun ω j => ξ j ω) ω ∂μ :=
          hindep.integral_fun_mul_eq_mul_integral hX hY
      _ = pmfA LΨ α β lam N k * ∫ ω, f k ω ∂μ := by rw [hXint]; rfl
  rw [hdecomp, integral_finset_sum _ (fun k hk => (hint k hk).indicator (hmeasS k)),
    Finset.sum_congr rfl hterm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  unfold pmfA
  ring
