-- Prove2me | solution 1 for NewtonCartan.contDiff_integral_I01
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:09:42.217085+00:00
-- url     : https://prove2.me/submissions/04e82e8d-1ae7-4192-973b-c64f676ee2df

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped ContDiff Topology Interval
open MeasureTheory Metric Set Filter ContinuousLinearMap

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable def partialX (g : E → ℝ → ℝ) (x : E) (s : ℝ) : E →L[ℝ] ℝ :=
  (fderiv ℝ (fun p : E × ℝ => g p.1 p.2) (x, s)).comp (inl ℝ E ℝ)

lemma hasFDerivAt_integral_I01 (g : E → ℝ → ℝ)
    (hg : ContDiff ℝ 1 (fun p : E × ℝ => g p.1 p.2)) (x₀ : E) :
    HasFDerivAt (fun x : E => ∫ s in (0 : ℝ)..1, g x s)
      (∫ s in (0 : ℝ)..1, partialX g x₀ s) x₀ := by
  let F : E → ℝ → ℝ := g
  let F' : E → ℝ → E →L[ℝ] ℝ := partialX g
  let sset : Set E := ball x₀ 1
  have hs : sset ∈ 𝓝 x₀ := ball_mem_nhds _ one_pos
  have hK : IsCompact (closedBall x₀ 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hDg : Continuous (fderiv ℝ (fun p : E × ℝ => g p.1 p.2)) :=
    hg.continuous_fderiv (by simp)
  let img := (fun p => ‖fderiv ℝ (fun q : E × ℝ => g q.1 q.2) p‖) ''
    (closedBall x₀ 1 ×ˢ Icc (0 : ℝ) 1)
  have hImg_bdd : BddAbove img :=
    (hK.image (continuous_norm.comp hDg)).bddAbove
  let M₀ : ℝ := sSup img
  let M : ℝ := M₀ + 1
  have hM0_nonneg : 0 ≤ M₀ := by
    apply Real.sSup_nonneg
    intro r hr
    obtain ⟨p, _, rfl⟩ := hr
    exact norm_nonneg _
  let bound : ℝ → ℝ := fun _ => M
  have hF_int : IntervalIntegrable (F x₀) volume (0 : ℝ) 1 :=
    (hg.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (volume.restrict (Ι (0:ℝ) 1)) :=
    Eventually.of_forall fun x =>
      (hg.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Ι (0:ℝ) 1)) := by
    have hC : Continuous fun s : ℝ => F' x₀ s := by
      have h1 : Continuous fun s : ℝ => fderiv ℝ (fun p : E × ℝ => g p.1 p.2) (x₀, s) :=
        hDg.comp (continuous_const.prodMk continuous_id)
      exact Continuous.clm_comp h1 continuous_const
    exact hC.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) 1 → ∀ x ∈ sset, ‖F' x t‖ ≤ bound t := by
    filter_upwards with t ht x hx
    have hx' : x ∈ closedBall x₀ 1 := ball_subset_closedBall hx
    have ht' : t ∈ Icc (0:ℝ) 1 := by
      have : t ∈ uIoc (0:ℝ) 1 := ht
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at this
      exact Ioc_subset_Icc_self this
    have hmem : (x, t) ∈ closedBall x₀ 1 ×ˢ Icc (0:ℝ) 1 := ⟨hx', ht'⟩
    have hle : ‖fderiv ℝ (fun q : E × ℝ => g q.1 q.2) (x, t)‖ ≤ M₀ :=
      le_csSup hImg_bdd (mem_image_of_mem _ hmem)
    have hcomp : ‖F' x t‖ ≤ ‖fderiv ℝ (fun q : E × ℝ => g q.1 q.2) (x, t)‖ := by
      dsimp [F', partialX]
      calc ‖(fderiv ℝ (fun q : E × ℝ => g q.1 q.2) (x, t)).comp (inl ℝ E ℝ)‖
          ≤ ‖fderiv ℝ (fun q : E × ℝ => g q.1 q.2) (x, t)‖ * ‖(inl ℝ E ℝ : E →L[ℝ] E × ℝ)‖ :=
            opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ (fun q : E × ℝ => g q.1 q.2) (x, t)‖ * 1 := by
            gcongr
            exact ContinuousLinearMap.norm_inl_le_one ℝ E ℝ
        _ = ‖fderiv ℝ (fun q : E × ℝ => g q.1 q.2) (x, t)‖ := by ring
    dsimp [bound, M]
    linarith
  have hbound_int : IntervalIntegrable bound volume (0:ℝ) 1 := intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) 1 → ∀ x ∈ sset,
      HasFDerivAt (fun x => F x t) (F' x t) x := by
    filter_upwards with t _ht x _hx
    have h := ((hg.differentiable (by simp)).differentiableAt (x := (x, t))).hasFDerivAt
    have hinl : HasFDerivAt (fun z : E => ((z, t) : E × ℝ)) (inl ℝ E ℝ) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
    exact h.comp x hinl
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff

lemma fderiv_integral_I01 (g : E → ℝ → ℝ)
    (hg : ContDiff ℝ 1 (fun p : E × ℝ => g p.1 p.2)) (x : E) :
    fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..1, g z s) x =
      ∫ s in (0 : ℝ)..1, partialX g x s :=
  (hasFDerivAt_integral_I01 g hg x).fderiv

/-- Scalarization of `partialX`: `partialX g x s v = Df(x,s)(v,0)`. -/
lemma partialX_apply (g : E → ℝ → ℝ) (x : E) (s : ℝ) (v : E) :
    partialX g x s v =
      fderiv ℝ (fun p : E × ℝ => g p.1 p.2) (x, s) (v, 0) := by
  simp [partialX, ContinuousLinearMap.comp_apply, inl_apply]

lemma contDiff_partialX_apply (g : E → ℝ → ℝ) {n : ℕ∞} (v : E)
    (hg : ContDiff ℝ (n + 1) (fun p : E × ℝ => g p.1 p.2)) :
    ContDiff ℝ n (fun p : E × ℝ => partialX g p.1 p.2 v) := by
  have hfderiv : ContDiff ℝ n (fderiv ℝ (fun p : E × ℝ => g p.1 p.2)) :=
    hg.fderiv_right (m := n) (by simp)
  have happly : ContDiff ℝ n
      fun p : E × ℝ => fderiv ℝ (fun q : E × ℝ => g q.1 q.2) p (v, (0 : ℝ)) :=
    hfderiv.clm_apply contDiff_const
  convert happly using 1
  ext p
  exact partialX_apply g p.1 p.2 v

lemma integrable_partialX (g : E → ℝ → ℝ)
    (hg : ContDiff ℝ 1 (fun p : E × ℝ => g p.1 p.2)) (x : E) :
    IntervalIntegrable (fun s => partialX g x s) volume (0 : ℝ) 1 := by
  have hC : Continuous fun s : ℝ => partialX g x s := by
    have hDg : Continuous (fderiv ℝ (fun p : E × ℝ => g p.1 p.2)) :=
      hg.continuous_fderiv (by simp)
    have h1 : Continuous fun s : ℝ => fderiv ℝ (fun p : E × ℝ => g p.1 p.2) (x, s) :=
      hDg.comp (continuous_const.prodMk continuous_id)
    exact Continuous.clm_comp h1 continuous_const
  exact hC.intervalIntegrable _ _

/-- ContDiff of `x ↦ ∫₀¹ g(x,s) ds` when `(x,s) ↦ g(x,s)` is ContDiff. -/
theorem contDiff_integral_I01_nat (k : ℕ) (g : E → ℝ → ℝ)
    (hg : ContDiff ℝ k (fun p : E × ℝ => g p.1 p.2)) :
    ContDiff ℝ k (fun x : E => ∫ s in (0 : ℝ)..1, g x s) := by
  induction k generalizing g with
  | zero =>
    have hg' : ContDiff ℝ (0 : ℕ∞ω) (fun p : E × ℝ => g p.1 p.2) := by
      convert hg; norm_cast
    rw [contDiff_zero] at hg'
    have hI : Continuous (fun x : E => ∫ s in (0 : ℝ)..1, g x s) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := g) hg' 0 1
    have : ContDiff ℝ (0 : ℕ∞ω) (fun x : E => ∫ s in (0 : ℝ)..1, g x s) := contDiff_zero.2 hI
    convert this; norm_cast
  | succ k ih =>
    have hg1 : ContDiff ℝ 1 (fun p : E × ℝ => g p.1 p.2) :=
      hg.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
    -- Align `↑(k+1)` with `↑k + 1` expected by `contDiff_succ_iff_hasFDerivAt`
    have hcast : ContDiff ℝ (↑k + 1 : ℕ∞ω) (fun x : E => ∫ s in (0 : ℝ)..1, g x s) ↔
        ContDiff ℝ ↑(k + 1) (fun x : E => ∫ s in (0 : ℝ)..1, g x s) := by
      constructor <;> intro h <;> convert h <;> simp [Nat.cast_succ]
    refine hcast.1 ?_
    have hg' : ContDiff ℝ (↑k + 1 : ℕ∞ω) (fun p : E × ℝ => g p.1 p.2) := by
      convert hg; simp [Nat.cast_succ]
    rw [contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ s in (0 : ℝ)..1, partialX g x s, ?_, fun x => hasFDerivAt_integral_I01 g hg1 x⟩
    refine (contDiff_clm_apply_iff (n := (k : ℕ∞))).2 fun v => ?_
    have happ :
        (fun x => (∫ s in (0 : ℝ)..1, partialX g x s) v) =
          fun x => ∫ s in (0 : ℝ)..1, partialX g x s v := by
      ext x
      exact ContinuousLinearMap.intervalIntegral_apply (integrable_partialX g hg1 x) v
    rw [happ]
    have hgN : ContDiff ℝ ((k : ℕ∞) + 1) (fun p : E × ℝ => g p.1 p.2) := by
      convert hg; simp [Nat.cast_succ]
    have hpx0 : ContDiff ℝ (k : ℕ∞) (fun p : E × ℝ => partialX g p.1 p.2 v) :=
      contDiff_partialX_apply g (n := (k : ℕ∞)) v hgN
    have hpx : ContDiff ℝ k (fun p : E × ℝ => partialX g p.1 p.2 v) := by
      convert hpx0; norm_cast
    exact ih (fun x s => partialX g x s v) hpx

theorem solution (n : ℕ∞) (g : E → ℝ → ℝ)
    (hg : ContDiff ℝ n (fun p : E × ℝ => g p.1 p.2)) :
    ContDiff ℝ n (fun x : E => ∫ s in (0 : ℝ)..1, g x s) := by
  refine contDiff_iff_forall_nat_le.2 fun m hm =>
    contDiff_integral_I01_nat m g (hg.of_le (by exact_mod_cast hm))


