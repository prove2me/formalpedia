-- Prove2me | solution 1 for OAI.QuinticLienard.upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T18:28:41.85099+00:00
-- url     : https://prove2.me/submissions/8bc306c0-9150-4af9-8482-6d2693065fbb

import Mathlib
import Definitions.Def_QuinticLienard
import Definitions.Def_OAIQWQL000
import Theorems.Thm_OAI_QuinticLienard_AxisFlow_matching_isolated_case2
import Theorems.Thm_OAI_QuinticLienard_AxisFlow_matching_isolated_case3
import Theorems.Thm_OAI_QuinticLienard_AxisFlow_matching_isolated_case4

section
-- module Solutions.OAIQW_QuinticLienard.SmoothFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuinticLienard.SmoothFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_contDiff_picard [CompleteSpace E] (W : Path E → Path E) (x₀ : E)
    (hW : ContDiffAt ℝ ω W (constCLM x₀)) :
    ∃ U : E × ℝ → Path E,
      ContDiffAt ℝ ω U (x₀,0) ∧ U (x₀,0) = constCLM x₀ ∧
      (∀ᶠ p in 𝓝 (x₀,(0:ℝ)),
        U p = constCLM p.1 + p.2 • primitiveCLM (W (U p))) ∧
      ∀ᶠ p in 𝓝 ((x₀,(0:ℝ)),constCLM x₀),
        p.2 = constCLM p.1.1 + p.1.2 • primitiveCLM (W p.2) → U p.1 = p.2 := by
  let Φ : (E × ℝ) × Path E → Path E :=
    fun p => p.2 - constCLM p.1.1 - p.1.2 • primitiveCLM (W p.2)
  have hΦ : ContDiffAt ℝ ω Φ ((x₀,0),constCLM x₀) := by
    apply ContDiffAt.sub
    · exact contDiffAt_snd.sub ((constCLM (E := E)).contDiff.contDiffAt.comp ((x₀,0),constCLM x₀) (contDiffAt_fst.fst))
    · exact contDiffAt_fst.snd.smul
        ((primitiveCLM (E := E)).contDiff.contDiffAt.comp ((x₀,0),constCLM x₀) (hW.comp ((x₀,0),constCLM x₀) contDiffAt_snd))
  have hpartial : fderiv ℝ Φ ((x₀,0),constCLM x₀) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) (Path E) = ContinuousLinearMap.id ℝ (Path E) := by
    have hd := (hΦ.differentiableAt (by simp)).hasFDerivAt.comp (constCLM x₀)
      ((hasFDerivAt_const (x₀,(0:ℝ)) (constCLM x₀)).prodMk (hasFDerivAt_id (constCLM x₀)))
    have he : HasFDerivAt (fun u : Path E => Φ ((x₀,0),u))
        (ContinuousLinearMap.id ℝ (Path E)) (constCLM x₀) := by
      simpa [Φ] using (hasFDerivAt_id (constCLM x₀)).sub_const (constCLM x₀)
    convert hd.unique he using 1; ext u; simp
  have hinv : (fderiv ℝ Φ ((x₀,0),constCLM x₀) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) (Path E)).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  let U := hΦ.implicitFunction (by simp) hinv
  refine ⟨U, hΦ.contDiffAt_implicitFunction (by simp) hinv,
    hΦ.implicitFunction_apply_self (by simp) hinv, ?_⟩
  constructor
  · filter_upwards [hΦ.eventually_apply_implicitFunction (by simp) hinv] with p hp
    change Φ (p,U p) = Φ ((x₀,0),constCLM x₀) at hp
    simp only [Φ, sub_self, zero_smul] at hp
    simpa [add_comm] using sub_eq_iff_eq_add.mp (sub_eq_zero.mp hp)
  · filter_upwards [hΦ.eventually_apply_eq_iff_implicitFunction (by simp) hinv] with p hp
    intro he
    apply hp.mp
    change p.2 - constCLM p.1.1 - p.1.2 • primitiveCLM (W p.2) = _
    rw [sub_sub, sub_eq_zero.mpr he]
    simp [Φ]

lemma hasDerivAt_extend_primitive [CompleteSpace E] (u : Path E) {s : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (extend (primitive u)) (extend u s) s := by
  have hd := (continuous_extend u).integral_hasStrictDerivAt 0 s
  apply hd.hasDerivAt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  simp [extend, primitive_apply, clamp, projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) (Ioo_subset_Icc_self ht)]

lemma picard_initial (W : Path E → Path E) {x : E} {t : ℝ} {u : Path E}
    (hu : u = constCLM x + t • primitiveCLM (W u)) : extend u 0 = x := by
  have he := congrArg (fun u : Path E => extend u 0) hu
  simpa [extend_add, extend_smul, primitiveCLM_apply] using he

lemma picard_derivative [CompleteSpace E] (W : Path E → Path E)
    {x : E} {t : ℝ} {u : Path E}
    (hu : u = constCLM x + t • primitiveCLM (W u))
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (extend u) (t • extend (W u) s) s := by
  nth_rw 1 [hu]
  simpa only [extend_add, extend_smul, primitiveCLM_apply, extend_const,
    Pi.add_apply, Pi.smul_apply, zero_add] using
    (hasDerivAt_const s x).add ((hasDerivAt_extend_primitive (W u) hs).const_smul t)

lemma dist_reparam_const_le (u : Path E) (q : ℝ) (x : E) :
    dist (reparam u q) (constCLM x) ≤ dist u (constCLM x) := by
  apply (ContinuousMap.dist_le (dist_nonneg)).mpr
  intro s
  exact ContinuousMap.dist_apply_le_dist (f := u) (g := constCLM x) (clamp (q * s))

lemma abs_mul_lt_one {q s : ℝ} (hq : |q| < 1) (hs : |s| ≤ 1) :
    q * s ∈ Ioo (-1 : ℝ) 1 := by
  apply abs_lt.mp
  calc
    |q * s| = |q| * |s| := abs_mul _ _
    _ ≤ |q| * 1 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ < 1 := by simpa using hq

lemma picard_rescale [CompleteSpace E] (W : Path E → Path E) (V : E → E)
    {x : E} {t q : ℝ} {u : Path E}
    (hWu : ∀ s, W u s = V (u s))
    (hWr : ∀ s, W (reparam u q) s = V (reparam u q s))
    (hu : u = constCLM x + t • primitiveCLM (W u)) (hq : |q| < 1) :
    reparam u q = constCLM x + (t*q) • primitiveCLM (W (reparam u q)) := by
  ext s
  let f : ℝ → E := fun y => extend u (q*y)
  let g : ℝ → E := fun y => (t*q) • extend (W (reparam u q)) y
  have hd (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) : HasDerivAt f (g y) y := by
    have hqy := abs_mul_lt_one hq (abs_le.mpr hy)
    have hder := (picard_derivative W hu hqy).scomp y ((hasDerivAt_id y).const_mul q)
    simpa [f, g, Function.comp_def, extend, hWu, hWr, reparam_apply, clamp,
      projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) hy, smul_smul, mul_comm]
      using hder
  have hgi : IntervalIntegrable g volume 0 s :=
    ((continuous_extend (W (reparam u q))).const_smul (t*q)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hd y ?_) hgi
  · have hf0 : f 0 = x := by simpa [f] using picard_initial W hu
    have hes : (∫ y in (0:ℝ)..(s:ℝ), g y) = (t*q) • primitive (W (reparam u q)) s := by
      simp [g, primitive_apply, intervalIntegral.integral_smul]
    rw [hf0, hes] at he
    change f s = x + (t*q) • primitive (W (reparam u q)) s
    exact (eq_sub_iff_add_eq.mp he).symm.trans (add_comm _ _)
  · exact uIcc_subset_Icc (by norm_num) s.property hy

theorem exists_analytic_local_flow_eventually [CompleteSpace E] (W : Path E → Path E)
    (V : E → E) (x₀ : E) (hW : ∀ᶠ u in 𝓝 (constCLM x₀), ∀ s, W u s = V (u s))
    (hsmooth : ContDiffAt ℝ ω W (constCLM x₀)) :
    ∃ f : E × ℝ → E, ContDiffAt ℝ ω f (x₀,0) ∧
      ∀ᶠ p in 𝓝 (x₀,(0:ℝ)),
        f (p.1,0) = p.1 ∧ HasDerivAt (fun t => f (p.1,t)) (V (f p)) p.2 := by
  obtain ⟨U,hU,hU₀,hEq,hUnique⟩ := exists_contDiff_picard W x₀ hsmooth
  obtain ⟨ε₀,hε₀,huniq⟩ := Metric.mem_nhds_iff.mp hUnique
  obtain ⟨η,hη,hWnear⟩ := Metric.mem_nhds_iff.mp hW
  let ε := min ε₀ η
  have hε : 0 < ε := lt_min hε₀ hη
  have hε₀le : ε ≤ ε₀ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  have hUc : Tendsto U (𝓝 (x₀,(0:ℝ))) (𝓝 (constCLM x₀)) := by
    have hc := hU.continuousAt
    rw [ContinuousAt, hU₀] at hc
    exact hc
  have hnear := hEq.and (hUc.eventually (Metric.ball_mem_nhds (constCLM x₀) hε))
  obtain ⟨δ,hδ,hδnear⟩ := Metric.mem_nhds_iff.mp hnear
  let τ := δ/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτδ : τ < δ := by dsimp [τ]; linarith
  let r := min δ (min ε τ)
  have hr : 0 < r := lt_min hδ (lt_min hε hτ)
  have hrδ : r ≤ δ := min_le_left _ _
  have hrε : r ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ : r ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  have hτnear (x : E) (hx : dist x x₀ < r) :
      U (x,τ) = constCLM x + τ • primitiveCLM (W (U (x,τ))) ∧
        dist (U (x,τ)) (constCLM x₀) < ε := by
    apply hδnear
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
    exact ⟨hx.trans_le hrδ, by simpa [abs_of_pos hτ] using hτδ⟩
  let e : UnitInterval := ⟨1,by norm_num⟩
  let f : E × ℝ → E := fun p => U p e
  have hf : ContDiffAt ℝ ω f (x₀,0) :=
    (ContinuousMap.evalCLM ℝ e : Path E →L[ℝ] E).contDiff.contDiffAt.comp (x₀,0) hU
  have hrep (x : E) (t : ℝ) (hx : dist x x₀ < r) (ht : |t| < r) :
      f (x,t) = extend (U (x,τ)) (t/τ) := by
    have hqt : |t/τ| < 1 := by
      rw [abs_div, abs_of_pos hτ, div_lt_one hτ]
      exact ht.trans_le hrτ
    have hWu := hWnear (show U (x,τ) ∈ Metric.ball (constCLM x₀) η from
      (hτnear x hx).2.trans_le hεη)
    have hWr := hWnear (show reparam (U (x,τ)) (t/τ) ∈ Metric.ball (constCLM x₀) η from
      (dist_reparam_const_le _ _ _).trans_lt ((hτnear x hx).2.trans_le hεη))
    have he := picard_rescale W V hWu hWr (hτnear x hx).1 hqt
    have hmul : τ * (t/τ) = t := by field_simp
    rw [hmul] at he
    have hev : U (x,t) = reparam (U (x,τ)) (t/τ) := by
      apply huniq (a := ((x,t),reparam (U (x,τ)) (t/τ))) _ he
      simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
      exact ⟨⟨(hx.trans_le hrε).trans_le hε₀le, (ht.trans_le hrε).trans_le hε₀le⟩,
        (dist_reparam_const_le _ _ _).trans_lt ((hτnear x hx).2.trans_le hε₀le)⟩
    simp [f, hev, e]
  refine ⟨f,hf,?_⟩
  filter_upwards [Metric.ball_mem_nhds (x₀,(0:ℝ)) hr] with p hp
  have hp' : dist p.1 x₀ < r ∧ |p.2| < r := by
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using hp
  have hint : p.2/τ ∈ Ioo (-1 : ℝ) 1 := by
    apply abs_lt.mp
    rw [abs_div, abs_of_pos hτ, div_lt_one hτ]
    exact hp'.2.trans_le hrτ
  constructor
  · rw [hrep p.1 0 hp'.1 (by simpa using hr), zero_div]
    exact picard_initial W (hτnear p.1 hp'.1).1
  · have hd := (picard_derivative W (hτnear p.1 hp'.1).1 hint).scomp p.2
        ((hasDerivAt_id p.2).div_const τ)
    have hder : HasDerivAt (fun t => extend (U (p.1,τ)) (t/τ)) (V (f p)) p.2 := by
      rw [hrep p.1 p.2 hp'.1 hp'.2]
      have hWu := hWnear (show U (p.1,τ) ∈ Metric.ball (constCLM x₀) η from
        (hτnear p.1 hp'.1).2.trans_le hεη)
      change ∀ s, W (U (p.1,τ)) s = V (U (p.1,τ) s) at hWu
      simpa [Function.comp_def, extend, hWu, smul_smul, ne_of_gt hτ] using hd
    apply hder.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (abs_lt.mp hp'.2).1 (abs_lt.mp hp'.2).2] with t ht
    exact hrep p.1 t hp'.1 (abs_lt.mpr ht)

namespace RationalExpr
variable {ι : Type uι} [Fintype ι]

lemma inverse_eval (u : Path ℝ) (hu : IsUnit u) (s : UnitInterval) :
    (Ring.inverse u) s = (u s)⁻¹ := by
  have he := congrArg (fun v : Path ℝ => v s) (Ring.inverse_mul_cancel u hu)
  change (Ring.inverse u) s * u s = 1 at he
  have hne := (u.isUnit_iff_forall_ne_zero.mp hu) s
  apply (mul_right_cancel₀ hne)
  rw [he,inv_mul_cancel₀ hne]

end RationalExpr

end QuinticLienard.SmoothFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.GlobalODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open Set Filter MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold

namespace QuinticLienard.GlobalODE

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section Flow
variable (V : E → E) {K L : ℝ≥0} (hK : LipschitzWith K V) (hL : ∀ x, ‖V x‖ ≤ L)

 theorem flow_deriv (x : E) (t : ℝ) :
    HasDerivAt (flow V hK hL x) (V (flow V hK hL x t)) t :=
  (Classical.choose_spec (bounded_lipschitz_global_solution V hK hL x)).2 t

 theorem flow_unique {x : E} {u : ℝ → E} (hu : ∀ t, HasDerivAt u (V (u t)) t)
    (h0 : u 0 = x) : u = flow V hK hL x := by
  apply ODE_solution_unique_univ (v := fun _ : ℝ => V) (s := fun _ => Set.univ) (t₀ := 0)
  · exact fun _ => hK.lipschitzOnWith
  · exact fun t => ⟨hu t, mem_univ _⟩
  · exact fun t => ⟨flow_deriv V hK hL x t, mem_univ _⟩
  · simpa using h0

 theorem flow_add (x : E) (s t : ℝ) :
    flow V hK hL x (s+t) = flow V hK hL (flow V hK hL x s) t := by
  have hu : ∀ t, HasDerivAt (fun t => flow V hK hL x (s+t))
      (V (flow V hK hL x (s+t))) t := by
    intro t
    simpa [Function.comp_def] using (flow_deriv V hK hL x (s+t)).scomp t ((hasDerivAt_id t).const_add s)
  exact congrFun (flow_unique V hK hL hu (by simp)) t

 theorem flow_lipschitz_time (x : E) : LipschitzWith L (flow V hK hL x) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact fun t => (flow_deriv V hK hL x t).differentiableAt
  · intro t
    rw [(flow_deriv V hK hL x t).deriv]
    exact_mod_cast hL (flow V hK hL x t)

 theorem flow_dist_initial (x y : E) (t : ℝ) :
    dist (flow V hK hL x t) (flow V hK hL y t) ≤ dist x y * Real.exp (K * |t|) := by
  have hpos {W : E → E} (hW : LipschitzWith K W) {f g : ℝ → E}
      (hf : ∀ s, HasDerivAt f (W (f s)) s) (hg : ∀ s, HasDerivAt g (W (g s)) s)
      {t : ℝ} (ht : 0 ≤ t) : dist (f t) (g t) ≤ dist (f 0) (g 0) * Real.exp (K*t) := by
    simpa using dist_le_of_trajectories_ODE (v := fun _ : ℝ => W)
      (fun _ => hW) (fun z _ => (hf z).continuousAt.continuousWithinAt)
      (fun z _ => (hf z).hasDerivWithinAt)
      (fun z _ => (hg z).continuousAt.continuousWithinAt)
      (fun z _ => (hg z).hasDerivWithinAt) (le_refl (dist (f 0) (g 0))) t ⟨ht,le_rfl⟩
  rcases le_total 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using hpos hK (flow_deriv V hK hL x)
      (flow_deriv V hK hL y) ht
  · have hder (a : E) (s : ℝ) : HasDerivAt (fun s => flow V hK hL a (-s))
        (-V (flow V hK hL a (-s))) s := by
      simpa [Function.comp_def] using (flow_deriv V hK hL a (-s)).scomp s (hasDerivAt_id s).neg
    simpa [abs_of_nonpos ht] using
      hpos hK.neg (hder x) (hder y) (neg_nonneg.mpr ht)

 theorem continuous_flow : Continuous (fun p : E × ℝ => flow V hK hL p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound (q : E × ℝ) : dist (flow V hK hL q.1 q.2) (flow V hK hL p.1 p.2) ≤
      L * dist q.2 p.2 + dist q.1 p.1 * Real.exp (K * |p.2|) := by
    calc
      _ ≤ dist (flow V hK hL q.1 q.2) (flow V hK hL q.1 p.2) +
          dist (flow V hK hL q.1 p.2) (flow V hK hL p.1 p.2) := dist_triangle _ _ _
      _ ≤ _ := add_le_add ((flow_lipschitz_time V hK hL q.1).dist_le_mul _ _)
        (flow_dist_initial V hK hL q.1 p.1 p.2)
  apply squeeze_zero (fun _ => dist_nonneg) hbound
  have hc : Continuous (fun q : E × ℝ =>
      L * dist q.2 p.2 + dist q.1 p.1 * Real.exp (K * |p.2|)) := by fun_prop
  simpa using hc.tendsto p

theorem local_family_eq (x₀ : E) (f : E × ℝ → E)
    (hf : ∀ᶠ p in 𝓝 (x₀,(0:ℝ)), f (p.1,0) = p.1 ∧
      HasDerivAt (fun t => f (p.1,t)) (V (f p)) p.2) :
    f =ᶠ[𝓝 (x₀,(0:ℝ))] (fun p => flow V hK hL p.1 p.2) := by
  obtain ⟨r,hr,hrf⟩ := Metric.mem_nhds_iff.mp hf
  have he (x : E) (hx : dist x x₀ < r) (t : ℝ) (ht : |t| < r) :
      f (x,t) = flow V hK hL x t := by
    have hdo (s : ℝ) (hs : s ∈ Ioo (-r) r) := hrf
      (show (x,s) ∈ ball (x₀,(0:ℝ)) r by
        simpa only [mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
          using And.intro hx (abs_lt.mpr hs))
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ : ℝ => V) (s := fun _ => Set.univ)
      (fun _ _ => hK.lipschitzOnWith)
      (show (0:ℝ) ∈ Ioo (-r) r by constructor <;> linarith)
      (fun s hs => ⟨(hdo s hs).2, mem_univ _⟩)
      (fun s _ => ⟨flow_deriv V hK hL x s, mem_univ _⟩)
      (by simpa using (hdo 0 (by constructor <;> linarith)).1)
      (abs_lt.mp ht)
  filter_upwards [Metric.ball_mem_nhds (x₀,(0:ℝ)) hr] with p hp
  have hp' : dist p.1 x₀ < r ∧ |p.2| < r := by
    simpa only [mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using hp
  exact he p.1 hp'.1 p.2 hp'.2

theorem analytic_flow_on_trajectory (x : E) {I : Set ℝ} (hI : IsPreconnected I)
    (h0 : 0 ∈ I)
    (hloc : ∀ t ∈ I, ContDiffAt ℝ ω (fun p : E × ℝ => flow V hK hL p.1 p.2)
      (flow V hK hL x t,0)) :
    ∀ t ∈ I, ContDiffAt ℝ ω (fun p : E × ℝ => flow V hK hL p.1 p.2) (x,t) := by
  let F : E × ℝ → E := fun p => flow V hK hL p.1 p.2
  let A : Set ℝ := {t | ContDiffAt ℝ ω F (x,t)}
  have hA : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change ContDiffAt ℝ ω F (x,t) at ht
    have hc : ContinuousAt (fun s : ℝ => (x,s)) t := by fun_prop
    exact hc.eventually ((ht : ContDiffAt ℝ ω F (x,t)).eventually (by simp))
  have hA0 : (I ∩ A).Nonempty := by
    refine ⟨0,h0,?_⟩
    simpa [A,F] using hloc 0 h0
  apply hI.subset_of_closure_inter_subset hA hA0
  intro t ht
  have hc : ContinuousAt (fun s : ℝ => (flow V hK hL x s,t-s)) t :=
    ((flow_lipschitz_time V hK hL x).continuous.continuousAt).prodMk
      (continuousAt_const.sub continuousAt_id)
  have he : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ ω F (flow V hK hL x s,t-s) := by
    apply hc.eventually
    simpa only [sub_self] using (hloc t ht.2).eventually (by simp)
  obtain ⟨s,hs,hsA⟩ := mem_closure_iff_nhds.mp ht.1 _ he
  change ContDiffAt ℝ ω F (x,s) at hsA
  have hslice : ContDiffAt ℝ ω (fun z : E => flow V hK hL z s) x :=
    (hsA : ContDiffAt ℝ ω F (x,s)).comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hpair : ContDiffAt ℝ ω (fun p : E × ℝ => (flow V hK hL p.1 s,p.2-s)) (x,t) :=
    (hslice.comp (x,t) contDiffAt_fst).prodMk (contDiffAt_snd.sub contDiffAt_const)
  change ContDiffAt ℝ ω F (flow V hK hL x s,t-s) at hs
  have ht' := hs.comp (x,t) hpair
  change ContDiffAt ℝ ω F (x,t)
  convert ht' using 1
  ext p
  simp only [F, Function.comp_def]
  rw [← flow_add V hK hL p.1 s (p.2-s)]
  congr 1
  ring
end Flow

omit [CompleteSpace E] in

theorem exists_bounded_lipschitz_cutoff_on [FiniteDimensional ℝ E]
    (V : E → E) {s U : Set E} (hs : IsCompact s) (hU : IsOpen U)
    (hsub : s ⊆ U) (hV : ContDiffOn ℝ 1 V U) :
    ∃ (W : E → E) (K L : ℝ≥0), LipschitzWith K W ∧ (∀ x, ‖W x‖ ≤ L) ∧
      ∀ x ∈ s, W =ᶠ[𝓝 x] V := by
  obtain ⟨f,hf0,hf1,_⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ,E)) (n := 1) hU.isClosed_compl hs.isClosed
    (disjoint_compl_left_iff.mpr hsub)
  have hfd : ContDiff ℝ 1 (fun x => f x) := contMDiff_iff_contDiff.mp f.contMDiff
  obtain ⟨r,hr⟩ := hs.isBounded.subset_closedBall (0:E)
  let b : ContDiffBump (0:E) := ⟨max r 0+1,max r 0+2,by positivity,by linarith⟩
  let W : E → E := fun x => b x • (f x • V x)
  have hWd : ContDiff ℝ 1 W := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact b.contDiff.contDiffAt.smul (hfd.contDiffAt.smul
        (hV.contDiffAt (hU.mem_nhds hx)))
    · apply (contDiffAt_const (c := (0:E))).congr_of_eventuallyEq
      filter_upwards [hf0.filter_mono (nhds_le_nhdsSet hx)] with y hy
      simp [W,hy]
  have hWs : HasCompactSupport W := b.hasCompactSupport.smul_right
  obtain ⟨K,hK⟩ := hWd.lipschitzWith_of_hasCompactSupport hWs (by norm_num)
  obtain ⟨L,hL⟩ := hWs.exists_bound_of_continuous hWd.continuous
  refine ⟨W,K,⟨max L 0,le_max_right _ _⟩,hK,
    fun x => (hL x).trans (le_max_left _ _),?_⟩
  intro x hx
  have hb : (fun y => b y) =ᶠ[𝓝 x] 1 := b.eventuallyEq_one_of_mem_ball (by
    have hx' := hr hx
    change dist x 0 ≤ r at hx'
    change dist x 0 < max r 0+1
    exact hx'.trans_lt ((le_max_left _ _).trans_lt (by linarith)))
  filter_upwards [hb,hf1.filter_mono (nhds_le_nhdsSet hx)] with y hy hy'
  simp [W,hy,hy']

theorem analytic_family_along_compact_solution [FiniteDimensional ℝ E]
    (V : E → E) {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U)
    (hloc : ∀ x ∈ U, ∃ f : E × ℝ → E, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ p in 𝓝 (x,(0:ℝ)), f (p.1,0) = p.1 ∧
        HasDerivAt (fun t => f (p.1,t)) (V (f p)) p.2)
    {γ : ℝ → E} {a b c : ℝ} (ha : a < c) (hb : c < b)
    (hγ : Continuous γ) (hγU : ∀ y ∈ Icc a b, γ y ∈ U)
    (hγd : ∀ y ∈ Icc a b, HasDerivAt γ (V (γ y)) y) :
    ∃ f : E × ℝ → E, Continuous f ∧ (∀ x, f (x,0) = x) ∧
      (∀ y ∈ Icc a b, f (γ c,y-c) = γ y) ∧
      (∀ y ∈ Icc a b, ContDiffAt ℝ ω f (γ c,y-c)) ∧
      ∀ y ∈ Icc a b, ∀ᶠ p in 𝓝 (γ c,y-c),
        HasDerivAt (fun t => f (p.1,t)) (V (f p)) p.2 := by
  obtain ⟨W,K,L,hK,hL,hW⟩ := exists_bounded_lipschitz_cutoff_on V
    (isCompact_Icc.image hγ) hU (by rintro _ ⟨y,hy,rfl⟩; exact hγU y hy) hV
  let f : E × ℝ → E := fun p => flow W hK hL p.1 p.2
  have hmatch : ∀ y ∈ Icc a b, f (γ c,y-c) = γ y := by
    apply ODE_solution_unique_of_mem_Icc
      (v := fun _ => W) (s := fun _ => Set.univ) (K := K)
      (fun _ _ => hK.lipschitzOnWith) ⟨ha,hb⟩
      ((continuous_flow W hK hL).comp (by fun_prop)).continuousOn
      _ (fun _ _ => mem_univ _) hγ.continuousOn _ (fun _ _ => mem_univ _)
      (by simp)
    · intro y _
      simpa [f,Function.comp_def] using
        (flow_deriv W hK hL (γ c) (y-c)).scomp y ((hasDerivAt_id y).sub_const c)
    · intro y hy
      rw [(hW (γ y) ⟨y,Ioo_subset_Icc_self hy,rfl⟩).self_of_nhds]
      exact hγd y (Ioo_subset_Icc_self hy)
  have hlocalW (y : ℝ) (hy : y ∈ Icc a b) :
      ContDiffAt ℝ ω f (γ y,0) := by
    obtain ⟨g,hgd,hge⟩ := hloc (γ y) (hγU y hy)
    have hg0 : g (γ y,0) = γ y := hge.self_of_nhds.1
    have heV : ∀ᶠ p in 𝓝 (γ y,(0:ℝ)), W (g p) = V (g p) := by
      have ht := hgd.continuousAt.tendsto
      rw [hg0] at ht
      exact ht.eventually (hW (γ y) ⟨y,hy,rfl⟩)
    have heq : g =ᶠ[𝓝 (γ y,(0:ℝ))] f := by
      apply local_family_eq W hK hL (γ y) g
      filter_upwards [hge,heV] with p hp hp'
      exact ⟨hp.1,hp' ▸ hp.2⟩
    exact hgd.congr_of_eventuallyEq heq.symm
  have hd : ∀ y ∈ Icc a b, ContDiffAt ℝ ω f (γ c,y-c) := by
    have hh := analytic_flow_on_trajectory W hK hL (γ c)
      (I := Icc (a-c) (b-c)) isPreconnected_Icc
      (show (0:ℝ) ∈ Icc (a-c) (b-c) by constructor <;> linarith)
      (fun s hs => by
        have hs' : s+c ∈ Icc a b := by constructor <;> linarith [hs.1,hs.2]
        have heq : flow W hK hL (γ c) s = γ (s+c) := by
          simpa [f] using hmatch (s+c) hs'
        rw [heq]
        exact hlocalW (s+c) hs')
    exact fun y hy => hh (y-c) (by constructor <;> linarith [hy.1,hy.2])
  refine ⟨f,continuous_flow W hK hL,fun x => flow_zero W hK hL x,hmatch,hd,?_⟩
  intro y hy
  have hfc : Tendsto f (𝓝 (γ c,y-c)) (𝓝 (γ y)) := by
    have hc : ContinuousAt f (γ c,y-c) := (continuous_flow W hK hL).continuousAt
    simpa only [hmatch y hy] using hc.tendsto
  filter_upwards [hfc.eventually (hW (γ y) ⟨y,hy,rfl⟩)] with p hp
  rw [←hp]
  exact flow_deriv W hK hL p.1 p.2

end QuinticLienard.GlobalODE

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PartialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

open Set Filter MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold

open Filter Set
open scoped Topology ContDiff

namespace QuinticLienard.PartialCalculus

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma direction_contDiffAt {f : E → F} {x : E} (hf : ContDiffAt ℝ ω f x) (v : E) :
    ContDiffAt ℝ ω (direction v f) x :=
  (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

lemma direction_hasFDerivAt {f : E → F} {x : E} (hf : ContDiffAt ℝ ω f x) (v : E) :
    HasFDerivAt (direction v f) ((fderiv ℝ (fderiv ℝ f) x).flip v) x := by
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := ω) (by simp)).differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt (fun y => fderiv ℝ f y v) _ x
  convert hd.clm_apply (hasFDerivAt_const v x) using 1
  ext y
  simp

lemma direction_direction {f : E → F} {x : E} (hf : ContDiffAt ℝ ω f x) (v w : E) :
    direction v (direction w f) x = (fderiv ℝ (fderiv ℝ f) x v) w := by
  rw [direction,(direction_hasFDerivAt hf w).fderiv]
  rfl

lemma direction_comm {f : E → F} {x : E} (hf : ContDiffAt ℝ ω f x) (v w : E) :
    direction v (direction w f) x = direction w (direction v f) x := by
  rw [direction_direction hf,direction_direction hf]
  exact hf.isSymmSndFDerivAt_of_omega.eq v w

lemma first_contDiffAt {f : ℝ × ℝ → F} {p : ℝ × ℝ} (hf : ContDiffAt ℝ ω f p) :
    ContDiffAt ℝ ω (first f) p := direction_contDiffAt hf _
lemma second_contDiffAt {f : ℝ × ℝ → F} {p : ℝ × ℝ} (hf : ContDiffAt ℝ ω f p) :
    ContDiffAt ℝ ω (second f) p := direction_contDiffAt hf _

lemma first_hasDerivAt {f : ℝ × ℝ → F} {x y : ℝ}
    (hf : DifferentiableAt ℝ f (x,y)) :
    HasDerivAt (fun s => f (s,y)) (first f (x,y)) x := by
  simpa [first,direction,Function.comp_def] using
    hf.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

lemma second_hasDerivAt {f : ℝ × ℝ → F} {x y : ℝ}
    (hf : DifferentiableAt ℝ f (x,y)) :
    HasDerivAt (fun s => f (x,s)) (second f (x,y)) y := by
  simpa [second,direction,Function.comp_def] using
    hf.hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

lemma mixed_comm {f : ℝ × ℝ → F} {p : ℝ × ℝ} (hf : ContDiffAt ℝ ω f p) :
    first (second f) p = second (first f) p := direction_comm hf _ _

lemma fderiv_pair (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (a b : ℝ) :
    fderiv ℝ f p (a,b) = a * first f p + b * second f p := by
  have he : (a,b) = a • (1,0) + b • (0,1) := by ext <;> simp
  rw [he,map_add,map_smul,map_smul]
  rfl

theorem scalar_ode_variation {u Φ : ℝ × ℝ → ℝ} {θ y : ℝ}
    (hu : ContDiffAt ℝ ω u (θ,y)) (hΦ : DifferentiableAt ℝ Φ (θ,u (θ,y)))
    (he : ∀ᶠ p in 𝓝 (θ,y), HasDerivAt (fun s => u (p.1,s))
      (Φ (p.1,u p)-p.2) p.2) :
    HasDerivAt (fun s => first u (θ,s))
      (first Φ (θ,u (θ,y)) + second Φ (θ,u (θ,y))*first u (θ,y)) y := by
  have huN : ∀ᶠ p in 𝓝 (θ,y), ContDiffAt ℝ ω u p := hu.eventually (by simp)
  have heq : ∀ᶠ p in 𝓝 (θ,y), second u p = Φ (p.1,u p)-p.2 := by
    filter_upwards [he,huN] with p hp hpu
    exact (second_hasDerivAt (hpu.differentiableAt (by simp))).unique hp
  have hslice : (fun s => second u (s,y)) =ᶠ[𝓝 θ] (fun s => Φ (s,u (s,y))-y) :=
    (continuousAt_id.prodMk continuousAt_const).eventually heq
  have hcomp := hΦ.hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_id θ).prodMk (first_hasDerivAt (hu.differentiableAt (by simp))))
  have hcoeff : HasDerivAt (fun s => Φ (s,u (s,y))-y)
      (first Φ (θ,u (θ,y))+second Φ (θ,u (θ,y))*first u (θ,y)) θ := by
    have hc : HasDerivAt (fun s => Φ (s,u (s,y))-y)
        (fderiv ℝ Φ (θ,u (θ,y)) (1,first u (θ,y))) θ := hcomp.sub_const y
    convert hc using 1
    rw [fderiv_pair]
    ring
  have hd1 := first_hasDerivAt ((second_contDiffAt hu).differentiableAt (by simp))
  have hecoeff := hd1.unique (hcoeff.congr_of_eventuallyEq hslice)
  have hd2 := second_hasDerivAt ((first_contDiffAt hu).differentiableAt (by simp))
  rw [←mixed_comm hu,hecoeff] at hd2
  exact hd2

theorem transverse_hit [CompleteSpace E] {f : E × ℝ → ℝ} {p : E} {y a : ℝ}
    (hf : ContDiffAt ℝ ω f (p,y)) (hd : HasDerivAt (fun s => f (p,s)) a y)
    (ha : a ≠ 0) :
    ∃ Y : E → ℝ, ContDiffAt ℝ ω Y p ∧ Y p = y ∧
      (∀ᶠ q in 𝓝 p, f (q,Y q) = f (p,y)) ∧
      ∀ᶠ q in 𝓝 (p,y), f q = f (p,y) ↔ Y q.1 = q.2 := by
  have hpartial : fderiv ℝ f (p,y) ∘L ContinuousLinearMap.inr ℝ E ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ a := by
    have hc := (hf.differentiableAt (by simp)).hasFDerivAt.comp y
      ((hasFDerivAt_const p y).prodMk (hasFDerivAt_id y))
    exact hc.unique hd.hasFDerivAt
  have hi : (fderiv ℝ f (p,y) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
    rw [hpartial]
    refine ⟨(LinearEquiv.smulOfNeZero ℝ ℝ a ha).toContinuousLinearEquiv, ?_⟩
    apply ContinuousLinearMap.ext
    intro z
    change a*z=z*a
    ring
  exact ⟨hf.implicitFunction (by simp) hi,
    hf.contDiffAt_implicitFunction (by simp) hi,
    hf.implicitFunction_apply_self (by simp) hi,
    hf.eventually_apply_implicitFunction (by simp) hi,
    hf.eventually_apply_eq_iff_implicitFunction (by simp) hi⟩

lemma eq_of_hasDerivAt_eq_on_Icc {f g : ℝ → F} {a b c : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    {d : ℝ → F}
    (hdf : ∀ y ∈ Icc a b, HasDerivAt f (d y) y)
    (hdg : ∀ y ∈ Icc a b, HasDerivAt g (d y) y)
    (hc : c ∈ Icc a b) (he : f c = g c) : EqOn f g (Icc a b) := by
  have hconst := constant_of_has_deriv_right_zero (hf.sub hg)
    (fun y hy => (by simpa only [sub_self] using
      ((hdf y (Ico_subset_Icc_self hy)).sub
        (hdg y (Ico_subset_Icc_self hy))).hasDerivWithinAt))
  intro y hy
  have hh := (hconst y hy).trans (hconst c hc).symm
  change f y-g y=f c-g c at hh
  simpa only [he, sub_self, sub_eq_zero] using hh

end QuinticLienard.PartialCalculus

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScalarArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open scoped Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff

namespace QuinticLienard.ScalarArcs

theorem bounded_profile_solution (φ : ℝ → ℝ) {K B : ℝ≥0}
    (hK : LipschitzWith K φ) (hB : ∀ x, |φ x| ≤ B) (c x₀ : ℝ) :
    ∃ u : ℝ → ℝ, u c = x₀ ∧ ∀ y, HasDerivAt u (φ (u y)-y) y := by
  have hshift (s : ℝ) : LipschitzWith K (fun x => φ x-s) :=
    LipschitzWith.of_dist_le_mul (fun x y => by simpa using hK.dist_le_mul x y)
  have hex (N : ℕ) : ∃ u : ℝ → ℝ, u 0 = x₀ ∧
      ∀ s, |s| < (N:ℝ)+1 → HasDerivAt u (φ (u s)-(s+c)) s := by
    let T : ℝ := (N:ℝ)+1
    let L : ℝ≥0 := B+(N+1)+‖c‖₊
    have hT : 0 < T := by dsimp [T]; positivity
    let t₀ : Icc (-T) T := ⟨0,by constructor <;> linarith⟩
    have hpl : IsPicardLindelof (fun s x : ℝ => φ x-(s+c)) t₀ x₀
        (L*(N+1)) 0 L K := by
      constructor
      · exact fun s _ => (hshift (s+c)).lipschitzOnWith
      · exact fun x _ => (continuous_const.sub (continuous_id.add continuous_const)).continuousOn
      · intro s hs x _
        have hab : |s| ≤ (N:ℝ)+1 := abs_le.mpr hs
        calc
          ‖φ x - (s+c)‖ = |φ x-(s+c)| := Real.norm_eq_abs _
          _ ≤ |φ x|+|s+c| := abs_sub _ _
          _ ≤ B + (|s|+|c|) := add_le_add (hB x) (abs_add_le _ _)
          _ ≤ L := by dsimp [L]; simp only [NNReal.coe_natCast]; linarith
      · simp [t₀,T,mul_add]
    obtain ⟨u,hu,hdu⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨u,hu,fun s hs => (hdu s (Ioo_subset_Icc_self (abs_lt.mp hs))).hasDerivAt
      (Icc_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2)⟩
  choose u hu hdu using hex
  have heq (N M : ℕ) {s : ℝ} (hN : |s| < (N:ℝ)+1) (hM : |s| < (M:ℝ)+1) :
      u N s = u M s := by
    let R : ℝ := min ((N:ℝ)+1) ((M:ℝ)+1)
    have hR : 0 < R := lt_min (by positivity) (by positivity)
    exact ODE_solution_unique_of_mem_Ioo
      (v := fun s x => φ x-(s+c)) (s := fun _ => Set.univ)
      (fun t _ => (hshift (t+c)).lipschitzOnWith)
      (show (0:ℝ) ∈ Ioo (-R) R by constructor <;> linarith)
      (fun t ht => ⟨hdu N t ((abs_lt.mpr ht).trans_le (min_le_left _ _)), mem_univ _⟩)
      (fun t ht => ⟨hdu M t ((abs_lt.mpr ht).trans_le (min_le_right _ _)), mem_univ _⟩)
      (by rw [hu N,hu M]) (abs_lt.mp (lt_min hN hM))
  let U : ℝ → ℝ := fun s => u ⌈|s|⌉₊ s
  have hp (N : ℕ) {s : ℝ} (hs : |s| < (N:ℝ)+1) : U s = u N s :=
    heq _ N ((Nat.le_ceil _).trans_lt (by linarith)) hs
  have hU (s : ℝ) : HasDerivAt U (φ (U s)-(s+c)) s := by
    let N := ⌈|s|⌉₊
    have hs : |s| < (N:ℝ)+1 := (Nat.le_ceil _).trans_lt (by linarith)
    have hevent : U =ᶠ[𝓝 s] u N := by
      filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2] with t ht
      exact hp N (abs_lt.mpr ht)
    rw [hp N hs]
    exact (hdu N s hs).congr_of_eventuallyEq hevent
  refine ⟨fun y => U (y-c),by simp [U,hu],fun y => ?_⟩
  simpa [Function.comp_def] using (hU (y-c)).comp y ((hasDerivAt_id y).sub_const c)

lemma weighted_strictAnti {f a : ℝ → ℝ} (ha : Continuous a) (c : ℝ)
    (hf : ∀ y, HasDerivAt f (a y * f y-1) y) :
    StrictAnti (fun y => Real.exp (-(∫ s in c..y, a s)) * f y) := by
  have hd (y : ℝ) : HasDerivAt (fun y => Real.exp (-(∫ s in c..y, a s)) * f y)
      (-Real.exp (-(∫ s in c..y, a s))) y := by
    have hd := (((ha.integral_hasStrictDerivAt c y).hasDerivAt.neg.exp).mul (hf y))
    exact hd.congr_deriv (by first | rfl | (simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply]; ring1) | ring1 | (dsimp; ring1))
  apply strictAnti_of_deriv_neg
  intro y
  rw [(hd y).deriv]
  exact neg_neg_of_pos (Real.exp_pos _)

theorem derivative_signs {φ u : ℝ → ℝ} {t : ℝ}
    (hφ : ContDiff ℝ 1 φ)
    (hu : ∀ y, HasDerivAt u (φ (u y)-y) y) (hpeak : u (φ t) = t) :
    (∀ y < φ t, 0 < φ (u y)-y) ∧ (∀ y > φ t, φ (u y)-y < 0) := by
  let a : ℝ → ℝ := fun y => deriv φ (u y)
  let f : ℝ → ℝ := fun y => φ (u y)-y
  have huc : Continuous u := continuous_iff_continuousAt.mpr (fun y => (hu y).continuousAt)
  have ha : Continuous a := (hφ.continuous_deriv (by norm_num)).comp huc
  have hf (y : ℝ) : HasDerivAt f (a y*f y-1) y :=
    (((hφ.differentiable (by norm_num) (u y)).hasDerivAt).comp y (hu y)).sub (hasDerivAt_id y)
  have hanti := weighted_strictAnti ha (φ t) hf
  have hf0 : f (φ t) = 0 := by simp [f,hpeak]
  constructor
  · intro y hy
    have hh := hanti hy
    dsimp only at hh
    rw [hf0,mul_zero] at hh
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hh
  · intro y hy
    have hh := hanti hy
    dsimp only at hh
    rw [hf0,mul_zero] at hh
    exact neg_of_mul_neg_right hh (le_of_lt (Real.exp_pos _))

lemma branch_monotonicity {φ u : ℝ → ℝ} {t : ℝ}
    (hφ : ContDiff ℝ 1 φ)
    (hu : ∀ y, HasDerivAt u (φ (u y)-y) y) (hpeak : u (φ t) = t) :
    StrictMonoOn u (Iic (φ t)) ∧ StrictAntiOn u (Ici (φ t)) := by
  have hc : Continuous u := continuous_iff_continuousAt.mpr (fun y => (hu y).continuousAt)
  have hs := derivative_signs hφ hu hpeak
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Iic _) hc.continuousOn
    intro y hy
    rw [(hu y).deriv]
    exact hs.1 y (by simpa using hy)
  · apply strictAntiOn_of_deriv_neg (convex_Ici _) hc.continuousOn
    intro y hy
    rw [(hu y).deriv]
    exact hs.2 y (by simpa using hy)

theorem endpoints {φ u : ℝ → ℝ} {t h B : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hB : ∀ x, |φ x| ≤ B)
    (hu : ∀ y, HasDerivAt u (φ (u y)-y) y) (hpeak : u (φ t) = t)
    (hht : h < t) :
    ∃ a b : ℝ, a < φ t ∧ φ t < b ∧ u a = h ∧ u b = h ∧
      a < φ h ∧ φ h < b ∧
      (∀ y, u y = h → y = a ∨ y = b) ∧
      (∀ y ∈ Icc a b, h ≤ u y ∧ u y ≤ t) := by
  have hc : Continuous u := continuous_iff_continuousAt.mpr (fun y => (hu y).continuousAt)
  have hd : Differentiable ℝ u := fun y => (hu y).differentiableAt
  have hs := derivative_signs hφ hu hpeak
  have hm := branch_monotonicity hφ hu hpeak
  let l := min (φ t) (-B-1)
  let r := max (φ t) (B+1)
  let A := l-(|u l-h|+1)
  let C := r+(|u r-h|+1)
  have hAl : A < l := by dsimp [A]; linarith [abs_nonneg (u l-h)]
  have hrC : r < C := by dsimp [C]; linarith [abs_nonneg (u r-h)]
  have hlc : l ≤ φ t := min_le_left _ _
  have hcr : φ t ≤ r := le_max_left _ _
  have huA : u A < h := by
    have hi := (convex_Iic l).mul_sub_le_image_sub_of_le_deriv hc.continuousOn
      hd.differentiableOn (C := 1) (fun y hy => by
        rw [(hu y).deriv]
        have hy' : y < l := by simpa using hy
        have hp := (abs_le.mp (hB (u y))).1
        have hl : l ≤ -B-1 := min_le_right _ _
        linarith) A hAl.le l (show l ∈ Iic l from le_refl l) hAl.le
    dsimp [A] at hi
    linarith [le_abs_self (u l-h)]
  have huC : u C < h := by
    have hi := (convex_Ici r).image_sub_le_mul_sub_of_deriv_le hc.continuousOn
      hd.differentiableOn (C := -1) (fun y hy => by
        rw [(hu y).deriv]
        have hy' : r < y := by simpa using hy
        have hp := (abs_le.mp (hB (u y))).2
        have hr : B+1 ≤ r := le_max_right _ _
        linarith) r (show r ∈ Ici r from le_refl r) C hrC.le hrC.le
    dsimp [C] at hi
    linarith [le_abs_self (u r-h)]
  obtain ⟨a,ha,hua⟩ := intermediate_value_Icc (hAl.le.trans hlc) hc.continuousOn
    (show h ∈ Icc (u A) (u (φ t)) by rw [hpeak]; exact ⟨huA.le,hht.le⟩)
  obtain ⟨b,hb,hub⟩ := intermediate_value_Icc' (hcr.trans hrC.le) hc.continuousOn
    (show h ∈ Icc (u C) (u (φ t)) by rw [hpeak]; exact ⟨huC.le,hht.le⟩)
  have hac : a < φ t := lt_of_le_of_ne ha.2 (by intro he; rw [he,hpeak] at hua; linarith)
  have hcb : φ t < b := lt_of_le_of_ne hb.1 (by intro he; rw [←he,hpeak] at hub; linarith)
  have hsa := hs.1 a hac
  have hsb := hs.2 b hcb
  rw [hua] at hsa
  rw [hub] at hsb
  refine ⟨a,b,hac,hcb,hua,hub,by linarith,by linarith,?_,?_⟩
  · intro y hy
    rcases le_total y (φ t) with hyl | hyr
    · exact Or.inl (hm.1.injOn hyl hac.le (hy.trans hua.symm))
    · exact Or.inr (hm.2.injOn hyr hcb.le (hy.trans hub.symm))
  · intro y hy
    rcases le_total y (φ t) with hyl | hyr
    · exact ⟨hua ▸ hm.1.monotoneOn hac.le hyl hy.1,
        hpeak ▸ hm.1.monotoneOn hyl (show φ t ∈ Iic (φ t) from le_refl (φ t)) hyl⟩
    · exact ⟨hub ▸ hm.2.antitoneOn hyr hcb.le hy.2,
        hpeak ▸ hm.2.antitoneOn (show φ t ∈ Ici (φ t) from le_refl (φ t)) hyr hyr⟩

theorem positive_profile_extension {φ : ℝ → ℝ} {h t : ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (hh : 0 < h) (hht : h < t) :
    ∃ (ψ : ℝ → ℝ) (K B : ℝ≥0), ContDiff ℝ 1 ψ ∧ LipschitzWith K ψ ∧
      (∀ x, |ψ x| ≤ B) ∧ EqOn ψ φ (Icc h t) := by
  let b : ContDiffBump t := ⟨t-h,t-h/2,by linarith,by linarith⟩
  let ψ : ℝ → ℝ := fun x => b x*φ x
  have hd : ContDiff ℝ 1 ψ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : 0 < x
    · exact b.contDiff.contDiffAt.mul (hφ.contDiffAt (isOpen_Ioi.mem_nhds hx))
    · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (show x < h/2 by linarith)] with y hy
      change y < h/2 at hy
      have hb : b y = 0 := by
        apply b.zero_of_le_dist
        dsimp [b]
        rw [Real.dist_eq]
        have ha := le_abs_self (y-t)
        have haa := neg_le_abs (y-t)
        linarith
      simp [ψ,hb]
  have hs : HasCompactSupport ψ := b.hasCompactSupport.mul_right
  obtain ⟨K,hK⟩ := hd.lipschitzWith_of_hasCompactSupport hs (by norm_num)
  obtain ⟨B,hB⟩ := hs.exists_bound_of_continuous hd.continuous
  refine ⟨ψ,K,⟨max B 0,le_max_right _ _⟩,hd,hK,fun x => ?_,?_⟩
  · exact (show |ψ x| ≤ B by simpa [Real.norm_eq_abs] using hB x).trans (le_max_left _ _)
  · intro x hx
    have hb : b x = 1 := b.one_of_mem_closedBall (by
      change dist x t ≤ t-h
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hx.2)]
      linarith [hx.1])
    simp [ψ,hb]

lemma arch_of_extension {φ ψ : ℝ → ℝ} {h t : ℝ} {K B : ℝ≥0}
    (hs : ContDiff ℝ 1 ψ) (hK : LipschitzWith K ψ) (hB : ∀ x, |ψ x| ≤ B)
    (he : EqOn ψ φ (Icc h t)) (hht : h < t) :
    ∃ u a b, IsArch φ u h t a b := by
  have het : ψ t = φ t := he ⟨hht.le,le_rfl⟩
  have heh : ψ h = φ h := he ⟨le_rfl,hht.le⟩
  obtain ⟨u,hup,hdu⟩ := bounded_profile_solution ψ hK hB (ψ t) t
  obtain ⟨a,b,hap,hpb,hua,hub,hat,htb,_,hrange⟩ := endpoints hs hB hdu hup hht
  have hm := branch_monotonicity hs hdu hup
  refine ⟨u,a,b,?_⟩
  constructor
  · exact continuous_iff_continuousAt.mpr (fun y => (hdu y).continuousAt)
  · simpa [het] using hap
  · simpa [het] using hpb
  · simpa [het] using hup
  · exact hua
  · exact hub
  · simpa [heh] using hat
  · simpa [heh] using htb
  · intro y hy
    rw [←he (hrange y hy)]
    exact hdu y
  · exact hrange
  · intro x hx y hy hxy
    exact hm.1 (by simpa [het] using hx.2) (by simpa [het] using hy.2) hxy
  · intro x hx y hy hxy
    exact hm.2 (by simpa [het] using hx.1) (by simpa [het] using hy.1) hxy

theorem positive_arch_exists {φ : ℝ → ℝ} {h t : ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (hh : 0 < h) (hht : h < t) :
    ∃ u a b, IsArch φ u h t a b := by
  obtain ⟨ψ,K,B,hs,hK,hB,he⟩ := positive_profile_extension hφ hh hht
  exact arch_of_extension hs hK hB he hht

theorem IsArch.unique {φ ψ u v : ℝ → ℝ} {h t a b c d : ℝ} {K : ℝ≥0}
    (hu : IsArch φ u h t a b) (hv : IsArch φ v h t c d)
    (hK : LipschitzWith K ψ) (he : EqOn ψ φ (Icc h t)) :
    a = c ∧ b = d ∧ EqOn u v (Icc a b) := by
  have hp : φ t ∈ Ioo (max a c) (min b d) :=
    ⟨max_lt hu.lower_lt_peak hv.lower_lt_peak,
      lt_min hu.peak_lt_upper hv.peak_lt_upper⟩
  have hsubu : Icc (max a c) (min b d) ⊆ Icc a b :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsubv : Icc (max a c) (min b d) ⊆ Icc c d :=
    Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
  have hcommon : EqOn u v (Icc (max a c) (min b d)) := by
    apply ODE_solution_unique_of_mem_Icc
      (v := fun y x => ψ x-y) (s := fun _ => Set.univ) (K := K)
      (fun y _ => (show LipschitzWith K (fun x => ψ x-y) from by
        exact LipschitzWith.of_dist_le_mul (fun x z => by simpa using hK.dist_le_mul x z)).lipschitzOnWith) hp
      hu.continuous.continuousOn _ (fun _ _ => mem_univ _)
      hv.continuous.continuousOn _ (fun _ _ => mem_univ _)
      (hu.peak.trans hv.peak.symm)
    · intro y hy
      have hy' := hsubu (Ioo_subset_Icc_self hy)
      rw [he (hu.range_mem y hy')]
      exact hu.equation y hy'
    · intro y hy
      have hy' := hsubv (Ioo_subset_Icc_self hy)
      rw [he (hv.range_mem y hy')]
      exact hv.equation y hy'
  have hac : a = c := by
    rcases lt_trichotomy a c with hac | hac | hca
    · have heq := hcommon (show c ∈ Icc (max a c) (min b d) from
        ⟨by simp [max_eq_right hac.le],
          le_min (hv.lower_lt_peak.trans hu.peak_lt_upper).le
            (hv.lower_lt_peak.trans hv.peak_lt_upper).le⟩)
      have hh := hu.inc ⟨le_rfl,hu.lower_lt_peak.le⟩
        ⟨hac.le,hv.lower_lt_peak.le⟩ hac
      rw [hu.lower,heq,hv.lower] at hh
      exact False.elim (lt_irrefl _ hh)
    · exact hac
    · have heq := hcommon (show a ∈ Icc (max a c) (min b d) from
        ⟨by simp [max_eq_left hca.le],
          le_min (hu.lower_lt_peak.trans hu.peak_lt_upper).le
            (hu.lower_lt_peak.trans hv.peak_lt_upper).le⟩)
      have hh := hv.inc ⟨le_rfl,hv.lower_lt_peak.le⟩
        ⟨hca.le,hu.lower_lt_peak.le⟩ hca
      rw [hv.lower,←heq,hu.lower] at hh
      exact False.elim (lt_irrefl _ hh)
  have hbd : b = d := by
    rcases lt_trichotomy b d with hbd | hbd | hdb
    · have heq := hcommon (show b ∈ Icc (max a c) (min b d) from
        ⟨max_le (hu.lower_lt_peak.trans hu.peak_lt_upper).le
          (hv.lower_lt_peak.trans hu.peak_lt_upper).le,
          by simp [min_eq_left hbd.le]⟩)
      have hh := hv.dec ⟨hu.peak_lt_upper.le,hbd.le⟩
        ⟨hv.peak_lt_upper.le,le_rfl⟩ hbd
      rw [hv.upper,←heq,hu.upper] at hh
      exact False.elim (lt_irrefl _ hh)
    · exact hbd
    · have heq := hcommon (show d ∈ Icc (max a c) (min b d) from
        ⟨max_le (hu.lower_lt_peak.trans hv.peak_lt_upper).le
          (hv.lower_lt_peak.trans hv.peak_lt_upper).le,
          by simp [min_eq_right hdb.le]⟩)
      have hh := hu.dec ⟨hv.peak_lt_upper.le,hdb.le⟩
        ⟨hu.peak_lt_upper.le,le_rfl⟩ hdb
      rw [hu.upper,heq,hv.upper] at hh
      exact False.elim (lt_irrefl _ hh)
  refine ⟨hac,hbd,?_⟩
  simpa [←hac,←hbd] using hcommon

theorem chosen_arch {φ : ℝ → ℝ} {h t : ℝ}
    (hex : ∃ u a b, IsArch φ u h t a b) :
    IsArch φ (archFunction φ h t) h t (lower φ h t) (upper φ h t) := by
  obtain ⟨u,a,b,hu⟩ := hex
  exact Classical.epsilon_spec (show ∃ p : (ℝ → ℝ) × ℝ × ℝ,
    IsArch φ p.1 h t p.2.1 p.2.2 from ⟨(u,a,b),hu⟩)

theorem midpoint_abs_lt_width {φ : ℝ → ℝ} {h t : ℝ}
    (hex : ∃ u a b, IsArch φ u h t a b) :
    |midpoint φ h t| < width φ h t := by
  have hu := chosen_arch hex
  rw [abs_lt]
  dsimp [midpoint,width]
  constructor <;> linarith [hu.lower_transverse,hu.upper_transverse]

lemma derivative_signs_on_Icc {φ u : ℝ → ℝ} {a b t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : Continuous u)
    (hu : ∀ y ∈ Icc a b, HasDerivAt u (φ (u y)-y) y)
    (hpeak : u (φ t) = t) (hp : φ t ∈ Icc a b) :
    (∀ y ∈ Icc a b, y < φ t → 0 < φ (u y)-y) ∧
    (∀ y ∈ Icc a b, φ t < y → φ (u y)-y < 0) := by
  let A : ℝ → ℝ := fun y => deriv φ (u y)
  let f : ℝ → ℝ := fun y => φ (u y)-y
  have hA : Continuous A := (hφ.continuous_deriv (by norm_num)).comp hc
  have hf : Continuous f := (hφ.continuous.comp hc).sub continuous_id
  have hfd (y : ℝ) (hy : y ∈ Icc a b) : HasDerivAt f (A y*f y-1) y :=
    (((hφ.differentiable (by norm_num) (u y)).hasDerivAt).comp y (hu y hy)).sub
      (hasDerivAt_id y)
  let K : ℝ → ℝ := fun y => Real.exp (-(∫ s in φ t..y, A s))
  have hKd (y : ℝ) : HasDerivAt K (-A y*K y) y := by
    exact (hA.integral_hasStrictDerivAt (φ t) y).hasDerivAt.neg.exp.congr_deriv
      (by first | rfl | (dsimp [K]; ring) | (simp [K]; ring))
  have hK : Continuous K := continuous_iff_continuousAt.mpr (fun y => (hKd y).continuousAt)
  have hd (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivAt (fun z => K z*f z) (-K y) y := by
    exact ((hKd y).mul (hfd y hy)).congr_deriv (by first | rfl | ring | (simp; ring))
  have hanti : StrictAntiOn (fun y => K y*f y) (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hK.mul hf).continuousOn
    intro y hy
    have hy' : y ∈ Icc a b := interior_subset hy
    change deriv (fun z => K z*f z) y < 0
    rw [(hd y hy').deriv]
    exact neg_neg_of_pos (Real.exp_pos _)
  have hf0 : f (φ t) = 0 := by simp [f,hpeak]
  constructor
  · intro y hy hyt
    have hh := hanti hy hp hyt
    dsimp only at hh
    rw [hf0,mul_zero] at hh
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hh
  · intro y hy hty
    have hh := hanti hp hy hty
    dsimp only at hh
    rw [hf0,mul_zero] at hh
    exact neg_of_mul_neg_right hh (le_of_lt (Real.exp_pos _))

theorem IsArch.of_solution_and_hits {φ u : ℝ → ℝ} {a b h t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : Continuous u)
    (hu : ∀ y ∈ Icc a b, HasDerivAt u (φ (u y)-y) y)
    (ha : a < φ t) (hb : φ t < b) (hpeak : u (φ t) = t)
    (hl : u a = h) (hr : u b = h) : IsArch φ u h t a b := by
  have hp : φ t ∈ Icc a b := ⟨ha.le,hb.le⟩
  have hs := derivative_signs_on_Icc hφ hc hu hpeak hp
  have hi : StrictMonoOn u (Icc a (φ t)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc.continuousOn
    intro y hy
    have hy' : y ∈ Ioo a (φ t) := by simpa only [interior_Icc] using hy
    have hyab : y ∈ Icc a b := ⟨hy'.1.le,hy'.2.le.trans hb.le⟩
    rw [(hu y hyab).deriv]
    exact hs.1 y hyab hy'.2
  have hd : StrictAntiOn u (Icc (φ t) b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc.continuousOn
    intro y hy
    have hy' : y ∈ Ioo (φ t) b := by simpa only [interior_Icc] using hy
    have hyab : y ∈ Icc a b := ⟨ha.le.trans hy'.1.le,hy'.2.le⟩
    rw [(hu y hyab).deriv]
    exact hs.2 y hyab hy'.1
  refine ⟨hc,ha,hb,hpeak,hl,hr,?_,?_,hu,?_,hi,hd⟩
  · have hh := hs.1 a ⟨le_rfl,(ha.trans hb).le⟩ ha
    rw [hl] at hh
    linarith
  · have hh := hs.2 b ⟨(ha.trans hb).le,le_rfl⟩ hb
    rw [hr] at hh
    linarith
  · intro y hy
    rcases le_total y (φ t) with hyl | hyr
    · exact ⟨hl ▸ hi.monotoneOn ⟨le_rfl,ha.le⟩ ⟨hy.1,hyl⟩ hy.1,
        hpeak ▸ hi.monotoneOn ⟨hy.1,hyl⟩ ⟨ha.le,le_rfl⟩ hyl⟩
    · exact ⟨hr ▸ hd.antitoneOn ⟨hyr,hy.2⟩ ⟨hb.le,le_rfl⟩ hy.2,
        hpeak ▸ hd.antitoneOn ⟨le_rfl,hb.le⟩ ⟨hyr,hy.2⟩ hyr⟩

theorem IsArch.subarch {φ u : ℝ → ℝ} {h₀ h t a₀ b₀ : ℝ}
    (hu : IsArch φ u h₀ t a₀ b₀) (hφ : ContDiff ℝ 1 φ)
    (hh : h₀ < h) (ht : h < t) :
    ∃ a b, a₀ < a ∧ b < b₀ ∧ IsArch φ u h t a b := by
  obtain ⟨a,ha,hua⟩ := intermediate_value_Icc hu.lower_lt_peak.le
    hu.continuous.continuousOn (show h ∈ Icc (u a₀) (u (φ t)) by
      rw [hu.lower,hu.peak]; exact ⟨hh.le,ht.le⟩)
  obtain ⟨b,hb,hub⟩ := intermediate_value_Icc' hu.peak_lt_upper.le
    hu.continuous.continuousOn (show h ∈ Icc (u b₀) (u (φ t)) by
      rw [hu.upper,hu.peak]; exact ⟨hh.le,ht.le⟩)
  have ha₀ : a₀ < a := lt_of_le_of_ne ha.1 (by
    intro he; rw [←he,hu.lower] at hua; exact hh.ne hua)
  have hat : a < φ t := lt_of_le_of_ne ha.2 (by
    intro he; rw [he,hu.peak] at hua; exact ht.ne hua.symm)
  have htb : φ t < b := lt_of_le_of_ne hb.1 (by
    intro he; rw [←he,hu.peak] at hub; exact ht.ne hub.symm)
  have hb₀ : b < b₀ := lt_of_le_of_ne hb.2 (by
    intro he; rw [he,hu.upper] at hub; exact hh.ne hub)
  refine ⟨a,b,ha₀,hb₀,IsArch.of_solution_and_hits hφ hu.continuous ?_
    hat htb hu.peak hua hub⟩
  intro y hy
  exact hu.equation y ⟨ha.1.trans hy.1,hy.2.trans hb.2⟩

end QuinticLienard.ScalarArcs

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ArcFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff

open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ArcFamilies
open PartialCalculus

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

theorem peak_family (Φ : P × ℝ → ℝ) {U : Set (State P)}
    (hU : IsOpen U) (hV : ContDiffOn ℝ 1 (field Φ) U)
    (hloc : ∀ x ∈ U, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t a b : ℝ} {u : ℝ → ℝ}
    (hΦ : ContDiffAt ℝ ω Φ (p,t))
    (ha : a < Φ (p,t)) (hb : Φ (p,t) < b)
    (hu : Continuous u) (hpeak : u (Φ (p,t)) = t)
    (hueq : ∀ y ∈ Icc a b, HasDerivAt u (Φ (p,u y)-y) y)
    (huU : ∀ y ∈ Icc a b, (p,(u y,y)) ∈ U) :
    ∃ w : (P × ℝ) × ℝ → ℝ,
      (∀ q, Continuous (fun y => w (q,y))) ∧
      (∀ q, w (q,Φ q) = q.2) ∧
      (∀ y ∈ Icc a b, w ((p,t),y) = u y) ∧
      (∀ y ∈ Icc a b, ContDiffAt ℝ ω w ((p,t),y)) ∧
      ∀ y ∈ Ioo a b, ∀ᶠ q in 𝓝 ((p,t),y),
        HasDerivAt (fun s => w (q.1,s)) (Φ (q.1.1,w q)-q.2) q.2 := by
  let c := Φ (p,t)
  let γ : ℝ → State P := fun y => (p,(u y,y))
  have hγ : Continuous γ := continuous_const.prodMk (hu.prodMk continuous_id)
  have hγd : ∀ y ∈ Icc a b, HasDerivAt γ (field Φ (γ y)) y := by
    intro y hy
    exact (hasDerivAt_const y p).prodMk ((hueq y hy).prodMk (hasDerivAt_id y))
  obtain ⟨f,hfc,hzero,hmatch,hd,he⟩ := GlobalODE.analytic_family_along_compact_solution
    (field Φ) hU hV hloc ha hb hγ huU hγd
  have hinit : γ c = (p,(t,c)) := by simp [γ,c,hpeak]
  have hode : ∀ᶠ x in 𝓝 (γ c), ∀ s ∈ Icc (a-c) (b-c),
      HasDerivAt (fun z => f (x,z)) (field Φ (f (x,s))) s := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have hs' : s+c ∈ Icc a b := by constructor <;> linarith [hs.1,hs.2]
    have hx := he (s+c) hs'
    simpa only [c,add_sub_cancel_right] using hx
  have hcoord : ∀ᶠ x in 𝓝 (γ c), ∀ s ∈ Icc (a-c) (b-c),
      (f (x,s)).1 = x.1 ∧ (f (x,s)).2.2 = x.2.2+s := by
    filter_upwards [hode] with x hx
    have h0 : (0:ℝ) ∈ Icc (a-c) (b-c) := by
      constructor <;> dsimp [c] <;> linarith
    have hpd : ∀ s ∈ Icc (a-c) (b-c), HasDerivAt (fun z => (f (x,z)).1) 0 s :=
      fun s hs => (hx s hs).fst
    have htd : ∀ s ∈ Icc (a-c) (b-c), HasDerivAt (fun z => (f (x,z)).2.2) 1 s :=
      fun s hs => (hx s hs).snd.snd
    have hpconst := eq_of_hasDerivAt_eq_on_Icc
      (fun s hs => (hpd s hs).continuousAt.continuousWithinAt)
      continuousOn_const hpd (fun s _ => hasDerivAt_const s x.1) h0
      (by simp only [hzero])
    have htconst := eq_of_hasDerivAt_eq_on_Icc
      (fun s hs => (htd s hs).continuousAt.continuousWithinAt)
      (continuous_const.add continuous_id).continuousOn htd
      (fun s _ => (hasDerivAt_id s).const_add x.2.2) h0
      (by simp [hzero])
    exact fun s hs => ⟨hpconst hs,htconst hs⟩
  let init : P × ℝ → State P := fun q => (q.1,(q.2,Φ q))
  let lift : (P × ℝ) × ℝ → State P × ℝ := fun q => (init q.1,q.2-Φ q.1)
  let w : (P × ℝ) × ℝ → ℝ := fun q => (f (lift q)).2.1
  have hlift (y : ℝ) : lift ((p,t),y) = (γ c,y-c) := by
    simp [lift,init,hinit,c]
  have hld (y : ℝ) : ContDiffAt ℝ ω lift ((p,t),y) := by
    have hp := hΦ.comp ((p,t),y) contDiffAt_fst
    exact (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk hp)).prodMk
      (contDiffAt_snd.sub hp)
  refine ⟨w,?_,?_,?_,?_,?_⟩
  · intro q
    change Continuous (fun y => (f (init q,y-Φ q)).2.1)
    exact (hfc.comp (continuous_const.prodMk (continuous_id.sub continuous_const))).snd.fst
  · intro q
    simp [w,lift,init,hzero]
  · intro y hy
    change (f (lift ((p,t),y))).2.1 = u y
    rw [hlift y,hmatch y hy]
  · intro y hy
    have hf := hd y hy
    rw [←hlift y] at hf
    exact (hf.comp ((p,t),y) (hld y)).snd.fst
  · intro y hy
    have ho : ∀ᶠ q in 𝓝 ((p,t),y),
        HasDerivAt (fun s => f ((lift q).1,s)) (field Φ (f (lift q))) (lift q).2 := by
      have hc := (hld y).continuousAt.tendsto
      rw [hlift y] at hc
      exact hc.eventually (he y (Ioo_subset_Icc_self hy))
    have hi : Tendsto (fun q : (P × ℝ) × ℝ => init q.1)
        (𝓝 ((p,t),y)) (𝓝 (γ c)) := by
      have hc := (hld y).fst.continuousAt.tendsto
      simpa only [hlift y] using hc
    have ht : ∀ᶠ q in 𝓝 ((p,t),y), (lift q).2 ∈ Icc (a-c) (b-c) := by
      have hc := (hld y).snd.continuousAt.tendsto
      have hyt : y-c ∈ Ioo (a-c) (b-c) := by constructor <;> linarith [hy.1,hy.2]
      rw [hlift y] at hc
      exact hc.eventually (mem_of_superset (Ioo_mem_nhds hyt.1 hyt.2) Ioo_subset_Icc_self)
    filter_upwards [ho,hi.eventually hcoord,ht] with q hq hqcoord hqt
    have hcoords := hqcoord _ hqt
    have hdq0 : HasDerivAt (fun s => (f ((lift q).1,s)).2.1)
        (Φ ((f (lift q)).1,(f (lift q)).2.1)-(f (lift q)).2.2) (lift q).2 := hq.snd.fst
    have hdq := hdq0.scomp q.2 ((hasDerivAt_id q.2).sub_const (Φ q.1))
    have hp : (f (lift q)).1 = q.1.1 := hcoords.1
    have ht : (f (lift q)).2.2 = q.2 := by
      calc
        (f (lift q)).2.2 = (init q.1).2.2+(lift q).2 := hcoords.2
        _ = q.2 := by simp [lift,init]
    simpa only [Function.comp_def,id_eq,smul_eq_mul,one_mul,hp,ht] using hdq

end QuinticLienard.ArcFamilies

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ArcEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ArcEndpoints
open PartialCalculus ScalarArcs

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma level_hit {w : P × ℝ → ℝ} {p : P} {y h d : ℝ}
    (hw : ContDiffAt ℝ ω w (p,y)) (hd : HasDerivAt (fun s => w (p,s)) d y)
    (hu : w (p,y) = h) (hne : d ≠ 0) :
    ∃ Y : P × ℝ → ℝ, ContDiffAt ℝ ω Y (p,h) ∧ Y (p,h) = y ∧
      ∀ᶠ q in 𝓝 (p,h), w (q.1,Y q) = q.2 := by
  let f : (P × ℝ) × ℝ → ℝ := fun q => w (q.1.1,q.2)-q.1.2
  have hf : ContDiffAt ℝ ω f ((p,h),y) :=
    (hw.comp ((p,h),y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub contDiffAt_fst.snd
  obtain ⟨Y,hY,hY0,he,_⟩ := transverse_hit hf (hd.sub_const h) hne
  refine ⟨Y,hY,hY0,?_⟩
  filter_upwards [he] with q hq
  change w (q.1,Y q)-q.2 = w (p,y)-h at hq
  rw [hu,sub_self,sub_eq_zero] at hq
  exact hq

end QuinticLienard.ArcEndpoints

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ArchVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ArchVariation
open PartialCalculus

lemma fixed_profile_variation {w : ℝ × ℝ → ℝ} {φ : ℝ → ℝ} {t y : ℝ}
    (hw : ContDiffAt ℝ ω w (t,y)) (hφ : DifferentiableAt ℝ φ (w (t,y)))
    (he : ∀ᶠ q in 𝓝 (t,y), HasDerivAt (fun s => w (q.1,s)) (φ (w q)-q.2) q.2) :
    HasDerivAt (fun s => first w (t,s)) (deriv φ (w (t,y))*first w (t,y)) y := by
  let Φ : ℝ × ℝ → ℝ := fun q => φ q.2
  have hd : DifferentiableAt ℝ Φ (t,w (t,y)) := hφ.comp (t,w (t,y)) differentiableAt_snd
  have h₁ : first Φ (t,w (t,y)) = 0 :=
    (first_hasDerivAt hd).unique (hasDerivAt_const t (φ (w (t,y))))
  have h₂ : second Φ (t,w (t,y)) = deriv φ (w (t,y)) :=
    (second_hasDerivAt hd).unique hφ.hasDerivAt
  simpa only [h₁,h₂,zero_add] using scalar_ode_variation hw hd he

lemma moving_peak_variation {w : ℝ × ℝ → ℝ} {φ : ℝ → ℝ} {t : ℝ}
    (hw : ContDiffAt ℝ ω w (t,φ t)) (hφ : DifferentiableAt ℝ φ t)
    (hp : ∀ᶠ s in 𝓝 t, w (s,φ s) = s)
    (he : HasDerivAt (fun y => w (t,y)) 0 (φ t)) : first w (t,φ t) = 1 := by
  have hs : second w (t,φ t) = 0 :=
    (second_hasDerivAt (hw.differentiableAt (by simp))).unique he
  have hd := (hw.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk hφ.hasDerivAt)
  have heq := hd.unique ((hasDerivAt_id t).congr_of_eventuallyEq hp)
  simpa only [fderiv_pair,hs,mul_zero,one_mul,add_zero] using heq

theorem positive_homogeneous {f a : ℝ → ℝ} {l r c : ℝ}
    (ha : Continuous a) (hf : ContinuousOn f (Icc l r))
    (hd : ∀ y ∈ Icc l r, HasDerivAt f (a y*f y) y)
    (hc : c ∈ Icc l r) (hinit : f c = 1) :
    ∀ y ∈ Icc l r, f y = Real.exp (∫ s in c..y, a s) := by
  let g : ℝ → ℝ := fun y => Real.exp (-(∫ s in c..y, a s))*f y
  have hg (y : ℝ) (hy : y ∈ Icc l r) : HasDerivAt g 0 y := by
    have hh := ((ha.integral_hasStrictDerivAt c y).hasDerivAt.neg.exp).mul (hd y hy)
    exact hh.congr_deriv (by first | rfl | (simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply]; ring1) | ring1 | (dsimp; ring1))
  have hgc : ContinuousOn g (Icc l r) :=
    ((continuous_iff_continuousAt.mpr (fun y =>
      ((ha.integral_hasStrictDerivAt c y).hasDerivAt.neg.exp).continuousAt)).continuousOn).mul hf
  have heq := eq_of_hasDerivAt_eq_on_Icc hgc continuousOn_const hg
    (fun y _ => hasDerivAt_const y (1:ℝ)) hc (by simp [g,hinit])
  intro y hy
  have h := heq hy
  change Real.exp (-(∫ s in c..y, a s))*f y=1 at h
  have he : Real.exp (∫ s in c..y, a s)*Real.exp (-(∫ s in c..y, a s))=1 := by
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  calc
    f y = (Real.exp (∫ s in c..y, a s)*Real.exp (-(∫ s in c..y, a s)))*f y := by rw [he,one_mul]
    _ = Real.exp (∫ s in c..y, a s) := by rw [mul_assoc,h,mul_one]

lemma hit_variation {w : ℝ × ℝ → ℝ} {Y h : ℝ → ℝ} {t d : ℝ}
    (hw : DifferentiableAt ℝ w (t,Y t)) (hY : DifferentiableAt ℝ Y t)
    (hh : HasDerivAt h d t) (he : ∀ᶠ s in 𝓝 t, w (s,Y s) = h s) :
    first w (t,Y t) + deriv Y t*second w (t,Y t) = d := by
  have hd := hw.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hY.hasDerivAt)
  have hq := hd.unique (hh.congr_of_eventuallyEq he)
  simpa only [fderiv_pair,one_mul] using hq

theorem endpoint_peak_signs {w : ℝ × ℝ → ℝ} {φ : ℝ → ℝ}
    {l r : ℝ → ℝ} {t h : ℝ}
    (hl : DifferentiableAt ℝ l t) (hr : DifferentiableAt ℝ r t)
    (hwl : DifferentiableAt ℝ w (t,l t)) (hwr : DifferentiableAt ℝ w (t,r t))
    (hel : ∀ᶠ s in 𝓝 t, w (s,l s) = h) (her : ∀ᶠ s in 𝓝 t, w (s,r s) = h)
    (hdl : HasDerivAt (fun y => w (t,y)) (φ h-l t) (l t))
    (hdr : HasDerivAt (fun y => w (t,y)) (φ h-r t) (r t))
    (hxl : 0 < first w (t,l t)) (hxr : 0 < first w (t,r t))
    (hlt : l t < φ h) (htr : φ h < r t) : deriv l t < 0 ∧ 0 < deriv r t := by
  have hlv := hit_variation hwl hl (hasDerivAt_const t h) hel
  have hrv := hit_variation hwr hr (hasDerivAt_const t h) her
  rw [(second_hasDerivAt hwl).unique hdl] at hlv
  rw [(second_hasDerivAt hwr).unique hdr] at hrv
  constructor
  · by_contra hn
    have hnon := mul_nonneg (le_of_not_gt hn) (sub_nonneg.mpr hlt.le)
    linarith
  · by_contra hn
    have hnon := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hn) (sub_nonpos.mpr htr.le)
    linarith

lemma width_midpoint_peak_bounds {l r : ℝ → ℝ} {t : ℝ}
    (hl : DifferentiableAt ℝ l t) (hr : DifferentiableAt ℝ r t)
    (hlneg : deriv l t < 0) (hrpos : 0 < deriv r t) :
    0 < deriv (fun s => (r s-l s)/2) t ∧
    |deriv (fun s => (r s+l s)/2) t / deriv (fun s => (r s-l s)/2) t| < 1 := by
  have hd₁ : HasDerivAt (fun s => (r s-l s)/2) ((deriv r t-deriv l t)/2) t :=
    (hr.hasDerivAt.sub hl.hasDerivAt).div_const 2
  have hd₂ : HasDerivAt (fun s => (r s+l s)/2) ((deriv r t+deriv l t)/2) t :=
    (hr.hasDerivAt.add hl.hasDerivAt).div_const 2
  rw [hd₁.deriv,hd₂.deriv]
  have hd : 0 < (deriv r t-deriv l t)/2 := by linarith
  refine ⟨hd,?_⟩
  rw [abs_lt]
  constructor
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_lt_iff₀ hd]; linarith

end QuinticLienard.ArchVariation

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.SqrtPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter Metric
open scoped Topology ContDiff
namespace QuinticLienard.SmoothFlow

lemma sqrtPath_analytic {c : ℝ} (hc : 0<c) :
    ContDiffAt ℝ ω sqrtPath (constCLM c) := by
  let b := Real.sqrt c
  have hb : 0<b := Real.sqrt_pos.mpr hc
  have hb2 : b^2=c := Real.sq_sqrt hc.le
  let Φ : Path ℝ × Path ℝ → Path ℝ := fun p => (1/(2*b)) • (p.2*p.2-p.1)
  have hΦ : ContDiffAt ℝ ω Φ (constCLM c,constCLM b) :=
    (contDiffAt_snd.mul contDiffAt_snd |>.sub contDiffAt_fst).const_smul _
  have hpartial : fderiv ℝ Φ (constCLM c,constCLM b) ∘L
      ContinuousLinearMap.inr ℝ (Path ℝ) (Path ℝ) = ContinuousLinearMap.id ℝ (Path ℝ) := by
    have hd := (hΦ.differentiableAt (by simp)).hasFDerivAt.comp (constCLM b)
      ((hasFDerivAt_const (constCLM c) (constCLM b)).prodMk (hasFDerivAt_id (constCLM b)))
    have he := (((hasFDerivAt_id (𝕜:=ℝ) (constCLM b)).mul (hasFDerivAt_id (𝕜:=ℝ) (constCLM b))).sub_const (constCLM c)).const_smul (1/(2*b))
    have heq := hd.unique he
    convert heq using 1
    · ext u t; simp
    · ext u t
      simp [smul_eq_mul]
      field_simp [ne_of_gt hb]
      ring
  have hinv : (fderiv ℝ Φ (constCLM c,constCLM b) ∘L
      ContinuousLinearMap.inr ℝ (Path ℝ) (Path ℝ)).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.refl ℝ _,rfl⟩
  let U := hΦ.implicitFunction (by simp) hinv
  have hU : ContDiffAt ℝ ω U (constCLM c) := hΦ.contDiffAt_implicitFunction (by simp) hinv
  have hU0 : U (constCLM c)=constCLM b := hΦ.implicitFunction_apply_self (by simp) hinv
  have hnear : ∀ᶠ v in 𝓝 (constCLM c), dist (U v) (constCLM b)<b := by
    have ht : Tendsto (fun v => dist (U v) (constCLM b)) (𝓝 (constCLM c)) (𝓝 0) := by
      simpa only [hU0,dist_self] using hU.continuousAt.dist (continuousAt_const (y:=constCLM b))
    exact ht.eventually (eventually_lt_nhds hb)
  apply hU.congr_of_eventuallyEq
  filter_upwards [hΦ.eventually_apply_implicitFunction (by simp) hinv,hnear] with v hv hn
  ext t
  have he := congrArg (fun w : Path ℝ => w t) hv
  change (1/(2*b))*(U v t*U v t-v t)=(1/(2*b))*(b*b-c) at he
  have hs : U v t*U v t=v t := by
    have hbne : 1/(2*b)≠0 := by positivity
    have hq := (mul_left_cancel₀ hbne) he
    nlinarith [hb2]
  have hdist := ContinuousMap.dist_apply_le_dist (f:=U v) (g:=constCLM b) t
  have hlt : |U v t-b|<b := by simpa only [Real.dist_eq,constCLM_apply] using hdist.trans_lt hn
  have hpos : 0≤U v t := by linarith [(abs_lt.mp hlt).1]
  change Real.sqrt (v t)=U v t
  rw [←hs,←pow_two,Real.sqrt_sq hpos]
end QuinticLienard.SmoothFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AlgebraicFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.SmoothFlow
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace AlgebraicExpr
lemma eval_analytic (p : AlgebraicExpr E) {x : E} (hp : p.RegularAt x) :
    ContDiffAt ℝ ω p.eval x := by
  induction p with
  | const c => exact contDiffAt_const
  | linear L => exact L.contDiff.contDiffAt
  | add p q ihp ihq => exact (ihp hp.1).add (ihq hp.2)
  | mul p q ihp ihq => exact (ihp hp.1).mul (ihq hp.2)
  | inv p ih => exact (ih hp.1).inv hp.2
  | sqrt p ih => exact (ih hp.1).sqrt (ne_of_gt hp.2)
lemma path_properties (p : AlgebraicExpr E) {x : E} (hp : p.RegularAt x) :
    p.onPaths (constCLM x)=constCLM (p.eval x) ∧
      ContDiffAt ℝ ω p.onPaths (constCLM x) ∧
      ∀ᶠ u in 𝓝 (constCLM x), ∀ s, p.onPaths u s=p.eval (u s) := by
  induction p with
  | const c => exact ⟨rfl,contDiffAt_const,Eventually.of_forall (fun _ _ => rfl)⟩
  | linear L => exact ⟨rfl,(pathMap L).contDiff.contDiffAt,Eventually.of_forall (fun _ _ => rfl)⟩
  | add p q ihp ihq =>
    obtain ⟨hp0,hpd,hpe⟩ := ihp hp.1
    obtain ⟨hq0,hqd,hqe⟩ := ihq hp.2
    refine ⟨?_,hpd.add hqd,?_⟩
    · simp only [onPaths,hp0,hq0]; ext s; rfl
    · filter_upwards [hpe,hqe] with u hu hv s
      exact congrArg₂ (·+·) (hu s) (hv s)
  | mul p q ihp ihq =>
    obtain ⟨hp0,hpd,hpe⟩ := ihp hp.1
    obtain ⟨hq0,hqd,hqe⟩ := ihq hp.2
    refine ⟨?_,hpd.mul hqd,?_⟩
    · simp only [onPaths,hp0,hq0]; ext s; rfl
    · filter_upwards [hpe,hqe] with u hu hv s
      exact congrArg₂ (·*·) (hu s) (hv s)
  | inv p ih =>
    obtain ⟨hp0,hpd,hpe⟩ := ih hp.1
    have hunit : IsUnit (p.onPaths (constCLM x)) := by
      rw [hp0]
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr (fun _ => hp.2)
    have hinv : ContDiffAt ℝ ω Ring.inverse (p.onPaths (constCLM x)) := by
      have hh := contDiffAt_ringInverse ℝ (n:=ω) hunit.unit
      rw [hunit.unit_spec] at hh
      exact hh
    refine ⟨?_,hinv.comp _ hpd,?_⟩
    · ext s
      rw [onPaths,RationalExpr.inverse_eval _ hunit,hp0]
      rfl
    · have hu : ∀ᶠ u in 𝓝 (constCLM x), IsUnit (p.onPaths u) :=
        hpd.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
      filter_upwards [hpe,hu] with u he hunit s
      rw [onPaths,RationalExpr.inverse_eval _ hunit,he s]
      rfl
  | sqrt p ih =>
    obtain ⟨hp0,hpd,hpe⟩ := ih hp.1
    refine ⟨?_,?_,?_⟩
    · simp only [onPaths,hp0,sqrtPath_const,eval]
    · apply (show ContDiffAt ℝ ω sqrtPath (p.onPaths (constCLM x)) by rw [hp0]; exact sqrtPath_analytic hp.2).comp _ hpd
    · filter_upwards [hpe] with u hu s
      exact congrArg Real.sqrt (hu s)
end AlgebraicExpr

open ArcFamilies
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

theorem algebraic_profile_flow (e : AlgebraicExpr (P × ℝ)) (x : State P)
    (he : e.RegularAt (x.1,x.2.1)) :
    ∃ f : State P × ℝ → State P, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ q in 𝓝 (x,(0:ℝ)), f (q.1,0)=q.1 ∧
        HasDerivAt (fun s => f (q.1,s)) (field e.eval (f q)) q.2 := by
  let L : State P →L[ℝ] P × ℝ :=
    (ContinuousLinearMap.fst ℝ P (ℝ×ℝ)).prod
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ P (ℝ×ℝ)))
  let Y : State P →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ P (ℝ×ℝ))
  let I : ℝ →L[ℝ] State P :=
    (ContinuousLinearMap.inr ℝ P (ℝ×ℝ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)
  let W : Path (State P) → Path (State P) := fun u =>
    constCLM (0,(0,1)) + pathMap I (e.onPaths (pathMap L u)-pathMap Y u)
  have hL : L x=(x.1,x.2.1) := rfl
  have hep := AlgebraicExpr.path_properties e he
  have hed : ContDiffAt ℝ ω e.onPaths (pathMap L (constCLM x)) := by
    simpa only [pathMap_const,hL] using hep.2.1
  have hW : ContDiffAt ℝ ω W (constCLM x) :=
    contDiffAt_const.add ((pathMap I).contDiff.contDiffAt.comp _
      ((hed.comp _ (pathMap L).contDiff.contDiffAt).sub (pathMap Y).contDiff.contDiffAt))
  apply exists_analytic_local_flow_eventually W (field e.eval) x _ hW
  have ht : Tendsto (pathMap L) (𝓝 (constCLM x)) (𝓝 (constCLM (x.1,x.2.1))) := by
    exact (pathMap L).continuous.continuousAt.tendsto
  filter_upwards [ht.eventually hep.2.2] with u hu s
  simp only [W,ContinuousMap.add_apply,pathMap_apply,ContinuousMap.sub_apply,hu s,constCLM_apply]
  simp [I,L,Y,field]
end QuinticLienard.SmoothFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AlgebraicNotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.SmoothFlow.AlgebraicExpr
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma regular_pow (p : AlgebraicExpr E) (n : ℕ) {x : E} (hp : p.RegularAt x) : (p^n).RegularAt x := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,hp⟩
end QuinticLienard.SmoothFlow.AlgebraicExpr

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScaledAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
open SmoothFlow SmoothFlow.AlgebraicExpr ArcFamilies
lemma X_pos {c : ℝ} (hc : 0<c) (q : Dom) : 0<(X c).eval q := by
  simp only [X,eval_sqrt,eval_mul,eval_add,eval_const,eval_pow,eval_A,eval_ρ]
  apply Real.sqrt_pos.mpr
  positivity
lemma Z_pos {c : ℝ} (hc : 0<c) {q : Dom} (hq : 0<q.2) : 0<(Z c).eval q := by
  simp only [Z,eval_sqrt,eval_mul,eval_add,eval_const,eval_pow,eval_A,eval_ρ,eval_s]
  apply Real.sqrt_pos.mpr
  positivity
lemma X_regular {c : ℝ} (hc : 0<c) (q : Dom) : (X c).RegularAt q := by
  simp only [X,regular_sqrt,regular_mul,regular_add,regular_const,true_and]
  refine ⟨⟨regular_pow A 2 (regular_A q),regular_pow ρ 2 (regular_ρ q)⟩,?_⟩
  simp only [eval_mul,eval_add,eval_const,eval_pow,eval_A,eval_ρ]
  positivity
lemma Z_regular {c : ℝ} (hc : 0<c) {q : Dom} (hq : 0<q.2) : (Z c).RegularAt q := by
  simp only [Z,regular_sqrt,regular_mul,regular_add,regular_const,true_and]
  refine ⟨⟨regular_pow A 2 (regular_A q),regular_pow ρ 2 (regular_ρ q),regular_s q⟩,?_⟩
  simp only [eval_mul,eval_add,eval_const,eval_pow,eval_A,eval_ρ,eval_s]
  positivity
lemma regular {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) {q : Dom} (hq : 0<q.2) :
    (Expr a c).RegularAt q := by
  have hx := X_regular hc q
  have hz := Z_regular hc hq
  have hxp := X_pos hc q
  have hzp := Z_pos hc hq
  have hsum : (Z c+X c).RegularAt q := ⟨hz,hx⟩
  have hsp : 0<(Z c+X c).eval q := by simpa only [eval_add] using add_pos hzp hxp
  have hp (e : AlgebraicExpr Dom) (n : ℕ) (he : e.RegularAt q) := regular_pow e n he
  simp only [Expr,K,B,η,Rem,C₁,C₂,C₃,C₄,Δ,regular_add,regular_mul,regular_div,
    regular_sub,regular_neg,regular_const,regular_ρ,regular_ε,regular_s,
    true_and,hx,hz,hp,eval_mul,eval_const,eval_pow,eval_add]
  repeat' constructor
  all_goals first | assumption | positivity
lemma local_flow (a : Fin 6 → ℝ) {c : ℝ} (hc : 0<c) (x : State Params) (hx : 0<x.2.1) :
    ∃ f : State Params × ℝ → State Params, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ q in 𝓝 (x,(0:ℝ)), f (q.1,0)=q.1 ∧
        HasDerivAt (fun s => f (q.1,s)) (field (Φ a c) (f q)) q.2 :=
  algebraic_profile_flow (Expr a c) x (regular hc hx)
end QuinticLienard.ScaledProfile

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter Metric
open scoped Topology ContDiff
namespace QuinticLienard.ScalarArcs

lemma IsArch.congr_profile {φ ψ u : ℝ → ℝ} {h t a b : ℝ}
    (hu : IsArch φ u h t a b) (hht : h ≤ t) (he : EqOn ψ φ (Icc h t)) :
    IsArch ψ u h t a b := by
  have heh := he (show h ∈ Icc h t from ⟨le_rfl,hht⟩)
  have het := he (show t ∈ Icc h t from ⟨hht,le_rfl⟩)
  refine ⟨hu.continuous,?_,?_,?_,hu.lower,hu.upper,?_,?_,?_,hu.range_mem,?_,?_⟩
  · simpa only [het] using hu.lower_lt_peak
  · simpa only [het] using hu.peak_lt_upper
  · simpa only [het] using hu.peak
  · simpa only [heh] using hu.lower_transverse
  · simpa only [heh] using hu.upper_transverse
  · intro y hy
    rw [he (hu.range_mem y hy)]
    exact hu.equation y hy
  · simpa only [het] using hu.inc
  · simpa only [het] using hu.dec

theorem IsArch.of_positive_solution_and_hits {φ u : ℝ → ℝ} {a b h t : ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (hc : Continuous u)
    (hu : ∀ y ∈ Icc a b, HasDerivAt u (φ (u y)-y) y)
    (hpos : ∀ y ∈ Icc a b, 0 < u y)
    (ha : a < φ t) (hb : φ t < b) (hpeak : u (φ t)=t)
    (hl : u a=h) (hr : u b=h) : IsArch φ u h t a b := by
  have hab := (ha.trans hb).le
  obtain ⟨l,hlm,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc.continuousOn
  obtain ⟨v,hvm,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc.continuousOn
  have hlow : 0 < u l/2 := by linarith [hpos l hlm]
  have hrange (y : ℝ) (hy : y ∈ Icc a b) : u y ∈ Icc (u l/2) (u v+1) := by
    have hlo : u l ≤ u y := hmin hy
    have hhi : u y ≤ u v := hmax hy
    constructor <;> linarith [hpos l hlm]
  have hlt : u l/2 < u v+1 := by
    have hlo : u l ≤ u v := hmin hvm
    linarith [hpos l hlm]
  obtain ⟨ψ,K,B,hψ,_,_,he⟩ := positive_profile_extension hφ hlow hlt
  have het : ψ t=φ t := by rw [←hpeak]; exact he (hrange (φ t) ⟨ha.le,hb.le⟩)
  have heh : ψ h=φ h := by rw [←hl]; exact he (hrange a ⟨le_rfl,hab⟩)
  have harch : IsArch ψ u h t a b := IsArch.of_solution_and_hits hψ hc
    (fun y hy => by rw [he (hrange y hy)]; exact hu y hy)
    (by simpa only [het] using ha) (by simpa only [het] using hb)
    (by simpa only [het] using hpeak) hl hr
  have hht : h ≤ t := by
    simpa only [hpeak] using harch.range_mem (φ t) ⟨ha.le,hb.le⟩ |>.1
  apply harch.congr_profile hht
  intro x hx
  apply (he _).symm
  have hhh := hrange a ⟨le_rfl,hab⟩
  have htt := hrange (φ t) ⟨ha.le,hb.le⟩
  rw [hl] at hhh
  rw [hpeak] at htt
  exact ⟨hhh.1.trans hx.1,hx.2.trans htt.2⟩

lemma IsArch.subarch_positive {φ u : ℝ → ℝ} {h₀ h t a₀ b₀ : ℝ}
    (hu : IsArch φ u h₀ t a₀ b₀) (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (h₀pos : 0 < h₀) (hh : h₀ < h) (ht : h < t) :
    ∃ a b, a₀ < a ∧ b < b₀ ∧ IsArch φ u h t a b := by
  obtain ⟨ψ,K,B,hs,_,_,he⟩ := positive_profile_extension hφ h₀pos (hh.trans ht)
  have hu' := hu.congr_profile (hh.trans ht).le he
  obtain ⟨a,b,ha,hb,hv⟩ := hu'.subarch hs hh ht
  refine ⟨a,b,ha,hb,hv.congr_profile ht.le ?_⟩
  intro x hx
  exact (he ⟨hh.le.trans hx.1,hx.2⟩).symm

lemma canonical_of_positive_arch {φ u : ℝ → ℝ} {h t a b : ℝ}
    (hu : IsArch φ u h t a b) (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hh : 0 < h) (hht : h < t) : lower φ h t=a ∧ upper φ h t=b := by
  obtain ⟨ψ,K,B,_,hK,_,he⟩ := positive_profile_extension hφ hh hht
  have hc := chosen_arch (positive_arch_exists hφ hh hht)
  have heq := hc.unique hu hK he
  exact ⟨heq.1,heq.2.1⟩
end QuinticLienard.ScalarArcs

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveEndpoints
open ScalarArcs ArcEndpoints ArcFamilies
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem actual_endpoint_families_positive (Φ : P × ℝ → ℝ)
    (hΦ : ∀ p, ContDiffOn ℝ 1 (fun x => Φ (p,x)) (Ioi 0))
    {w : (P × ℝ) × ℝ → ℝ} {p : P} {t h a b A B : ℝ}
    (hwc : ∀ q, Continuous (fun y => w (q,y)))
    (hpeak : ∀ q, w (q,Φ q) = q.2)
    (hw : ∀ y ∈ Icc A B, ContDiffAt ℝ ω w ((p,t),y))
    (he : ∀ y ∈ Icc A B, ∀ᶠ q in 𝓝 ((p,t),y),
      HasDerivAt (fun s => w (q.1,s)) (Φ (q.1.1,w q)-q.2) q.2)
    (hpos : ∀ y ∈ Icc A B, 0 < w ((p,t),y))
    (hu : IsArch (fun x => Φ (p,x)) (fun y => w ((p,t),y)) h t a b)
    (hA : A < a) (hB : b < B) (hΦp : ContinuousAt Φ (p,t)) :
    ∃ l r : (P × ℝ) × ℝ → ℝ,
      ContDiffAt ℝ ω l ((p,t),h) ∧ ContDiffAt ℝ ω r ((p,t),h) ∧
      l ((p,t),h) = a ∧ r ((p,t),h) = b ∧
      ∀ᶠ q in 𝓝 ((p,t),h),
        IsArch (fun x => Φ (q.1.1,x)) (fun y => w (q.1,y))
          q.2 q.1.2 (l q) (r q) := by
  have hab : a < b := hu.lower_lt_peak.trans hu.peak_lt_upper
  have haAB : a ∈ Icc A B := ⟨hA.le,(hab.trans hB).le⟩
  have hbAB : b ∈ Icc A B := ⟨(hA.trans hab).le,hB.le⟩
  have had : HasDerivAt (fun y => w ((p,t),y)) (Φ (p,h)-a) a := by
    simpa only [hu.lower] using hu.equation a ⟨le_rfl,hab.le⟩
  have hbd : HasDerivAt (fun y => w ((p,t),y)) (Φ (p,h)-b) b := by
    simpa only [hu.upper] using hu.equation b ⟨hab.le,le_rfl⟩
  obtain ⟨l,hld,hl0,hle⟩ := level_hit (hw a haAB) had hu.lower (by
    have hh := hu.lower_transverse
    exact ne_of_gt (sub_pos.mpr hh))
  obtain ⟨r,hrd,hr0,hre⟩ := level_hit (hw b hbAB) hbd hu.upper (by
    have hh := hu.upper_transverse
    exact ne_of_lt (sub_neg.mpr hh))
  have hode : ∀ᶠ q in 𝓝 (p,t), ∀ y ∈ Icc A B,
      HasDerivAt (fun s => w (q,s)) (Φ (q.1,w (q,y))-y) y :=
    isCompact_Icc.eventually_forall_of_forall_eventually he
  have hpcont : ContinuousAt (fun q : (P × ℝ) × ℝ => Φ q.1) ((p,t),h) :=
    ContinuousAt.comp (f := Prod.fst) (g := Φ) (x := ((p,t),h)) hΦp continuousAt_fst
  have hnear : ∀ᶠ q in 𝓝 ((p,t),h),
      A < l q ∧ l q < Φ q.1 ∧ Φ q.1 < r q ∧ r q < B := by
    have ha' : A < l ((p,t),h) := by simpa only [hl0] using hA
    have hl' : l ((p,t),h) < Φ ((p,t),h).1 := by simpa only [hl0] using hu.lower_lt_peak
    have hr' : Φ ((p,t),h).1 < r ((p,t),h) := by simpa only [hr0] using hu.peak_lt_upper
    have hb' : r ((p,t),h) < B := by simpa only [hr0] using hB
    filter_upwards [continuousAt_const.eventually_lt hld.continuousAt ha',
      hld.continuousAt.eventually_lt hpcont hl',
      hpcont.eventually_lt hrd.continuousAt hr',
      hrd.continuousAt.eventually_lt continuousAt_const hb'] with q h₁ h₂ h₃ h₄
    exact ⟨h₁,h₂,h₃,h₄⟩
  have hpositive : ∀ᶠ q in 𝓝 (p,t), ∀ y ∈ Icc A B, 0 < w (q,y) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro y hy
    exact continuousAt_const.eventually_lt (hw y hy).continuousAt (hpos y hy)
  refine ⟨l,r,hld,hrd,hl0,hr0,?_⟩
  filter_upwards [hle,hre,hnear,continuousAt_fst.eventually hode,continuousAt_fst.eventually hpositive] with q hl hr hq ho hp
  apply IsArch.of_positive_solution_and_hits (hΦ q.1.1) (hwc q.1)
    (fun y hy => ho y ⟨hq.1.le.trans hy.1,hy.2.trans hq.2.2.2.le⟩)
    (fun y hy => hp y ⟨hq.1.le.trans hy.1,hy.2.trans hq.2.2.2.le⟩)
    hq.2.1 hq.2.2.1 (hpeak q.1) hl hr

end QuinticLienard.PositiveEndpoints

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveEndpoints
open ScalarArcs ArcEndpoints ArcFamilies
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem endpoints_and_witness (Φ : P × ℝ → ℝ) (hΦ : ∀ q : P × ℝ, 0 < q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0 < x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hh : 0 < h) (hht : h < t) :
    ContDiffAt ℝ ω (lowerFamily Φ) ((p,t),h) ∧
    ContDiffAt ℝ ω (upperFamily Φ) ((p,t),h) ∧
    ∃ w : (P × ℝ) × ℝ → ℝ,
      (∀ q, Continuous (fun y => w (q,y))) ∧
      (∀ q, w (q,Φ q) = q.2) ∧
      (∀ y ∈ Icc (lowerFamily Φ ((p,t),h)) (upperFamily Φ ((p,t),h)),
        ContDiffAt ℝ ω w ((p,t),y)) ∧
      (∀ y ∈ Icc (lowerFamily Φ ((p,t),h)) (upperFamily Φ ((p,t),h)),
        ∀ᶠ q in 𝓝 ((p,t),y),
          HasDerivAt (fun s => w (q.1,s)) (Φ (q.1.1,w q)-q.2) q.2) ∧
      ∀ᶠ q in 𝓝 ((p,t),h),
        IsArch (fun x => Φ (q.1.1,x)) (fun y => w (q.1,y))
          q.2 q.1.2 (lowerFamily Φ q) (upperFamily Φ q) := by
  have hφ (p : P) : ContDiffOn ℝ 1 (fun x => Φ (p,x)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  obtain ⟨u,a₀,b₀,hu⟩ := positive_arch_exists (hφ p) (show 0<h/2 by linarith) (show h/2<t by linarith)
  obtain ⟨a,b,ha,hb,harch⟩ := hu.subarch_positive (hφ p) (show 0<h/2 by linarith) (show h/2<h by linarith) hht
  let U : Set (State P) := {x | 0<x.2.1}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_snd.fst
  have hV : ContDiffOn ℝ 1 (field Φ) U := by
    intro x hx
    have hd : ContDiffAt ℝ ω (field Φ) x :=
      contDiffAt_const.prodMk ((((hΦ (x.1,x.2.1) hx).comp x
        (contDiffAt_fst.prodMk contDiffAt_snd.fst)).sub contDiffAt_snd.snd).prodMk contDiffAt_const)
    exact (hd.of_le (by simp)).contDiffWithinAt
  obtain ⟨w,hwc,hwpeak,hwmatch,hwd,hwe⟩ := peak_family Φ hU hV
    (fun x hx => hloc x hx) (hΦ (p,t) (hh.trans hht)) hu.lower_lt_peak hu.peak_lt_upper
    hu.continuous hu.peak hu.equation (fun y hy => (show 0<h/2 by linarith).trans_le (hu.range_mem y hy).1)
  let A := (a₀+a)/2
  let B := (b+b₀)/2
  have hA : a₀ < A ∧ A < a := by dsimp [A]; constructor <;> linarith
  have hB : b < B ∧ B < b₀ := by dsimp [B]; constructor <;> linarith
  have hsub : Icc A B ⊆ Ioo a₀ b₀ :=
    fun _ hy => ⟨hA.1.trans_le hy.1,hy.2.trans_lt hB.2⟩
  have hpos (y : ℝ) (hy : y ∈ Icc A B) : 0 < w ((p,t),y) := by
    rw [hwmatch y (Ioo_subset_Icc_self (hsub hy))]
    exact (show 0<h/2 by linarith).trans_le (hu.range_mem y (Ioo_subset_Icc_self (hsub hy))).1
  have hwb : IsArch (fun x => Φ (p,x)) (fun y => w ((p,t),y)) h t a b := by
    apply IsArch.of_positive_solution_and_hits (hφ p) (hwc (p,t))
      (fun y hy => (hwe y (hsub ⟨hA.2.le.trans hy.1,hy.2.trans hB.1.le⟩)).self_of_nhds)
      (fun y hy => hpos y ⟨hA.2.le.trans hy.1,hy.2.trans hB.1.le⟩)
      harch.lower_lt_peak harch.peak_lt_upper (hwpeak (p,t))
    · rw [hwmatch a ⟨ha.le,(harch.lower_lt_peak.trans hu.peak_lt_upper).le⟩]
      exact harch.lower
    · rw [hwmatch b ⟨(hu.lower_lt_peak.trans harch.peak_lt_upper).le,hb.le⟩]
      exact harch.upper
  obtain ⟨l,r,hld,hrd,_,_,he⟩ := actual_endpoint_families_positive Φ hφ hwc hwpeak
    (fun y hy => hwd y (Ioo_subset_Icc_self (hsub hy)))
    (fun y hy => hwe y (hsub hy)) hpos hwb hA.2 hB.1 (hΦ (p,t) (hh.trans hht)).continuousAt
  have hlr := canonical_of_positive_arch hwb (hφ p) hh hht
  change lowerFamily Φ ((p,t),h) = a ∧ upperFamily Φ ((p,t),h) = b at hlr
  have hinc : Icc (lowerFamily Φ ((p,t),h)) (upperFamily Φ ((p,t),h)) ⊆
      Ioo a₀ b₀ := by
    rw [hlr.1,hlr.2]
    exact fun _ hy => ⟨ha.trans_le hy.1,hy.2.trans_lt hb⟩
  have ht : ∀ᶠ q : (P × ℝ) × ℝ in 𝓝 ((p,t),h), q.2 < q.1.2 :=
    continuousAt_snd.eventually_lt continuousAt_fst.snd hht
  have hp : ∀ᶠ q : (P × ℝ) × ℝ in 𝓝 ((p,t),h), 0<q.2 :=
    continuousAt_const.eventually_lt continuousAt_snd hh
  have hcanon : ∀ᶠ q in 𝓝 ((p,t),h), lowerFamily Φ q=l q ∧ upperFamily Φ q=r q := by
    filter_upwards [he,ht,hp] with q hq hqt hqp
    exact canonical_of_positive_arch hq (hφ q.1.1) hqp hqt
  refine ⟨hld.congr_of_eventuallyEq (hcanon.mono fun _ h => h.1),
    hrd.congr_of_eventuallyEq (hcanon.mono fun _ h => h.2),
    w,hwc,hwpeak,fun y hy => hwd y (Ioo_subset_Icc_self (hinc hy)),
    fun y hy => hwe y (hinc hy),?_⟩
  filter_upwards [he,hcanon] with q hq hqc
  rwa [hqc.1,hqc.2]

end QuinticLienard.PositiveEndpoints

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveVariation
open ScalarArcs ArcEndpoints ArcFamilies PartialCalculus ArchVariation

lemma positive_homogeneous_on {f a : ℝ → ℝ} {l r c : ℝ}
    (ha : ContinuousOn a (Icc l r)) (hf : ContinuousOn f (Icc l r))
    (hd : ∀ y ∈ Icc l r, HasDerivAt f (a y*f y) y)
    (hc : c ∈ Icc l r) (hinit : f c = 1) :
    ∀ y ∈ Icc l r, 0 < f y := by
  let a₀ := IccExtend (hc.1.trans hc.2) (fun x : Icc l r => a x)
  have hcont : Continuous a₀ := continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_domRestrict.mp ha)
  have heq (y : ℝ) (hy : y ∈ Icc l r) : a₀ y=a y := by simp [a₀,IccExtend,projIcc_of_mem (hc.1.trans hc.2) hy]
  have hsol := positive_homogeneous hcont hf (fun y hy => by simpa only [heq y hy] using hd y hy) hc hinit
  intro y hy
  rw [hsol y hy]
  exact Real.exp_pos _

lemma peak_derivative_positive_local {w : ℝ × ℝ → ℝ} {φ : ℝ → ℝ}
    {t a b : ℝ} (ht : 0<t) (hφ : ∀ x, 0<x → ContDiffAt ℝ ω φ x)
    (hw : ∀ y ∈ Icc a b, ContDiffAt ℝ ω w (t,y))
    (he : ∀ y ∈ Icc a b, ∀ᶠ q in 𝓝 (t,y),
      HasDerivAt (fun s => w (q.1,s)) (φ (w q)-q.2) q.2)
    (hpos : ∀ y ∈ Icc a b, 0<w (t,y))
    (hp : ∀ᶠ s in 𝓝 t, w (s,φ s) = s)
    (hc : φ t ∈ Icc a b) : ∀ y ∈ Icc a b, 0 < first w (t,y) := by
  have init : first w (t,φ t) = 1 := by
    apply moving_peak_variation (hw _ hc) ((hφ t ht).differentiableAt (by simp)) hp
    simpa only [hp.self_of_nhds,sub_self] using (he _ hc).self_of_nhds
  have hcoeff : ContinuousOn (fun y => deriv φ (w (t,y))) (Icc a b) := by
    intro y hy
    have hd : ContinuousAt (deriv φ) (w (t,y)) :=
      ((hφ _ (hpos y hy)).derivWithin (m:=ω) (by simp)).continuousAt
    have hc : ContinuousAt (fun s => w (t,s)) y :=
      (hw y hy).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
    exact (ContinuousAt.comp (f:=fun s => w (t,s)) (g:=deriv φ) hd hc).continuousWithinAt
  have hfirst : ContinuousOn (fun y => first w (t,y)) (Icc a b) := by
    intro y hy
    exact (((first_contDiffAt (hw y hy)).continuousAt).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  exact positive_homogeneous_on hcoeff hfirst
    (fun y hy => fixed_profile_variation (hw y hy) ((hφ _ (hpos y hy)).differentiableAt (by simp)) (he y hy)) hc init

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

lemma endpoints (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hh : 0<h) (hht : h<t) :
    ContDiffAt ℝ ω (lowerFamily Φ) ((p,t),h) ∧ ContDiffAt ℝ ω (upperFamily Φ) ((p,t),h) := by
  obtain ⟨hl,hr,_⟩ := PositiveEndpoints.endpoints_and_witness Φ hΦ hloc hh hht (p:=p)
  exact ⟨hl,hr⟩

lemma endpoint_witness (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hh : 0<h) (hht : h<t) :
    ∃ w : (P × ℝ) × ℝ → ℝ,
      (∀ q, Continuous (fun y => w (q,y))) ∧
      (∀ q, w (q,Φ q) = q.2) ∧
      (∀ y ∈ Icc (lowerFamily Φ ((p,t),h)) (upperFamily Φ ((p,t),h)),
        ContDiffAt ℝ ω w ((p,t),y)) ∧
      (∀ y ∈ Icc (lowerFamily Φ ((p,t),h)) (upperFamily Φ ((p,t),h)),
        ∀ᶠ q in 𝓝 ((p,t),y),
          HasDerivAt (fun s => w (q.1,s)) (Φ (q.1.1,w q)-q.2) q.2) ∧
      ∀ᶠ q in 𝓝 ((p,t),h),
        IsArch (fun x => Φ (q.1.1,x)) (fun y => w (q.1,y))
          q.2 q.1.2 (lowerFamily Φ q) (upperFamily Φ q) := by
  exact (PositiveEndpoints.endpoints_and_witness Φ hΦ hloc hh hht).2.2

theorem peak_signs (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    deriv (fun s => lowerFamily Φ ((p,s),h)) t < 0 ∧
      0 < deriv (fun s => upperFamily Φ ((p,s),h)) t := by
  obtain ⟨w,_,hpeak,hwd,hwe,harch⟩ := endpoint_witness Φ hΦ hloc hhpos hht
  have hu := harch.self_of_nhds
  have hφ (x : ℝ) (hx : 0<x) : ContDiffAt ℝ ω (fun x => Φ (p,x)) x :=
    (hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)
  let w₀ : ℝ × ℝ → ℝ := fun q => w ((p,q.1),q.2)
  let l : ℝ → ℝ := fun s => lowerFamily Φ ((p,s),h)
  let r : ℝ → ℝ := fun s => upperFamily Φ ((p,s),h)
  have hw₀ (y : ℝ) (hy : y ∈ Icc (l t) (r t)) : ContDiffAt ℝ ω w₀ (t,y) :=
    (hwd y hy).comp (t,y) ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)
  have he₀ (y : ℝ) (hy : y ∈ Icc (l t) (r t)) :
      ∀ᶠ q in 𝓝 (t,y), HasDerivAt (fun s => w₀ (q.1,s)) (Φ (p,w₀ q)-q.2) q.2 := by
    have hc : ContinuousAt (fun q : ℝ × ℝ => ((p,q.1),q.2)) (t,y) :=
      (continuousAt_const.prodMk continuousAt_fst).prodMk continuousAt_snd
    exact hc.eventually (hwe y hy)
  have hh := peak_derivative_positive_local (hhpos.trans hht) hφ hw₀ he₀
    (fun y hy => hhpos.trans_le (hu.range_mem y hy).1)
    (Eventually.of_forall (fun s => hpeak (p,s)))
    ⟨hu.lower_lt_peak.le,hu.peak_lt_upper.le⟩
  obtain ⟨hl,hr⟩ := endpoints Φ hΦ hloc (p := p) hhpos hht
  have hld : DifferentiableAt ℝ l t :=
    (hl.comp t ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hrd : DifferentiableAt ℝ r t :=
    (hr.comp t ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hag : ∀ᶠ s in 𝓝 t,
      IsArch (fun x => Φ (p,x)) (fun y => w₀ (s,y)) h s (l s) (r s) :=
    ((continuousAt_const.prodMk continuousAt_id).prodMk continuousAt_const).eventually harch
  have hab := hu.lower_lt_peak.le.trans hu.peak_lt_upper.le
  have hal : l t ∈ Icc (l t) (r t) := ⟨le_rfl,hab⟩
  have har : r t ∈ Icc (l t) (r t) := ⟨hab,le_rfl⟩
  have hel0 : w ((p,t),l t) = h := hu.lower
  have her0 : w ((p,t),r t) = h := hu.upper
  apply endpoint_peak_signs (φ := fun s => Φ (p,s)) hld hrd ((hw₀ _ hal).differentiableAt (by simp))
    ((hw₀ _ har).differentiableAt (by simp))
    (hag.mono fun _ hq => hq.lower) (hag.mono fun _ hq => hq.upper)
  · simpa only [hel0] using hu.equation _ hal
  · simpa only [her0] using hu.equation _ har
  · exact hh _ hal
  · exact hh _ har
  · exact hu.lower_transverse
  · exact hu.upper_transverse

theorem base_derivatives (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    HasDerivAt (fun s => lowerFamily Φ ((p,t),s))
      (1/(Φ (p,h)-lowerFamily Φ ((p,t),h))) h ∧
    HasDerivAt (fun s => upperFamily Φ ((p,t),s))
      (1/(Φ (p,h)-upperFamily Φ ((p,t),h))) h := by
  obtain ⟨w,_,_,_,_,he⟩ := endpoint_witness Φ hΦ hloc hhpos hht
  have hu := he.self_of_nhds
  obtain ⟨hl,hr⟩ := endpoints Φ hΦ hloc (p := p) hhpos hht
  let l : ℝ → ℝ := fun s => lowerFamily Φ ((p,t),s)
  let r : ℝ → ℝ := fun s => upperFamily Φ ((p,t),s)
  have hld : DifferentiableAt ℝ l h :=
    (hl.comp h (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hrd : DifferentiableAt ℝ r h :=
    (hr.comp h (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hag : ∀ᶠ s in 𝓝 h,
      IsArch (fun x => Φ (p,x)) (fun y => w ((p,t),y)) s t (l s) (r s) :=
    (continuousAt_const.prodMk continuousAt_id).eventually he
  have hab := hu.lower_lt_peak.le.trans hu.peak_lt_upper.le
  have hal : l h ∈ Icc (l h) (r h) := ⟨le_rfl,hab⟩
  have har : r h ∈ Icc (l h) (r h) := ⟨hab,le_rfl⟩
  have hel : w ((p,t),l h) = h := hu.lower
  have her : w ((p,t),r h) = h := hu.upper
  have hdl : HasDerivAt (fun y => w ((p,t),y)) (Φ (p,h)-l h) (l h) := by
    simpa only [hel] using hu.equation _ hal
  have hdr : HasDerivAt (fun y => w ((p,t),y)) (Φ (p,h)-r h) (r h) := by
    simpa only [her] using hu.equation _ har
  have hlv := (hdl.comp h hld.hasDerivAt).unique
    ((hasDerivAt_id h).congr_of_eventuallyEq (hag.mono fun _ hq => hq.lower))
  have hrv := (hdr.comp h hrd.hasDerivAt).unique
    ((hasDerivAt_id h).congr_of_eventuallyEq (hag.mono fun _ hq => hq.upper))
  have hlne : Φ (p,h)-l h ≠ 0 := ne_of_gt (sub_pos.mpr hu.lower_transverse)
  have hrne : Φ (p,h)-r h ≠ 0 := ne_of_lt (sub_neg.mpr hu.upper_transverse)
  have hleq : deriv l h = 1/(Φ (p,h)-l h) := by
    apply (eq_div_iff hlne).mpr
    simpa only [mul_comm] using hlv
  have hreq : deriv r h = 1/(Φ (p,h)-r h) := by
    apply (eq_div_iff hrne).mpr
    simpa only [mul_comm] using hrv
  exact ⟨by simpa only [hleq] using hld.hasDerivAt,
    by simpa only [hreq] using hrd.hasDerivAt⟩

theorem peak_width_midpoint_bounds (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    0 < deriv (fun s => width (fun u => Φ (p,u)) h s) t ∧
      |deriv (fun s => midpoint (fun u => Φ (p,u)) h s) t /
        deriv (fun s => width (fun u => Φ (p,u)) h s) t| < 1 := by
  obtain ⟨hl,hr⟩ := endpoints Φ hΦ hloc (p := p) hhpos hht
  have hld := (hl.comp t
    ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt
      (by simp)
  have hrd := (hr.comp t
    ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt
      (by simp)
  obtain ⟨hls,hrs⟩ := peak_signs Φ hΦ hloc hhpos hht
  have hb := width_midpoint_peak_bounds hld hrd hls hrs
  have hmid : deriv (fun s => midpoint (fun u => Φ (p,u)) h s) t =
      deriv (fun s => (upperFamily Φ ((p,s),h)+lowerFamily Φ ((p,s),h))/2) t := by
    exact (((hrd.hasDerivAt.add hld.hasDerivAt).div_const 2).sub_const (Φ (p,h))).deriv.trans
      (((hrd.hasDerivAt.add hld.hasDerivAt).div_const 2).deriv.symm)
  rw [hmid]
  exact hb

end QuinticLienard.PositiveVariation

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveWidth
open ScalarArcs ArcEndpoints ArcFamilies PositiveVariation

theorem width_small_base {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (t : ℝ) (ht : 0<t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, t-δ < h → h < t → width φ h t < ε := by
  obtain ⟨u,a,b,hu⟩ := positive_arch_exists hφ (show 0<t/2 by linarith) (show t/2<t by linarith)
  let d := min (ε/2) (min ((φ t-a)/2) ((b-φ t)/2))
  have hd : 0 < d := lt_min (by linarith) (lt_min (by linarith [hu.lower_lt_peak])
    (by linarith [hu.peak_lt_upper]))
  have hdε : d ≤ ε/2 := min_le_left _ _
  have hda : d ≤ (φ t-a)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdb : d ≤ (b-φ t)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hleft : φ t-d ∈ Icc a (φ t) := by constructor <;> linarith [hu.lower_lt_peak]
  have hright : φ t+d ∈ Icc (φ t) b := by constructor <;> linarith [hu.peak_lt_upper]
  have hutl : u (φ t-d) < t := by
    simpa only [hu.peak] using hu.inc hleft ⟨hu.lower_lt_peak.le,le_rfl⟩ (by linarith)
  have hutr : u (φ t+d) < t := by
    simpa only [hu.peak] using hu.dec ⟨le_rfl,hu.peak_lt_upper.le⟩ hright (by linarith)
  let H := max (t/2) (max (u (φ t-d)) (u (φ t+d)))
  have hH : H < t := max_lt (by linarith) (max_lt hutl hutr)
  refine ⟨t-H,sub_pos.mpr hH,?_⟩
  intro h hh hht
  have hHh : H < h := by linarith
  have h₀ : t/2 < h := (le_max_left _ _).trans_lt hHh
  have hlh : u (φ t-d) < h :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hHh
  have hrh : u (φ t+d) < h :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hHh
  obtain ⟨l,r,hal,hrb,hv⟩ := hu.subarch_positive hφ (show 0<t/2 by linarith) h₀ hht
  have hl : φ t-d < l := by
    by_contra hn
    have hh := hu.inc.monotoneOn ⟨hal.le,hv.lower_lt_peak.le⟩ hleft (le_of_not_gt hn)
    rw [hv.lower] at hh
    exact (not_le_of_gt hlh) hh
  have hr : r < φ t+d := by
    by_contra hn
    have hh := hu.dec.antitoneOn hright ⟨hv.peak_lt_upper.le,hrb.le⟩ (le_of_not_gt hn)
    rw [hv.upper] at hh
    exact (not_le_of_gt hrh) hh
  obtain ⟨heql,heqr⟩ := canonical_of_positive_arch hv hφ (by linarith) hht
  dsimp [width]
  rw [heql,heqr]
  linarith

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)

include hΦ hloc

theorem width_analytic {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    ContDiffAt ℝ ω (widthFamily Φ) ((p,t),h) := by
  obtain ⟨hl,hr⟩ := endpoints Φ hΦ hloc (p := p) hhpos hht
  exact (hr.sub hl).div_const 2

omit hloc [FiniteDimensional ℝ P] in
theorem width_pos {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    0 < widthFamily Φ ((p,t),h) := by
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  have hu := chosen_arch (positive_arch_exists hφ hhpos hht)
  dsimp [widthFamily,width]
  linarith [hu.lower_lt_peak,hu.peak_lt_upper]

omit hloc [FiniteDimensional ℝ P] in
theorem gap_pos {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    0 < (widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2 := by
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  have hb := midpoint_abs_lt_width (positive_arch_exists hφ hhpos hht)
  have ha := width_pos Φ hΦ (p := p) hhpos hht
  change |midpointFamily Φ ((p,t),h)| < widthFamily Φ ((p,t),h) at hb
  exact sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos ha] using hb))

theorem width_base_deriv {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    HasDerivAt (fun s => widthFamily Φ ((p,t),s))
      (-widthFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2)) h := by
  obtain ⟨hl,hr⟩ := base_derivatives Φ hΦ hloc (p := p) hhpos hht
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  have hu := chosen_arch (positive_arch_exists hφ hhpos hht)
  have hlne : Φ (p,h)-lowerFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hu.lower_transverse)
  have hrne : Φ (p,h)-upperFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_lt (sub_neg.mpr hu.upper_transverse)
  have hqne := ne_of_gt (gap_pos Φ hΦ (p := p) hhpos hht)
  have he : (1/(Φ (p,h)-upperFamily Φ ((p,t),h)) -
      1/(Φ (p,h)-lowerFamily Φ ((p,t),h)))/2 =
      -widthFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) := by
    apply (eq_div_iff hqne).mpr
    dsimp [widthFamily,midpointFamily,width,ScalarArcs.midpoint,lowerFamily,upperFamily] at *
    field_simp
    ring
  rw [←he]
  exact (hr.sub hl).div_const 2

theorem height_energy_antitone (p : P) (t : ℝ) :
    AntitoneOn (fun h => (widthFamily Φ ((p,t),h))^2+2*h) (Ioo 0 t) := by
  let f : ℝ → ℝ := fun h => (widthFamily Φ ((p,t),h))^2+2*h
  have hd (h : ℝ) (hh : h ∈ Ioo 0 t) : HasDerivAt f
      (2*widthFamily Φ ((p,t),h)*(-widthFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2))+2) h := by
    simpa [f] using! ((width_base_deriv Φ hΦ hloc (p:=p) hh.1 hh.2).pow 2).add
      ((hasDerivAt_id h).const_mul 2)
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 t)
    (fun h hh => (hd h hh).continuousAt.continuousWithinAt)
    (fun h hh => (hd h (interior_subset hh)).differentiableAt.differentiableWithinAt)
  intro h hh
  have hh' : h ∈ Ioo 0 t := interior_subset hh
  rw [(hd h hh').deriv]
  have hq := gap_pos Φ hΦ (p:=p) hh'.1 hh'.2
  have he : 2*widthFamily Φ ((p,t),h)*(-widthFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2))+2 =
      -(2*(midpointFamily Φ ((p,t),h))^2)/
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) := by
    field_simp
    ring
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (by norm_num) (sq_nonneg _))) hq.le

theorem height_bound {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h<t) :
    2*(t-h) ≤ (widthFamily Φ ((p,t),h))^2 := by
  have ha := height_energy_antitone Φ hΦ hloc p t
  by_contra hn
  have hw := sq_nonneg (widthFamily Φ ((p,t),h))
  let H := ((widthFamily Φ ((p,t),h))^2/2+h+t)/2
  have hH : h<H := by dsimp [H]; linarith
  have hHt : H<t := by dsimp [H]; linarith
  have hle := ha ⟨hhpos,hht⟩ ⟨hhpos.trans hH,hHt⟩ hH.le
  have hW := sq_nonneg (widthFamily Φ ((p,t),H))
  dsimp [H] at hle hW
  linarith

theorem width_strictAnti_base (p : P) (t : ℝ) :
    StrictAntiOn (fun h => widthFamily Φ ((p,t),h)) (Ioo 0 t) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 t)
    (fun h hh => (width_base_deriv Φ hΦ hloc hh.1 hh.2).continuousAt.continuousWithinAt)
  intro h hh
  have hh' : h ∈ Ioo 0 t := interior_subset hh
  rw [(width_base_deriv Φ hΦ hloc (p:=p) hh'.1 hh'.2).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (width_pos Φ hΦ (p:=p) hh'.1 hh'.2))
    (gap_pos Φ hΦ (p:=p) hh'.1 hh'.2)

theorem width_strictMono_peak (p : P) (h : ℝ) (hhpos : 0<h) :
    StrictMonoOn (fun t => widthFamily Φ ((p,t),h)) (Ioi h) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi h)
  · intro t ht
    exact ((width_analytic Φ hΦ hloc hhpos ht).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).continuousAt.continuousWithinAt
  · intro t ht
    exact (peak_width_midpoint_bounds Φ hΦ hloc (p:=p) hhpos (interior_subset ht)).1

theorem small_peak_exists (p : P) (h : ℝ) (hhpos : 0<h) {ε : ℝ} (hε : 0<ε) :
    ∃ t>h, widthFamily Φ ((p,t),h)<ε := by
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  obtain ⟨δ,hδ,hsmall⟩ := width_small_base hφ h hhpos hε
  let b := h-min δ h/2
  have hbh : b<h := by dsimp [b]; linarith [lt_min hδ hhpos]
  have hbpos : 0<b := by dsimp [b]; linarith [min_le_right δ h]
  have hwb : widthFamily Φ ((p,h),b)<ε := hsmall b (by dsimp [b]; linarith [min_le_left δ h]) hbh
  have hg : ContinuousAt (fun t : ℝ => ((p,t),b)) h :=
    (continuousAt_const.prodMk continuousAt_id).prodMk continuousAt_const
  have hc : ContinuousAt (fun t => widthFamily Φ ((p,t),b)) h :=
    ContinuousAt.comp (f:=fun t : ℝ => ((p,t),b)) (g:=widthFamily Φ)
      (width_analytic Φ hΦ hloc (p:=p) hbpos hbh).continuousAt hg
  obtain ⟨η,hη,hnear⟩ := Metric.eventually_nhds_iff.mp (hc.eventually_lt continuousAt_const hwb)
  let t := h+η/2
  have hht : h<t := by dsimp [t]; linarith
  have hsmallt : widthFamily Φ ((p,t),b)<ε :=
    hnear (by rw [Real.dist_eq]; dsimp [t]; rw [abs_of_pos (by linarith)]; linarith)
  exact ⟨t,hht,((width_strictAnti_base Φ hΦ hloc p t)
    ⟨hbpos,hbh.trans hht⟩ ⟨hhpos,hht⟩ hbh).trans hsmallt⟩

theorem peak_exists (p : P) (h : ℝ) (hhpos : 0<h) {r : ℝ} (hr : 0 < r) :
    ∃! t, h < t ∧ widthFamily Φ ((p,t),h) = r := by
  obtain ⟨a,ha,har⟩ := small_peak_exists Φ hΦ hloc p h hhpos hr
  let b := a+r^2+1
  have hab : a < b := by dsimp [b]; nlinarith [sq_nonneg r]
  have hhb : h < b := ha.trans hab
  have hbr : r < widthFamily Φ ((p,b),h) := by
    have hb := height_bound Φ hΦ hloc (p := p) hhpos hhb
    have hw := width_pos Φ hΦ (p := p) hhpos hhb
    dsimp [b] at hb
    nlinarith
  have hc : ContinuousOn (fun t => widthFamily Φ ((p,t),h)) (Icc a b) := by
    intro t ht
    exact ((width_analytic Φ hΦ hloc hhpos (ha.trans_le ht.1)).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).continuousAt.continuousWithinAt
  obtain ⟨t,ht,htr⟩ := intermediate_value_Icc hab.le hc ⟨har.le,hbr.le⟩
  refine ⟨t,⟨ha.trans_le ht.1,htr⟩,?_⟩
  intro s hs
  exact (width_strictMono_peak Φ hΦ hloc p h hhpos).injOn hs.1 (ha.trans_le ht.1)
    (hs.2.trans htr.symm)

theorem peak_spec {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    h < peakAtWidth Φ ((p,h),r) ∧
      widthFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) = r :=
  Classical.epsilon_spec (peak_exists Φ hΦ hloc p h hhpos hr).exists

theorem peak_eq {p : P} {h r t : ℝ} (hr : 0 < r) (hhpos : 0<h) (hht : h < t)
    (he : widthFamily Φ ((p,t),h) = r) : peakAtWidth Φ ((p,h),r) = t := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  exact (width_strictMono_peak Φ hΦ hloc p h hhpos).injOn hs.1 hht (hs.2.trans he.symm)

end QuinticLienard.PositiveWidth

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.OriginalProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuinticProfile
open SmoothFlow SmoothFlow.AlgebraicExpr ArcFamilies ScaledProfile
lemma representation (a : Fin 6 → ℝ) : (expr a).eval=profile a := by
  funext q
  simp [expr,xExpr,profile,poly,root]
lemma regular (a : Fin 6 → ℝ) {q : ℝ × ℝ} (hq : 0<q.2) : (expr a).RegularAt q := by
  have hx : xExpr.RegularAt q := by
    simp [xExpr,RegularAt,eval]
    positivity
  have hp (n : ℕ) := regular_pow xExpr n hx
  simp only [expr,regular_add,regular_mul,regular_const,hx,hp,true_and]
lemma analytic (a : Fin 6 → ℝ) {q : ℝ × ℝ} (hq : 0<q.2) : ContDiffAt ℝ ω (profile a) q := by
  rw [←representation]
  exact (expr a).eval_analytic (regular a hq)
lemma local_flow (a : Fin 6 → ℝ) (x : State ℝ) (hx : 0<x.2.1) :
    ∃ f : State ℝ × ℝ → State ℝ, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ q in 𝓝 (x,(0:ℝ)), f (q.1,0)=q.1 ∧
        HasDerivAt (fun s => f (q.1,s)) (field (profile a) (f q)) q.2 := by
  simpa only [representation] using algebraic_profile_flow (expr a) x (regular a hx)
end QuinticLienard.QuinticProfile

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ProfileDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
lemma root_pos {h : ℝ} (hh : 0<h) : 0<root h := Real.sqrt_pos.mpr (by positivity)
lemma root_sq {h : ℝ} (hh : 0≤h) : (root h)^2=2*h := Real.sq_sqrt (by positivity)
end QuinticLienard.ScaledProfile

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScalarArcs
lemma IsArch.endpoint_bounds {φ u : ℝ → ℝ} {h t a b B : ℝ}
    (hu : IsArch φ u h t a b) (hh : 0≤h) (ht : h<t) (hB : 0≤B)
    (hb : ∀ x ∈ Icc h t, |φ x|≤B) :
    -4*(B+t+1)≤a ∧ b≤4*(B+t+1) := by
  have hab := hu.lower_lt_peak.trans hu.peak_lt_upper
  have hct := hb t ⟨ht.le,le_rfl⟩
  have hc : -B≤φ t ∧ φ t≤B := abs_le.mp hct
  have hdp (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivAt (fun y=>u y+(y-B)^2/2) (φ (u y)-B) y := by
    convert! (hu.equation y hy).add ((((hasDerivAt_id y).sub_const B).pow 2).div_const 2) using 1
    simp only [id_eq]
    ring
  have hdm (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivAt (fun y=>u y+(y+B)^2/2) (φ (u y)+B) y := by
    convert! (hu.equation y hy).add ((((hasDerivAt_id y).add_const B).pow 2).div_const 2) using 1
    simp only [id_eq]
    ring
  have hmp : AntitoneOn (fun y=>u y+(y-B)^2/2) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun y hy=>(hdp y hy).continuousAt.continuousWithinAt)
      (fun y hy=>(hdp y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hdp y (interior_subset hy)).deriv]
    exact sub_nonpos.mpr (abs_le.mp (hb _ (hu.range_mem y (interior_subset hy)))).2
  have hmm : MonotoneOn (fun y=>u y+(y+B)^2/2) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun y hy=>(hdm y hy).continuousAt.continuousWithinAt)
      (fun y hy=>(hdm y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hdm y (interior_subset hy)).deriv]
    have hx := (abs_le.mp (hb _ (hu.range_mem y (interior_subset hy)))).1
    linarith
  have hl := hmm (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩)
    (show φ t ∈ Icc a b from ⟨hu.lower_lt_peak.le,hu.peak_lt_upper.le⟩) hu.lower_lt_peak.le
  have hr := hmp (show φ t ∈ Icc a b from ⟨hu.lower_lt_peak.le,hu.peak_lt_upper.le⟩)
    (show b ∈ Icc a b from ⟨hab.le,le_rfl⟩) hu.peak_lt_upper.le
  dsimp only at hl hr
  rw [hu.lower,hu.peak] at hl
  rw [hu.upper,hu.peak] at hr
  have hsq : (φ t)^2≤B^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) (show 0≤φ t+B by linarith [hc.1])]
  have hBc : |B*φ t|≤B^2 := by rw [abs_mul,abs_of_nonneg hB,pow_two]; exact mul_le_mul_of_nonneg_left hct hB
  have hBc' := abs_le.mp hBc
  have htl : 0≤t := hh.trans ht.le
  have hBt : 0≤B*t := mul_nonneg hB htl
  constructor
  · by_contra! hn
    have hcomp : (4*(B+t+1)-B)^2<(a+B)^2 := by nlinarith [sq_nonneg (a+B+4*(B+t+1)-B)]
    nlinarith [sq_nonneg t,sq_nonneg B]
  · by_contra! hn
    have hcomp : (4*(B+t+1)-B)^2<(b-B)^2 := by nlinarith [sq_nonneg (b-B-(4*(B+t+1)-B))]
    nlinarith [sq_nonneg t,sq_nonneg B]

lemma lower_strictMono_base {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (t : ℝ) :
    StrictMonoOn (fun h=>lower φ h t) (Ioo 0 t) := by
  intro h hh k hk hhk
  have hu := chosen_arch (positive_arch_exists hφ hh.1 hh.2)
  obtain ⟨a,b,ha,_,hab⟩ := hu.subarch_positive hφ hh.1 hhk hk.2
  dsimp only
  rw [(canonical_of_positive_arch hab hφ hk.1 hk.2).1]
  exact ha
lemma upper_strictAnti_base {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (t : ℝ) :
    StrictAntiOn (fun h=>upper φ h t) (Ioo 0 t) := by
  intro h hh k hk hhk
  have hu := chosen_arch (positive_arch_exists hφ hh.1 hh.2)
  obtain ⟨a,b,_,hb,hab⟩ := hu.subarch_positive hφ hh.1 hhk hk.2
  dsimp only
  rw [(canonical_of_positive_arch hab hφ hk.1 hk.2).2]
  exact hb

lemma axis_bounded {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : ContinuousOn φ (Ici 0)) {t : ℝ} (ht : 0<t) :
    BddBelow ((fun h=>lower φ h t) '' Ioo 0 t) ∧ BddAbove ((fun h=>upper φ h t) '' Ioo 0 t) := by
  obtain ⟨v,hv,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr ht.le)
    (hc.abs.mono (show Icc 0 t ⊆ Ici 0 from fun _ h=>h.1))
  have hb (h : ℝ) (hh : h ∈ Ioo 0 t) :=
    (chosen_arch (positive_arch_exists hφ hh.1 hh.2)).endpoint_bounds hh.1.le hh.2 (abs_nonneg (φ v))
      (fun x hx=>hmax ⟨hh.1.le.trans hx.1,hx.2⟩)
  exact ⟨⟨-4*(|φ v|+t+1),fun x hx=> by obtain ⟨h,hh,rfl⟩:=hx; exact (hb h hh).1⟩,
    ⟨4*(|φ v|+t+1),fun x hx=> by obtain ⟨h,hh,rfl⟩:=hx; exact (hb h hh).2⟩⟩

lemma lower_axis_tendsto {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : ContinuousOn φ (Ici 0)) {t : ℝ} (ht : 0<t) :
    Tendsto (fun h=>lower φ h t) (𝓝[>] 0) (𝓝 (axisLower φ t)) := by
  have hb := (axis_bounded hφ hc ht).1
  have hne : ((fun h=>lower φ h t) '' Ioo 0 t).Nonempty :=
    (nonempty_Ioo.mpr ht).image _
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds ht).filter_mono inf_le_left] with h hh hht
    exact ha.trans_le (csInf_le hb (mem_image_of_mem _ ⟨hh,hht⟩))
  · intro b hb'
    obtain ⟨x,hx,hxb⟩ := exists_lt_of_csInf_lt hne hb'
    obtain ⟨k,hk,rfl⟩ := hx
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hk.1).filter_mono inf_le_left] with h hh hhk
    exact ((lower_strictMono_base hφ t) ⟨hh,hhk.trans hk.2⟩ hk hhk).trans hxb
lemma upper_axis_tendsto {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : ContinuousOn φ (Ici 0)) {t : ℝ} (ht : 0<t) :
    Tendsto (fun h=>upper φ h t) (𝓝[>] 0) (𝓝 (axisUpper φ t)) := by
  have hb := (axis_bounded hφ hc ht).2
  have hne : ((fun h=>upper φ h t) '' Ioo 0 t).Nonempty :=
    (nonempty_Ioo.mpr ht).image _
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨x,hx,hax⟩ := exists_lt_of_lt_csSup hne ha
    obtain ⟨k,hk,rfl⟩ := hx
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hk.1).filter_mono inf_le_left] with h hh hhk
    exact hax.trans ((upper_strictAnti_base hφ t) ⟨hh,hhk.trans hk.2⟩ hk hhk)
  · intro b hb'
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds ht).filter_mono inf_le_left] with h hh hht
    exact (le_csSup hb (mem_image_of_mem _ ⟨hh,hht⟩)).trans_lt hb'

end QuinticLienard.ScalarArcs

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.BoundaryFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter Metric
open scoped Topology ContDiff
namespace QuinticLienard.GlobalODE
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem unique_on_open_interval (V : E → E) {U : Set E} (hU : IsOpen U)
    (hV : ContDiffOn ℝ 1 V U) {f g : ℝ → E} {a b c : ℝ}
    (hc : c ∈ Ioo a b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (V (f t)) t ∧ f t ∈ U)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (V (g t)) t ∧ g t ∈ U)
    (he : f c=g c) : EqOn f g (Ioo a b) := by
  intro t ht
  let A := (a+min t c)/2
  let B := (b+max t c)/2
  have hA : a<A ∧ A < min t c := by dsimp [A]; constructor <;> linarith [lt_min ht.1 hc.1]
  have hB : max t c < B ∧ B<b := by dsimp [B]; constructor <;> linarith [max_lt ht.2 hc.2]
  have hs : Icc A B ⊆ Ioo a b := fun _ h=>⟨hA.1.trans_le h.1,h.2.trans_lt hB.2⟩
  have hfc : ContinuousOn f (Icc A B) := fun x hx=>(hf x (hs hx)).1.continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc A B) := fun x hx=>(hg x (hs hx)).1.continuousAt.continuousWithinAt
  obtain ⟨W,K,L,hK,_,hW⟩ := exists_bounded_lipschitz_cutoff_on V
    ((isCompact_Icc.image_of_continuousOn hfc).union (isCompact_Icc.image_of_continuousOn hgc)) hU
    (by rintro _ (⟨x,hx,rfl⟩|⟨x,hx,rfl⟩); exact (hf x (hs hx)).2; exact (hg x (hs hx)).2) hV
  have hct : c ∈ Ioo A B := ⟨hA.2.trans_le (min_le_right _ _),(le_max_right _ _).trans_lt hB.1⟩
  have heq := ODE_solution_unique_of_mem_Icc (v:=fun _=>W) (s:=fun _=>(Set.univ : Set E))
    (fun _ _=>hK.lipschitzOnWith) hct hfc
    (fun x hx=>by rw [(hW (f x) (Or.inl (mem_image_of_mem _ (Ioo_subset_Icc_self hx)))).self_of_nhds]; exact (hf x (hs (Ioo_subset_Icc_self hx))).1)
    (fun _ _=>mem_univ _) hgc
    (fun x hx=>by rw [(hW (g x) (Or.inr (mem_image_of_mem _ (Ioo_subset_Icc_self hx)))).self_of_nhds]; exact (hg x (hs (Ioo_subset_Icc_self hx))).1)
    (fun _ _=>mem_univ _) he
  exact heq ⟨(hA.2.trans_le (min_le_left _ _)).le,((le_max_left _ _).trans_lt hB.1).le⟩
end QuinticLienard.GlobalODE
namespace QuinticLienard.AxisFlow
open SmoothFlow SmoothFlow.AlgebraicExpr ScaledProfile
lemma polynomial_eval (a : Fin 6 → ℝ) (z : ℝ×ℝ) : (polynomial a).eval z=poly a z.1 := by
  simp [polynomial,poly,X]
lemma polynomial_regular (a : Fin 6 → ℝ) (z : ℝ×ℝ) : (polynomial a).RegularAt z := by
  simp [polynomial,X,regular_pow]
lemma rhs_eval (a : Fin 6 → ℝ) (z : ℝ×ℝ) : (rhs a).eval z=z.1/(poly a z.1-z.2) := by
  simp [rhs,X,Y,polynomial_eval,div_eq_mul_inv,sub_eq_add_neg]
lemma rhs_regular (a : Fin 6 → ℝ) {z : ℝ×ℝ} (hz : z ∈ domain a) : (rhs a).RegularAt z := by
  simp only [rhs,regular_mul,regular_inv,regular_add,regular_const,polynomial_regular,true_and]
  simpa [domain,X,Y,polynomial_eval,sub_eq_add_neg] using hz
lemma domain_open (a : Fin 6 → ℝ) : IsOpen (domain a) := by
  apply isOpen_ne_fun
  · unfold poly
    fun_prop
  · fun_prop
lemma field_analytic (a : Fin 6 → ℝ) {z : ℝ×ℝ} (hz : z ∈ domain a) : ContDiffAt ℝ ω (field a) z := by
  have he := (rhs a).eval_analytic (rhs_regular a hz)
  change ContDiffAt ℝ ω (fun q : ℝ×ℝ=>(1,q.1/(poly a q.1-q.2))) z
  simpa only [rhs_eval] using (contDiffAt_const.prodMk he : ContDiffAt ℝ ω (fun q=>((1:ℝ),(rhs a).eval q)) z)
lemma local_flow (a : Fin 6 → ℝ) {z : ℝ×ℝ} (hz : z ∈ domain a) :
    ∃ f : ((ℝ×ℝ)×ℝ) → ℝ×ℝ, ContDiffAt ℝ ω f (z,0) ∧
      ∀ᶠ q in 𝓝 (z,(0:ℝ)), f (q.1,0)=q.1 ∧ HasDerivAt (fun s=>f (q.1,s)) (field a (f q)) q.2 := by
  let I : ℝ →L[ℝ] ℝ×ℝ := ContinuousLinearMap.inr ℝ ℝ ℝ
  let W : Path (ℝ×ℝ) → Path (ℝ×ℝ) := fun u=>constCLM (1,0)+pathMap I ((rhs a).onPaths u)
  have hp := AlgebraicExpr.path_properties (rhs a) (rhs_regular a hz)
  have hW : ContDiffAt ℝ ω W (constCLM z) := contDiffAt_const.add
    ((pathMap I).contDiff.contDiffAt.comp _ hp.2.1)
  apply exists_analytic_local_flow_eventually W (field a) z _ hW
  filter_upwards [hp.2.2] with u hu s
  simp only [W,ContinuousMap.add_apply,constCLM_apply,pathMap_apply,hu s,rhs_eval]
  simp [I,field]
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.BoundaryGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter Metric
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open PartialCalculus

theorem boundary_germ {V : (ℝ×ℝ) → ℝ×ℝ} {U : Set (ℝ×ℝ)}
    (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U)
    {y : ℝ×ℝ → ℝ} {t₀ A T : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 t₀) (hT : 0<T)
    (ha : ∀ x ∈ Ioo 0 T, ContDiffAt ℝ ω y (t₀,x))
    (he : ∀ t ∈ J, ∀ x ∈ Ioo 0 T,
      HasDerivAt (fun s=>(s,y (t,s))) (V (x,y (t,x))) x ∧ (x,y (t,x)) ∈ U)
    (hlim : Tendsto (fun x=>y (t₀,x)) (𝓝[>] 0) (𝓝 A))
    (hf : ∃ f : ((ℝ×ℝ)×ℝ) → ℝ×ℝ, ContDiffAt ℝ ω f ((0,A),0) ∧
      ∀ᶠ q in 𝓝 ((0,A),(0:ℝ)), f (q.1,0)=q.1 ∧
        HasDerivAt (fun s=>f (q.1,s)) (V (f q)) q.2)
    (hAU : (0,A) ∈ U) :
    ∃ G : ℝ×ℝ → ℝ, ContDiffAt ℝ ω G (t₀,0) ∧ G (t₀,0)=A ∧
      (∀ᶠ q in 𝓝 (t₀,(0:ℝ)), 0<q.2 → G q=y q) ∧
      ∃ δ ∈ Ioo 0 T, ∃ k : ℝ, 0<k ∧ first G (t₀,0)=k*first y (t₀,δ) := by
  obtain ⟨f,hfa,hfe⟩ := hf
  let e : (ℝ×ℝ)×ℝ := ((0,1),0)
  let F : ((ℝ×ℝ)×ℝ) → ℝ := fun q=>(f q).2
  have hFa : ContDiffAt ℝ ω F ((0,A),0) := hfa.snd
  have hD : direction e F ((0,A),0)=1 := by
    have hpath : HasDerivAt (fun s=>F ((0,s),0)) (direction e F ((0,A),0)) A := by
      simpa only [direction,e,Function.comp_def,id_eq] using hFa.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt A
        (((hasDerivAt_const A (0:ℝ)).prodMk (hasDerivAt_id A)).prodMk (hasDerivAt_const A (0:ℝ)))
    have heq : (fun s=>F ((0,s),0)) =ᶠ[𝓝 A] (fun s=>s) := by
      filter_upwards [((continuousAt_const.prodMk continuousAt_id).prodMk continuousAt_const).eventually hfe] with s hs
      exact congrArg Prod.snd hs.1
    exact (hpath.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id A)
  have hpos : ∀ᶠ q in 𝓝 ((0,A),(0:ℝ)), 0<direction e F q := by
    exact (direction_contDiffAt hFa e).continuousAt.eventually (eventually_gt_nhds (by simpa only [hD] using (zero_lt_one : (0:ℝ)<1)))
  have hfu : ∀ᶠ q in 𝓝 ((0,A),(0:ℝ)), f q ∈ U := by
    have hval := hfe.self_of_nhds.1
    exact hfa.continuousAt.eventually (hU.mem_nhds (by simpa only [hval] using hAU))
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp
    ((hfa.eventually (by simp)).and (hfe.and (hpos.and hfu)))
  have hzl : Tendsto (fun x : ℝ=>(x,y (t₀,x))) (𝓝[>] 0) (𝓝 (0,A)) :=
    ((continuousAt_id : ContinuousAt (fun x : ℝ=>x) 0).tendsto.mono_left inf_le_left).prodMk_nhds hlim
  have hzsmall : ∀ᶠ x in 𝓝[>] (0:ℝ), dist (x,y (t₀,x)) (0,A)<ρ/2 :=
    hzl (Metric.ball_mem_nhds _ (by linarith))
  have hex : ∀ᶠ x in 𝓝[>] (0:ℝ), 0<x ∧ x<T ∧ x<ρ/4 ∧ dist (x,y (t₀,x)) (0,A)<ρ/2 := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hT).filter_mono inf_le_left,
      (eventually_lt_nhds (show (0:ℝ)<ρ/4 by linarith)).filter_mono inf_le_left,hzsmall] with x hx hxT hxρ hxz
    exact ⟨hx,hxT,hxρ,hxz⟩
  obtain ⟨δ,hδ,hδT,hδρ,hδz⟩ := hex.exists
  have hzcont : ContinuousAt (fun t : ℝ=>(δ,y (t,δ))) t₀ := continuousAt_const.prodMk
    ((ha δ ⟨hδ,hδT⟩).continuousAt.comp (f:=fun t : ℝ=>(t,δ)) (continuousAt_id.prodMk continuousAt_const))

  have hzN' : ∀ᶠ t in 𝓝 t₀, dist (δ,y (t,δ)) (0,A)<ρ/2 :=
    (hzcont.dist continuousAt_const).eventually (eventually_lt_nhds hδz)
  let G : ℝ×ℝ → ℝ := fun q=>F ((δ,y (q.1,δ)),q.2-δ)
  have hnear (t x : ℝ) (ht : dist (δ,y (t,δ)) (0,A)<ρ/2) (hx : |x|<2*δ) :
      ((δ,y (t,δ)),x-δ) ∈ ball ((0,A),0) ρ := by
    rw [mem_ball,Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
    constructor
    · linarith
    · have hb := abs_le.mp (le_of_lt hx)
      rw [abs_lt]
      constructor <;> linarith
  have hzero := hball (hnear t₀ 0 hδz (by simpa only [abs_zero] using mul_pos (by norm_num : (0:ℝ)<2) hδ))
  have hinner : ContDiffAt ℝ ω (fun q : ℝ×ℝ=>((δ,y (q.1,δ)),q.2-δ)) (t₀,0) :=
    (contDiffAt_const.prodMk ((ha δ ⟨hδ,hδT⟩).comp (t₀,(0:ℝ))
      (contDiffAt_fst.prodMk contDiffAt_const))).prodMk (contDiffAt_snd.sub contDiffAt_const)
  have hGF : ContDiffAt ℝ ω F ((δ,y (t₀,δ)),0-δ) := hzero.1.snd
  have hGa : ContDiffAt ℝ ω G (t₀,0) := hGF.comp (f:=fun q : ℝ×ℝ=>((δ,y (q.1,δ)),q.2-δ)) (t₀,0) hinner
  have hag : ∀ᶠ q in 𝓝 (t₀,(0:ℝ)), 0<q.2 → G q=y q := by
    have hpN : ∀ᶠ t in 𝓝 t₀, t ∈ J ∧ dist (δ,y (t,δ)) (0,A)<ρ/2  := (show ∀ᶠ t in 𝓝 t₀, t ∈ J from hJ).and hzN'
    have hdN : ∀ᶠ x in 𝓝 (0:ℝ), |x|<δ := (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hδ)
    filter_upwards [continuousAt_fst.eventually hpN,continuousAt_snd.eventually hdN] with q hq hqx hx
    let γ : ℝ → ℝ×ℝ := fun s=>(s,y (q.1,s))
    let ψ : ℝ → ℝ×ℝ := fun s=>f ((δ,y (q.1,δ)),s-δ)
    have hdomain : ∀ s ∈ Ioo 0 (min T (2*δ)), |s|<2*δ := by
      intro s hs
      simpa only [abs_of_pos hs.1] using hs.2.trans_le (min_le_right _ _)
    have hc : δ ∈ Ioo 0 (min T (2*δ)) := ⟨hδ,lt_min hδT (by linarith)⟩
    have heq := GlobalODE.unique_on_open_interval V hU hV hc
      (fun s hs=>he q.1 hq.1 s ⟨hs.1,hs.2.trans_le (min_le_left _ _)⟩)
      (fun s hs=>by
        have hfq := hball (hnear q.1 s hq.2 (hdomain s hs))
        refine ⟨?_,hfq.2.2.2⟩
        have hd : HasDerivAt (fun v=>f ((δ,y (q.1,δ)),v)) (V (f ((δ,y (q.1,δ)),s-δ))) (s-δ) := hfq.2.1.2
        simpa only [one_smul,Function.comp_def,id_eq] using hd.scomp (h:=fun v : ℝ=>v-δ) s ((hasDerivAt_id s).sub_const δ))
      (show γ δ=ψ δ by
        dsimp only [γ,ψ]
        rw [sub_self]
        exact (hball (hnear q.1 δ hq.2 (by rw [abs_of_pos hδ]; linarith))).2.1.1.symm)
    have hxx : q.2 ∈ Ioo 0 (min T (2*δ)) := ⟨hx,lt_min
      ((lt_of_le_of_lt (le_abs_self _) hqx).trans hδT) (by linarith [le_abs_self q.2])⟩
    exact (congrArg Prod.snd (heq hxx)).symm
  have hGlim : Tendsto (fun x=>G (t₀,x)) (𝓝[>] 0) (𝓝 (G (t₀,0))) :=
    ((hGa.continuousAt.comp (continuousAt_const.prodMk continuousAt_id))).tendsto.mono_left inf_le_left
  have heq0 : (fun x=>G (t₀,x)) =ᶠ[𝓝[>] 0] (fun x=>y (t₀,x)) := by
    filter_upwards [((continuousAt_const.prodMk continuousAt_id).eventually hag).filter_mono inf_le_left,
      self_mem_nhdsWithin] with x hx hx0
    exact hx hx0
  have hzero' := hzero
  simp only [zero_sub] at hzero'
  refine ⟨G,hGa,tendsto_nhds_unique hGlim (hlim.congr' heq0.symm),hag,δ,⟨hδ,hδT⟩,
    direction e F ((δ,y (t₀,δ)),-δ),hzero'.2.2.1,?_⟩
  have hdy := first_hasDerivAt ((ha δ ⟨hδ,hδT⟩).differentiableAt (by simp))
  have hdG := hzero'.1.snd.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt t₀
    (((hasDerivAt_const t₀ δ).prodMk hdy).prodMk (hasDerivAt_const t₀ (-δ)))
  have heqD : ((0,first y (t₀,δ)),0)=first y (t₀,δ) • e := by ext <;> simp [e]
  have hdval : first G (t₀,0)=fderiv ℝ F ((δ,y (t₀,δ)),-δ) ((0,first y (t₀,δ)),0) := by
    exact (first_hasDerivAt (hGa.differentiableAt (by simp))).unique (by simpa only [G,F,Function.comp_def,zero_sub] using hdG)
  rw [hdval,heqD,map_smul]
  simp only [smul_eq_mul, direction]
  ring
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScaledProfile ScalarArcs ArcFamilies PartialCalculus
lemma φ_continuous (a : Fin 6 → ℝ) : Continuous (φ a) := by
  unfold φ poly root
  fun_prop
lemma φ_smooth (a : Fin 6 → ℝ) : ContDiffOn ℝ 1 (φ a) (Ioi 0) := by
  intro h hh
  exact (((QuinticProfile.analytic a (q:=((0:ℝ),h)) hh).comp h
    (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
lemma φ_square (a : Fin 6 → ℝ) {x : ℝ} (hx : 0≤x) : φ a (x^2/2)=poly a x := by
  have he : 2*(x^2/2)=x^2 := by ring
  simp only [φ,root,he,Real.sqrt_sq hx]
lemma branch_analytic (a : Fin 6 → ℝ) (u : Bool) {t x : ℝ} (hx : 0<x) (ht : x^2/2<t) :
    ContDiffAt ℝ ω (branch a u) (t,x) := by
  have hh : 0<x^2/2 := div_pos (sq_pos_of_pos hx) (by norm_num)
  obtain ⟨hl,hr⟩ := PositiveVariation.endpoints (QuinticProfile.profile a)
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh ht
  have hc : ContDiffAt ℝ ω (fun q : ℝ×ℝ=>(((0:ℝ),q.1),q.2^2/2)) (t,x) := by fun_prop
  cases u
  · exact hl.comp (t,x) hc
  · exact hr.comp (t,x) hc
lemma branch_equation (a : Fin 6 → ℝ) (u : Bool) {t x : ℝ} (hx : 0<x) (ht : x^2/2<t) :
    HasDerivAt (fun s=>(s,branch a u (t,s))) (field a (x,branch a u (t,x))) x ∧
      (x,branch a u (t,x)) ∈ domain a := by
  have hh : 0<x^2/2 := div_pos (sq_pos_of_pos hx) (by norm_num)
  obtain ⟨hl,hr⟩ := PositiveVariation.base_derivatives (QuinticProfile.profile a)
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh ht
  have hd : HasDerivAt (fun s : ℝ=>s^2/2) x x := by convert! ((hasDerivAt_id x).pow 2).div_const 2 using 1; simp
  have hu := chosen_arch (positive_arch_exists (φ_smooth a) hh ht)
  have he : HasDerivAt (fun s=>branch a u (t,s)) (x/(poly a x-branch a u (t,x))) x := by
    cases u
    · convert! hl.comp x hd using 1
      change x/(poly a x-branch a false (t,x))=1/(φ a (x^2/2)-_) * x
      rw [φ_square a hx.le]
      change x/(poly a x-branch a false (t,x))=1/(poly a x-branch a false (t,x))*x
      ring
    · convert! hr.comp x hd using 1
      change x/(poly a x-branch a true (t,x))=1/(φ a (x^2/2)-_) * x
      rw [φ_square a hx.le]
      change x/(poly a x-branch a true (t,x))=1/(poly a x-branch a true (t,x))*x
      ring
  refine ⟨(hasDerivAt_id x).prodMk he,?_⟩
  cases u
  · exact ne_of_gt (by change 0<poly a x-_ ; rw [←φ_square a hx.le]; exact sub_pos.mpr hu.lower_transverse)
  · exact ne_of_lt (by change poly a x-_<0 ; rw [←φ_square a hx.le]; exact sub_neg.mpr hu.upper_transverse)
lemma branch_peak_sign (a : Fin 6 → ℝ) (u : Bool) {t x : ℝ} (hx : 0<x) (ht : x^2/2<t) :
    if u then 0<first (branch a u) (t,x) else first (branch a u) (t,x)<0 := by
  have hh : 0<x^2/2 := div_pos (sq_pos_of_pos hx) (by norm_num)
  obtain ⟨hl,hr⟩ := PositiveVariation.peak_signs (QuinticProfile.profile a)
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh ht
  have hd := (first_hasDerivAt ((branch_analytic a u hx ht).differentiableAt (by simp))).deriv
  cases u
  · change first (branch a false) (t,x)<0
    rw [←hd]
    exact hl
  · change 0<first (branch a true) (t,x)
    rw [←hd]
    exact hr
lemma branch_tendsto (a : Fin 6 → ℝ) (u : Bool) {t : ℝ} (ht : 0<t) :
    Tendsto (fun x=>branch a u (t,x)) (𝓝[>] 0) (𝓝 (axisEndpoint a u t)) := by
  have hc : Tendsto (fun x : ℝ=>x^2/2) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    have hh := (((continuousAt_id.pow 2).div_const 2 : ContinuousAt (fun x : ℝ=>x^2/2) 0).tendsto).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from inf_le_left)
    simpa only [Pi.pow_apply,id_eq,zero_pow (by norm_num : (2:ℕ)≠0),zero_div] using hh
  have he : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), x^2/2 ∈ Ioi (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_pos (sq_pos_of_pos (show 0<x from hx)) (by norm_num)
  have hs : Tendsto (fun x : ℝ=>x^2/2) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hc,he⟩
  cases u
  · exact (lower_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn ht).comp hs
  · exact (upper_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn ht).comp hs

theorem endpoint_germ (a : Fin 6 → ℝ) (u : Bool) {t : ℝ} (ht : 0<t)
    (htr : axisEndpoint a u t≠poly a 0) :
    ∃ G : ℝ×ℝ → ℝ, ContDiffAt ℝ ω G (t,0) ∧ G (t,0)=axisEndpoint a u t ∧
      (∀ᶠ q in 𝓝 (t,(0:ℝ)), 0<q.2 → G q=branch a u q) ∧
      (if u then 0<first G (t,0) else first G (t,0)<0) := by
  let T := Real.sqrt t
  have hT : 0<T := Real.sqrt_pos.mpr ht
  have hbound {x : ℝ} (hx : x ∈ Ioo 0 T) : x^2/2<t/2 := by
    have hs : x^2<T^2 := sq_lt_sq₀ hx.1.le hT.le |>.mpr hx.2
    dsimp only [T] at hs
    rw [Real.sq_sqrt ht.le] at hs
    linarith
  have hAU : (0,axisEndpoint a u t) ∈ domain a := sub_ne_zero.mpr htr.symm
  obtain ⟨G,hG,h0,he,δ,hδ,k,hk,hD⟩ := boundary_germ (V:=field a) (domain_open a)
    (fun z hz=>(field_analytic a hz).of_le (by simp) |>.contDiffWithinAt)
    (y:=branch a u) (J:=Ioi (t/2)) (Ioi_mem_nhds (by linarith)) hT
    (fun x hx=>branch_analytic a u hx.1 (by linarith [hbound hx]))
    (fun p hp x hx=>branch_equation a u hx.1 ((hbound hx).trans hp))
    (branch_tendsto a u ht) (local_flow a hAU) hAU
  refine ⟨G,hG,h0,he,?_⟩
  have hs := branch_peak_sign a u hδ.1 (show δ^2/2<t by linarith [hbound hδ])
  cases u
  · simp only [Bool.false_eq_true,↓reduceIte] at hs ⊢
    rw [hD]
    exact mul_neg_of_pos_of_neg hk hs
  · simp only [↓reduceIte] at hs ⊢
    rw [hD]
    exact mul_pos hk hs
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScalarArcs ScaledProfile PartialCalculus
lemma endpoint_germ_eq {a : Fin 6 → ℝ} {u : Bool} {t : ℝ} {G : ℝ×ℝ → ℝ}
    (ht : 0<t) (hG : ContDiffAt ℝ ω G (t,0))
    (he : ∀ᶠ q in 𝓝 (t,(0:ℝ)), 0<q.2 → G q=branch a u q) :
    ∀ᶠ s in 𝓝 t, G (s,0)=axisEndpoint a u s := by
  have hGc : ∀ᶠ s in 𝓝 t, ContinuousAt G (s,0) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually (hG.eventually (by simp))] with s hs
    exact hs.continuousAt
  filter_upwards [eventually_gt_nhds ht,he.curry_nhds,hGc] with s hs hse hsc
  have hlim : Tendsto (fun x=>G (s,x)) (𝓝[>] 0) (𝓝 (G (s,0))) :=
    (hsc.comp (f:=fun x : ℝ=>(s,x)) (continuousAt_const.prodMk continuousAt_id)).tendsto.mono_left inf_le_left
  have hEq : (fun x=>G (s,x)) =ᶠ[𝓝[>] 0] (fun x=>branch a u (s,x)) := by
    filter_upwards [hse.filter_mono inf_le_left,self_mem_nhdsWithin] with x hx hx0
    exact hx hx0
  exact tendsto_nhds_unique hlim ((branch_tendsto a u hs).congr' hEq.symm)
lemma axisEndpoint_analytic (a : Fin 6 → ℝ) (u : Bool) {t : ℝ} (ht : 0<t)
    (htr : axisEndpoint a u t≠poly a 0) : ContDiffAt ℝ ω (axisEndpoint a u) t := by
  obtain ⟨G,hG,_,he,_⟩ := endpoint_germ a u ht htr
  exact (hG.comp t (contDiffAt_id.prodMk contDiffAt_const)).congr_of_eventuallyEq
    ((endpoint_germ_eq ht hG he).mono fun _ h=>h.symm)
lemma axisEndpoint_sign (a : Fin 6 → ℝ) (u : Bool) {t : ℝ} (ht : 0<t)
    (htr : axisEndpoint a u t≠poly a 0) :
    if u then 0<deriv (axisEndpoint a u) t else deriv (axisEndpoint a u) t<0 := by
  obtain ⟨G,hG,_,he,hd⟩ := endpoint_germ a u ht htr
  have hde : deriv (axisEndpoint a u) t=first G (t,0) :=
    ((first_hasDerivAt (hG.differentiableAt (by simp))).congr_of_eventuallyEq
      ((endpoint_germ_eq ht hG he).mono fun _ h=>h.symm)).deriv
  rwa [hde]

lemma endpoint_peak_order (a : Fin 6 → ℝ) {h s t : ℝ} (hh : 0<h) (hs : h<s) (hst : s≤t) :
    endpoint a false h t≤endpoint a false h s ∧ endpoint a true h s≤endpoint a true h t := by
  have ha (u : Bool) (p : ℝ) (hp : h<p) : ContDiffAt ℝ ω (fun q=>endpoint a u h q) p := by
    obtain ⟨hl,hr⟩ := PositiveVariation.endpoints (QuinticProfile.profile a)
      (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh hp
    cases u
    · exact hl.comp p ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)
    · exact hr.comp p ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)
  have hd (p : ℝ) (hp : h<p) := PositiveVariation.peak_signs (QuinticProfile.profile a)
      (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh hp
  have hl : AntitoneOn (endpoint a false h) (Ioi h) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi h)
      (fun p hp=>(ha false p hp).continuousAt.continuousWithinAt)
      (fun p hp=>(ha false p (interior_subset hp)).differentiableAt (by simp) |>.differentiableWithinAt)
    intro p hp
    exact (hd p (interior_subset hp)).1.le
  have hr : MonotoneOn (endpoint a true h) (Ioi h) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi h)
      (fun p hp=>(ha true p hp).continuousAt.continuousWithinAt)
      (fun p hp=>(ha true p (interior_subset hp)).differentiableAt (by simp) |>.differentiableWithinAt)
    intro p hp
    exact (hd p (interior_subset hp)).2.le
  exact ⟨hl hs (hs.trans_le hst) hst,hr hs (hs.trans_le hst) hst⟩
lemma axis_peak_order (a : Fin 6 → ℝ) {s t : ℝ} (hs : 0<s) (hst : s≤t) :
    axisEndpoint a false t≤axisEndpoint a false s ∧ axisEndpoint a true s≤axisEndpoint a true t := by
  have hE : ∀ᶠ h in 𝓝[>] (0:ℝ), endpoint a false h t≤endpoint a false h s ∧
      endpoint a true h s≤endpoint a true h t := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hs).filter_mono inf_le_left] with h hh hs'
    exact endpoint_peak_order a hh hs' hst
  have hls := lower_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn hs
  have hlt := lower_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn (hs.trans_le hst)
  have hrs := upper_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn hs
  have hrt := upper_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn (hs.trans_le hst)
  exact ⟨le_of_tendsto_of_tendsto hlt hls (hE.mono fun _ h=>h.1),
    le_of_tendsto_of_tendsto hrs hrt (hE.mono fun _ h=>h.2)⟩

lemma transversePeaks_upper (a : Fin 6 → ℝ) {s t : ℝ} (hs : s ∈ transversePeaks a) (hst : s≤t) :
    t ∈ transversePeaks a := by
  have he := axis_peak_order a hs.1 hst
  exact ⟨hs.1.trans_le hst,he.1.trans_lt hs.2.1,hs.2.2.trans_le he.2⟩
lemma transversePeaks_open (a : Fin 6 → ℝ) : IsOpen (transversePeaks a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  have hl := (axisEndpoint_analytic a false ht.1 ht.2.1.ne).continuousAt
  have hr := (axisEndpoint_analytic a true ht.1 ht.2.2.ne').continuousAt
  exact (eventually_gt_nhds ht.1).and
    ((hl.eventually_lt continuousAt_const ht.2.1).and (continuousAt_const.eventually_lt hr ht.2.2))
lemma transversePeaks_ordConnected (a : Fin 6 → ℝ) : OrdConnected (transversePeaks a) := by
  constructor
  intro s hs t _ x hx
  exact transversePeaks_upper a hs hx.1
lemma axisWidth_analytic (a : Fin 6 → ℝ) {t : ℝ} (ht : t ∈ transversePeaks a) :
    ContDiffAt ℝ ω (axisWidth a) t :=
  ((axisEndpoint_analytic a true ht.1 ht.2.2.ne').sub (axisEndpoint_analytic a false ht.1 ht.2.1.ne)).div_const 2
lemma axisWidth_pos_deriv (a : Fin 6 → ℝ) {t : ℝ} (ht : t ∈ transversePeaks a) :
    0<axisWidth a t ∧ 0<deriv (axisWidth a) t ∧ |axisCenter a t|<axisWidth a t ∧
      |deriv (axisCenter a) t/deriv (axisWidth a) t|<1 := by
  have hl := axisEndpoint_sign a false ht.1 ht.2.1.ne
  have hr := axisEndpoint_sign a true ht.1 ht.2.2.ne'
  simp only [Bool.false_eq_true,↓reduceIte] at hl hr
  have hld := (axisEndpoint_analytic a false ht.1 ht.2.1.ne).differentiableAt (by simp)
  have hrd := (axisEndpoint_analytic a true ht.1 ht.2.2.ne').differentiableAt (by simp)
  have hwd : deriv (axisWidth a) t=(deriv (axisEndpoint a true) t-deriv (axisEndpoint a false) t)/2 :=
    ((hrd.hasDerivAt.sub hld.hasDerivAt).div_const 2).deriv
  have hcd : deriv (axisCenter a) t=(deriv (axisEndpoint a true) t+deriv (axisEndpoint a false) t)/2 :=
    (((hrd.hasDerivAt.add hld.hasDerivAt).div_const 2).sub_const (poly a 0)).deriv
  have hp : 0<axisWidth a t := by dsimp [axisWidth]; linarith [ht.2.1,ht.2.2]
  refine ⟨hp,by rw [hwd]; linarith,?_,?_⟩
  · rw [abs_lt]
    dsimp [axisCenter,axisWidth]
    constructor <;> linarith [ht.2.1,ht.2.2]
  · rw [hwd,hcd]
    rw [abs_div,abs_of_pos (show 0<(deriv (axisEndpoint a true) t-deriv (axisEndpoint a false) t)/2 by linarith),div_lt_one]
    · rw [abs_lt]; constructor <;> linarith
    · linarith
lemma axisWidth_strictMono (a : Fin 6 → ℝ) : StrictMonoOn (axisWidth a) (transversePeaks a) := by
  apply strictMonoOn_of_deriv_pos (convex_iff_ordConnected.mpr (transversePeaks_ordConnected a))
    (fun t ht=>(axisWidth_analytic a ht).continuousAt.continuousWithinAt)
  intro t ht
  exact (axisWidth_pos_deriv a (interior_subset ht)).2.1
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisWidthGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScalarArcs ScaledProfile PartialCalculus PositiveWidth

lemma axisPeak_spec (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) :
    axisPeak a r ∈ transversePeaks a ∧ axisWidth a (axisPeak a r)=r :=
  Classical.epsilon_spec hr
lemma axisPeak_eq (a : Fin 6 → ℝ) {r t : ℝ} (ht : t ∈ transversePeaks a) (he : axisWidth a t=r) :
    axisPeak a r=t := by
  have hs := axisPeak_spec a (mem_image_of_mem (axisWidth a) ht)
  rw [he] at hs
  exact (axisWidth_strictMono a).injOn hs.1 ht (hs.2.trans he.symm)

theorem width_germ (a : Fin 6 → ℝ) {t : ℝ} (ht : t ∈ transversePeaks a) :
    ∃ Y G : ℝ×ℝ → ℝ,
      ContDiffAt ℝ ω Y (0,axisWidth a t) ∧ ContDiffAt ℝ ω G (0,axisWidth a t) ∧
      Y (0,axisWidth a t)=t ∧ G (0,axisWidth a t)=axisCenter a t ∧
      (∀ᶠ r in 𝓝 (axisWidth a t), r ∈ axisWidths a ∧ Y (0,r)=axisPeak a r ∧ G (0,r)=axisM a r) ∧
      (∀ᶠ q in 𝓝 ((0:ℝ),axisWidth a t), 0<q.1 →
        Y q=peakAtWidth (QuinticProfile.profile a) ((0,q.1^2/2),q.2) ∧
        G q=QuinticFit.M a (q.1^2/2,q.2)) := by
  obtain ⟨l,hla,hl0,hle,_⟩ := endpoint_germ a false ht.1 ht.2.1.ne
  obtain ⟨b,hba,hb0,hbe,_⟩ := endpoint_germ a true ht.1 ht.2.2.ne'
  have hle0 := endpoint_germ_eq ht.1 hla hle
  have hbe0 := endpoint_germ_eq ht.1 hba hbe
  let W : ℝ×ℝ → ℝ := fun q=>(b (q.2,q.1)-l (q.2,q.1))/2
  have hWa : ContDiffAt ℝ ω W (0,t) := ((hba.sub hla).div_const 2).comp (0,t)
    (contDiffAt_snd.prodMk contDiffAt_fst)
  have hW0 : W (0,t)=axisWidth a t := by dsimp [W,axisWidth]; rw [hl0,hb0]
  have hWslice : (fun s=>W (0,s)) =ᶠ[𝓝 t] axisWidth a := by
    filter_upwards [hle0,hbe0] with s hls hbs
    simp only [W,axisWidth,hls,hbs]
  have hWd : HasDerivAt (fun s=>W (0,s)) (deriv (axisWidth a) t) t :=
    ((axisWidth_analytic a ht).differentiableAt (by simp)).hasDerivAt.congr_of_eventuallyEq hWslice
  obtain ⟨Y,hY,hY0,hYe⟩ := ArcEndpoints.level_hit hWa hWd hW0 (axisWidth_pos_deriv a ht).2.1.ne'
  let G : ℝ×ℝ → ℝ := fun q=>(b (Y q,q.1)+l (Y q,q.1))/2-poly a q.1
  have hYa : ContDiffAt ℝ ω (fun q=>(Y q,q.1)) (0,axisWidth a t) := hY.prodMk contDiffAt_fst
  have hGa : ContDiffAt ℝ ω G (0,axisWidth a t) := by
    have hh : ContDiffAt ℝ ω (fun q=>(b q+l q)/2) (t,0) := (hba.add hla).div_const 2
    have hc : ContDiffAt ℝ ω (fun q : ℝ×ℝ=>poly a q.1) (0,axisWidth a t) := by unfold poly; fun_prop
    exact (show ContDiffAt ℝ ω (fun q=>(b (Y q,q.1)+l (Y q,q.1))/2) (0,axisWidth a t) from
      (by
        have hh' : ContDiffAt ℝ ω (fun q=>(b q+l q)/2) (Y (0,axisWidth a t),0) := by rw [hY0]; exact hh
        exact hh'.comp (f:=fun q : ℝ×ℝ=>(Y q,q.1)) (0,axisWidth a t) hYa)).sub hc
  have hG0 : G (0,axisWidth a t)=axisCenter a t := by dsimp [G,axisCenter]; rw [hY0,hl0,hb0]
  have hYlim : ContinuousAt (fun r=>Y (0,r)) (axisWidth a t) :=
    hY.continuousAt.comp (f:=fun r : ℝ=>(0,r)) (continuousAt_const.prodMk continuousAt_id)
  have hYt : Tendsto (fun r=>Y (0,r)) (𝓝 (axisWidth a t)) (𝓝 t) := by simpa only [hY0] using hYlim.tendsto
  have hYtrans : ∀ᶠ r in 𝓝 (axisWidth a t), Y (0,r) ∈ transversePeaks a :=
    hYlim.eventually ((transversePeaks_open a).mem_nhds (by simpa only [hY0] using ht))
  have hslice : ∀ᶠ r in 𝓝 (axisWidth a t), r ∈ axisWidths a ∧ Y (0,r)=axisPeak a r ∧ G (0,r)=axisM a r := by
    have hNb : ∀ᶠ r in 𝓝 (axisWidth a t), b (Y (0,r),0)=axisEndpoint a true (Y (0,r)) := hYt.eventually hbe0
    have hNl : ∀ᶠ r in 𝓝 (axisWidth a t), l (Y (0,r),0)=axisEndpoint a false (Y (0,r)) := hYt.eventually hle0
    filter_upwards [hYtrans,(continuousAt_const.prodMk continuousAt_id).eventually hYe,hNb,hNl] with r htr he hb hl
    have hwr : axisWidth a (Y (0,r))=r := by simpa only [W,axisWidth,id_eq,hb,hl] using he
    have hpeak := (axisPeak_eq a htr hwr).symm
    refine ⟨⟨Y (0,r),htr,hwr⟩,hpeak,?_⟩
    dsimp only [G,axisM,axisCenter]
    rw [hb,hl,hpeak]
  have hposr : 0<axisWidth a t := (axisWidth_pos_deriv a ht).1
  have hheight : ∀ᶠ q in 𝓝 ((0:ℝ),axisWidth a t), q.1^2/2<Y q :=
    ((continuousAt_fst.pow 2).div_const 2).eventually_lt hY.continuousAt (by simpa only [Pi.pow_apply,zero_pow (by norm_num : (2:ℕ)≠0),zero_div,hY0] using ht.1)
  have hposEq : ∀ᶠ q in 𝓝 ((0:ℝ),axisWidth a t), 0<q.1 →
      Y q=peakAtWidth (QuinticProfile.profile a) ((0,q.1^2/2),q.2) ∧
      G q=QuinticFit.M a (q.1^2/2,q.2) := by
    have hNl := hYa.continuousAt.eventually (by simpa only [hY0] using hle)
    have hNb := hYa.continuousAt.eventually (by simpa only [hY0] using hbe)
    filter_upwards [hYe,hNl,hNb,hheight,continuousAt_snd.eventually (eventually_gt_nhds hposr)] with q hq hl hb hh hr hx
    have hh0 : 0<q.1^2/2 := div_pos (sq_pos_of_pos hx) (by norm_num)
    have hwr : widthFamily (QuinticProfile.profile a) (((0:ℝ),Y q),q.1^2/2)=q.2 := by
      have he := hq
      simp only [W,hb hx,hl hx,branch,endpoint,Bool.false_eq_true,↓reduceIte] at he
      exact he
    have hp := peak_eq (QuinticProfile.profile a) (fun _ h=>QuinticProfile.analytic a h)
      (QuinticProfile.local_flow a) hr hh0 hh hwr
    refine ⟨hp.symm,?_⟩
    dsimp only [G,QuinticFit.M,PositiveTransport.M,midpointAtWidth,midpointFamily]
    rw [hp]
    rw [hb hx,hl hx]
    change (endpoint a true (q.1^2/2) (Y q)+endpoint a false (q.1^2/2) (Y q))/2-poly a q.1=
      ScalarArcs.midpoint (φ a) (q.1^2/2) (Y q)
    dsimp only [ScalarArcs.midpoint]
    rw [φ_square a hx.le]
    rfl
  exact ⟨Y,G,hY,hGa,hY0,hG0,hslice,hposEq⟩
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisWidthRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScalarArcs ScaledProfile PartialCalculus PositiveWidth
lemma axisWidths_open (a : Fin 6 → ℝ) : IsOpen (axisWidths a) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro r ⟨t,ht,rfl⟩
  obtain ⟨Y,G,_,_,_,_,he,_⟩ := width_germ a ht
  exact he.mono fun _ h=>h.1
lemma axisM_analytic (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) : ContDiffAt ℝ ω (axisM a) r := by
  obtain ⟨t,ht,rfl⟩ := hr
  obtain ⟨Y,G,_,hG,_,_,he,_⟩ := width_germ a ht
  exact (hG.comp _ (contDiffAt_const.prodMk contDiffAt_id)).congr_of_eventuallyEq (he.mono fun _ h=>h.2.2.symm)
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisZeros
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open PartialCalculus QuadraticCoordinates QuadraticFit RealAnalysis

lemma matchingDomain_open (a b : Fin 6 → ℝ) : IsOpen (matchingDomain a b) :=
  (axisWidths_open a).inter (axisWidths_open b)
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CoefficientCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
lemma reflectX_poly (a : Fin 6 → ℝ) (x : ℝ) : poly (reflectX a) x=poly a (-x) := by
  simp [reflectX,poly]
  ring
end QuinticLienard.ScaledProfile

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.FiniteFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard.GlobalODE
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
theorem analytic_cutoff_along_compact_solution [FiniteDimensional ℝ E]
    (V : E → E) {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U)
    (hloc : ∀ x ∈ U, ∃ f : E × ℝ → E, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ p in 𝓝 (x,(0:ℝ)), f (p.1,0) = p.1 ∧
        HasDerivAt (fun t => f (p.1,t)) (V (f p)) p.2)
    {γ : ℝ → E} {a b c : ℝ} (ha : a < c) (hb : c < b)
    (hγ : Continuous γ) (hγU : ∀ y ∈ Icc a b, γ y ∈ U)
    (hγd : ∀ y ∈ Icc a b, HasDerivAt γ (V (γ y)) y) :
    ∃ (W : E → E) (K L : ℝ≥0) (hK : LipschitzWith K W) (hL : ∀ x, ‖W x‖ ≤ L),
      (∀ y ∈ Icc a b, flow W hK hL (γ c) (y-c) = γ y) ∧
      (∀ y ∈ Icc a b, ContDiffAt ℝ ω (fun p : E × ℝ=>flow W hK hL p.1 p.2) (γ c,y-c)) ∧
      ∀ y ∈ Icc a b, ∀ᶠ p : E × ℝ in 𝓝 (γ c,y-c),
        W (flow W hK hL p.1 p.2)=V (flow W hK hL p.1 p.2) := by
  obtain ⟨W,K,L,hK,hL,hW⟩ := exists_bounded_lipschitz_cutoff_on V
    (isCompact_Icc.image hγ) hU (by rintro _ ⟨y,hy,rfl⟩; exact hγU y hy) hV
  let f : E × ℝ → E := fun p => flow W hK hL p.1 p.2
  have hmatch : ∀ y ∈ Icc a b, f (γ c,y-c) = γ y := by
    apply ODE_solution_unique_of_mem_Icc
      (v := fun _ => W) (s := fun _ => Set.univ) (K := K)
      (fun _ _ => hK.lipschitzOnWith) ⟨ha,hb⟩
      ((continuous_flow W hK hL).comp (by fun_prop)).continuousOn
      _ (fun _ _ => mem_univ _) hγ.continuousOn _ (fun _ _ => mem_univ _)
      (by simp)
    · intro y _
      simpa [f,Function.comp_def] using
        (flow_deriv W hK hL (γ c) (y-c)).scomp y ((hasDerivAt_id y).sub_const c)
    · intro y hy
      rw [(hW (γ y) ⟨y,Ioo_subset_Icc_self hy,rfl⟩).self_of_nhds]
      exact hγd y (Ioo_subset_Icc_self hy)
  have hlocalW (y : ℝ) (hy : y ∈ Icc a b) :
      ContDiffAt ℝ ω f (γ y,0) := by
    obtain ⟨g,hgd,hge⟩ := hloc (γ y) (hγU y hy)
    have hg0 : g (γ y,0) = γ y := hge.self_of_nhds.1
    have heV : ∀ᶠ p in 𝓝 (γ y,(0:ℝ)), W (g p) = V (g p) := by
      have ht := hgd.continuousAt.tendsto
      rw [hg0] at ht
      exact ht.eventually (hW (γ y) ⟨y,hy,rfl⟩)
    have heq : g =ᶠ[𝓝 (γ y,(0:ℝ))] f := by
      apply local_family_eq W hK hL (γ y) g
      filter_upwards [hge,heV] with p hp hp'
      exact ⟨hp.1,hp' ▸ hp.2⟩
    exact hgd.congr_of_eventuallyEq heq.symm
  have hd : ∀ y ∈ Icc a b, ContDiffAt ℝ ω f (γ c,y-c) := by
    have hh := analytic_flow_on_trajectory W hK hL (γ c)
      (I := Icc (a-c) (b-c)) isPreconnected_Icc
      (show (0:ℝ) ∈ Icc (a-c) (b-c) by constructor <;> linarith)
      (fun s hs => by
        have hs' : s+c ∈ Icc a b := by constructor <;> linarith [hs.1,hs.2]
        have heq : flow W hK hL (γ c) s = γ (s+c) := by
          simpa [f] using hmatch (s+c) hs'
        rw [heq]
        exact hlocalW (s+c) hs')
    exact fun y hy => hh (y-c) (by constructor <;> linarith [hy.1,hy.2])
  refine ⟨W,K,L,hK,hL,hmatch,hd,?_⟩
  intro y hy
  have hfc : Tendsto f (𝓝 (γ c,y-c)) (𝓝 (γ y)) := by
    have hc : ContinuousAt f (γ c,y-c) := (continuous_flow W hK hL).continuousAt
    simpa only [hmatch y hy] using hc.tendsto
  exact hfc.eventually (hW (γ y) ⟨y,hy,rfl⟩)
end QuinticLienard.GlobalODE

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PeriodicBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
lemma vectorField_contDiff (F : Polynomial ℝ) : ContDiff ℝ ω (vectorField F) := by
  have hp : ContDiff ℝ ω (fun x : ℝ=>F.eval x) := by simpa [Polynomial.aeval_def] using! F.contDiff_aeval ω
  exact (contDiff_snd.sub (hp.comp contDiff_fst)).prodMk contDiff_fst.neg
lemma IsSolution.continuous {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) : Continuous z :=
  continuous_iff_continuousAt.mpr fun t=>(hz t).continuousAt
lemma IsSolution.x_deriv {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) (t : ℝ) :
    HasDerivAt (fun s=>(z s).1) ((z t).2-F.eval (z t).1) t := by
  simpa [vectorField] using! (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hz t)
lemma IsSolution.y_deriv {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) (t : ℝ) :
    HasDerivAt (fun s=>(z s).2) (-(z t).1) t := by
  simpa [vectorField] using! (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hz t)
lemma IsSolution.eq_of_eq {F : Polynomial ℝ} {z w : ℝ → Plane}
    (hz : IsSolution F z) (hw : IsSolution F w) {c : ℝ} (hc : z c=w c) : z=w := by
  funext t
  have h := GlobalODE.unique_on_open_interval (vectorField F) isOpen_univ
    (vectorField_contDiff F |>.of_le (by simp) |>.contDiffOn)
    (a:=min t c-1) (b:=max t c+1) (c:=c)
    (by constructor <;> linarith [min_le_right t c,le_max_right t c])
    (fun s _=>⟨hz s,mem_univ _⟩) (fun s _=>⟨hw s,mem_univ _⟩) hc
  exact h (by constructor <;> linarith [min_le_left t c,le_max_left t c])
lemma IsSolution.shift {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) (s : ℝ) :
    IsSolution F (fun t=>z (t+s)) := by
  intro t
  simpa using! (hz (t+s)).scomp t ((hasDerivAt_id t).add_const s)
lemma IsSolution.periodic_of_hit {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    {s t : ℝ} (he : z (s+t)=z s) : Function.Periodic z t := by
  have h := (hz.shift t).eq_of_eq hz (c:=s) he
  exact fun x=>congrFun h x
lemma equilibrium_solution (F : Polynomial ℝ) : IsSolution F (fun _=>(0,F.eval 0)) := by
  intro t
  simpa [vectorField] using! hasDerivAt_const t ((0,F.eval 0):Plane)
lemma IsSolution.avoids_equilibrium {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    (hn : ∃ s t, z s≠z t) (s : ℝ) : z s≠(0,F.eval 0) := by
  intro he
  have h := hz.eq_of_eq (equilibrium_solution F) he
  obtain ⟨t,u,htu⟩ := hn
  exact htu (by rw [h])
lemma IsSolution.axis_transverse {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    (hn : ∃ s t, z s≠z t) {s : ℝ} (hs : (z s).1=0) : (z s).2≠F.eval 0 := by
  intro h
  exact hz.avoids_equilibrium hn s (Prod.ext hs h)
lemma IsSolution.axis_finite {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    (hn : ∃ s t,z s≠z t) (a b : ℝ) : {t ∈ Icc a b | (z t).1=0}.Finite := by
  have hk : IsCompact {t ∈ Icc a b | (z t).1=0} :=
    isCompact_Icc.inter_right (isClosed_eq hz.continuous.fst continuous_const)
  apply hk.finite
  rw [isDiscrete_iff_nhdsNE]
  intro t ht
  have he := (hz.x_deriv t).eventually_ne (c:=0) (by
    change (z t).2-F.eval (z t).1≠0
    rw [ht.2]
    exact sub_ne_zero.mpr (hz.axis_transverse hn ht.2))
  apply Filter.eventually_false_iff_eq_bot.mp
  have hh : ∀ᶠ s in 𝓝[≠] t ⊓ 𝓟 {t ∈ Icc a b | (z t).1=0}, False := by
    filter_upwards [he.filter_mono inf_le_left, (show ∀ᶠ s in 𝓝[≠] t ⊓ 𝓟 {t ∈ Icc a b | (z t).1=0}, s ∈ {t ∈ Icc a b | (z t).1=0} from Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h=>h)))] with s hs hs'
    exact hs hs'.2
  exact hh
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PhysicalFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard
open ScaledProfile GlobalODE
lemma vectorField_local_flow {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) (z : Plane) :
    ∃ f : Plane × ℝ → Plane, ContDiffAt ℝ ω f (z,0) ∧
      ∀ᶠ q in 𝓝 (z,(0:ℝ)), f (q.1,0)=q.1 ∧
        HasDerivAt (fun s=>f (q.1,s)) (vectorField F (f q)) q.2 := by
  let A : Plane →L[ℝ] Plane := (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (-(ContinuousLinearMap.fst ℝ ℝ ℝ))
  let I : ℝ →L[ℝ] Plane := ContinuousLinearMap.inl ℝ ℝ ℝ
  let W : SmoothFlow.Path Plane → SmoothFlow.Path Plane := fun u=>SmoothFlow.pathMap A u-
    SmoothFlow.pathMap I ((AxisFlow.polynomial a).onPaths u)
  have hp := SmoothFlow.AlgebraicExpr.path_properties (AxisFlow.polynomial a) (AxisFlow.polynomial_regular a z)
  have hW : ContDiffAt ℝ ω W (SmoothFlow.constCLM z) :=
    (SmoothFlow.pathMap A).contDiff.contDiffAt.sub
      ((SmoothFlow.pathMap I).contDiff.contDiffAt.comp _ hp.2.1)
  apply SmoothFlow.exists_analytic_local_flow_eventually W (vectorField F) z _ hW
  filter_upwards [hp.2.2] with u hu s
  simp only [W,ContinuousMap.sub_apply,SmoothFlow.pathMap_apply,hu s,AxisFlow.polynomial_eval]
  simp [A,I,vectorField,hF]
lemma IsSolution.cutoff {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} (hz : IsSolution F z) {T : ℝ} (hT : 0<T) :
    ∃ (W : Plane → Plane) (K L : ℝ≥0) (hK : LipschitzWith K W) (hL : ∀ x, ‖W x‖≤L),
      (∀ t ∈ Icc (-1) (T+1), GlobalODE.flow W hK hL (z 0) t=z t) ∧
      (∀ t ∈ Icc (-1) (T+1), ContDiffAt ℝ ω (fun q : Plane × ℝ=>GlobalODE.flow W hK hL q.1 q.2) (z 0,t)) ∧
      ∀ t ∈ Icc (-1) (T+1), ∀ᶠ q : Plane × ℝ in 𝓝 (z 0,t),
        W (GlobalODE.flow W hK hL q.1 q.2)=vectorField F (GlobalODE.flow W hK hL q.1 q.2) := by
  simpa using GlobalODE.analytic_cutoff_along_compact_solution (vectorField F) isOpen_univ
    ((vectorField_contDiff F).of_le (by simp)).contDiffOn
    (fun x _=>vectorField_local_flow hF x) (a:=-1) (b:=T+1) (c:=0)
    (by norm_num) (by linarith) hz.continuous (fun _ _=>mem_univ _) (fun t _=>hz t)
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ClosedCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology NNReal
namespace QuinticLienard
open GlobalODE
lemma flow_periodic_of_hit {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (W : E → E) {K L : ℝ≥0} (hK : LipschitzWith K W) (hL : ∀ x,‖W x‖≤L)
    {x : E} {T : ℝ} (he : flow W hK hL x T=x) : Function.Periodic (flow W hK hL x) T := by
  intro t
  rw [add_comm,flow_add,he]
lemma flow_true_of_closed {F : Polynomial ℝ} (W : Plane → Plane) {K L : ℝ≥0}
    (hK : LipschitzWith K W) (hL : ∀ x,‖W x‖≤L) {x : Plane} {T : ℝ}
    (hT : 0<T) (he : flow W hK hL x T=x)
    (hW : ∀ t ∈ Icc 0 T,W (flow W hK hL x t)=vectorField F (flow W hK hL x t)) :
    IsSolution F (flow W hK hL x) := by
  have hp := flow_periodic_of_hit W hK hL he
  intro t
  have ht : flow W hK hL x t ∈ flow W hK hL x '' Icc 0 T := by
    rw [show Icc 0 T=Icc 0 (0+T) by simp,hp.image_Icc hT 0]
    exact mem_range_self t
  obtain ⟨s,hs,heq⟩ := ht
  have hd := flow_deriv W hK hL x t
  rwa [←heq,hW s hs,heq] at hd
lemma periodic_range_subset {z : ℝ → Plane} {T : ℝ} (hp : Function.Periodic z T) (hT : 0<T)
    {U : Set Plane} (hU : ∀ t ∈ Icc 0 T,z t ∈ U) : range z ⊆ U := by
  rw [←hp.image_Icc hT 0]
  rintro p ⟨t,ht,rfl⟩
  exact hU t (by simpa using ht)
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.IntervalInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology NNReal
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology
namespace QuinticLienard.RealAnalysis

theorem continuous_interval_inverse {f : ℝ → ℝ} {a b c d : ℝ} (hcd : c≤d)
    (hc : ContinuousOn f (Icc a b)) (hb : BijOn f (Icc a b) (Icc c d)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ y,g y ∈ Icc a b) ∧
      (∀ y ∈ Icc c d,f (g y)=y) ∧ (∀ t ∈ Icc a b,g (f t)=t) := by
  let F : Icc a b → Icc c d := fun t=>⟨f t,hb.mapsTo t.property⟩
  have hF : Function.Bijective F := by
    constructor
    · intro x y h
      exact Subtype.ext (hb.injOn x.property y.property (congrArg Subtype.val h))
    · intro y
      obtain ⟨x,hx,he⟩ := hb.surjOn y.property
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let e : Icc a b ≃ Icc c d := Equiv.ofBijective F hF
  have hec : Continuous e := by
    exact (hc.domRestrict).subtype_mk _
  let H : Icc a b ≃ₜ Icc c d := hec.homeoOfEquivCompactToT2
  let clamp : ℝ → Icc c d := fun y=>⟨max c (min d y),le_max_left _ _,max_le hcd (min_le_left _ _)⟩
  have hcl : Continuous clamp := (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _
  have hcl_eq (y : ℝ) (hy : y ∈ Icc c d) : (clamp y : ℝ)=y := by simp [clamp,max_eq_right hy.1,min_eq_right hy.2]
  let g : ℝ → ℝ := fun y=>H.symm (clamp y)
  refine ⟨g,continuous_subtype_val.comp (H.symm.continuous.comp hcl),fun y=>(H.symm (clamp y)).property,?_,?_⟩
  · intro y hy
    have h := congrArg Subtype.val (H.apply_symm_apply (clamp y))
    change f (g y)=(clamp y : ℝ) at h
    exact h.trans (hcl_eq y hy)
  · intro t ht
    have hclt : clamp (f t)=H ⟨t,ht⟩ := Subtype.ext (hcl_eq (f t) (hb.mapsTo ht))
    dsimp [g]
    rw [hclt,H.symm_apply_apply]
end QuinticLienard.RealAnalysis

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ExcursionGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open RealAnalysis ScaledProfile AxisFlow

lemma IsRightExcursion.y_strictAnti {F : Polynomial ℝ} {z : ℝ → Plane} {s t : ℝ}
    (hz : IsSolution F z) (he : IsRightExcursion z s t) : StrictAntiOn (fun v=>(z v).2) (Icc s t) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc s t) hz.continuous.snd.continuousOn
  intro v hv
  have hv' : v ∈ Ioo s t := by simpa using hv
  rw [(hz.y_deriv v).deriv]
  exact neg_neg_of_pos (he.positive v hv')
lemma IsRightExcursion.y_lt {F : Polynomial ℝ} {z : ℝ → Plane} {s t : ℝ}
    (hz : IsSolution F z) (he : IsRightExcursion z s t) : (z t).2<(z s).2 :=
  he.y_strictAnti hz ⟨le_rfl,he.lt.le⟩ ⟨he.lt.le,le_rfl⟩ he.lt
lemma IsRightExcursion.graph {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} {s t : ℝ}
    (hz : IsSolution F z) (he : IsRightExcursion z s t) :
    ∃ u : ℝ → ℝ, Continuous u ∧ u (z t).2=0 ∧ u (z s).2=0 ∧
      (∀ y ∈ Ioo (z t).2 (z s).2,0<u y ∧ HasDerivAt u (φ a (u y)-y) y) ∧
      (∀ v ∈ Icc s t,u (z v).2=(z v).1^2/2) := by
  have hylt := he.y_lt hz
  have hanti := he.y_strictAnti hz
  have hb : BijOn (fun v=>(z v).2) (Icc s t) (Icc (z t).2 (z s).2) := by
    refine ⟨?_,hanti.injOn,?_⟩
    · intro v hv
      exact ⟨hanti.antitoneOn hv ⟨he.lt.le,le_rfl⟩ hv.2,
        hanti.antitoneOn ⟨le_rfl,he.lt.le⟩ hv hv.1⟩
    · intro y hy
      exact intermediate_value_Icc' he.lt.le hz.continuous.snd.continuousOn hy
  obtain ⟨τ,hτc,hτmem,hτr,hτl⟩ := continuous_interval_inverse hylt.le hz.continuous.snd.continuousOn hb
  have hτint (y : ℝ) (hy : y ∈ Ioo (z t).2 (z s).2) : τ y ∈ Ioo s t := by
    have hm := hτmem y
    refine ⟨lt_of_le_of_ne hm.1 ?_,lt_of_le_of_ne hm.2 ?_⟩
    · intro hn
      have hh := hτr y (Ioo_subset_Icc_self hy)
      rw [←hn] at hh
      exact hy.2.ne hh.symm
    · intro hn
      have hh := hτr y (Ioo_subset_Icc_self hy)
      rw [hn] at hh
      exact hy.1.ne hh
  let u : ℝ → ℝ := fun y=>(z (τ y)).1^2/2
  have hu : ∀ v ∈ Icc s t,u (z v).2=(z v).1^2/2 := fun v hv=>by dsimp [u];rw [hτl v hv]
  refine ⟨u,(hz.continuous.fst.comp hτc).pow 2 |>.div_const 2,?_,?_,?_,hu⟩
  · rw [hu t ⟨he.lt.le,le_rfl⟩,he.right];norm_num
  · rw [hu s ⟨le_rfl,he.lt.le⟩,he.left];norm_num
  · intro y hy
    have hx := he.positive (τ y) (hτint y hy)
    have hτd : HasDerivAt τ (-(z (τ y)).1)⁻¹ y :=
      HasDerivAt.of_local_left_inverse hτc.continuousAt (hz.y_deriv (τ y)) (neg_ne_zero.mpr hx.ne')
        ((show ∀ᶠ v in 𝓝 y,v ∈ Ioo (z t).2 (z s).2 from Ioo_mem_nhds hy.1 hy.2).mono fun v hv=>hτr v (Ioo_subset_Icc_self hv))
    refine ⟨div_pos (sq_pos_of_pos hx) (by norm_num),?_⟩
    convert! (((hz.x_deriv (τ y)).pow 2).div_const 2).comp y hτd using 1
    symm
    change (2*(z (τ y)).1^(2-1)*((z (τ y)).2-F.eval (z (τ y)).1)/2)*(-(z (τ y)).1)⁻¹=φ a ((z (τ y)).1^2/2)-y
    rw [AxisFlow.φ_square a hx.le,←hF,hτr y (Ioo_subset_Icc_self hy)]
    field_simp [hx.ne']
    ring
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ExcursionSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
lemma HasDerivAt.pos_right_of_pos {f : ℝ → ℝ} {s d : ℝ}
    (hd : HasDerivAt f d s) (h0 : f s=0) (hpos : 0<d) : ∀ᶠ t in 𝓝[>] s,0<f t := by
  have hl := hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE s)
  filter_upwards [hl.eventually (eventually_gt_nhds hpos),self_mem_nhdsWithin] with t ht hst
  rw [slope_def_field,h0,sub_zero] at ht
  exact (div_pos_iff.mp ht).resolve_right (fun h=> (not_lt_of_ge (sub_nonneg.mpr hst.le)) h.2) |>.1
lemma HasDerivAt.nonneg_of_pos_right {f : ℝ → ℝ} {s t d : ℝ}
    (hd : HasDerivAt f d s) (h0 : f s=0) (hst : s<t) (hf : ∀ v ∈ Ioo s t,0<f v) : 0≤d := by
  apply ge_of_tendsto (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE s))
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hst).filter_mono inf_le_left] with v hsv hvt
  rw [slope_def_field,h0,sub_zero]
  exact (div_pos (hf v ⟨hsv,hvt⟩) (sub_pos.mpr hsv)).le
lemma HasDerivAt.nonpos_of_pos_left {f : ℝ → ℝ} {s t d : ℝ}
    (hd : HasDerivAt f d t) (h0 : f t=0) (hst : s<t) (hf : ∀ v ∈ Ioo s t,0<f v) : d≤0 := by
  apply le_of_tendsto (hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE t))
  filter_upwards [self_mem_nhdsWithin,(eventually_gt_nhds hst).filter_mono inf_le_left] with v hvt hsv
  rw [slope_def_field,h0,sub_zero]
  exact (div_neg_of_pos_of_neg (hf v ⟨hsv,hvt⟩) (sub_neg.mpr hvt)).le
lemma IsRightExcursion.endpoint_signs {F : Polynomial ℝ} {z : ℝ → Plane} {s t : ℝ}
    (hz : IsSolution F z) (hn : ∃ s t,z s≠z t) (he : IsRightExcursion z s t) :
    (z t).2<F.eval 0 ∧ F.eval 0<(z s).2 := by
  have hs := HasDerivAt.nonneg_of_pos_right (hz.x_deriv s) he.left he.lt he.positive
  have ht := HasDerivAt.nonpos_of_pos_left (hz.x_deriv t) he.right he.lt he.positive
  rw [he.left] at hs
  rw [he.right] at ht
  exact ⟨lt_of_le_of_ne (sub_nonpos.mp ht) (hz.axis_transverse hn he.right),
    lt_of_le_of_ne (sub_nonneg.mp hs) (hz.axis_transverse hn he.left).symm⟩
lemma IsSolution.right_excursion_after {F : Polynomial ℝ} {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T)
    (hp : Function.Periodic z T) {s : ℝ} (hs : (z s).1=0) (hy : F.eval 0<(z s).2) :
    ∃ t,IsRightExcursion z s t := by
  let S : Set ℝ := {t ∈ Ioc s (s+T) | (z t).1=0}
  have hS : S.Finite := (hz.axis_finite hn s (s+T)).subset (fun _ h=>⟨⟨h.1.1.le,h.1.2⟩,h.2⟩)
  have hne : S.Nonempty := ⟨s+T,⟨by constructor <;> linarith,hp s ▸ hs⟩⟩
  obtain ⟨t,ht,hmin⟩ := hS.isCompact.exists_isMinOn hne continuous_id.continuousOn
  have hst : s<t := ht.1.1
  refine ⟨t,hst,hs,ht.2,?_⟩
  have hd : 0<(z s).2-F.eval (z s).1 := by rw [hs];exact sub_pos.mpr hy
  have he := HasDerivAt.pos_right_of_pos (hz.x_deriv s) hs hd
  intro v hv
  by_contra! hvn
  have hew : ∀ᶠ w in 𝓝[>] s,s<w ∧ w<v ∧ 0<(z w).1 := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hv.1).filter_mono inf_le_left,he] with w hsw hwv hwp
    exact ⟨hsw,hwv,hwp⟩
  obtain ⟨w,hw,hwv,hwp⟩ := hew.exists
  obtain ⟨q,hq,hqz⟩ := intermediate_value_Icc' hwv.le hz.continuous.fst.continuousOn ⟨hvn,hwp.le⟩
  have hqS : q ∈ S := ⟨⟨hw.trans_le hq.1,hq.2.trans (hv.2.le.trans ht.1.2)⟩,hqz⟩
  have hh : t≤q := hmin hqS
  exact (not_le_of_gt (hq.2.trans_lt hv.2)) hh
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PeriodicSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
lemma IsSolution.reverseY {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) :
    IsSolution (-F) (reverseY z) := by
  intro t
  have hx := (hz.x_deriv (-t)).scomp t (hasDerivAt_id t).neg
  have hy := (hz.y_deriv (-t)).scomp t (hasDerivAt_id t).neg
  convert! hx.prodMk hy.neg using 1
  simp [QuinticLienard.reverseY,vectorField]
  ring
lemma IsSolution.reverseX {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) :
    IsSolution (polynomialReflect F) (reverseX z) := by
  intro t
  have hx := (hz.x_deriv (-t)).scomp t (hasDerivAt_id t).neg
  have hy := (hz.y_deriv (-t)).scomp t (hasDerivAt_id t).neg
  convert! hx.neg.prodMk hy using 1; simp [QuinticLienard.reverseX,vectorField]
lemma reverseY_nonconstant {z : ℝ → Plane} (hn : ∃ s t,z s≠z t) : ∃ s t,reverseY z s≠reverseY z t := by
  obtain ⟨s,t,hst⟩ := hn
  refine ⟨-s,-t,fun h=>hst (Prod.ext ?_ ?_)⟩
  · simpa [QuinticLienard.reverseY] using congrArg Prod.fst h
  · simpa [QuinticLienard.reverseY] using congrArg (fun p : Plane=> -p.2) h
lemma reverseX_nonconstant {z : ℝ → Plane} (hn : ∃ s t,z s≠z t) : ∃ s t,reverseX z s≠reverseX z t := by
  obtain ⟨s,t,hst⟩ := hn
  refine ⟨-s,-t,fun h=>hst (Prod.ext ?_ ?_)⟩
  · simpa [QuinticLienard.reverseX] using congrArg (fun p : Plane=> -p.1) h
  · simpa [QuinticLienard.reverseX] using congrArg Prod.snd h
lemma reverseY_periodic {z : ℝ → Plane} {T : ℝ} (hp : Function.Periodic z T) : Function.Periodic (reverseY z) T := by
  intro t
  simp only [QuinticLienard.reverseY,neg_add]
  rw [hp.neg (-t)]
lemma reverseX_periodic {z : ℝ → Plane} {T : ℝ} (hp : Function.Periodic z T) : Function.Periodic (reverseX z) T := by
  intro t
  simp only [QuinticLienard.reverseX,neg_add]
  rw [hp.neg (-t)]
lemma IsSolution.right_excursion_before {F : Polynomial ℝ} {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T)
    (hp : Function.Periodic z T) {t : ℝ} (ht : (z t).1=0) (hy : (z t).2<F.eval 0) :
    ∃ s,IsRightExcursion z s t := by
  obtain ⟨s,hs⟩ := hz.reverseY.right_excursion_after (reverseY_nonconstant hn) hT (reverseY_periodic hp)
    (s:=-t) (by simpa [QuinticLienard.reverseY] using ht) (by simpa [QuinticLienard.reverseY] using neg_lt_neg hy)
  refine ⟨-s,by linarith [hs.lt],?_,ht,?_⟩
  · exact hs.right
  · intro v hv
    have H := hs.positive (-v) ⟨by linarith [hv.2],by linarith [hv.1]⟩
    simpa [QuinticLienard.reverseY] using H
lemma IsSolution.y_extrema {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    {T : ℝ} (hT : 0<T) (hp : Function.Periodic z T) :
    ∃ s t,(z s).1=0 ∧ (z t).1=0 ∧ ∀ v,(z s).2≤(z v).2 ∧ (z v).2≤(z t).2 := by
  obtain ⟨s,hs,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT.le) hz.continuous.snd.continuousOn
  obtain ⟨t,ht,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT.le) hz.continuous.snd.continuousOn
  have hb (v : ℝ) : (z s).2≤(z v).2 ∧ (z v).2≤(z t).2 := by
    have hv : z v ∈ z '' Icc 0 T := by rw [show Icc 0 T=Icc 0 (0+T) by simp,hp.image_Icc hT 0];exact mem_range_self v
    obtain ⟨w,hw,he⟩ := hv
    rw [←he]
    exact ⟨hmin hw,hmax hw⟩
  have hsd := (show IsLocalMin (fun v=>(z v).2) s from Filter.Eventually.of_forall fun v=>(hb v).1).hasDerivAt_eq_zero (hz.y_deriv s)
  have htd := (show IsLocalMax (fun v=>(z v).2) t from Filter.Eventually.of_forall fun v=>(hb v).2).hasDerivAt_eq_zero (hz.y_deriv t)
  exact ⟨s,t,neg_eq_zero.mp hsd,neg_eq_zero.mp htd,hb⟩
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.OpenArch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScalarArcs

lemma IsOpenArch.peak_exists {φ u : ℝ → ℝ} {A B : ℝ} (hu : IsOpenArch φ u A B) :
    ∃ H : ℝ,0<H ∧ φ H ∈ Ioo A B ∧ u (φ H)=H ∧ ∀ y ∈ Icc A B,u y≤H := by
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hu.lt.le) hu.continuous.continuousOn
  have hmid : (A+B)/2 ∈ Ioo A B := ⟨by linarith [hu.lt],by linarith [hu.lt]⟩
  have hmpos : 0<u m := (hu.positive _ hmid).trans_le (hmax (Ioo_subset_Icc_self hmid))
  have hmi : m ∈ Ioo A B := by
    refine ⟨lt_of_le_of_ne hm.1 ?_,lt_of_le_of_ne hm.2 ?_⟩
    · intro he;rw [←he,hu.left] at hmpos;exact lt_irrefl _ hmpos
    · intro he;rw [he,hu.right] at hmpos;exact lt_irrefl _ hmpos
  have hzero := (hmax.isLocalMax (Icc_mem_nhds hmi.1 hmi.2)).hasDerivAt_eq_zero (hu.equation _ hmi)
  have he : φ (u m)=m := sub_eq_zero.mp hzero
  exact ⟨u m,hmpos,he.symm ▸ hmi,by rw [he],fun _ hy=>hmax hy⟩
lemma profile_extension_along_compact {φ u : ℝ → ℝ} {S : Set ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (hu : Continuous u) (hS : IsCompact S) (hn : S.Nonempty)
    (hp : ∀ y ∈ S,0<u y) :
    ∃ ψ : ℝ → ℝ,ContDiff ℝ 1 ψ ∧ ∀ y ∈ S,ψ (u y)=φ (u y) := by
  obtain ⟨m,hm,hmin⟩ := hS.exists_isMinOn hn hu.continuousOn
  obtain ⟨M,hM,hmax⟩ := hS.exists_isMaxOn hn hu.continuousOn
  obtain ⟨ψ,K,B,hψ,_,_,he⟩ := positive_profile_extension hφ (half_pos (hp m hm))
    (show u m/2<u M+1 by have hv : u m ≤ u M := hmax hm;
                          linarith [hp m hm])
  exact ⟨ψ,hψ,fun y hy=>he ⟨by have hv : u m ≤ u y := hmin hy; linarith [hp m hm],by have hv : u y ≤ u M := hmax hy; linarith⟩⟩
lemma IsOpenArch.derivative_signs {φ u : ℝ → ℝ} {A B H : ℝ}
    (hu : IsOpenArch φ u A B) (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hp : φ H ∈ Ioo A B) (hpeak : u (φ H)=H) :
    (∀ y ∈ Ioo A B,y<φ H → 0<φ (u y)-y) ∧
    (∀ y ∈ Ioo A B,φ H<y → φ (u y)-y<0) := by
  have hs (y : ℝ) (hy : y ∈ Ioo A B) :
      (y<φ H → 0<φ (u y)-y) ∧ (φ H<y → φ (u y)-y<0) := by
    let l := min y (φ H)
    let r := max y (φ H)
    have hsub : Icc l r ⊆ Ioo A B := by
      intro v hv
      exact ⟨(lt_min hy.1 hp.1).trans_le hv.1,hv.2.trans_lt (max_lt hy.2 hp.2)⟩
    have hyp : y ∈ Icc l r := ⟨min_le_left _ _,le_max_left _ _⟩
    have hpp : φ H ∈ Icc l r := ⟨min_le_right _ _,le_max_right _ _⟩
    obtain ⟨ψ,hψ,he⟩ := profile_extension_along_compact hφ hu.continuous isCompact_Icc ⟨y,hyp⟩
      (fun v hv=>hu.positive v (hsub hv))
    have heH : ψ H=φ H := by simpa only [hpeak] using he _ hpp
    have hd : ∀ v ∈ Icc l r,HasDerivAt u (ψ (u v)-v) v := fun v hv=>by
      rw [he v hv]; exact hu.equation v (hsub hv)
    have signs := derivative_signs_on_Icc (t := H) hψ hu.continuous hd
      (by simpa only [heH] using hpeak) (by simpa only [heH] using hpp)
    constructor
    · intro h
      have hh := signs.1 y hyp (by simpa only [heH] using h)
      simpa only [he y hyp] using hh
    · intro h
      have hh := signs.2 y hyp (by simpa only [heH] using h)
      simpa only [he y hyp] using hh
  exact ⟨fun y hy=> (hs y hy).1,fun y hy=> (hs y hy).2⟩
lemma IsOpenArch.monotonicity {φ u : ℝ → ℝ} {A B H : ℝ}
    (hu : IsOpenArch φ u A B) (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hp : φ H ∈ Ioo A B) (hpeak : u (φ H)=H) :
    StrictMonoOn u (Icc A (φ H)) ∧ StrictAntiOn u (Icc (φ H) B) := by
  have hs := hu.derivative_signs hφ hp hpeak
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hu.continuous.continuousOn
    intro y hy
    have hy' : y ∈ Ioo A (φ H) := by simpa using hy
    have hyab : y ∈ Ioo A B := ⟨hy'.1,hy'.2.trans hp.2⟩
    rw [(hu.equation y hyab).deriv]
    exact hs.1 y hyab hy'.2
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hu.continuous.continuousOn
    intro y hy
    have hy' : y ∈ Ioo (φ H) B := by simpa using hy
    have hyab : y ∈ Ioo A B := ⟨hp.1.trans hy'.1,hy'.2⟩
    rw [(hu.equation y hyab).deriv]
    exact hs.2 y hyab hy'.1
lemma IsOpenArch.subarch {φ u : ℝ → ℝ} {A B H h : ℝ}
    (hu : IsOpenArch φ u A B) (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hp : φ H ∈ Ioo A B) (hpeak : u (φ H)=H) (hh : 0<h) (hH : h<H) :
    ∃ a b,A<a ∧ b<B ∧ IsArch φ u h H a b := by
  obtain ⟨a,ha,hua⟩ := intermediate_value_Icc hp.1.le hu.continuous.continuousOn
    (show h ∈ Icc (u A) (u (φ H)) by rw [hu.left,hpeak];exact ⟨hh.le,hH.le⟩)
  obtain ⟨b,hb,hub⟩ := intermediate_value_Icc' hp.2.le hu.continuous.continuousOn
    (show h ∈ Icc (u B) (u (φ H)) by rw [hu.right,hpeak];exact ⟨hh.le,hH.le⟩)
  have hAa : A<a := lt_of_le_of_ne ha.1 (by intro he;rw [←he,hu.left] at hua;exact hh.ne hua)
  have hap : a<φ H := lt_of_le_of_ne ha.2 (by intro he;rw [he,hpeak] at hua;exact hH.ne hua.symm)
  have hpb : φ H<b := lt_of_le_of_ne hb.1 (by intro he;rw [←he,hpeak] at hub;exact hH.ne hub.symm)
  have hbB : b<B := lt_of_le_of_ne hb.2 (by intro he;rw [he,hu.right] at hub;exact hh.ne hub)
  have hs := hu.derivative_signs hφ hp hpeak
  have hm := hu.monotonicity hφ hp hpeak
  refine ⟨a,b,hAa,hbB,hu.continuous,hap,hpb,hpeak,hua,hub,?_,?_,?_,?_,
    hm.1.mono (Icc_subset_Icc hAa.le le_rfl),hm.2.mono (Icc_subset_Icc le_rfl hbB.le)⟩
  · have H := hs.1 a ⟨hAa,hap.trans hp.2⟩ hap
    rw [hua] at H;linarith
  · have H := hs.2 b ⟨hp.1.trans hpb,hbB⟩ hpb
    rw [hub] at H;linarith
  · intro y hy;exact hu.equation y ⟨hAa.trans_le hy.1,hy.2.trans_lt hbB⟩
  · intro y hy
    rcases le_total y (φ H) with hyp|hpy
    · exact ⟨hua ▸ hm.1.monotoneOn ha ⟨hAa.le.trans hy.1,hyp⟩ hy.1,
        hpeak ▸ hm.1.monotoneOn ⟨hAa.le.trans hy.1,hyp⟩ ⟨hp.1.le,le_rfl⟩ hyp⟩
    · exact ⟨hub ▸ hm.2.antitoneOn ⟨hpy,hy.2.trans hbB.le⟩ hb hy.2,
        hpeak ▸ hm.2.antitoneOn ⟨le_rfl,hp.2.le⟩ ⟨hpy,hy.2.trans hbB.le⟩ hpy⟩
end QuinticLienard.ScalarArcs

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.OpenArchAxis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScalarArcs
lemma IsOpenArch.axis_endpoints {φ u : ℝ → ℝ} {A B H : ℝ}
    (hu : IsOpenArch φ u A B) (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : ContinuousOn φ (Ici 0)) (hH : 0<H) (hp : φ H ∈ Ioo A B) (hpeak : u (φ H)=H) :
    axisLower φ H=A ∧ axisUpper φ H=B := by
  have he : ∀ᶠ h in 𝓝[>] (0:ℝ),
      A<lower φ h H ∧ lower φ h H<φ H ∧ φ H<upper φ h H ∧ upper φ h H<B ∧
      u (lower φ h H)=h ∧ u (upper φ h H)=h := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hH).filter_mono inf_le_left] with h hh hHt
    obtain ⟨a,b,ha,hb,hab⟩ := hu.subarch hφ hp hpeak hh hHt
    obtain ⟨hl,hr⟩ := canonical_of_positive_arch hab hφ hh hHt
    rw [hl,hr]
    exact ⟨ha,hab.lower_lt_peak,hab.peak_lt_upper,hb,hab.lower,hab.upper⟩
  have hl := lower_axis_tendsto hφ hc hH
  have hr := upper_axis_tendsto hφ hc hH
  have hal : A≤axisLower φ H := ge_of_tendsto hl (he.mono fun _ h=>h.1.le)
  have hlp : axisLower φ H≤φ H := le_of_tendsto hl (he.mono fun _ h=>h.2.1.le)
  have hpr : φ H≤axisUpper φ H := ge_of_tendsto hr (he.mono fun _ h=>h.2.2.1.le)
  have hrb : axisUpper φ H≤B := le_of_tendsto hr (he.mono fun _ h=>h.2.2.2.1.le)
  have hul : u (axisLower φ H)=0 := tendsto_nhds_unique (hu.continuous.continuousAt.tendsto.comp hl)
    ((tendsto_id.mono_left inf_le_left : Tendsto (fun h : ℝ=>h) (𝓝[>] 0) (𝓝 0)).congr'
      (he.mono fun _ h=>h.2.2.2.2.1.symm))
  have hur : u (axisUpper φ H)=0 := tendsto_nhds_unique (hu.continuous.continuousAt.tendsto.comp hr)
    ((tendsto_id.mono_left inf_le_left : Tendsto (fun h : ℝ=>h) (𝓝[>] 0) (𝓝 0)).congr'
      (he.mono fun _ h=>h.2.2.2.2.2.symm))
  constructor
  · apply le_antisymm _ hal
    by_contra! hn
    have hh := hu.positive _ ⟨hn,hlp.trans_lt hp.2⟩
    rw [hul] at hh
    exact lt_irrefl _ hh
  · apply le_antisymm hrb
    by_contra! hn
    have hh := hu.positive _ ⟨hp.1.trans_le hpr,hn⟩
    rw [hur] at hh
    exact lt_irrefl _ hh
end QuinticLienard.ScalarArcs

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ExcursionAxis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow
lemma IsRightExcursion.axis_peak {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} {s t : ℝ}
    (hz : IsSolution F z) (hn : ∃ s t,z s≠z t) (he : IsRightExcursion z s t) :
    ∃ H ∈ transversePeaks a,axisEndpoint a false H=(z t).2 ∧ axisEndpoint a true H=(z s).2 := by
  obtain ⟨u,huc,hul,hur,hud,_⟩ := he.graph hF hz
  have hu : IsOpenArch (φ a) u (z t).2 (z s).2 :=
    ⟨he.y_lt hz,huc,hul,hur,fun y hy=>(hud y hy).1,fun y hy=>(hud y hy).2⟩
  obtain ⟨H,hH,hp,hpeak,_⟩ := hu.peak_exists
  obtain ⟨hl,hr⟩ := hu.axis_endpoints (φ_smooth a) (φ_continuous a).continuousOn hH hp hpeak
  have hs := he.endpoint_signs hz hn
  refine ⟨H,⟨hH,?_,?_⟩,hl,hr⟩
  · change axisLower (φ a) H<poly a 0
    rw [hl,←hF]
    exact hs.1
  · change poly a 0<axisUpper (φ a) H
    rw [hr,←hF]
    exact hs.2
namespace AxisFlow
lemma axisLower_strictAnti (a : Fin 6 → ℝ) : StrictAntiOn (axisEndpoint a false) (transversePeaks a) := by
  apply strictAntiOn_of_deriv_neg (convex_iff_ordConnected.mpr (transversePeaks_ordConnected a))
    (fun t ht=>(axisEndpoint_analytic a false ht.1 ht.2.1.ne).continuousAt.continuousWithinAt)
  intro t ht
  exact axisEndpoint_sign a false (interior_subset ht).1 (interior_subset ht).2.1.ne
lemma axisUpper_strictMono (a : Fin 6 → ℝ) : StrictMonoOn (axisEndpoint a true) (transversePeaks a) := by
  apply strictMonoOn_of_deriv_pos (convex_iff_ordConnected.mpr (transversePeaks_ordConnected a))
    (fun t ht=>(axisEndpoint_analytic a true ht.1 ht.2.2.ne').continuousAt.continuousWithinAt)
  intro t ht
  exact axisEndpoint_sign a true (interior_subset ht).1 (interior_subset ht).2.2.ne'
lemma axis_order {a : Fin 6 → ℝ} {s t : ℝ} (hs : s ∈ transversePeaks a) (ht : t ∈ transversePeaks a) :
    (axisEndpoint a true s≤axisEndpoint a true t ↔ axisEndpoint a false t≤axisEndpoint a false s) := by
  constructor
  · intro h
    have hst : s≤t := by
      by_contra! hn
      exact (not_lt_of_ge h) (axisUpper_strictMono a ht hs hn)
    exact (axisLower_strictAnti a).antitoneOn hs ht hst
  · intro h
    have hst : s≤t := by
      by_contra! hn
      exact (not_lt_of_ge h) (axisLower_strictAnti a ht hs hn)
    exact (axisUpper_strictMono a).monotoneOn hs ht hst
end AxisFlow
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PeriodicMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow
lemma IsSolution.y_extrema_signs {F : Polynomial ℝ} {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T) (hp : Function.Periodic z T)
    {s t : ℝ} (hs : (z s).1=0) (ht : (z t).1=0)
    (hb : ∀ v,(z s).2≤(z v).2 ∧ (z v).2≤(z t).2) : (z s).2<F.eval 0 ∧ F.eval 0<(z t).2 := by
  constructor
  · by_contra! h
    have hlt : F.eval 0<(z s).2 := lt_of_le_of_ne h (hz.axis_transverse hn hs).symm
    obtain ⟨v,hv⟩ := hz.right_excursion_after hn hT hp hs hlt
    exact (not_lt_of_ge (hb v).1) (hv.y_lt hz)
  · by_contra! h
    have hlt : (z t).2<F.eval 0 := lt_of_le_of_ne h (hz.axis_transverse hn ht)
    obtain ⟨v,hv⟩ := hz.right_excursion_before hn hT hp ht hlt
    exact (not_lt_of_ge (hb v).2) (hv.y_lt hz)
lemma IsSolution.right_peak_at_extrema {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T) (hp : Function.Periodic z T)
    {s t : ℝ} (hs : (z s).1=0) (ht : (z t).1=0)
    (hb : ∀ v,(z s).2≤(z v).2 ∧ (z v).2≤(z t).2) :
    ∃ H ∈ transversePeaks a,axisEndpoint a false H=(z s).2 ∧ axisEndpoint a true H=(z t).2 := by
  have hsign := hz.y_extrema_signs hn hT hp hs ht hb
  obtain ⟨v,hv⟩ := hz.right_excursion_after hn hT hp ht hsign.2
  obtain ⟨w,hw⟩ := hz.right_excursion_before hn hT hp hs hsign.1
  obtain ⟨H,hH,hHl,hHr⟩ := hv.axis_peak hF hz hn
  obtain ⟨K,hK,hKl,hKr⟩ := hw.axis_peak hF hz hn
  have hcomp : axisEndpoint a true K≤axisEndpoint a true H := by rw [hKr,hHr];exact (hb w).2
  have hc := (axis_order hK hH).mp hcomp
  rw [hHl,hKl] at hc
  exact ⟨H,hH,hHl.trans (le_antisymm hc (hb v).1),hHr⟩
lemma IsSolution.matching_at_extrema {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T) (hp : Function.Periodic z T)
    {s t : ℝ} (hs : (z s).1=0) (ht : (z t).1=0)
    (hb : ∀ v,(z s).2≤(z v).2 ∧ (z v).2≤(z t).2) :
    let r := ((z t).2-(z s).2)/2
    r ∈ matchingDomain a (reflectX a) ∧ matchingDelta a (reflectX a) r=0 ∧
      axisM a r=((z t).2+(z s).2)/2-poly a 0 := by
  obtain ⟨H,hH,hHl,hHr⟩ := hz.right_peak_at_extrema hF hn hT hp hs ht hb
  obtain ⟨K,hK,hKl,hKr⟩ := hz.reverseX.right_peak_at_extrema
    (a:=reflectX a) (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly])
    (reverseX_nonconstant hn) hT (reverseX_periodic hp) (s:=-s) (t:=-t)
    (by simpa [QuinticLienard.reverseX] using congrArg Neg.neg hs) (by simpa [QuinticLienard.reverseX] using congrArg Neg.neg ht)
    (fun v=>by simpa [QuinticLienard.reverseX] using hb (-v))
  simp only [QuinticLienard.reverseX,neg_neg] at hKl hKr
  dsimp only
  have hwH : axisWidth a H=((z t).2-(z s).2)/2 := by rw [axisWidth,hHl,hHr]
  have hwK : axisWidth (reflectX a) K=((z t).2-(z s).2)/2 := by rw [axisWidth,hKl,hKr]
  have hpa := axisPeak_eq a hH hwH
  have hpb := axisPeak_eq (reflectX a) hK hwK
  have hM : axisM a (((z t).2-(z s).2)/2)=((z t).2+(z s).2)/2-poly a 0 := by
    rw [axisM,hpa,axisCenter,hHl,hHr]
  have hMb : axisM (reflectX a) (((z t).2-(z s).2)/2)=((z t).2+(z s).2)/2-poly a 0 := by
    rw [axisM,hpb,axisCenter,hKl,hKr,reflectX_poly]
    simp
  refine ⟨⟨⟨H,hH,hwH⟩,⟨K,hK,hwK⟩⟩,?_,hM⟩
  rw [matchingDelta,hM,hMb,sub_self]
lemma IsPeriodicOrbit.matching {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {C : Set Plane} (hC : IsPeriodicOrbit F C) :
    ∃ r ∈ matchingDomain a (reflectX a),matchingDelta a (reflectX a) r=0 ∧
      (0,poly a 0+axisM a r+r) ∈ C ∧
      ∀ p ∈ C,poly a 0+axisM a r-r≤p.2 ∧ p.2≤poly a 0+axisM a r+r := by
  obtain ⟨z,T,hz,hT,hp,hn,rfl⟩ := hC
  obtain ⟨s,t,hs,ht,hb⟩ := hz.y_extrema hT hp
  obtain ⟨hr,hd,hM⟩ := hz.matching_at_extrema hF hn hT hp hs ht hb
  refine ⟨((z t).2-(z s).2)/2,hr,hd,?_,?_⟩
  · refine ⟨t,?_⟩
    apply Prod.ext ht
    rw [hM]
    ring
  · rintro p ⟨v,rfl⟩
    rw [hM]
    constructor <;> linarith [(hb v).1,(hb v).2]
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PeriodicOval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow
lemma IsPeriodicOrbit.eq_of_common {F : Polynomial ℝ} {C D : Set Plane}
    (hC : IsPeriodicOrbit F C) (hD : IsPeriodicOrbit F D) {p : Plane} (hp : p ∈ C) (hq : p ∈ D) : C=D := by
  obtain ⟨z,T,hz,_,_,_,rfl⟩ := hC
  obtain ⟨w,S,hw,_,_,_,rfl⟩ := hD
  obtain ⟨s,hs⟩ := hp
  obtain ⟨t,ht⟩ := hq
  have he := (hz.shift s).eq_of_eq (hw.shift t) (c:=0) (by simpa using hs.trans ht.symm)
  have hr (f : ℝ → Plane) (v : ℝ) : range (fun u=>f (u+v))=range f := by
    ext x
    constructor
    · rintro ⟨u,rfl⟩;exact mem_range_self _
    · rintro ⟨u,rfl⟩;exact ⟨u-v,by simp⟩
  rw [←hr z s,he,hr]
lemma IsSolution.oval_at_max {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T) (hp : Function.Periodic z T)
    {s t : ℝ} (hs : (z s).1=0) (ht : (z t).1=0)
    (hb : ∀ v,(z s).2≤(z v).2 ∧ (z v).2≤(z t).2) :
    ∃ v w, IsRightExcursion z t v ∧ IsRightExcursion (QuinticLienard.reverseX z) (-w) (-v) ∧ z w=z t := by
  have hsign := hz.y_extrema_signs hn hT hp hs ht hb
  obtain ⟨v,hv⟩ := hz.right_excursion_after hn hT hp ht hsign.2
  obtain ⟨H,hH,hHl,hHr⟩ := hv.axis_peak hF hz hn
  obtain ⟨K,hK,hKl,hKr⟩ := hz.right_peak_at_extrema hF hn hT hp hs ht hb
  have hHK : H=K := (axisUpper_strictMono a).injOn hH hK (hHr.trans hKr.symm)
  have hvmin : (z v).2=(z s).2 := by rw [←hHl,hHK,hKl]
  obtain ⟨u,hu⟩ := hz.reverseX.right_excursion_before (reverseX_nonconstant hn) hT (reverseX_periodic hp)
    (t:=-v) (by simpa [QuinticLienard.reverseX] using congrArg Neg.neg hv.right)
    (by simpa [QuinticLienard.reverseX,polynomialReflect_eval,hvmin] using hsign.1)
  obtain ⟨L,hL,hLl,hLr⟩ := hu.axis_peak (a:=reflectX a)
    (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly]) hz.reverseX (reverseX_nonconstant hn)
  obtain ⟨M,hM,hMl,hMr⟩ := hz.reverseX.right_peak_at_extrema (a:=reflectX a)
    (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly])
    (reverseX_nonconstant hn) hT (reverseX_periodic hp) (s:=-s) (t:=-t)
    (by simpa [QuinticLienard.reverseX] using congrArg Neg.neg hs)
    (by simpa [QuinticLienard.reverseX] using congrArg Neg.neg ht)
    (fun v=>by simpa [QuinticLienard.reverseX] using hb (-v))
  simp only [QuinticLienard.reverseX,neg_neg] at hLl hLr hMl hMr
  have hLM : L=M := (axisLower_strictAnti (reflectX a)).injOn hL hM (by rw [hLl,hMl,hvmin])
  refine ⟨v,-u,hv,by simpa using hu,Prod.ext ?_ ?_⟩
  · have h := hu.left
    simp only [QuinticLienard.reverseX] at h
    rw [neg_eq_zero] at h
    exact h.trans ht.symm
  · rw [←hLr,hLM,hMr]
lemma IsPeriodicOrbit.oval {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {C : Set Plane} (hC : IsPeriodicOrbit F C) :
    ∃ (z : ℝ → Plane) (S T : ℝ), IsSolution F z ∧ 0<S ∧ S<T ∧
      Function.Periodic z T ∧ IsRightExcursion z 0 S ∧
      IsRightExcursion (QuinticLienard.reverseX z) (-T) (-S) ∧ C=range z := by
  obtain ⟨z,P,hz,hP,hp,hn,rfl⟩ := hC
  obtain ⟨s,t,hs,ht,hb⟩ := hz.y_extrema hP hp
  obtain ⟨v,w,hv,hw,he⟩ := hz.oval_at_max hF hn hP hp hs ht hb
  let f := fun u=>z (u+t)
  have hvw : v<w := by linarith [hw.lt]
  have hf : IsSolution F f := hz.shift t
  refine ⟨f,v-t,w-t,hf,sub_pos.mpr hv.lt,sub_lt_sub_right hvw _,?_,?_,?_,?_⟩
  · exact hf.periodic_of_hit (s:=0) (by simpa [f] using he)
  · refine ⟨by linarith [hv.lt],by simpa [f] using hv.left,by simpa [f] using hv.right,?_⟩
    intro u hu
    exact hv.positive (u+t) ⟨by linarith [hu.1],by linarith [hu.2]⟩
  · refine ⟨by linarith,?_,?_,?_⟩
    · simpa [QuinticLienard.reverseX,f] using hw.left
    · simpa [QuinticLienard.reverseX,f] using hw.right
    · intro u hu
      have H := hw.positive (u-t) ⟨by linarith [hu.1],by linarith [hu.2]⟩
      simpa [QuinticLienard.reverseX,f,sub_eq_add_neg,add_comm] using H
  · ext p
    constructor
    · rintro ⟨u,rfl⟩; exact ⟨u-t,by simp [f]⟩
    · rintro ⟨u,rfl⟩; exact mem_range_self _
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.StableExcursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology
namespace QuinticLienard
lemma stable_positive_arc {P : Type uP} [TopologicalSpace P] {p : P}
    {f g : P × ℝ → ℝ}
    (hd : ∀ q t, HasDerivAt (fun s=>f (q,s)) (g (q,t)) t)
    (hc : ∀ t ∈ Ioo (0:ℝ) 1, ContinuousAt f (p,t))
    (hg0 : ContinuousAt g (p,0)) (hg1 : ContinuousAt g (p,1))
    (hf0 : ∀ᶠ q in 𝓝 p, f (q,0)=0) (hf1 : ∀ᶠ q in 𝓝 p, f (q,1)=0)
    (hpos : ∀ t ∈ Ioo (0:ℝ) 1, 0<f (p,t))
    (h0 : 0<g (p,0)) (h1 : g (p,1)<0) :
    ∀ᶠ q in 𝓝 p, ∀ t ∈ Ioo (0:ℝ) 1, 0<f (q,t) := by
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp (hg0.eventually (eventually_gt_nhds h0))
  obtain ⟨C,hC,D,hD,hCD⟩ := mem_nhds_prod_iff.mp (hg1.eventually (eventually_lt_nhds h1))
  obtain ⟨e,he,heB⟩ := Metric.mem_nhds_iff.mp hB
  obtain ⟨d,hdp,hdD⟩ := Metric.mem_nhds_iff.mp hD
  let δ := min (min e d) 1 / 4
  have hδ : 0<δ := div_pos (lt_min (lt_min he hdp) zero_lt_one) (by norm_num)
  have hδe : δ<e := by dsimp [δ]; have h:=min_le_left (min e d) 1; have h':=min_le_left e d; linarith
  have hδd : δ<d := by dsimp [δ]; have h:=min_le_left (min e d) 1; have h':=min_le_right e d; linarith
  have hδ1 : δ<1/2 := by dsimp [δ]; have h:=min_le_right (min e d) 1; linarith
  have hmid : ∀ᶠ q in 𝓝 p, ∀ t ∈ Icc δ (1-δ), 0<f (q,t) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have ht' : t ∈ Ioo (0:ℝ) 1 := ⟨hδ.trans_le ht.1,by linarith [ht.2]⟩
    exact (hc t ht').eventually (eventually_gt_nhds (hpos t ht'))
  filter_upwards [hA,hC,hf0,hf1,hmid] with q hqA hqC hq0 hq1 hqm
  intro t ht
  by_cases htl : t≤δ
  · have hm : StrictMonoOn (fun s=>f (q,s)) (Icc 0 δ) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 δ)
        (fun s _=>(hd q s).continuousAt.continuousWithinAt)
      intro s hs
      rw [(hd q s).deriv]
      apply hAB ⟨hqA,heB ?_⟩
      have hs' := interior_subset hs
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hs'.1]
      exact hs'.2.trans_lt hδe
    have h:=hm ⟨le_rfl,hδ.le⟩ ⟨ht.1.le,htl⟩ ht.1
    simpa only [hq0] using h
  · by_cases htr : 1-δ≤t
    · have hm : StrictAntiOn (fun s=>f (q,s)) (Icc (1-δ) 1) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc (1-δ) 1)
          (fun s _=>(hd q s).continuousAt.continuousWithinAt)
        intro s hs
        rw [(hd q s).deriv]
        apply hCD ⟨hqC,hdD ?_⟩
        have hs' := interior_subset hs
        rw [Metric.mem_ball,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hs'.2)]
        linarith [hs'.1]
      have h:=hm ⟨htr,ht.2.le⟩ ⟨by linarith,le_rfl⟩ ht.2
      simpa only [hq1] using h
    · exact hqm t ⟨(lt_of_not_ge htl).le,(lt_of_not_ge htr).le⟩
lemma stable_positive_between {P : Type uP} [TopologicalSpace P] {p : P}
    {f g : P × ℝ → ℝ} {α β : P → ℝ}
    (hd : ∀ q t, HasDerivAt (fun s=>f (q,s)) (g (q,t)) t)
    (hc : Continuous f) (hg : Continuous g)
    (hα : ContinuousAt α p) (hβ : ContinuousAt β p)
    (hf0 : ∀ᶠ q in 𝓝 p,f (q,α q)=0) (hf1 : ∀ᶠ q in 𝓝 p,f (q,β q)=0)
    (hlt : α p<β p) (hpos : ∀ t ∈ Ioo (α p) (β p),0<f (p,t))
    (h0 : 0<g (p,α p)) (h1 : g (p,β p)<0) :
    ∀ᶠ q in 𝓝 p,α q<β q ∧ ∀ t ∈ Ioo (α q) (β q),0<f (q,t) := by
  let θ : P × ℝ → ℝ := fun q=>α q.1+(β q.1-α q.1)*q.2
  have hα' (t : ℝ) : ContinuousAt (fun q : P × ℝ=>α q.1) (p,t) := hα.comp continuousAt_fst
  have hβ' (t : ℝ) : ContinuousAt (fun q : P × ℝ=>β q.1) (p,t) := hβ.comp continuousAt_fst
  have hθ (t : ℝ) : ContinuousAt θ (p,t) :=
    (hα' t).add (((hβ' t).sub (hα' t)).mul continuousAt_snd)
  have hf : ∀ t,ContinuousAt (fun q : P × ℝ=>f (q.1,θ q)) (p,t) :=
    fun t=>hc.continuousAt.comp (continuousAt_fst.prodMk (hθ t))
  have hgg : ∀ t,ContinuousAt (fun q : P × ℝ=>(β q.1-α q.1)*g (q.1,θ q)) (p,t) :=
    fun t=>((hβ' t).sub (hα' t)).mul (hg.continuousAt.comp (continuousAt_fst.prodMk (hθ t)))
  have hdd (q : P) (t : ℝ) : HasDerivAt (fun s=>f (q,θ (q,s))) ((β q-α q)*g (q,θ (q,t))) t := by
    convert! (hd q (θ (q,t))).scomp t (((hasDerivAt_id t).const_mul (β q-α q)).const_add (α q)) using 1
    ring
  have hne := stable_positive_arc hdd (fun t _=>hf t) (hgg 0) (hgg 1)
    (by simpa [θ] using hf0) (by simpa [θ] using hf1)
    (fun t ht=>hpos _ ⟨by dsimp [θ];nlinarith [mul_pos (sub_pos.mpr hlt) ht.1],by dsimp [θ];nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr ht.2)]⟩)
    (by simpa [θ] using mul_pos (sub_pos.mpr hlt) h0)
    (by simpa [θ] using mul_neg_of_pos_of_neg (sub_pos.mpr hlt) h1)
  filter_upwards [hne,(hα.prodMk hβ).eventually (isOpen_lt continuous_fst continuous_snd |>.mem_nhds hlt)] with q hq hlq
  refine ⟨hlq,?_⟩
  intro t ht
  have hl : 0<β q-α q := sub_pos.mpr hlq
  have hu : (t-α q)/(β q-α q) ∈ Ioo (0:ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr ht.1) hl,(div_lt_one hl).mpr (sub_lt_sub_right ht.2 _)⟩
  have he : θ (q,(t-α q)/(β q-α q))=t := by dsimp [θ];field_simp;ring
  simpa only [he] using hq _ hu
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ReturnNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard
open ScaledProfile GlobalODE PartialCalculus
lemma ReturnFlow.continuous (R : ReturnFlow) : Continuous (fun p : ℝ × ℝ=>R.path p.1 p.2) :=
  (continuous_flow R.W R.lip R.bound).comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
lemma IsSolution.return_neighborhood {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} (hz : IsSolution F z)
    {S T : ℝ} (hS : 0<S) (hST : S<T) (hp : Function.Periodic z T)
    (hr : IsRightExcursion z 0 S) (hl : IsRightExcursion (QuinticLienard.reverseX z) (-T) (-S)) :
    ∃ R : ReturnFlow,
      ContDiffAt ℝ ω R.τ (z 0).2 ∧ ContDiffAt ℝ ω R.σ (z 0).2 ∧ R.τ (z 0).2=S ∧ R.σ (z 0).2=T ∧
      (∀ t ∈ Icc (-1) (T+1),R.path (z 0).2 t=z t) ∧
      (∀ᶠ s in 𝓝 (z 0).2,0<R.τ s ∧ R.τ s<R.σ s ∧
        IsRightExcursion (R.path s) 0 (R.τ s) ∧
        IsRightExcursion (QuinticLienard.reverseX (R.path s)) (-R.σ s) (-R.τ s) ∧
        (R.path s (R.τ s)).2<F.eval 0 ∧ F.eval 0<s ∧ F.eval 0<(R.path s (R.σ s)).2 ∧
        ∀ t ∈ Icc 0 (R.σ s),R.W (R.path s t)=vectorField F (R.path s t)) ∧
      ∀ U : Set Plane,IsOpen U → range z ⊆ U →
        ∀ᶠ s in 𝓝 (z 0).2,∀ t ∈ Icc 0 (R.σ s),R.path s t ∈ U := by
  have hT := hS.trans hST
  have hnon : ∃ u v,z u≠z v := by
    refine ⟨0,S/2,?_⟩
    intro he
    have hpos := hr.positive (S/2) ⟨by linarith,by linarith⟩
    rw [←he,hr.left] at hpos
    exact lt_irrefl _ hpos
  have hsign := hr.endpoint_signs hz hnon
  have hzT : z T=z 0 := by simpa using hp 0
  obtain ⟨W,K,L,hK,hL,hm,ha,he⟩ := hz.cutoff hF hT
  let f : ℝ × ℝ → Plane := fun q=>flow W hK hL (0,q.1) q.2
  have hfc : Continuous f := (continuous_flow W hK hL).comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  have hinit : ((0,(z 0).2):Plane)=z 0 := Prod.ext hr.left.symm rfl
  have hmatch (t : ℝ) (ht : t ∈ Icc (-1) (T+1)) : f ((z 0).2,t)=z t := by simpa [f,hinit] using hm t ht
  have han (t : ℝ) (ht : t ∈ Icc (-1) (T+1)) : ContDiffAt ℝ ω f ((z 0).2,t) := by
    have hg : ContDiffAt ℝ ω (fun q : ℝ × ℝ => (((0 : ℝ),q.1),q.2)) ((z 0).2,t) :=
      (contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd
    have hh : ContDiffAt ℝ ω (fun q : Plane × ℝ=>flow W hK hL q.1 q.2) ((0,(z 0).2),t) := by
      simpa only [hinit] using ha t ht
    exact hh.comp ((z 0).2,t) hg
  have hd (s t : ℝ) : HasDerivAt (fun v=>f (s,v)) (W (f (s,t))) t := flow_deriv W hK hL (0,s) t
  have hxd (s t : ℝ) : HasDerivAt (fun v=>(f (s,v)).1) (W (f (s,t))).1 t := by
    simpa using! (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hd s t)
  have heq (t : ℝ) (ht : t ∈ Icc (-1) (T+1)) : ∀ᶠ q in 𝓝 ((z 0).2,t),W (f q)=vectorField F (f q) := by
    have hh : ContinuousAt (fun q : ℝ × ℝ=>(((0:ℝ),q.1),q.2)) ((z 0).2,t) := by fun_prop
    have hhe := he t ht
    rw [←hinit] at hhe
    exact hh.eventually hhe
  have hSm : S ∈ Icc (-1) (T+1) := ⟨by linarith,by linarith⟩
  have hTm : T ∈ Icc (-1) (T+1) := ⟨by linarith,by linarith⟩
  have h0m : (0:ℝ) ∈ Icc (-1) (T+1) := ⟨by norm_num,by linarith⟩
  have hxS : (f ((z 0).2,S)).1=0 := by rw [hmatch S hSm,hr.right]
  have hxT : (f ((z 0).2,T)).1=0 := by rw [hmatch T hTm,hzT,hr.left]
  have hvS : (W (f ((z 0).2,S))).1=(z S).2-F.eval 0 := by
    rw [(heq S hSm).self_of_nhds,hmatch S hSm];simp [vectorField,hr.right]
  have hvT : (W (f ((z 0).2,T))).1=(z 0).2-F.eval 0 := by
    rw [(heq T hTm).self_of_nhds,hmatch T hTm,hzT];simp [vectorField,hr.left]
  obtain ⟨τ,hτ,hτ0,hτeq,_⟩ := transverse_hit (han S hSm).fst (hxd (z 0).2 S)
    (by rw [hvS];exact sub_ne_zero.mpr hsign.1.ne)
  obtain ⟨σ,hσ,hσ0,hσeq,_⟩ := transverse_hit (han T hTm).fst (hxd (z 0).2 T)
    (by rw [hvT];exact sub_ne_zero.mpr hsign.2.ne')
  have hτx : ∀ᶠ s in 𝓝 (z 0).2,(f (s,τ s)).1=0 := by simpa only [hxS] using hτeq
  have hσx : ∀ᶠ s in 𝓝 (z 0).2,(f (s,σ s)).1=0 := by simpa only [hxT] using hσeq
  have hv0 : (W (f ((z 0).2,0))).1=(z 0).2-F.eval 0 := by
    rw [(heq 0 h0m).self_of_nhds,hmatch 0 h0m];simp [vectorField,hr.left]
  have rightStable := stable_positive_between (α:=fun _ : ℝ=>(0:ℝ)) hxd hfc.fst (hK.continuous.comp hfc |>.fst)
    continuousAt_const hτ.continuousAt
    (Filter.Eventually.of_forall fun s=>by simp [f]) hτx
    (by simpa only [hτ0] using hS)
    (fun t ht=>by
      rw [hτ0] at ht
      rw [hmatch t ⟨by linarith [ht.1],by linarith [ht.2]⟩]
      exact hr.positive t ht)
    (by dsimp only [Function.comp_def,Pi.neg_apply];rw [hv0];exact sub_pos.mpr hsign.2)
    (by dsimp only [Function.comp_def,Pi.neg_apply];rw [hτ0,hvS];exact sub_neg.mpr hsign.1)
  have leftStable := stable_positive_between (fun s t=>(hxd s t).neg) hfc.fst.neg (hK.continuous.comp hfc |>.fst.neg)
    hτ.continuousAt hσ.continuousAt (hτx.mono fun _ h=>by simp [h]) (hσx.mono fun _ h=>by simp [h])
    (by simpa only [hτ0,hσ0] using hST)
    (fun t ht=>by
      rw [hτ0,hσ0] at ht
      dsimp only [Pi.neg_apply]
      rw [hmatch t ⟨by linarith [ht.1],by linarith [ht.2]⟩]
      simpa [QuinticLienard.reverseX] using hl.positive (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩)
    (by dsimp only [Function.comp_def,Pi.neg_apply];rw [hτ0,hvS];linarith [hsign.1])
    (by dsimp only [Function.comp_def,Pi.neg_apply];rw [hσ0,hvT];linarith [hsign.2])
  have hfaith : ∀ᶠ s in 𝓝 (z 0).2,∀ t ∈ Icc 0 (T+1),W (f (s,t))=vectorField F (f (s,t)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    exact fun t ht=>heq t ⟨by linarith [ht.1],ht.2⟩
  have hσbound : ∀ᶠ s in 𝓝 (z 0).2,σ s<T+1 := hσ.continuousAt.eventually (eventually_lt_nhds (show σ (z 0).2<T+1 by rw [hσ0];linarith))
  have hlow : ∀ᶠ s in 𝓝 (z 0).2,(f (s,τ s)).2<F.eval 0 := by
    have hc := hfc.snd.continuousAt.comp (continuousAt_id.prodMk hτ.continuousAt)
    exact hc.eventually (eventually_lt_nhds (by simpa only [Function.comp_def,id_eq,hτ0,hmatch S hSm] using hsign.1))
  have hhigh : ∀ᶠ s in 𝓝 (z 0).2,F.eval 0<(f (s,σ s)).2 := by
    have hc := hfc.snd.continuousAt.comp (continuousAt_id.prodMk hσ.continuousAt)
    exact hc.eventually (eventually_gt_nhds (by simpa only [Function.comp_def,id_eq,hσ0,hmatch T hTm,hzT] using hsign.2))
  let R : ReturnFlow := ⟨W,K,L,hK,hL,τ,σ⟩
  refine ⟨R,hτ,hσ,hτ0,hσ0,hmatch,?_,?_⟩
  · filter_upwards [rightStable,leftStable,hτx,hσx,hlow,hhigh,hfaith,hσbound,eventually_gt_nhds hsign.2] with s hrs hls hτs hσs hlo hhi hfa hbo hstart
    refine ⟨hrs.1,hls.1,⟨hrs.1,by simp [R,ReturnFlow.path],hτs,hrs.2⟩,?_,hlo,hstart,hhi,?_⟩
    · refine ⟨by dsimp [R];linarith [hls.1],?_,?_,?_⟩
      · simpa [QuinticLienard.reverseX,R,ReturnFlow.path,f] using congrArg Neg.neg hσs
      · simpa [QuinticLienard.reverseX,R,ReturnFlow.path,f] using congrArg Neg.neg hτs
      · intro t ht
        exact hls.2 (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
    · intro t ht
      exact hfa t ⟨ht.1,ht.2.trans hbo.le⟩
  · intro U hU hzU
    have hu : ∀ᶠ s in 𝓝 (z 0).2,∀ t ∈ Icc 0 (T+1),f (s,t) ∈ U := by
      apply isCompact_Icc.eventually_forall_of_forall_eventually
      intro t ht
      apply hfc.continuousAt.eventually
      rw [hmatch t ⟨by linarith [ht.1],ht.2⟩]
      exact hU.mem_nhds (hzU (mem_range_self t))
    filter_upwards [hu,hσbound] with s hs hb t ht
    exact hs t ⟨ht.1,ht.2.trans hb.le⟩
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.LocalExcursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff
open scoped Topology
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open RealAnalysis ScaledProfile ScalarArcs AxisFlow
lemma IsRightExcursion.graph_on {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} {s t : ℝ}
    (hc : Continuous z) (hz : ∀ v ∈ Icc s t, HasDerivAt z (vectorField F (z v)) v) (he : IsRightExcursion z s t) :
    ∃ u : ℝ → ℝ, Continuous u ∧ u (z t).2=0 ∧ u (z s).2=0 ∧
      (∀ y ∈ Ioo (z t).2 (z s).2,0<u y ∧ HasDerivAt u (φ a (u y)-y) y) ∧
      (∀ v ∈ Icc s t,u (z v).2=(z v).1^2/2) := by
  have hxd (v : ℝ) (hv : v ∈ Icc s t) : HasDerivAt (fun w=>(z w).1) ((z v).2-F.eval (z v).1) v := by
    simpa [vectorField] using! (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt v (hz v hv)
  have hyd (v : ℝ) (hv : v ∈ Icc s t) : HasDerivAt (fun w=>(z w).2) (-(z v).1) v := by
    simpa [vectorField] using! (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt v (hz v hv)
  have hanti : StrictAntiOn (fun v=>(z v).2) (Icc s t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc s t) hc.snd.continuousOn
    intro v hv
    rw [(hyd v (interior_subset hv)).deriv]
    exact neg_neg_of_pos (he.positive v (by simpa using hv))
  have hylt := hanti ⟨le_rfl,he.lt.le⟩ ⟨he.lt.le,le_rfl⟩ he.lt
  have hb : BijOn (fun v=>(z v).2) (Icc s t) (Icc (z t).2 (z s).2) := by
    refine ⟨?_,hanti.injOn,?_⟩
    · intro v hv
      exact ⟨hanti.antitoneOn hv ⟨he.lt.le,le_rfl⟩ hv.2,
        hanti.antitoneOn ⟨le_rfl,he.lt.le⟩ hv hv.1⟩
    · intro y hy
      exact intermediate_value_Icc' he.lt.le hc.snd.continuousOn hy
  obtain ⟨τ,hτc,hτmem,hτr,hτl⟩ := continuous_interval_inverse hylt.le hc.snd.continuousOn hb
  have hτint (y : ℝ) (hy : y ∈ Ioo (z t).2 (z s).2) : τ y ∈ Ioo s t := by
    have hm := hτmem y
    refine ⟨lt_of_le_of_ne hm.1 ?_,lt_of_le_of_ne hm.2 ?_⟩
    · intro hn
      have hh := hτr y (Ioo_subset_Icc_self hy)
      rw [←hn] at hh
      exact hy.2.ne hh.symm
    · intro hn
      have hh := hτr y (Ioo_subset_Icc_self hy)
      rw [hn] at hh
      exact hy.1.ne hh
  let u : ℝ → ℝ := fun y=>(z (τ y)).1^2/2
  have hu : ∀ v ∈ Icc s t,u (z v).2=(z v).1^2/2 := fun v hv=>by dsimp [u];rw [hτl v hv]
  refine ⟨u,(hc.fst.comp hτc).pow 2 |>.div_const 2,?_,?_,?_,hu⟩
  · rw [hu t ⟨he.lt.le,le_rfl⟩,he.right];norm_num
  · rw [hu s ⟨le_rfl,he.lt.le⟩,he.left];norm_num
  · intro y hy
    have hx := he.positive (τ y) (hτint y hy)
    have hτd : HasDerivAt τ (-(z (τ y)).1)⁻¹ y :=
      HasDerivAt.of_local_left_inverse hτc.continuousAt (hyd (τ y) (Ioo_subset_Icc_self (hτint y hy))) (neg_ne_zero.mpr hx.ne')
        ((show ∀ᶠ v in 𝓝 y,v ∈ Ioo (z t).2 (z s).2 from Ioo_mem_nhds hy.1 hy.2).mono fun v hv=>hτr v (Ioo_subset_Icc_self hv))
    refine ⟨div_pos (sq_pos_of_pos hx) (by norm_num),?_⟩
    convert! (((hxd (τ y) (Ioo_subset_Icc_self (hτint y hy))).pow 2).div_const 2).comp y hτd using 1
    symm
    change (2*(z (τ y)).1^(2-1)*((z (τ y)).2-F.eval (z (τ y)).1)/2)*(-(z (τ y)).1)⁻¹=φ a ((z (τ y)).1^2/2)-y
    rw [AxisFlow.φ_square a hx.le,←hF,hτr y (Ioo_subset_Icc_self hy)]
    field_simp [hx.ne']
    ring
lemma IsRightExcursion.axis_peak_on {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} {s t : ℝ}
    (hc : Continuous z) (hz : ∀ v ∈ Icc s t, HasDerivAt z (vectorField F (z v)) v)
    (hl : (z t).2<F.eval 0) (hr : F.eval 0<(z s).2) (he : IsRightExcursion z s t) :
    ∃ H ∈ transversePeaks a,axisEndpoint a false H=(z t).2 ∧ axisEndpoint a true H=(z s).2 := by
  obtain ⟨u,huc,hul,hur,hud,_⟩ := he.graph_on hF hc hz
  have hylt : (z t).2<(z s).2 := hl.trans hr
  have hu : IsOpenArch (φ a) u (z t).2 (z s).2 :=
    ⟨hylt,huc,hul,hur,fun y hy=>(hud y hy).1,fun y hy=>(hud y hy).2⟩
  obtain ⟨H,hH,hp,hpeak,_⟩ := hu.peak_exists
  obtain ⟨hlo,hro⟩ := hu.axis_endpoints (φ_smooth a) (φ_continuous a).continuousOn hH hp hpeak
  refine ⟨H,⟨hH,?_,?_⟩,hlo,hro⟩
  · change axisLower (φ a) H<poly a 0
    rw [hlo,←hF]
    exact hl
  · change poly a 0<axisUpper (φ a) H
    rw [hro,←hF]
    exact hr
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ReturnMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow GlobalODE
lemma axisPeak_endpoints {a : Fin 6 → ℝ} {r : ℝ} (hr : r ∈ axisWidths a) :
    axisEndpoint a false (axisPeak a r)=poly a 0+axisM a r-r ∧
    axisEndpoint a true (axisPeak a r)=poly a 0+axisM a r+r := by
  have hw := (axisPeak_spec a hr).2
  dsimp [axisWidth] at hw
  dsimp [axisM,axisCenter]
  constructor <;> linarith
lemma ReturnFlow.fixed_of_matching {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) (R : ReturnFlow) {r : ℝ}
    (hr : r ∈ matchingDomain a (reflectX a)) (hd : matchingDelta a (reflectX a) r=0)
    (hs : 0<R.τ (poly a 0+axisM a r+r)) (hST : R.τ (poly a 0+axisM a r+r)<R.σ (poly a 0+axisM a r+r))
    (hR : IsRightExcursion (R.path (poly a 0+axisM a r+r)) 0 (R.τ (poly a 0+axisM a r+r)))
    (hL : IsRightExcursion (QuinticLienard.reverseX (R.path (poly a 0+axisM a r+r)))
      (-R.σ (poly a 0+axisM a r+r)) (-R.τ (poly a 0+axisM a r+r)))
    (hlo : (R.path (poly a 0+axisM a r+r) (R.τ (poly a 0+axisM a r+r))).2<F.eval 0)
    (hhi : F.eval 0<poly a 0+axisM a r+r)
    (hhi' : F.eval 0<(R.path (poly a 0+axisM a r+r) (R.σ (poly a 0+axisM a r+r))).2)
    (hW : ∀ t ∈ Icc 0 (R.σ (poly a 0+axisM a r+r)),R.W (R.path (poly a 0+axisM a r+r) t)=vectorField F (R.path (poly a 0+axisM a r+r) t)) :
    R.path (poly a 0+axisM a r+r) (R.σ (poly a 0+axisM a r+r))=(0,poly a 0+axisM a r+r) := by
  let b := poly a 0+axisM a r+r
  have hpc : Continuous (R.path b) := R.continuous.comp (continuous_const.prodMk continuous_id)
  have hpd (t : ℝ) (ht : t ∈ Icc 0 (R.σ b)) : HasDerivAt (R.path b) (vectorField F (R.path b t)) t := by
    have H := flow_deriv R.W R.lip R.bound (0,b) t
    rw [show R.W (flow R.W R.lip R.bound (0,b) t)=vectorField F (R.path b t) from hW t ht] at H
    exact H
  obtain ⟨H,hH,hHa,hHb⟩ := hR.axis_peak_on hF hpc
    (fun t ht=>hpd t ⟨ht.1,ht.2.trans hST.le⟩) hlo (by simpa using hhi)
  have hPH := axisPeak_endpoints hr.1
  have hPK := axisPeak_endpoints hr.2
  have hHeq : H=axisPeak a r := (axisUpper_strictMono a).injOn hH (axisPeak_spec a hr.1).1 (by simpa [b] using hHb.trans (by simpa [b] using hPH.2.symm))
  have ha : (R.path b (R.τ b)).2=poly a 0+axisM a r-r := by rw [←hHa,hHeq,hPH.1]
  have hM : axisM a r=axisM (reflectX a) r := sub_eq_zero.mp hd
  have hzero : poly (reflectX a) 0=poly a 0 := by simp [reflectX_poly]
  have hzc : Continuous (QuinticLienard.reverseX (R.path b)) :=
    (hpc.fst.comp continuous_neg).neg.prodMk (hpc.snd.comp continuous_neg)
  have hzd (t : ℝ) (ht : t ∈ Icc (-R.σ b) (-R.τ b)) :
      HasDerivAt (QuinticLienard.reverseX (R.path b))
        (vectorField (polynomialReflect F) (QuinticLienard.reverseX (R.path b) t)) t := by
    have hv : -t ∈ Icc 0 (R.σ b) := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hd0 := (hpd (-t) hv).scomp t (hasDerivAt_id t).neg
    have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd0
    have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd0
    convert! hx.neg.prodMk hy using 1; simp [QuinticLienard.reverseX,vectorField]
  obtain ⟨K,hK,hKa,hKb⟩ := hL.axis_peak_on (a:=reflectX a)
    (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly]) hzc hzd
    (by simpa [QuinticLienard.reverseX] using hlo) (by simpa [QuinticLienard.reverseX] using hhi')
  simp only [QuinticLienard.reverseX,neg_neg] at hKa hKb
  have hKeq : K=axisPeak (reflectX a) r := (axisLower_strictAnti (reflectX a)).injOn hK (axisPeak_spec _ hr.2).1
    (by rw [hKa,ha,hPK.1,hzero,hM])
  apply Prod.ext
  · have hx := hL.left
    simpa [QuinticLienard.reverseX] using congrArg Neg.neg hx
  · rw [←hKb,hKeq,hPK.2,hzero,←hM]
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.OvalMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow RealAnalysis
lemma IsRightExcursion.nonconstant {z : ℝ → Plane} {s t : ℝ} (hr : IsRightExcursion z s t) : ∃ u v,z u≠z v := by
  refine ⟨s,(s+t)/2,?_⟩
  intro he
  have hh := hr.positive ((s+t)/2) ⟨by linarith [hr.lt],by linarith [hr.lt]⟩
  rw [←he,hr.left] at hh
  exact lt_irrefl _ hh
lemma IsSolution.oval_axis_positive {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    {S T : ℝ} (hS : 0<S) (hST : S<T) (hp : Function.Periodic z T)
    (hr : IsRightExcursion z 0 S) (hl : IsRightExcursion (QuinticLienard.reverseX z) (-T) (-S))
    {p : Plane} (hpr : p ∈ range z) (hpx : p.1=0) (hpy : F.eval 0<p.2) : p=z 0 := by
  have hT := hS.trans hST
  have hsign := hr.endpoint_signs hz hr.nonconstant
  have hzT : z T=z 0 := by simpa using hp 0
  rw [←hp.image_Icc hT 0] at hpr
  obtain ⟨t,ht,rfl⟩ := hpr
  simp only [zero_add,mem_Icc] at ht
  rcases eq_or_lt_of_le ht.1 with he|he
  · rw [←he]
  rcases eq_or_lt_of_le ht.2 with heT|heT
  · rw [heT,hzT]
  rcases lt_trichotomy t S with hs|hs|hs
  · exact False.elim ((ne_of_gt (hr.positive t ⟨he,hs⟩)) hpx)
  · subst t
    exact False.elim ((not_lt_of_ge hsign.1.le) hpy)
  · have hx := hl.positive (-t) ⟨by linarith,by linarith⟩
    simp only [QuinticLienard.reverseX,neg_neg,hpx,neg_zero] at hx
    exact False.elim (lt_irrefl _ hx)
lemma IsSolution.oval_matching {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} (hz : IsSolution F z)
    {S T : ℝ} (hp : Function.Periodic z T)
    (hr : IsRightExcursion z 0 S) (hl : IsRightExcursion (QuinticLienard.reverseX z) (-T) (-S)) :
    let r := ((z 0).2-(z S).2)/2
    r ∈ matchingDomain a (reflectX a) ∧ matchingDelta a (reflectX a) r=0 ∧ poly a 0+axisM a r+r=(z 0).2 := by
  have hzT : z T=z 0 := by simpa using hp 0
  obtain ⟨H,hH,hHa,hHb⟩ := hr.axis_peak hF hz hr.nonconstant
  obtain ⟨K,hK,hKa,hKb⟩ := hl.axis_peak (a:=reflectX a)
    (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly]) hz.reverseX (reverseX_nonconstant hr.nonconstant)
  simp only [QuinticLienard.reverseX,neg_neg,hzT] at hKa hKb
  dsimp only
  have hwH : axisWidth a H=((z 0).2-(z S).2)/2 := by rw [axisWidth,hHa,hHb]
  have hwK : axisWidth (reflectX a) K=((z 0).2-(z S).2)/2 := by rw [axisWidth,hKa,hKb]
  have hpa := axisPeak_eq a hH hwH
  have hpb := axisPeak_eq (reflectX a) hK hwK
  have hM : axisM a (((z 0).2-(z S).2)/2)=((z 0).2+(z S).2)/2-poly a 0 := by
    rw [axisM,hpa,axisCenter,hHa,hHb]
  have hMb : axisM (reflectX a) (((z 0).2-(z S).2)/2)=((z 0).2+(z S).2)/2-poly a 0 := by
    rw [axisM,hpb,axisCenter,hKa,hKb,reflectX_poly]
    simp
  refine ⟨⟨⟨H,hH,hwH⟩,⟨K,hK,hwK⟩⟩,?_,?_⟩
  · rw [matchingDelta,hM,hMb,sub_self]
  · rw [hM];ring
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CycleIsolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow RealAnalysis GlobalODE
lemma IsLimitCycle.matching {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {C : Set Plane} (hC : IsLimitCycle F C) :
    ∃ r,IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r ∧
      (0,poly a 0+axisM a r+r) ∈ C := by
  obtain ⟨z,S,T,hz,hS,hST,hp,hr,hl,hCz⟩ := hC.1.oval hF
  obtain ⟨hr0,hd0,hb0⟩ := hz.oval_matching hF hp hr hl
  let r0 := ((z 0).2-(z S).2)/2
  let b : ℝ → ℝ := fun r=>poly a 0+axisM a r+r
  change b r0=(z 0).2 at hb0
  obtain ⟨U,hU,hCU,hiso⟩ := hC.2
  have hzU : range z ⊆ U := hCz ▸ hCU
  obtain ⟨R,_,_,_,_,_,hne,hnear⟩ := hz.return_neighborhood hF hS hST hp hr hl
  have hbc : ContinuousAt b r0 :=
    (continuousAt_const.add (axisM_analytic a hr0.1).continuousAt).add continuousAt_id
  have hbt : Tendsto b (𝓝 r0) (𝓝 (z 0).2) := by simpa only [hb0] using hbc.tendsto
  have hne' := hbt.eventually hne
  have hnear' := hbt.eventually (hnear U hU hzU)
  have isolated : ∀ᶠ r in 𝓝 r0,r ∈ matchingDomain a (reflectX a) → matchingDelta a (reflectX a) r=0 → r=r0 := by
    filter_upwards [hne',hnear'] with r hn hu hmem hdelta
    obtain ⟨hs,hst,hR,hL,hlo,hhi,hhi',hW⟩ := hn
    have hfix := R.fixed_of_matching hF hmem hdelta hs hst hR hL hlo hhi hhi' hW
    have hper : Function.Periodic (R.path (b r)) (R.σ (b r)) := flow_periodic_of_hit R.W R.lip R.bound hfix
    have hsol : IsSolution F (R.path (b r)) := flow_true_of_closed R.W R.lip R.bound (hs.trans hst) hfix hW
    have horbit : IsPeriodicOrbit F (range (R.path (b r))) :=
      ⟨R.path (b r),R.σ (b r),hsol,hs.trans hst,hper,hR.nonconstant,rfl⟩
    have hin : range (R.path (b r)) ⊆ U := periodic_range_subset hper (hs.trans hst) hu
    have he : range (R.path (b r))=C := hiso _ horbit hin
    have hstart : ((0,b r):Plane) ∈ range z := by
      rw [←hCz,←he]
      exact ⟨0,R.path_zero _⟩
    have hpoint := hz.oval_axis_positive hS hST hp hr hl hstart rfl hhi
    have hbeq : b r=b r0 := (congrArg Prod.snd hpoint).trans hb0.symm
    have hPeq : axisPeak a r=axisPeak a r0 :=
      (axisUpper_strictMono a).injOn (axisPeak_spec a hmem.1).1 (axisPeak_spec a hr0.1).1
        (by rw [(axisPeak_endpoints hmem.1).2,(axisPeak_endpoints hr0.1).2];exact hbeq)
    calc r=axisWidth a (axisPeak a r) := (axisPeak_spec a hmem.1).2.symm
         _=axisWidth a (axisPeak a r0) := congrArg (axisWidth a) hPeq
         _=r0 := (axisPeak_spec a hr0.1).2
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp isolated
  refine ⟨r0,⟨hr0,hd0,ε,hε,?_⟩,?_⟩
  · intro r hr hmem hd
    apply hball ?_ hmem hd
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith [hr.1,hr.2]
  · rw [hCz]
    refine ⟨0,Prod.ext hr.left ?_⟩
    exact hb0.symm
lemma limitCycle_encard_le_matching {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) :
    {C : Set Plane | IsLimitCycle F C}.encard ≤
      {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r}.encard := by
  classical
  let f : {C : Set Plane // IsLimitCycle F C} → ℝ := fun C=>Classical.choose (C.prop.matching hF)
  have hf (C : {C : Set Plane // IsLimitCycle F C}) :
      IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) (f C) ∧
      (0,poly a 0+axisM a (f C)+f C) ∈ (C : Set Plane) := Classical.choose_spec (C.prop.matching hF)
  have hi : Function.Injective f := by
    intro C D he
    apply Subtype.ext
    exact C.prop.1.eq_of_common D.prop.1 (hf C).2 (by rw [he];exact (hf D).2)
  have hm : Set.MapsTo f univ {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r} :=
    fun C _=>(hf C).1
  have H := Set.encard_le_encard_of_injOn hm hi.injOn
  rw [Set.encard_univ] at H
  exact H
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CaseOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow RealAnalysis
lemma linear_pos_open {a E F : ℝ → ℝ} {l r : ℝ} (hlr : l<r)
    (ha : ContinuousOn a (Icc l r)) (hE : ContinuousOn E (Icc l r))
    (hd : ∀ s ∈ Ioo l r,HasDerivAt E (-a s*E s+F s) s)
    (hF : ∀ s ∈ Ioo l r,0<F s) (h0 : 0≤E l) : 0<E r := by
  let ac : ℝ → ℝ := fun s=>a (projIcc l r hlr.le s)
  have hc : Continuous ac := (continuousOn_iff_continuous_domRestrict.mp ha).comp continuous_projIcc
  let w : ℝ → ℝ := fun s=>Real.exp (∫ u in l..s,ac u)
  have hw : Continuous w := continuous_iff_continuousAt.mpr fun s=>((hc.integral_hasStrictDerivAt l s).hasDerivAt.exp).continuousAt
  have hwd (s : ℝ) (hs : s ∈ Ioo l r) : HasDerivAt (fun s=>w s*E s) (w s*F s) s := by
    have H := ((hc.integral_hasStrictDerivAt l s).hasDerivAt.exp).mul (hd s hs)
    have he : ac s=a s := by simp only [ac,projIcc_of_mem hlr.le (Ioo_subset_Icc_self hs)]
    rw [he] at H
    convert! H using 1
    dsimp only [w]
    ring
  have hm : StrictMonoOn (fun s=>w s*E s) (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hw.continuousOn.mul hE)
    intro s hs
    have hs' : s ∈ Ioo l r := by simpa using hs
    change 0<deriv (fun s=>w s*E s) s
    rw [(hwd s hs').deriv]
    exact mul_pos (Real.exp_pos _) (hF s hs')
  have hp := hm ⟨le_rfl,hlr.le⟩ ⟨hlr.le,le_rfl⟩ hlr
  have hw0 : w l=1 := by simp [w]
  dsimp only at hp
  rw [hw0,one_mul] at hp
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (h0.trans_lt hp)
lemma oddPart_pos {a : Fin 6 → ℝ} (h1 : 0≤a 1) (h3 : 0≤a 3) (h5 : 0≤a 5)
    (hne : a 1≠0 ∨ a 3≠0 ∨ a 5≠0) {u : ℝ} (hu : 0<u) : 0<oddPart a u := by
  have hr := root_pos hu
  have hA := mul_nonneg h1 hr.le
  have hB := mul_nonneg h3 (pow_nonneg hr.le 3)
  have hC := mul_nonneg h5 (pow_nonneg hr.le 5)
  rcases hne with h|h|h
  · have H := mul_pos (lt_of_le_of_ne h1 h.symm) hr
    dsimp [oddPart];linarith
  · have H := mul_pos (lt_of_le_of_ne h3 h.symm) (pow_pos hr 3)
    dsimp [oddPart];linarith
  · have H := mul_pos (lt_of_le_of_ne h5 h.symm) (pow_pos hr 5)
    dsimp [oddPart];linarith
lemma profile_odd_difference (a : Fin 6 → ℝ) {u v : ℝ} (hu : 0≤u) (hv : 0≤v) :
    φ a u-φ (reflectX a) v=(2*a 2+4*a 4*(u+v))*(u-v)+oddPart a u+oddPart a v := by
  have hu4 : (root u)^4=4*u^2 := by calc
    _=((root u)^2)^2 := by ring
    _=4*u^2 := by rw [root_sq hu];ring
  have hv4 : (root v)^4=4*v^2 := by calc
    _=((root v)^2)^2 := by ring
    _=4*v^2 := by rw [root_sq hv];ring
  rw [φ,φ,reflectX_poly]
  have hn (x : ℝ) : poly a (-x)=a 0-a 1*x+a 2*x^2-a 3*x^3+a 4*x^4-a 5*x^5 := by dsimp [poly];ring
  rw [hn]
  dsimp [poly,oddPart]
  rw [root_sq hu,root_sq hv,hu4,hv4]
  ring
lemma no_periodic_case1 {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) (h1 : 0≤a 1) (h3 : 0≤a 3) (h5 : 0≤a 5)
    (hne : a 1≠0 ∨ a 3≠0 ∨ a 5≠0) {C : Set Plane} : ¬IsPeriodicOrbit F C := by
  intro hC
  obtain ⟨z,S,T,hz,_,_,hp,hr,hl,_⟩ := hC.oval hF
  have hzT : z T=z 0 := by simpa using hp 0
  obtain ⟨u,hu,huA,huB,hud,_⟩ := hr.graph hF hz
  obtain ⟨v,hv,hvA,hvB,hvd,_⟩ := hl.graph (a:=reflectX a)
    (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly]) hz.reverseX
  simp only [QuinticLienard.reverseX,neg_neg,hzT] at hvA hvB hvd
  have hpos := linear_pos_open (a:=fun y=>-(2*a 2+4*a 4*(u y+v y)))
    (E:=fun y=>u y-v y) (F:=fun y=>oddPart a (u y)+oddPart a (v y)) (hr.y_lt hz)
    (by fun_prop) (hu.sub hv).continuousOn
    (fun y hy=>by
      convert! (hud y hy).2.sub (hvd y hy).2 using 1
      rw [show (φ a (u y)-y)-(φ (reflectX a) (v y)-y)=φ a (u y)-φ (reflectX a) (v y) by ring]
      rw [profile_odd_difference a (hud y hy).1.le (hvd y hy).1.le]
      ring)
    (fun y hy=>add_pos (oddPart_pos h1 h3 h5 hne (hud y hy).1) (oddPart_pos h1 h3 h5 hne (hvd y hy).1))
    (by rw [huA,hvA,sub_self])
  rw [huB,hvB,sub_self] at hpos
  exact lt_irrefl _ hpos
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CycleTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology
namespace QuinticLienard
lemma IsPeriodicOrbit.flipY {F : Polynomial ℝ} {C : Set Plane} (hC : IsPeriodicOrbit F C) :
    IsPeriodicOrbit (-F) (QuinticLienard.flipY '' C) := by
  obtain ⟨z,T,hz,hT,hp,hn,rfl⟩ := hC
  refine ⟨reverseY z,T,hz.reverseY,hT,reverseY_periodic hp,reverseY_nonconstant hn,?_⟩
  ext p
  constructor
  · rintro ⟨q,⟨t,rfl⟩,rfl⟩
    exact ⟨-t,by simp [reverseY]⟩
  · rintro ⟨t,rfl⟩
    exact ⟨z (-t),mem_range_self _,rfl⟩
lemma IsLimitCycle.map_homeomorph {F G : Polynomial ℝ} (e : Plane ≃ₜ Plane)
    (he : ∀ C,IsPeriodicOrbit F C → IsPeriodicOrbit G (e '' C))
    (he' : ∀ C,IsPeriodicOrbit G C → IsPeriodicOrbit F (e.symm '' C))
    {C : Set Plane} (hC : IsLimitCycle F C) : IsLimitCycle G (e '' C) := by
  obtain ⟨U,hU,hCU,hiso⟩ := hC.2
  refine ⟨he C hC.1,e '' U,e.isOpenMap U hU,image_mono hCU,?_⟩
  intro D hD hDU
  have hi : e.symm '' D ⊆ U := by
    rintro p ⟨q,hq,rfl⟩
    obtain ⟨v,hv,hvq⟩ := hDU hq
    simpa only [←hvq,e.symm_apply_apply] using hv
  have H := congrArg (fun S=>e '' S) (hiso _ (he' D hD) hi)
  simpa only [image_image,Function.comp_def,e.apply_symm_apply,image_id'] using H
lemma IsLimitCycle.flipY {F : Polynomial ℝ} {C : Set Plane} (hC : IsLimitCycle F C) :
    IsLimitCycle (-F) (QuinticLienard.flipY '' C) := by
  apply hC.map_homeomorph QuinticLienard.flipY (fun _ h=>h.flipY)
  intro D hD
  simpa only [flipY_symm,neg_neg] using hD.flipY
lemma limitCycle_encard_neg (F : Polynomial ℝ) :
    {C : Set Plane | IsLimitCycle F C}.encard={C : Set Plane | IsLimitCycle (-F) C}.encard := by
  have h (G : Polynomial ℝ) : {C : Set Plane | IsLimitCycle G C}.encard≤{C : Set Plane | IsLimitCycle (-G) C}.encard := by
    apply encard_le_encard_of_injOn (f:=fun C=>flipY '' C) (fun _ h=>h.flipY)
    exact (Set.image_injective.mpr flipY.injective).injOn
  exact le_antisymm (h F) (by simpa only [neg_neg] using h (-F))
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.UpperAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile AxisFlow RealAnalysis
lemma no_isolated_zero_of_zero_on {f : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hz : ∀ x ∈ J,f x=0) (x : ℝ) : ¬IsIsolatedZeroOn f J x := by
  rintro ⟨hx,_,ε,hε,hiso⟩
  have he : ∀ᶠ y in 𝓝[>] x,x<y ∧ y ∈ J ∧ y ∈ Ioo (x-ε) (x+ε) := by
    filter_upwards [self_mem_nhdsWithin,(show ∀ᶠ y in 𝓝 x,y∈J from hJ.mem_nhds hx).filter_mono inf_le_left,
      (show ∀ᶠ y in 𝓝 x,y∈Ioo (x-ε) (x+ε) from Ioo_mem_nhds (by linarith) (by linarith)).filter_mono inf_le_left] with y hy hyJ hyI
    exact ⟨hy,hyJ,hyI⟩
  obtain ⟨y,hxy,hyJ,hyI⟩ := he.exists
  exact (ne_of_gt hxy) (hiso y hyI hyJ (hz y hyJ))
lemma reflectX_eq_of_even {a : Fin 6 → ℝ} (h1 : a 1=0) (h3 : a 3=0) (h5 : a 5=0) : reflectX a=a := by
  ext i
  fin_cases i <;> simp [reflectX,h1,h3,h5]
lemma no_isolated_matching_even {a : Fin 6 → ℝ} (h1 : a 1=0) (h3 : a 3=0) (h5 : a 5=0) :
    {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r}=∅ := by
  apply eq_empty_of_forall_notMem
  intro r
  apply no_isolated_zero_of_zero_on (matchingDomain_open a (reflectX a))
  intro x _
  rw [matchingDelta,reflectX_eq_of_even h1 h3 h5,sub_self]
lemma upper_nonnegative {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) (h5 : 0≤a 5) : {C : Set Plane | IsLimitCycle F C}.encard≤2 := by
  by_cases h1 : 0≤a 1
  · by_cases h3 : 0≤a 3
    · by_cases hz : a 1=0 ∧ a 3=0 ∧ a 5=0
      · have H := limitCycle_encard_le_matching hF
        rw [no_isolated_matching_even hz.1 hz.2.1 hz.2.2,encard_empty] at H
        exact H.trans (by norm_num)
      · have hne : a 1≠0 ∨ a 3≠0 ∨ a 5≠0 := by tauto
        have he : {C : Set Plane | IsLimitCycle F C}=∅ := by
          apply eq_empty_of_forall_notMem
          intro C hC
          exact no_periodic_case1 hF h1 h3 h5 hne hC.1
        rw [he,encard_empty]
        norm_num
    · exact (limitCycle_encard_le_matching hF).trans (matching_isolated_case2 h1 (lt_of_not_ge h3) h5)
  · by_cases h3 : 0≤a 3
    · exact (limitCycle_encard_le_matching hF).trans (matching_isolated_case3 (lt_of_not_ge h1) h3 h5)
    · exact (limitCycle_encard_le_matching hF).trans (matching_isolated_case4 (lt_of_not_ge h1) (lt_of_not_ge h3) h5)
lemma quintic_representation {F : Polynomial ℝ} (hF : F.degree≤5) : ∀ x,F.eval x=poly (fun i : Fin 6=>F.coeff i) x := by
  have hd : F.natDegree≤5 := Polynomial.natDegree_le_of_degree_le hF
  intro x
  rw [Polynomial.eval_eq_sum_range' (show F.natDegree<6 by omega)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one,poly]
  norm_num
lemma upper_bound_oai (F : Polynomial ℝ) (hF : F.degree≤5) : {C : Set Plane | IsLimitCycle F C}.encard≤2 := by
  by_cases h5 : 0≤F.coeff 5
  · exact upper_nonnegative (quintic_representation hF) h5
  · rw [limitCycle_encard_neg F]
    have hd : (-F).degree≤5 := by simpa only [Polynomial.degree_neg] using hF
    apply upper_nonnegative (quintic_representation hd)
    simpa using (neg_nonneg.mpr (le_of_not_ge h5))
end QuinticLienard

end OAI
end

theorem solution : type_of% @OAI.QuinticLienard.upper_bound_oai := @OAI.QuinticLienard.upper_bound_oai
