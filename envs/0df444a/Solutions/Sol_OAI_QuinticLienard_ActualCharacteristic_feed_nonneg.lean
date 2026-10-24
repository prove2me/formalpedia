-- Prove2me | solution 1 for OAI.QuinticLienard.ActualCharacteristic.feed_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T18:13:20.344522+00:00
-- url     : https://prove2.me/submissions/9348a1b5-71e4-4bee-a701-d4c1ed5d296e

import Mathlib
import Definitions.Def_OAIQWQL000
import Theorems.Thm_OAI_QuinticLienard_ActualCharacteristic_fitted_slope_lt

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

theorem exists_analytic_local_flow [CompleteSpace E] (W : Path E → Path E)
    (V : E → E) (x₀ : E) (hW : ∀ u s, W u s = V (u s))
    (hsmooth : ContDiffAt ℝ ω W (constCLM x₀)) :
    ∃ f : E × ℝ → E, ContDiffAt ℝ ω f (x₀,0) ∧
      ∀ᶠ p in 𝓝 (x₀,(0:ℝ)),
        f (p.1,0) = p.1 ∧ HasDerivAt (fun t => f (p.1,t)) (V (f p)) p.2 :=
  exists_analytic_local_flow_eventually W V x₀ (Filter.Eventually.of_forall hW) hsmooth

section PolynomialFields
variable {ι : Type uι} [Fintype ι]

omit [Fintype ι] in
lemma scalarPolynomial_eval (p : MvPolynomial ι ℝ) (u : Path (ι → ℝ)) (s : UnitInterval) :
    scalarPolynomial p u s = MvPolynomial.eval (u s) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [scalarPolynomial]
  | add p q hp hq => simpa [scalarPolynomial, MvPolynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
    simpa [scalarPolynomial, MvPolynomial.eval₂_mul] using congrArg (· * u s i) hp

lemma contDiff_scalarPolynomial (p : MvPolynomial ι ℝ) :
    ContDiff ℝ ω (scalarPolynomial p) := by
  unfold scalarPolynomial
  induction p using MvPolynomial.induction_on with
  | C a => simpa [scalarPolynomial] using (contDiff_const : ContDiff ℝ ω (fun _ : Path (ι → ℝ) => algebraMap ℝ (Path ℝ) a))
  | add p q hp hq => simpa [scalarPolynomial, MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp =>
    simpa [scalarPolynomial, MvPolynomial.eval₂_mul] using hp.mul (coordinate i).contDiff

theorem polynomial_local_flow (P : ι → MvPolynomial ι ℝ) (x₀ : ι → ℝ) :
    ∃ f : (ι → ℝ) × ℝ → (ι → ℝ), ContDiffAt ℝ ω f (x₀,0) ∧
      ∀ᶠ p in 𝓝 (x₀,(0:ℝ)), f (p.1,0) = p.1 ∧
        HasDerivAt (fun t => f (p.1,t)) (fun i => MvPolynomial.eval (f p) (P i)) p.2 := by
  let W : Path (ι → ℝ) → Path (ι → ℝ) := fun u => assemble (fun i => scalarPolynomial (P i) u)
  have hW : ContDiff ℝ ω W :=
    (assemble (ι := ι)).contDiff.comp (contDiff_pi.mpr (fun i => contDiff_scalarPolynomial (P i)))
  apply exists_analytic_local_flow W (fun x i => MvPolynomial.eval x (P i)) x₀
  · intro u s
    ext i
    exact scalarPolynomial_eval (P i) u s
  · exact hW.contDiffAt

end PolynomialFields

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

theorem entire_profile_extension {φ : ℝ → ℝ} {h t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hht : h < t) :
    ∃ (ψ : ℝ → ℝ) (K B : ℝ≥0), ContDiff ℝ 1 ψ ∧ LipschitzWith K ψ ∧
      (∀ x, |ψ x| ≤ B) ∧ EqOn ψ φ (Icc h t) := by
  let b : ContDiffBump t := ⟨t-h,t-h+1,by linarith,by linarith⟩
  let ψ : ℝ → ℝ := fun x => b x*φ x
  have hd : ContDiff ℝ 1 ψ := b.contDiff.mul hφ
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

theorem entire_arch_exists {φ : ℝ → ℝ} {h t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hht : h < t) :
    ∃ u a b, IsArch φ u h t a b := by
  obtain ⟨ψ,K,B,hs,hK,hB,he⟩ := entire_profile_extension hφ hht
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

theorem actual_endpoint_families (Φ : P × ℝ → ℝ)
    (hΦ : ∀ p, ContDiff ℝ 1 (fun x => Φ (p,x)))
    {w : (P × ℝ) × ℝ → ℝ} {p : P} {t h a b A B : ℝ}
    (hwc : ∀ q, Continuous (fun y => w (q,y)))
    (hpeak : ∀ q, w (q,Φ q) = q.2)
    (hw : ∀ y ∈ Icc A B, ContDiffAt ℝ ω w ((p,t),y))
    (he : ∀ y ∈ Icc A B, ∀ᶠ q in 𝓝 ((p,t),y),
      HasDerivAt (fun s => w (q.1,s)) (Φ (q.1.1,w q)-q.2) q.2)
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
  refine ⟨l,r,hld,hrd,hl0,hr0,?_⟩
  filter_upwards [hle,hre,hnear,continuousAt_fst.eventually hode] with q hl hr hq ho
  apply IsArch.of_solution_and_hits (hΦ q.1.1) (hwc q.1)
    (fun y hy => ho y ⟨hq.1.le.trans hy.1,hy.2.trans hq.2.2.2.le⟩)
    hq.2.1 hq.2.2.1 (hpeak q.1) hl hr

omit [CompleteSpace P] in

theorem canonical_endpoints_contDiffAt (Φ : P × ℝ → ℝ)
    (hΦ : ∀ p, ContDiff ℝ 1 (fun x => Φ (p,x)))
    {p : P} {t h : ℝ} (hht : h < t)
    {l r : (P × ℝ) × ℝ → ℝ}
    (hl : ContDiffAt ℝ ω l ((p,t),h)) (hr : ContDiffAt ℝ ω r ((p,t),h))
    (he : ∀ᶠ q in 𝓝 ((p,t),h),
      ∃ u, IsArch (fun x => Φ (q.1.1,x)) u q.2 q.1.2 (l q) (r q)) :
    ContDiffAt ℝ ω (lowerFamily Φ) ((p,t),h) ∧
    ContDiffAt ℝ ω (upperFamily Φ) ((p,t),h) := by
  have ht : ∀ᶠ q : (P × ℝ) × ℝ in 𝓝 ((p,t),h), q.2 < q.1.2 :=
    continuousAt_snd.eventually_lt continuousAt_fst.snd hht
  have heq : ∀ᶠ q in 𝓝 ((p,t),h), lowerFamily Φ q = l q ∧ upperFamily Φ q = r q := by
    filter_upwards [he,ht] with q hq hqt
    obtain ⟨u,hu⟩ := hq
    obtain ⟨ψ,K,B,hs,hK,_,hψ⟩ := entire_profile_extension (hΦ q.1.1) hqt
    have hc := chosen_arch (entire_arch_exists (hΦ q.1.1) hqt)
    have hh := hc.unique hu hK hψ
    exact ⟨hh.1,hh.2.1⟩
  exact ⟨hl.congr_of_eventuallyEq (heq.mono fun _ h => h.1),
    hr.congr_of_eventuallyEq (heq.mono fun _ h => h.2)⟩

end QuinticLienard.ArcEndpoints

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CanonicalAnalytic
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
namespace QuinticLienard.CanonicalAnalytic
open ScalarArcs ArcEndpoints ArcFamilies
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

theorem endpoints (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hht : h < t) :
    ContDiffAt ℝ ω (lowerFamily Φ) ((p,t),h) ∧
    ContDiffAt ℝ ω (upperFamily Φ) ((p,t),h) := by
  have hφ (p : P) : ContDiff ℝ 1 (fun x => Φ (p,x)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  obtain ⟨u,a₀,b₀,hu⟩ := entire_arch_exists (hφ p) (show h-1 < t by linarith)
  obtain ⟨a,b,ha,hb,harch⟩ := hu.subarch (hφ p) (show h-1 < h by linarith) hht
  have hV : ContDiffOn ℝ 1 (field Φ) univ := by
    have hd : ContDiff ℝ ω (field Φ) :=
      contDiff_const.prodMk (((hΦ.comp (contDiff_fst.prodMk contDiff_snd.fst)).sub
        contDiff_snd.snd).prodMk contDiff_const)
    exact (hd.of_le (by simp)).contDiffOn
  obtain ⟨w,hwc,hwpeak,hwmatch,hwd,hwe⟩ := peak_family Φ isOpen_univ hV
    (fun x _ => hloc x) hΦ.contDiffAt hu.lower_lt_peak hu.peak_lt_upper
    hu.continuous hu.peak hu.equation (fun _ _ => mem_univ _)
  let A := (a₀+a)/2
  let B := (b+b₀)/2
  have hA : a₀ < A ∧ A < a := by dsimp [A]; constructor <;> linarith
  have hB : b < B ∧ B < b₀ := by dsimp [B]; constructor <;> linarith
  have hsub : Icc A B ⊆ Ioo a₀ b₀ :=
    fun _ hy => ⟨hA.1.trans_le hy.1,hy.2.trans_lt hB.2⟩
  have hwb : IsArch (fun x => Φ (p,x)) (fun y => w ((p,t),y)) h t a b := by
    apply IsArch.of_solution_and_hits (hφ p) (hwc (p,t))
      (fun y hy => (hwe y (hsub ⟨hA.2.le.trans hy.1,hy.2.trans hB.1.le⟩)).self_of_nhds)
      harch.lower_lt_peak harch.peak_lt_upper (hwpeak (p,t))
    · rw [hwmatch a ⟨ha.le,(harch.lower_lt_peak.trans hu.peak_lt_upper).le⟩]
      exact harch.lower
    · rw [hwmatch b ⟨(hu.lower_lt_peak.trans harch.peak_lt_upper).le,hb.le⟩]
      exact harch.upper
  obtain ⟨l,r,hl,hr,_,_,he⟩ := actual_endpoint_families Φ hφ hwc hwpeak
    (fun y hy => hwd y (Ioo_subset_Icc_self (hsub hy)))
    (fun y hy => hwe y (hsub hy)) hwb hA.2 hB.1 hΦ.continuous.continuousAt
  exact canonical_endpoints_contDiffAt Φ hφ hht hl hr
    (he.mono fun q hq => ⟨fun y => w (q.1,y),hq⟩)

end QuinticLienard.CanonicalAnalytic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PolynomialModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

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
namespace QuinticLienard.PolynomialModel

lemma local_flow_equiv {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (V : E → E) (W : F → F)
    (he : ∀ x, W (e x) = e (V x)) {x : E}
    (hf : ∃ f : F × ℝ → F, ContDiffAt ℝ ω f (e x,0) ∧
      ∀ᶠ q in 𝓝 (e x,(0:ℝ)), f (q.1,0) = q.1 ∧
        HasDerivAt (fun t => f (q.1,t)) (W (f q)) q.2) :
    ∃ f : E × ℝ → E, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ q in 𝓝 (x,(0:ℝ)), f (q.1,0) = q.1 ∧
        HasDerivAt (fun t => f (q.1,t)) (V (f q)) q.2 := by
  obtain ⟨f,hfd,hfe⟩ := hf
  let lift : E × ℝ → F × ℝ := fun q => (e q.1,q.2)
  have hl : ContDiff ℝ ω lift := (e.contDiff.comp contDiff_fst).prodMk contDiff_snd
  refine ⟨fun q => e.symm (f (lift q)),
    e.symm.contDiff.contDiffAt.comp (x,0) (hfd.comp (x,0) hl.contDiffAt),?_⟩
  filter_upwards [hl.continuous.continuousAt.eventually hfe] with q hq
  constructor
  · simp [lift,hq.1]
  · have hd := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt q.2 hq.2
    have hw : e.symm (W (f (lift q))) = V (e.symm (f (lift q))) := by
      rw [←e.apply_symm_apply (f (lift q)),he,e.symm_apply_apply,e.symm_apply_apply]
    simpa only [Function.comp_def,ContinuousLinearEquiv.coe_coe,hw] using hd

lemma stateEquiv_apply (z : ModelState) : stateEquiv z = ![z.1.1,z.1.2,z.2.1,z.2.2] := rfl

lemma profile_contDiff : ContDiff ℝ ω profile :=
  (contDiff_fst.fst.mul contDiff_snd).add
    ((contDiff_fst.snd.div_const 2).mul (contDiff_snd.pow 2))

lemma polynomial_representation (x : ModelState) :
    (fun i => MvPolynomial.eval (stateEquiv x) (polynomials i)) =
      stateEquiv (ArcFamilies.field profile x) := by
  ext i
  fin_cases i <;> simp [polynomials,stateEquiv_apply,ArcFamilies.field,profile]
  ring

theorem model_local_flow (x : ModelState) :
    ∃ f : ModelState × ℝ → ModelState, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ q in 𝓝 (x,(0:ℝ)), f (q.1,0) = q.1 ∧
        HasDerivAt (fun s => f (q.1,s)) (ArcFamilies.field profile (f q)) q.2 :=
  local_flow_equiv stateEquiv (ArcFamilies.field profile)
    (fun x i => MvPolynomial.eval x (polynomials i)) polynomial_representation
    (SmoothFlow.polynomial_local_flow polynomials (stateEquiv x))

end QuinticLienard.PolynomialModel

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

theorem peak_derivative_positive {w : ℝ × ℝ → ℝ} {φ : ℝ → ℝ}
    {t a b : ℝ} (hφ : ContDiff ℝ 1 φ)
    (hwc : Continuous (fun y => w (t,y)))
    (hw : ∀ y ∈ Icc a b, ContDiffAt ℝ ω w (t,y))
    (he : ∀ y ∈ Icc a b, ∀ᶠ q in 𝓝 (t,y),
      HasDerivAt (fun s => w (q.1,s)) (φ (w q)-q.2) q.2)
    (hp : ∀ᶠ s in 𝓝 t, w (s,φ s) = s)
    (hc : φ t ∈ Icc a b) : ∀ y ∈ Icc a b, 0 < first w (t,y) := by
  have hφd := hφ.differentiable (by norm_num)
  have init : first w (t,φ t) = 1 := by
    apply moving_peak_variation (hw _ hc) (hφd t) hp
    have hd := (he _ hc).self_of_nhds
    simpa only [hp.self_of_nhds,sub_self] using hd
  have hcoeff : Continuous (fun y => deriv φ (w (t,y))) :=
    (hφ.continuous_deriv (by norm_num)).comp hwc
  have hfirst : ContinuousOn (fun y => first w (t,y)) (Icc a b) := by
    intro y hy
    exact (((first_contDiffAt (hw y hy)).continuousAt).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hd := positive_homogeneous hcoeff hfirst
    (fun y hy => fixed_profile_variation (hw y hy) (hφd _) (he y hy)) hc init
  intro y hy
  rw [hd y hy]
  exact Real.exp_pos _

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
-- module Solutions.OAIQW_QuinticLienard.CanonicalVariation
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
namespace QuinticLienard.CanonicalVariation
open ScalarArcs ArcEndpoints ArcFamilies PartialCalculus ArchVariation

lemma canonical_of_arch {φ u : ℝ → ℝ} {h t a b : ℝ}
    (hu : IsArch φ u h t a b) (hφ : ContDiff ℝ 1 φ) (hht : h < t) :
    lower φ h t = a ∧ upper φ h t = b := by
  obtain ⟨ψ,K,B,_,hK,_,hψ⟩ := entire_profile_extension hφ hht
  have hc := chosen_arch (entire_arch_exists hφ hht)
  have hh := hc.unique hu hK hψ
  exact ⟨hh.1,hh.2.1⟩

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

theorem endpoint_witness (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hht : h < t) :
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
  have hφ (p : P) : ContDiff ℝ 1 (fun x => Φ (p,x)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  obtain ⟨u,a₀,b₀,hu⟩ := entire_arch_exists (hφ p) (show h-1 < t by linarith)
  obtain ⟨a,b,ha,hb,harch⟩ := hu.subarch (hφ p) (show h-1 < h by linarith) hht
  have hV : ContDiffOn ℝ 1 (field Φ) univ := by
    have hd : ContDiff ℝ ω (field Φ) :=
      contDiff_const.prodMk (((hΦ.comp (contDiff_fst.prodMk contDiff_snd.fst)).sub
        contDiff_snd.snd).prodMk contDiff_const)
    exact (hd.of_le (by simp)).contDiffOn
  obtain ⟨w,hwc,hwpeak,hwmatch,hwd,hwe⟩ := peak_family Φ isOpen_univ hV
    (fun x _ => hloc x) hΦ.contDiffAt hu.lower_lt_peak hu.peak_lt_upper
    hu.continuous hu.peak hu.equation (fun _ _ => mem_univ _)
  let A := (a₀+a)/2
  let B := (b+b₀)/2
  have hA : a₀ < A ∧ A < a := by dsimp [A]; constructor <;> linarith
  have hB : b < B ∧ B < b₀ := by dsimp [B]; constructor <;> linarith
  have hsub : Icc A B ⊆ Ioo a₀ b₀ :=
    fun _ hy => ⟨hA.1.trans_le hy.1,hy.2.trans_lt hB.2⟩
  have hwb : IsArch (fun x => Φ (p,x)) (fun y => w ((p,t),y)) h t a b := by
    apply IsArch.of_solution_and_hits (hφ p) (hwc (p,t))
      (fun y hy => (hwe y (hsub ⟨hA.2.le.trans hy.1,hy.2.trans hB.1.le⟩)).self_of_nhds)
      harch.lower_lt_peak harch.peak_lt_upper (hwpeak (p,t))
    · rw [hwmatch a ⟨ha.le,(harch.lower_lt_peak.trans hu.peak_lt_upper).le⟩]
      exact harch.lower
    · rw [hwmatch b ⟨(hu.lower_lt_peak.trans harch.peak_lt_upper).le,hb.le⟩]
      exact harch.upper
  obtain ⟨l,r,_,_,_,_,he⟩ := actual_endpoint_families Φ hφ hwc hwpeak
    (fun y hy => hwd y (Ioo_subset_Icc_self (hsub hy)))
    (fun y hy => hwe y (hsub hy)) hwb hA.2 hB.1 hΦ.continuous.continuousAt
  have hlr := canonical_of_arch hwb (hφ p) hht
  change lowerFamily Φ ((p,t),h) = a ∧ upperFamily Φ ((p,t),h) = b at hlr
  have hinc : Icc (lowerFamily Φ ((p,t),h)) (upperFamily Φ ((p,t),h)) ⊆
      Ioo a₀ b₀ := by
    rw [hlr.1,hlr.2]
    exact fun _ hy => ⟨ha.trans_le hy.1,hy.2.trans_lt hb⟩
  refine ⟨w,hwc,hwpeak,fun y hy => hwd y (Ioo_subset_Icc_self (hinc hy)),
    fun y hy => hwe y (hinc hy),?_⟩
  have ht : ∀ᶠ q : (P × ℝ) × ℝ in 𝓝 ((p,t),h), q.2 < q.1.2 :=
    continuousAt_snd.eventually_lt continuousAt_fst.snd hht
  filter_upwards [he,ht] with q hq hqt
  have hcanon := canonical_of_arch hq (hφ q.1.1) hqt
  change lowerFamily Φ q = l q ∧ upperFamily Φ q = r q at hcanon
  rwa [hcanon.1,hcanon.2]

theorem peak_signs (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hht : h < t) :
    deriv (fun s => lowerFamily Φ ((p,s),h)) t < 0 ∧
      0 < deriv (fun s => upperFamily Φ ((p,s),h)) t := by
  obtain ⟨w,hwc,hpeak,hwd,hwe,harch⟩ := endpoint_witness Φ hΦ hloc hht
  have hu := harch.self_of_nhds
  have hφ : ContDiff ℝ 1 (fun x => Φ (p,x)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
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
  have hh := peak_derivative_positive hφ (hwc (p,t)) hw₀ he₀
    (Eventually.of_forall (fun s => hpeak (p,s)))
    ⟨hu.lower_lt_peak.le,hu.peak_lt_upper.le⟩
  obtain ⟨hl,hr⟩ := CanonicalAnalytic.endpoints Φ hΦ hloc (p := p) hht
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

theorem base_derivatives (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hht : h < t) :
    HasDerivAt (fun s => lowerFamily Φ ((p,t),s))
      (1/(Φ (p,h)-lowerFamily Φ ((p,t),h))) h ∧
    HasDerivAt (fun s => upperFamily Φ ((p,t),s))
      (1/(Φ (p,h)-upperFamily Φ ((p,t),h))) h := by
  obtain ⟨w,_,_,_,_,he⟩ := endpoint_witness Φ hΦ hloc hht
  have hu := he.self_of_nhds
  obtain ⟨hl,hr⟩ := CanonicalAnalytic.endpoints Φ hΦ hloc (p := p) hht
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

theorem peak_width_midpoint_bounds (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hht : h < t) :
    0 < deriv (fun s => width (fun u => Φ (p,u)) h s) t ∧
      |deriv (fun s => midpoint (fun u => Φ (p,u)) h s) t /
        deriv (fun s => width (fun u => Φ (p,u)) h s) t| < 1 := by
  obtain ⟨hl,hr⟩ := CanonicalAnalytic.endpoints Φ hΦ hloc (p := p) hht
  have hld := (hl.comp t
    ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt
      (by simp)
  have hrd := (hr.comp t
    ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt
      (by simp)
  obtain ⟨hls,hrs⟩ := peak_signs Φ hΦ hloc hht
  have hb := width_midpoint_peak_bounds hld hrd hls hrs
  have hmid : deriv (fun s => midpoint (fun u => Φ (p,u)) h s) t =
      deriv (fun s => (upperFamily Φ ((p,s),h)+lowerFamily Φ ((p,s),h))/2) t := by
    exact (((hrd.hasDerivAt.add hld.hasDerivAt).div_const 2).sub_const (Φ (p,h))).deriv.trans
      (((hrd.hasDerivAt.add hld.hasDerivAt).div_const 2).deriv.symm)
  rw [hmid]
  exact hb

end QuinticLienard.CanonicalVariation

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.WidthCoordinates
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
namespace QuinticLienard.WidthCoordinates
open ScalarArcs ArcEndpoints ArcFamilies CanonicalVariation

theorem width_small_base {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, t-δ < h → h < t → width φ h t < ε := by
  obtain ⟨u,a,b,hu⟩ := entire_arch_exists hφ (show t-1 < t by linarith)
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
  let H := max (t-1) (max (u (φ t-d)) (u (φ t+d)))
  have hH : H < t := max_lt (by linarith) (max_lt hutl hutr)
  refine ⟨t-H,sub_pos.mpr hH,?_⟩
  intro h hh hht
  have hHh : H < h := by linarith
  have h₀ : t-1 < h := (le_max_left _ _).trans_lt hHh
  have hlh : u (φ t-d) < h :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hHh
  have hrh : u (φ t+d) < h :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hHh
  obtain ⟨l,r,hal,hrb,hv⟩ := hu.subarch hφ h₀ hht
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
  obtain ⟨heql,heqr⟩ := canonical_of_arch hv hφ hht
  dsimp [width]
  rw [heql,heqr]
  linarith

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)

include hΦ hloc

theorem width_analytic {p : P} {t h : ℝ} (hht : h < t) :
    ContDiffAt ℝ ω (widthFamily Φ) ((p,t),h) := by
  obtain ⟨hl,hr⟩ := CanonicalAnalytic.endpoints Φ hΦ hloc (p := p) hht
  exact (hr.sub hl).div_const 2

theorem midpoint_analytic {p : P} {t h : ℝ} (hht : h < t) :
    ContDiffAt ℝ ω (midpointFamily Φ) ((p,t),h) := by
  obtain ⟨hl,hr⟩ := CanonicalAnalytic.endpoints Φ hΦ hloc (p := p) hht
  exact ((hr.add hl).div_const 2).sub
    (hΦ.contDiffAt.comp ((p,t),h) (contDiffAt_fst.fst.prodMk contDiffAt_snd))

omit hloc [FiniteDimensional ℝ P] in
theorem width_pos {p : P} {t h : ℝ} (hht : h < t) :
    0 < widthFamily Φ ((p,t),h) := by
  have hφ : ContDiff ℝ 1 (fun u => Φ (p,u)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hu := chosen_arch (entire_arch_exists hφ hht)
  dsimp [widthFamily,width]
  linarith [hu.lower_lt_peak,hu.peak_lt_upper]

omit hloc [FiniteDimensional ℝ P] in
theorem gap_pos {p : P} {t h : ℝ} (hht : h < t) :
    0 < (widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2 := by
  have hφ : ContDiff ℝ 1 (fun u => Φ (p,u)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hb := midpoint_abs_lt_width (entire_arch_exists hφ hht)
  have ha := width_pos Φ hΦ (p := p) hht
  change |midpointFamily Φ ((p,t),h)| < widthFamily Φ ((p,t),h) at hb
  exact sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos ha] using hb))

theorem width_base_deriv {p : P} {t h : ℝ} (hht : h < t) :
    HasDerivAt (fun s => widthFamily Φ ((p,t),s))
      (-widthFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2)) h := by
  obtain ⟨hl,hr⟩ := base_derivatives Φ hΦ hloc (p := p) hht
  have hφ : ContDiff ℝ 1 (fun u => Φ (p,u)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hu := chosen_arch (entire_arch_exists hφ hht)
  have hlne : Φ (p,h)-lowerFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hu.lower_transverse)
  have hrne : Φ (p,h)-upperFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_lt (sub_neg.mpr hu.upper_transverse)
  have hqne := ne_of_gt (gap_pos Φ hΦ (p := p) hht)
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
    AntitoneOn (fun h => (widthFamily Φ ((p,t),h))^2+2*h) (Iio t) := by
  let f : ℝ → ℝ := fun h => (widthFamily Φ ((p,t),h))^2+2*h
  have hd (h : ℝ) (hh : h ∈ Iio t) : HasDerivAt f
      (2 * widthFamily Φ ((p,t),h) *
        (-widthFamily Φ ((p,t),h) /
          ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2))+2) h := by
    simpa [f] using! ((width_base_deriv Φ hΦ hloc (p := p) hh).pow 2).add
      ((hasDerivAt_id h).const_mul 2)
  apply antitoneOn_of_deriv_nonpos (convex_Iio t)
    (fun h hh => (hd h hh).continuousAt.continuousWithinAt)
    (fun h hh => (hd h (interior_subset (s := Iio t) hh)).differentiableAt.differentiableWithinAt)
  intro h hh
  rw [(hd h (interior_subset (s := Iio t) hh)).deriv]
  have hq := gap_pos Φ hΦ (p := p) (show h < t from interior_subset (s := Iio t) hh)
  have he : 2 * widthFamily Φ ((p,t),h) *
        (-widthFamily Φ ((p,t),h) /
          ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2))+2 =
      -(2*(midpointFamily Φ ((p,t),h))^2) /
          ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) := by
    field_simp
    ring
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (by norm_num) (sq_nonneg _))) hq.le

theorem height_bound {p : P} {t h : ℝ} (hht : h < t) :
    2*(t-h) ≤ (widthFamily Φ ((p,t),h))^2 := by
  have ha := height_energy_antitone Φ hΦ hloc p t
  by_contra hn
  have hw := sq_nonneg (widthFamily Φ ((p,t),h))
  let H := ((widthFamily Φ ((p,t),h))^2/2+h+t)/2
  have hH : h < H := by dsimp [H]; linarith
  have hHt : H < t := by dsimp [H]; linarith
  have hle := ha hht hHt hH.le
  have hW := sq_nonneg (widthFamily Φ ((p,t),H))
  dsimp [H] at hle hW
  linarith

theorem width_strictAnti_base (p : P) (t : ℝ) :
    StrictAntiOn (fun h => widthFamily Φ ((p,t),h)) (Iio t) := by
  apply strictAntiOn_of_deriv_neg (convex_Iio t)
    (fun h hh => (width_base_deriv Φ hΦ hloc hh).continuousAt.continuousWithinAt)
  intro h hh
  rw [(width_base_deriv Φ hΦ hloc (p := p) (show h < t from interior_subset (s := Iio t) hh)).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (width_pos Φ hΦ (p := p) (show h < t from interior_subset (s := Iio t) hh)))
    (gap_pos Φ hΦ (p := p) (show h < t from interior_subset (s := Iio t) hh))

theorem width_strictMono_peak (p : P) (h : ℝ) :
    StrictMonoOn (fun t => widthFamily Φ ((p,t),h)) (Ioi h) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi h)
  · intro t ht
    exact ((width_analytic Φ hΦ hloc ht).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).continuousAt.continuousWithinAt
  · intro t ht
    exact (peak_width_midpoint_bounds Φ hΦ hloc (p := p) (interior_subset ht)).1

theorem small_peak_exists (p : P) (h : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t > h, widthFamily Φ ((p,t),h) < ε := by
  have hφ : ContDiff ℝ 1 (fun u => Φ (p,u)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  obtain ⟨δ,hδ,hsmall⟩ := width_small_base hφ h hε
  let b := h-δ/2
  have hbh : b < h := by dsimp [b]; linarith
  have hwb : widthFamily Φ ((p,h),b) < ε :=
    hsmall b (by dsimp [b]; linarith) hbh
  have hg : ContinuousAt (fun t : ℝ => ((p,t),b)) h :=
    (continuousAt_const.prodMk continuousAt_id).prodMk continuousAt_const
  have hc : ContinuousAt (fun t => widthFamily Φ ((p,t),b)) h :=
    ContinuousAt.comp (f := fun t : ℝ => ((p,t),b)) (g := widthFamily Φ)
      (x := h) (width_analytic Φ hΦ hloc (p := p) hbh).continuousAt hg
  obtain ⟨η,hη,hnear⟩ := Metric.eventually_nhds_iff.mp
    (hc.eventually_lt continuousAt_const hwb)
  let t := h+η/2
  have hht : h < t := by dsimp [t]; linarith
  have hsmallt : widthFamily Φ ((p,t),b) < ε :=
    hnear (by rw [Real.dist_eq]; dsimp [t]; rw [abs_of_pos (by linarith)]; linarith)
  exact ⟨t,hht,((width_strictAnti_base Φ hΦ hloc p t)
    (hbh.trans hht) hht hbh).trans hsmallt⟩

theorem peak_exists (p : P) (h : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃! t, h < t ∧ widthFamily Φ ((p,t),h) = r := by
  obtain ⟨a,ha,har⟩ := small_peak_exists Φ hΦ hloc p h hr
  let b := a+r^2+1
  have hab : a < b := by dsimp [b]; nlinarith [sq_nonneg r]
  have hhb : h < b := ha.trans hab
  have hbr : r < widthFamily Φ ((p,b),h) := by
    have hb := height_bound Φ hΦ hloc (p := p) hhb
    have hw := width_pos Φ hΦ (p := p) hhb
    dsimp [b] at hb
    nlinarith
  have hc : ContinuousOn (fun t => widthFamily Φ ((p,t),h)) (Icc a b) := by
    intro t ht
    exact ((width_analytic Φ hΦ hloc (ha.trans_le ht.1)).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).continuousAt.continuousWithinAt
  obtain ⟨t,ht,htr⟩ := intermediate_value_Icc hab.le hc ⟨har.le,hbr.le⟩
  refine ⟨t,⟨ha.trans_le ht.1,htr⟩,?_⟩
  intro s hs
  exact (width_strictMono_peak Φ hΦ hloc p h).injOn hs.1 (ha.trans_le ht.1)
    (hs.2.trans htr.symm)

theorem base_exists (p : P) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃! h, h < t ∧ widthFamily Φ ((p,t),h) = r := by
  have hφ : ContDiff ℝ 1 (fun u => Φ (p,u)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  obtain ⟨δ,hδ,hsmall⟩ := width_small_base hφ t hr
  let b := t-δ/2
  have hbt : b < t := by dsimp [b]; linarith
  have hbr : widthFamily Φ ((p,t),b) < r := hsmall b (by dsimp [b]; linarith) hbt
  let a := b-r^2-1
  have hab : a < b := by dsimp [a]; nlinarith [sq_nonneg r]
  have hat : a < t := hab.trans hbt
  have har : r < widthFamily Φ ((p,t),a) := by
    have hb := height_bound Φ hΦ hloc (p := p) hat
    have hw := width_pos Φ hΦ (p := p) hat
    dsimp [a] at hb
    nlinarith
  have hc : ContinuousOn (fun h => widthFamily Φ ((p,t),h)) (Icc a b) := by
    intro h hh
    exact (width_base_deriv Φ hΦ hloc (hh.2.trans_lt hbt)).continuousAt.continuousWithinAt
  obtain ⟨h,hh,hhr⟩ := intermediate_value_Icc' hab.le hc ⟨hbr.le,har.le⟩
  refine ⟨h,⟨hh.2.trans_lt hbt,hhr⟩,?_⟩
  intro s hs
  exact (width_strictAnti_base Φ hΦ hloc p t).injOn hs.1 (hh.2.trans_lt hbt)
    (hs.2.trans hhr.symm)

theorem peak_spec {p : P} {h r : ℝ} (hr : 0 < r) :
    h < peakAtWidth Φ ((p,h),r) ∧
      widthFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) = r :=
  Classical.epsilon_spec (peak_exists Φ hΦ hloc p h hr).exists

theorem base_spec {p : P} {t r : ℝ} (hr : 0 < r) :
    baseAtWidth Φ ((p,t),r) < t ∧
      widthFamily Φ ((p,t),baseAtWidth Φ ((p,t),r)) = r :=
  Classical.epsilon_spec (base_exists Φ hΦ hloc p t hr).exists

theorem peak_eq {p : P} {h r t : ℝ} (hr : 0 < r) (hht : h < t)
    (he : widthFamily Φ ((p,t),h) = r) : peakAtWidth Φ ((p,h),r) = t := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  exact (width_strictMono_peak Φ hΦ hloc p h).injOn hs.1 hht (hs.2.trans he.symm)

theorem base_eq {p : P} {t r h : ℝ} (hr : 0 < r) (hht : h < t)
    (he : widthFamily Φ ((p,t),h) = r) : baseAtWidth Φ ((p,t),r) = h := by
  have hs := base_spec Φ hΦ hloc (p := p) (t := t) hr
  exact (width_strictAnti_base Φ hΦ hloc p t).injOn hs.1 hht (hs.2.trans he.symm)

theorem peak_analytic {p : P} {h r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ω (peakAtWidth Φ) ((p,h),r) := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  let W : (P × ℝ) × ℝ → ℝ := fun q => widthFamily Φ ((q.1.1,q.2),q.1.2)
  have hwd : ContDiffAt ℝ ω W ((p,h),t) :=
    (width_analytic Φ hΦ hloc hs.1).comp ((p,h),t)
      ((contDiffAt_fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)
  have hwtd : DifferentiableAt ℝ (fun s => W ((p,h),s)) t :=
    (hwd.comp t (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hdpos : 0 < deriv (fun s => W ((p,h),s)) t :=
    (peak_width_midpoint_bounds Φ hΦ hloc hs.1).1
  obtain ⟨Y,hY,hY0,he⟩ := level_hit hwd hwtd.hasDerivAt hs.2 hdpos.ne'
  have hlt : ∀ᶠ q in 𝓝 ((p,h),r), q.1.2 < Y q :=
    continuousAt_fst.snd.eventually_lt hY.continuousAt (by simpa only [hY0] using hs.1)
  have hpos : ∀ᶠ q : (P × ℝ) × ℝ in 𝓝 ((p,h),r), 0 < q.2 :=
    continuousAt_const.eventually_lt continuousAt_snd hr
  apply hY.congr_of_eventuallyEq
  filter_upwards [he,hlt,hpos] with q hq hltq hposq
  exact peak_eq Φ hΦ hloc hposq hltq hq

theorem base_analytic {p : P} {t r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ω (baseAtWidth Φ) ((p,t),r) := by
  let h := baseAtWidth Φ ((p,t),r)
  have hs := base_spec Φ hΦ hloc (p := p) (t := t) hr
  have hwd := width_analytic Φ hΦ hloc (p := p) hs.1
  have hd := width_base_deriv Φ hΦ hloc (p := p) hs.1
  have hdneg : -widthFamily Φ ((p,t),h) /
      ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (width_pos Φ hΦ hs.1)) (gap_pos Φ hΦ hs.1)
  obtain ⟨Y,hY,hY0,he⟩ := level_hit hwd hd hs.2 hdneg.ne
  have hlt : ∀ᶠ q in 𝓝 ((p,t),r), Y q < q.1.2 :=
    hY.continuousAt.eventually_lt continuousAt_fst.snd (by simpa only [hY0] using hs.1)
  have hpos : ∀ᶠ q : (P × ℝ) × ℝ in 𝓝 ((p,t),r), 0 < q.2 :=
    continuousAt_const.eventually_lt continuousAt_snd hr
  apply hY.congr_of_eventuallyEq
  filter_upwards [he,hlt,hpos] with q hq hltq hposq
  exact base_eq Φ hΦ hloc hposq hltq hq

theorem midpointAtWidth_analytic {p : P} {h r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ω (midpointAtWidth Φ) ((p,h),r) := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  exact (midpoint_analytic Φ hΦ hloc hs.1).comp ((p,h),r)
    ((contDiffAt_fst.fst.prodMk (peak_analytic Φ hΦ hloc hr)).prodMk contDiffAt_fst.snd)

theorem midpointAtWidth_abs_lt {p : P} {h r : ℝ} (hr : 0 < r) :
    |midpointAtWidth Φ ((p,h),r)| < r := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  have hφ : ContDiff ℝ 1 (fun u => Φ (p,u)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hb := midpoint_abs_lt_width (entire_arch_exists hφ hs.1)
  change |midpointAtWidth Φ ((p,h),r)| < widthFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) at hb
  rwa [hs.2] at hb

end QuinticLienard.WidthCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.WidthTransport
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
namespace QuinticLienard.WidthTransport
open ScalarArcs ArcEndpoints ArcFamilies CanonicalVariation WidthCoordinates PartialCalculus
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

theorem peak_width_deriv {p : P} {h r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => peakAtWidth Φ ((p,h),s))
      (1/deriv (fun t => widthFamily Φ ((p,t),h)) (peakAtWidth Φ ((p,h),r))) r := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  let f : ℝ → ℝ := fun t => widthFamily Φ ((p,t),h)
  let g : ℝ → ℝ := fun s => peakAtWidth Φ ((p,h),s)
  have hf : DifferentiableAt ℝ f t :=
    ((width_analytic Φ hΦ hloc hs.1).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ g r :=
    ((peak_analytic Φ hΦ hloc hr).comp r
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have he : (f ∘ g) =ᶠ[𝓝 r] id := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact (peak_spec Φ hΦ hloc hs).2
  have hc := (hf.hasDerivAt.comp r hg.hasDerivAt).unique
    ((hasDerivAt_id r).congr_of_eventuallyEq he)
  have hp : 0 < deriv f t := (peak_width_midpoint_bounds Φ hΦ hloc hs.1).1
  have heq : deriv g r = 1/deriv f t := by
    apply (eq_div_iff hp.ne').mpr
    simpa only [mul_comm] using hc
  simpa only [heq] using hg.hasDerivAt

theorem midpoint_width_deriv_abs_lt {p : P} {h r : ℝ} (hr : 0 < r) :
    |deriv (fun s => midpointAtWidth Φ ((p,h),s)) r| < 1 := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  let m : ℝ → ℝ := fun t => midpointFamily Φ ((p,t),h)
  have hm : DifferentiableAt ℝ m t :=
    ((midpoint_analytic Φ hΦ hloc hs.1).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hc := hm.hasDerivAt.comp r (peak_width_deriv Φ hΦ hloc hr)
  have hder : deriv (fun s => midpointAtWidth Φ ((p,h),s)) r =
      deriv m t / deriv (fun t => widthFamily Φ ((p,t),h)) t := by
    simpa only [Function.comp_def,mul_one_div,midpointAtWidth,m,t] using! hc.deriv
  rw [hder]
  exact (peak_width_midpoint_bounds Φ hΦ hloc (p := p) hs.1).2

theorem midpoint_base_deriv {p : P} {t h : ℝ} (hht : h < t) :
    HasDerivAt (fun s => midpointFamily Φ ((p,t),s))
      (midpointFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) -
        deriv (fun u => Φ (p,u)) h) h := by
  obtain ⟨hl,hr⟩ := base_derivatives Φ hΦ hloc (p := p) hht
  have hφ : ContDiff ℝ 1 (fun u => Φ (p,u)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hdφ := (hφ.differentiable (by simp) h).hasDerivAt
  have hu := chosen_arch (entire_arch_exists hφ hht)
  have hlne : Φ (p,h)-lowerFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hu.lower_transverse)
  have hrne : Φ (p,h)-upperFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_lt (sub_neg.mpr hu.upper_transverse)
  have hqne := ne_of_gt (gap_pos Φ hΦ (p := p) hht)
  have he : (1/(Φ (p,h)-upperFamily Φ ((p,t),h)) +
      1/(Φ (p,h)-lowerFamily Φ ((p,t),h)))/2 =
      midpointFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) := by
    apply (eq_div_iff hqne).mpr
    dsimp [widthFamily,midpointFamily,width,ScalarArcs.midpoint,lowerFamily,upperFamily] at *
    field_simp
    ring
  rw [←he]
  exact ((hr.add hl).div_const 2).sub hdφ

theorem base_peak_deriv_pos {p : P} {t r : ℝ} (hr : 0 < r) :
    0 < deriv (fun s => baseAtWidth Φ ((p,s),r)) t := by
  let h := baseAtWidth Φ ((p,t),r)
  have hs := base_spec Φ hΦ hloc (p := p) (t := t) hr
  let W : ℝ × ℝ → ℝ := fun q => widthFamily Φ ((p,q.1),q.2)
  let g : ℝ → ℝ := fun s => baseAtWidth Φ ((p,s),r)
  have hW : ContDiffAt ℝ ω W (t,h) :=
    (width_analytic Φ hΦ hloc hs.1).comp (t,h)
      ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)
  have hg : DifferentiableAt ℝ g t :=
    ((base_analytic Φ hΦ hloc hr).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hcomp := (hW.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk hg.hasDerivAt)
  have hc := hcomp.unique ((hasDerivAt_const t r).congr_of_eventuallyEq
    (Eventually.of_forall (fun s => (base_spec Φ hΦ hloc (p := p) (t := s) hr).2)))
  rw [fderiv_pair] at hc
  have hp : 0 < first W (t,h) := by
    have he := (first_hasDerivAt (hW.differentiableAt (by simp))).deriv
    rw [←he]
    exact (peak_width_midpoint_bounds Φ hΦ hloc hs.1).1
  have hn : second W (t,h) < 0 := by
    have he := (second_hasDerivAt (hW.differentiableAt (by simp))).unique
      (width_base_deriv Φ hΦ hloc (p := p) hs.1)
    rw [he]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (width_pos Φ hΦ hs.1)) (gap_pos Φ hΦ hs.1)
  change 0 < deriv g t
  nlinarith

theorem M_analytic {p : P} {h r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ω (M Φ p) (h,r) :=
  (midpointAtWidth_analytic Φ hΦ hloc hr).comp (h,r)
    ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)

theorem v_analytic {p : P} {h r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ω (v Φ p) (h,r) := second_contDiffAt (M_analytic Φ hΦ hloc hr)

theorem M_abs_lt {p : P} {h r : ℝ} (hr : 0 < r) : |M Φ p (h,r)| < r :=
  midpointAtWidth_abs_lt Φ hΦ hloc hr

theorem M_gap_pos {p : P} {h r : ℝ} (hr : 0 < r) : 0 < r^2-(M Φ p (h,r))^2 :=
  sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos hr] using M_abs_lt Φ hΦ hloc (p := p) (h := h) hr))

theorem midpoint_reparam {p : P} {h t : ℝ} (hht : h < t) :
    M Φ p (h,widthFamily Φ ((p,t),h)) = midpointFamily Φ ((p,t),h) := by
  dsimp [M,midpointAtWidth]
  rw [peak_eq Φ hΦ hloc (width_pos Φ hΦ (p := p) hht) hht rfl]

theorem transport_midpoint {p : P} {h r : ℝ} (hr : 0 < r) :
    first (M Φ p) (h,r) - r/(r^2-(M Φ p (h,r))^2)*v Φ p (h,r) =
      M Φ p (h,r)/(r^2-(M Φ p (h,r))^2)-deriv (fun u => Φ (p,u)) h := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  have hM := M_analytic Φ hΦ hloc (p := p) (h := h) hr
  have hw := width_base_deriv Φ hΦ hloc (p := p) hs.1
  have hm := midpoint_base_deriv Φ hΦ hloc (p := p) hs.1
  change HasDerivAt (fun s => widthFamily Φ ((p,t),s))
    (-widthFamily Φ ((p,t),h)/(widthFamily Φ ((p,t),h)^2-M Φ p (h,r)^2)) h at hw
  change HasDerivAt (fun s => midpointFamily Φ ((p,t),s))
    (M Φ p (h,r)/(widthFamily Φ ((p,t),h)^2-M Φ p (h,r)^2)-deriv (fun u => Φ (p,u)) h) h at hm
  have hsr := hs.2
  change widthFamily Φ ((p,t),h) = r at hsr
  rw [hsr] at hw hm
  have hMc := hM.differentiableAt (by simp)
  have hMd : HasFDerivAt (M Φ p) (fderiv ℝ (M Φ p) (h,r))
      (h,widthFamily Φ ((p,t),h)) := by simpa only [hsr] using hMc.hasFDerivAt
  have hcomp := hMd.comp_hasDerivAt h ((hasDerivAt_id h).prodMk hw)
  have he : (fun s => M Φ p (s,widthFamily Φ ((p,t),s))) =ᶠ[𝓝 h]
      (fun s => midpointFamily Φ ((p,t),s)) := by
    filter_upwards [continuousAt_id.eventually_lt continuousAt_const (peak_spec Φ hΦ hloc (p := p) (h := h) hr).1] with s hs
    exact midpoint_reparam Φ hΦ hloc hs
  have hcoeff := hcomp.unique (hm.congr_of_eventuallyEq he)
  rw [fderiv_pair] at hcoeff
  change first (M Φ p) (h,r) - r/(r^2-M Φ p (h,r)^2)*second (M Φ p) (h,r) = _
  convert hcoeff using 1
  ring

theorem transport_midpoint_cross {p : P} {h r : ℝ} (hr : 0 < r) :
    (r^2-M Φ p (h,r)^2)*first (M Φ p) (h,r) - r*v Φ p (h,r) =
      M Φ p (h,r) - (r^2-M Φ p (h,r)^2)*deriv (fun u => Φ (p,u)) h := by
  have ht := transport_midpoint Φ hΦ hloc (p := p) (h := h) hr
  have hq := ne_of_gt (M_gap_pos Φ hΦ hloc (p := p) (h := h) hr)
  field_simp [hq] at ht
  nlinarith [ht]

theorem transport_v {p : P} {h r : ℝ} (hr : 0 < r) :
    first (v Φ p) (h,r) - r/(r^2-M Φ p (h,r)^2)*second (v Φ p) (h,r) =
      -2*M Φ p (h,r)*r*(1-v Φ p (h,r)^2)/(r^2-M Φ p (h,r)^2)^2 := by
  have hMa := M_analytic Φ hΦ hloc (p := p) (h := h) hr
  have hMd := second_hasDerivAt (hMa.differentiableAt (by simp))
  change HasDerivAt (fun s => M Φ p (h,s)) (v Φ p (h,r)) r at hMd
  have hvd := second_hasDerivAt ((v_analytic Φ hΦ hloc (p := p) (h := h) hr).differentiableAt (by simp))
  have hfd := second_hasDerivAt ((first_contDiffAt hMa).differentiableAt (by simp))
  rw [←mixed_comm hMa] at hfd
  change HasDerivAt (fun s => first (M Φ p) (h,s)) (first (v Φ p) (h,r)) r at hfd
  have hqd : HasDerivAt (fun s => s^2-M Φ p (h,s)^2)
      (2*r-2*M Φ p (h,r)*v Φ p (h,r)) r := by
    simpa using! ((hasDerivAt_id r).pow 2).sub (hMd.pow 2)
  have hleft := (hqd.mul hfd).sub ((hasDerivAt_id r).mul hvd)
  have hright := hMd.sub (hqd.mul_const (deriv (fun u => Φ (p,u)) h))
  have he : (fun s => (s^2-M Φ p (h,s)^2)*first (M Φ p) (h,s)-s*v Φ p (h,s))
      =ᶠ[𝓝 r] (fun s => M Φ p (h,s)-(s^2-M Φ p (h,s)^2)*deriv (fun u => Φ (p,u)) h) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact transport_midpoint_cross Φ hΦ hloc hs
  have hc := hleft.unique (hright.congr_of_eventuallyEq he)
  have ht := transport_midpoint_cross Φ hΦ hloc (p := p) (h := h) hr
  have hq := ne_of_gt (M_gap_pos Φ hΦ hloc (p := p) (h := h) hr)
  dsimp only [id] at hc
  field_simp [hq]
  linear_combination (r^2-M Φ p (h,r)^2)*hc -
    (2*r-2*M Φ p (h,r)*v Φ p (h,r))*ht

end QuinticLienard.WidthTransport

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ArchSymmetries
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
namespace QuinticLienard.ArchSymmetries
open ScalarArcs CanonicalVariation ArcEndpoints ArcFamilies WidthCoordinates WidthTransport

lemma affine_cancel {c : ℝ} (hc : c ≠ 0) (C y : ℝ) : (C+c*y-C)/c = y := by
  field_simp
  ring

theorem IsArch.affine {φ ψ u : ℝ → ℝ} {h t a b c H C : ℝ}
    (hu : IsArch φ u h t a b) (hc : 0 < c)
    (he : ∀ x, ψ (H+c^2*x) = C+c*φ x) :
    IsArch ψ (fun y => H+c^2*u ((y-C)/c))
      (H+c^2*h) (H+c^2*t) (C+c*a) (C+c*b) := by
  have hc2 : 0 < c^2 := sq_pos_of_pos hc
  have hpre {y : ℝ} (hy : y ∈ Icc (C+c*a) (C+c*b)) :
      (y-C)/c ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ hc).mpr
      nlinarith [hy.1]
    · apply (div_le_iff₀ hc).mpr
      nlinarith [hy.2]
  constructor
  · exact continuous_const.add (continuous_const.mul
      (hu.continuous.comp ((continuous_id.sub continuous_const).div_const c)))
  · rw [he]
    nlinarith [hu.lower_lt_peak]
  · rw [he]
    nlinarith [hu.peak_lt_upper]
  · rw [he,affine_cancel hc.ne',hu.peak]
  · rw [affine_cancel hc.ne',hu.lower]
  · rw [affine_cancel hc.ne',hu.upper]
  · rw [he]
    nlinarith [hu.lower_transverse]
  · rw [he]
    nlinarith [hu.upper_transverse]
  · intro y hy
    have hd := (((hu.equation _ (hpre hy)).comp y
      (((hasDerivAt_id y).sub_const C).div_const c)).const_mul (c^2)).const_add H
    have hd' : HasDerivAt (fun y => H+c^2*u ((y-C)/c))
        (c^2*((φ (u ((y-C)/c))-(y-C)/c)*(1/c))) y := by
      simpa using! hd
    convert hd' using 1
    rw [he]
    field_simp
    ring
  · intro y hy
    have hh := hu.range_mem _ (hpre hy)
    constructor <;> nlinarith [hh.1,hh.2]
  · intro y₁ hy₁ y₂ hy₂ hyy
    rw [he] at hy₁ hy₂
    have hm : (y₁-C)/c < (y₂-C)/c := (div_lt_div_iff_of_pos_right hc).mpr (by linarith)
    have hh := hu.inc (show (y₁-C)/c ∈ Icc a (φ t) from
      ⟨(le_div_iff₀ hc).mpr (by nlinarith [hy₁.1]), (div_le_iff₀ hc).mpr (by nlinarith [hy₁.2])⟩)
      (show (y₂-C)/c ∈ Icc a (φ t) from
      ⟨(le_div_iff₀ hc).mpr (by nlinarith [hy₂.1]), (div_le_iff₀ hc).mpr (by nlinarith [hy₂.2])⟩) hm
    nlinarith
  · intro y₁ hy₁ y₂ hy₂ hyy
    rw [he] at hy₁ hy₂
    have hm : (y₁-C)/c < (y₂-C)/c := (div_lt_div_iff_of_pos_right hc).mpr (by linarith)
    have hh := hu.dec (show (y₁-C)/c ∈ Icc (φ t) b from
      ⟨(le_div_iff₀ hc).mpr (by nlinarith [hy₁.1]), (div_le_iff₀ hc).mpr (by nlinarith [hy₁.2])⟩)
      (show (y₂-C)/c ∈ Icc (φ t) b from
      ⟨(le_div_iff₀ hc).mpr (by nlinarith [hy₂.1]), (div_le_iff₀ hc).mpr (by nlinarith [hy₂.2])⟩) hm
    nlinarith

theorem IsArch.reflect {φ u : ℝ → ℝ} {h t a b : ℝ}
    (hu : IsArch φ u h t a b) :
    IsArch (fun x => -φ x) (fun y => u (-y)) h t (-b) (-a) := by
  constructor
  · exact hu.continuous.comp continuous_neg
  · simpa using hu.peak_lt_upper
  · simpa using hu.lower_lt_peak
  · simpa using hu.peak
  · simpa using hu.upper
  · simpa using hu.lower
  · simpa using hu.upper_transverse
  · simpa using hu.lower_transverse
  · intro y hy
    have hd := (hu.equation (-y) (by constructor <;> linarith [hy.1,hy.2])).comp y (hasDerivAt_neg y)
    have hd' : HasDerivAt (fun y => u (-y)) ((φ (u (-y))- -y)*(-1)) y := by
      simpa using! hd
    convert hd' using 1
    ring
  · intro y hy
    exact hu.range_mem (-y) (by constructor <;> linarith [hy.1,hy.2])
  · intro y₁ hy₁ y₂ hy₂ hyy
    exact hu.dec (show -y₂ ∈ Icc (φ t) b by constructor <;> linarith [hy₂.1,hy₂.2])
      (show -y₁ ∈ Icc (φ t) b by constructor <;> linarith [hy₁.1,hy₁.2]) (by linarith)
  · intro y₁ hy₁ y₂ hy₂ hyy
    exact hu.inc (show -y₂ ∈ Icc a (φ t) by constructor <;> linarith [hy₂.1,hy₂.2])
      (show -y₁ ∈ Icc a (φ t) by constructor <;> linarith [hy₁.1,hy₁.2]) (by linarith)

theorem canonical_affine {φ ψ : ℝ → ℝ} {h t c H C : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (hht : h < t)
    (hc : 0 < c) (he : ∀ x, ψ (H+c^2*x) = C+c*φ x) :
    lower ψ (H+c^2*h) (H+c^2*t) = C+c*lower φ h t ∧
    upper ψ (H+c^2*h) (H+c^2*t) = C+c*upper φ h t := by
  have hu := chosen_arch (entire_arch_exists hφ hht)
  exact canonical_of_arch (IsArch.affine hu hc he) hψ (by nlinarith [sq_pos_of_pos hc])

theorem canonical_reflect {φ : ℝ → ℝ} {h t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hht : h < t) :
    lower (fun x => -φ x) h t = -upper φ h t ∧
    upper (fun x => -φ x) h t = -lower φ h t :=
  canonical_of_arch (IsArch.reflect (chosen_arch (entire_arch_exists hφ hht))) hφ.neg hht

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

omit hloc [FiniteDimensional ℝ P] in
lemma profile_C1 (p : P) : ContDiff ℝ 1 (fun u => Φ (p,u)) :=
  (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)

omit hloc [FiniteDimensional ℝ P] in
theorem width_affine {p q : P} {h t c H C : ℝ} (hht : h < t) (hc : 0 < c)
    (he : ∀ x, Φ (q,H+c^2*x) = C+c*Φ (p,x)) :
    widthFamily Φ ((q,H+c^2*t),H+c^2*h) = c*widthFamily Φ ((p,t),h) := by
  have hh := canonical_affine (profile_C1 Φ hΦ p) (profile_C1 Φ hΦ q) hht hc he
  dsimp [widthFamily,width]
  rw [hh.1,hh.2]
  ring

omit hloc [FiniteDimensional ℝ P] in
theorem midpoint_affine {p q : P} {h t c H C : ℝ} (hht : h < t) (hc : 0 < c)
    (he : ∀ x, Φ (q,H+c^2*x) = C+c*Φ (p,x)) :
    midpointFamily Φ ((q,H+c^2*t),H+c^2*h) = c*midpointFamily Φ ((p,t),h) := by
  have hh := canonical_affine (profile_C1 Φ hΦ p) (profile_C1 Φ hΦ q) hht hc he
  dsimp [midpointFamily,ScalarArcs.midpoint]
  rw [hh.1,hh.2,he]
  ring

theorem fixed_width_affine {p q : P} {h r c H C : ℝ} (hr : 0 < r) (hc : 0 < c)
    (he : ∀ x, Φ (q,H+c^2*x) = C+c*Φ (p,x)) :
    peakAtWidth Φ ((q,H+c^2*h),c*r) = H+c^2*peakAtWidth Φ ((p,h),r) ∧
    midpointAtWidth Φ ((q,H+c^2*h),c*r) = c*midpointAtWidth Φ ((p,h),r) := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  have hw := width_affine Φ hΦ hs.1 hc he
  rw [hs.2] at hw
  have hp := peak_eq Φ hΦ hloc (mul_pos hc hr)
    (show H+c^2*h < H+c^2*peakAtWidth Φ ((p,h),r) by nlinarith [sq_pos_of_pos hc]) hw
  refine ⟨hp,?_⟩
  dsimp [midpointAtWidth]
  rw [hp]
  exact midpoint_affine Φ hΦ hs.1 hc he

theorem fixed_width_reflect {p q : P} {h r : ℝ} (hr : 0 < r)
    (he : ∀ x, Φ (q,x) = -Φ (p,x)) :
    peakAtWidth Φ ((q,h),r) = peakAtWidth Φ ((p,h),r) ∧
    midpointAtWidth Φ ((q,h),r) = -midpointAtWidth Φ ((p,h),r) := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  have hf : (fun x => Φ (q,x)) = (fun x => -Φ (p,x)) := funext he
  have hh := canonical_reflect (profile_C1 Φ hΦ p) hs.1
  have hw : widthFamily Φ ((q,peakAtWidth Φ ((p,h),r)),h) = r := by
    dsimp [widthFamily,width] at hs ⊢
    rw [hf,hh.1,hh.2]
    linarith [hs.2]
  have hp := peak_eq Φ hΦ hloc hr hs.1 hw
  refine ⟨hp,?_⟩
  dsimp [midpointAtWidth]
  rw [hp]
  dsimp [midpointFamily,ScalarArcs.midpoint]
  rw [hf,hh.1,hh.2,he]
  ring

end QuinticLienard.ArchSymmetries

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.QuadraticCoordinates
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
namespace QuinticLienard.QuadraticCoordinates
open ScalarArcs CanonicalVariation ArchSymmetries PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus

lemma H_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω H ((d,k),r) :=
  (midpointAtWidth_analytic profile profile_contDiff model_local_flow hr).comp ((d,k),r)
    ((contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd)

lemma P_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω P ((d,k),r) :=
  direction_contDiffAt (H_analytic hr) _
lemma Q_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω Q ((d,k),r) :=
  direction_contDiffAt (H_analytic hr) _
lemma Hr_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω Hr ((d,k),r) :=
  direction_contDiffAt (H_analytic hr) _
lemma R_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω R ((d,k),r) :=
  direction_contDiffAt (P_analytic hr) _
lemma S_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω S ((d,k),r) :=
  direction_contDiffAt (Q_analytic hr) _

lemma P_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => H ((s,k),r)) (P ((d,k),r)) d := by
  simpa [P,direction] using!
    ((H_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt d
      (((hasDerivAt_id d).prodMk (hasDerivAt_const d k)).prodMk (hasDerivAt_const d r))
lemma Q_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => H ((d,s),r)) (Q ((d,k),r)) k := by
  simpa [Q,direction] using!
    ((H_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k
      (((hasDerivAt_const k d).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
lemma Hr_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => H ((d,k),s)) (Hr ((d,k),r)) r := by
  simpa [Hr,direction] using!
    ((H_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r (d,k)).prodMk (hasDerivAt_id r))
lemma Hr_abs_lt {d k r : ℝ} (hr : 0 < r) : |Hr ((d,k),r)| < 1 := by
  rw [←(Hr_hasDerivAt (d := d) (k := k) hr).deriv]
  exact midpoint_width_deriv_abs_lt profile profile_contDiff model_local_flow hr

lemma H_abs_lt {d k r : ℝ} (hr : 0 < r) : |H ((d,k),r)| < r :=
  midpointAtWidth_abs_lt profile profile_contDiff model_local_flow hr

lemma H_gap_pos {d k r : ℝ} (hr : 0 < r) : 0 < r^2-(H ((d,k),r))^2 :=
  sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos hr] using H_abs_lt (d := d) (k := k) hr))

lemma translation (d k h : ℝ) {r : ℝ} (hr : 0 < r) :
    M profile (d,k) (h,r) = H ((d+k*h,k),r) := by
  have hh := (fixed_width_affine profile profile_contDiff model_local_flow
    (p := (d+k*h,k)) (q := (d,k)) (h := 0) (H := h)
    (C := d*h+k/2*h^2) hr (show 0 < (1:ℝ) by norm_num)
    (by intro x; dsimp [profile]; ring)).2
  simpa [M,H] using hh

lemma scaling (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    H ((d,k),r) = r*H ((d*r,k*r^3),1) := by
  have hh := (fixed_width_affine profile profile_contDiff model_local_flow
    (p := (d*r,k*r^3)) (q := (d,k)) (h := 0) (H := 0) (C := 0)
    (show 0 < (1:ℝ) by norm_num) hr (by intro x; dsimp [profile]; ring)).2
  simpa [H] using hh

lemma reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    H ((-d,-k),r) = -H ((d,k),r) := by
  exact (fixed_width_reflect profile profile_contDiff model_local_flow
    (p := (d,k)) (q := (-d,-k)) (h := 0) hr
    (by intro x; dsimp [profile]; ring)).2

lemma parabolic_arch {r : ℝ} (hr : 0 < r) :
    IsArch (fun _ => 0) (fun y => (r^2-y^2)/2) 0 (r^2/2) (-r) r := by
  constructor
  · fun_prop
  · simpa using hr
  · exact hr
  · norm_num
  · ring
  · ring
  · linarith
  · exact hr
  · intro y _
    convert ((hasDerivAt_const y (r^2)).sub ((hasDerivAt_id y).pow 2)).div_const 2 using 1 <;>
      (first | rfl | (dsimp; ring))
  · intro y hy
    have hh : y^2 ≤ r^2 := by nlinarith [mul_nonneg (show 0 ≤ r-y by linarith [hy.2]) (show 0 ≤ r+y by linarith [hy.1])]
    constructor <;> nlinarith [sq_nonneg y]
  · intro y₁ hy₁ y₂ hy₂ hyy
    have hh := mul_pos (sub_pos.mpr hyy) (show 0 < -y₁-y₂ by linarith [hy₂.2])
    dsimp
    nlinarith
  · intro y₁ hy₁ y₂ hy₂ hyy
    have hh := mul_pos (sub_pos.mpr hyy) (show 0 < y₁+y₂ by linarith [hy₁.1])
    dsimp
    nlinarith

lemma zero_data {r : ℝ} (hr : 0 < r) :
    peakAtWidth profile (((0,0),0),r) = r^2/2 ∧ H ((0,0),r) = 0 := by
  have ht : 0 < r^2/2 := div_pos (sq_pos_of_pos hr) (by norm_num)
  have he : (fun x => profile ((0,0),x)) = (fun _ => (0:ℝ)) := by ext; simp [profile]
  have hu := canonical_of_arch (parabolic_arch hr) contDiff_const ht
  have hw : widthFamily profile (((0,0),r^2/2),0) = r := by
    dsimp [widthFamily,width]
    rw [he,hu.1,hu.2]
    ring
  have hp := peak_eq profile profile_contDiff model_local_flow hr ht hw
  refine ⟨hp,?_⟩
  dsimp [H,midpointAtWidth]
  rw [hp]
  dsimp [midpointFamily,ScalarArcs.midpoint]
  rw [he,hu.1,hu.2]
  simp [profile]

end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.FixedWidthFamilies
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
namespace QuinticLienard.FixedWidthFamilies
open ScalarArcs ArcEndpoints ArcFamilies CanonicalVariation WidthCoordinates PartialCalculus ArchVariation

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

lemma endpoint_formulas {p : P} {h r : ℝ} (hr : 0 < r) :
    lowerFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) =
      midpointAtWidth Φ ((p,h),r)+Φ (p,h)-r ∧
    upperFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) =
      midpointAtWidth Φ ((p,h),r)+Φ (p,h)+r := by
  have hs := (peak_spec Φ hΦ hloc (p := p) (h := h) hr).2
  dsimp [widthFamily,width] at hs
  dsimp [lowerFamily,upperFamily,midpointAtWidth,midpointFamily,ScalarArcs.midpoint]
  constructor <;> linarith

theorem witness {γ : ℝ → P} {θ h r : ℝ} (hγ : ContDiffAt ℝ ω γ θ) (hr : 0 < r) :
    ∃ u : ℝ × ℝ → ℝ,
      (∀ s, Continuous (fun y => u (s,y))) ∧
      (∀ y ∈ Icc (midpointAtWidth Φ ((γ θ,h),r)+Φ (γ θ,h)-r)
        (midpointAtWidth Φ ((γ θ,h),r)+Φ (γ θ,h)+r), ContDiffAt ℝ ω u (θ,y)) ∧
      (∀ y ∈ Icc (midpointAtWidth Φ ((γ θ,h),r)+Φ (γ θ,h)-r)
        (midpointAtWidth Φ ((γ θ,h),r)+Φ (γ θ,h)+r),
        ∀ᶠ q in 𝓝 (θ,y), HasDerivAt (fun s => u (q.1,s)) (Φ (γ q.1,u q)-q.2) q.2) ∧
      ∀ᶠ s in 𝓝 θ, IsArch (fun x => Φ (γ s,x)) (fun y => u (s,y)) h
        (peakAtWidth Φ ((γ s,h),r))
        (midpointAtWidth Φ ((γ s,h),r)+Φ (γ s,h)-r)
        (midpointAtWidth Φ ((γ s,h),r)+Φ (γ s,h)+r) := by
  let T : ℝ → ℝ := fun s => peakAtWidth Φ ((γ s,h),r)
  have hmap : ContDiffAt ℝ ω (fun s => ((γ s,h),r)) θ :=
    (hγ.prodMk contDiffAt_const).prodMk contDiffAt_const
  have hT : ContDiffAt ℝ ω T θ := by
    have hh := (peak_analytic Φ hΦ hloc (p := γ θ) (h := h) hr).comp θ hmap
    exact hh
  have hs := peak_spec Φ hΦ hloc (p := γ θ) (h := h) hr
  obtain ⟨w,hwc,_,hwd,hwe,hwa⟩ := endpoint_witness Φ hΦ hloc hs.1
  let u : ℝ × ℝ → ℝ := fun q => w ((γ q.1,T q.1),q.2)
  have hlift (y : ℝ) : ContDiffAt ℝ ω (fun q : ℝ × ℝ => ((γ q.1,T q.1),q.2)) (θ,y) :=
    ((hγ.comp (θ,y) contDiffAt_fst).prodMk (hT.comp (θ,y) contDiffAt_fst)).prodMk contDiffAt_snd
  have hf := endpoint_formulas Φ hΦ hloc (p := γ θ) (h := h) hr
  rw [hf.1,hf.2] at hwd hwe
  refine ⟨u,fun s => hwc (γ s,T s),fun y hy => (hwd y hy).comp (θ,y) (hlift y),?_,?_⟩
  · intro y hy
    filter_upwards [(hlift y).continuousAt.eventually (hwe y hy)] with q hq
    exact hq
  · have hc : ContinuousAt (fun s => ((γ s,T s),h)) θ :=
      (hγ.continuousAt.prodMk hT.continuousAt).prodMk continuousAt_const
    filter_upwards [hc.eventually hwa] with s hs
    have hh := endpoint_formulas Φ hΦ hloc (p := γ s) (h := h) hr
    simpa only [T,hh.1,hh.2] using hs

end QuinticLienard.FixedWidthFamilies

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ParameterVariation
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

namespace QuinticLienard.ParameterVariation
open ScalarArcs PartialCalculus ArchVariation

lemma arch_interior_pos {φ u : ℝ → ℝ} {h t a b y : ℝ}
    (hu : IsArch φ u h t a b) (hy : y ∈ Ioo a b) : h < u y := by
  by_cases hh : y ≤ φ t
  · have hi := hu.inc (show a ∈ Icc a (φ t) from ⟨le_rfl,hu.lower_lt_peak.le⟩)
      (show y ∈ Icc a (φ t) from ⟨hy.1.le,hh⟩) hy.1
    simpa only [hu.lower] using hi
  · have hi := hu.dec (show y ∈ Icc (φ t) b from ⟨(le_of_not_ge hh),hy.2.le⟩)
      (show b ∈ Icc (φ t) b from ⟨hu.peak_lt_upper.le,le_rfl⟩) hy.2
    simpa only [hu.upper] using hi

theorem positive_displacement {z a f : ℝ → ℝ} {l r δ : ℝ}
    (ha : Continuous a) (hz : ContinuousOn z (Icc l r))
    (hd : ∀ y ∈ Icc l r, HasDerivAt z (a y*z y+f y) y)
    (hf : ∀ y ∈ Ioo l r, 0 < f y) (hl : l < 0) (hr : 0 < r)
    (hzl : z l = δ*l) (hzr : z r = δ*r) : 0 < δ := by
  let w : ℝ → ℝ := fun y => Real.exp (-(∫ s in l..y, a s))
  let g : ℝ → ℝ := fun y => w y*z y
  have hwd (y : ℝ) : HasDerivAt w (-a y*w y) y := by
    exact (ha.integral_hasStrictDerivAt l y).hasDerivAt.neg.exp.congr_deriv
      (by first | rfl | (dsimp [w]; ring) | (simp [w]; ring))
  have hgc : ContinuousOn g (Icc l r) :=
    (continuous_iff_continuousAt.mpr (fun y => (hwd y).continuousAt)).continuousOn.mul hz
  have hgd (y : ℝ) (hy : y ∈ Icc l r) : HasDerivAt g (w y*f y) y := by
    exact ((hwd y).mul (hd y hy)).congr_deriv (by first | rfl | ring | (simp; ring))
  have hm : StrictMonoOn g (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hgc
    intro y hy
    rw [(hgd y (interior_subset hy)).deriv]
    exact mul_pos (Real.exp_pos _) (hf y (by simpa only [interior_Icc] using hy))
  have hh := hm (show l ∈ Icc l r from ⟨le_rfl,(hl.trans hr).le⟩)
    (show r ∈ Icc l r from ⟨(hl.trans hr).le,le_rfl⟩) (hl.trans hr)
  dsimp [g] at hh
  rw [hzl,hzr] at hh
  have hwpos : 0 < w r := Real.exp_pos _
  have hwnon : 0 < w l := Real.exp_pos _
  have hden : 0 < w r*r-w l*l := by nlinarith
  nlinarith

theorem midpoint_positive {Φ u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {θ r t : ℝ}
    (hΦ : ContDiff ℝ ω Φ) (hbase : ∀ s, Φ (s,0) = 0)
    (hY : DifferentiableAt ℝ Y θ) (hr : 0 < r)
    (ha : IsArch (fun x => Φ (θ,x)) (fun y => u (θ,y)) 0 t (Y θ-r) (Y θ+r))
    (hu : ∀ y ∈ Icc (Y θ-r) (Y θ+r), ContDiffAt ℝ ω u (θ,y))
    (he : ∀ y ∈ Icc (Y θ-r) (Y θ+r), ∀ᶠ q in 𝓝 (θ,y),
      HasDerivAt (fun s => u (q.1,s)) (Φ (q.1,u q)-q.2) q.2)
    (hl : ∀ᶠ s in 𝓝 θ, u (s,Y s-r) = 0)
    (hb : ∀ᶠ s in 𝓝 θ, u (s,Y s+r) = 0)
    (hpos : ∀ x, 0 < x → 0 < first Φ (θ,x)) : 0 < deriv Y θ := by
  let l := Y θ-r
  let b := Y θ+r
  have hlb : l < b := by dsimp [l,b]; linarith
  have hll : l ∈ Icc l b := ⟨le_rfl,hlb.le⟩
  have hbb : b ∈ Icc l b := ⟨hlb.le,le_rfl⟩
  have ha0 : l < 0 := by simpa only [hbase] using ha.lower_transverse
  have hb0 : 0 < b := by simpa only [hbase] using ha.upper_transverse
  have hac : Continuous (fun y => second Φ (θ,u (θ,y))) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (second_contDiffAt (hΦ.contDiffAt)).continuousAt.comp
      (continuousAt_const.prodMk ha.continuous.continuousAt)
  have hzc : ContinuousOn (fun y => first u (θ,y)) (Icc l b) := by
    intro y hy
    exact ((first_contDiffAt (hu y hy)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hzdl : HasDerivAt (fun y => u (θ,y)) (-l) l := by
    simpa only [show u (θ,l) = 0 from ha.lower,hbase,zero_sub] using ha.equation l hll
  have hzdb : HasDerivAt (fun y => u (θ,y)) (-b) b := by
    simpa only [show u (θ,b) = 0 from ha.upper,hbase,zero_sub] using ha.equation b hbb
  have hel := hit_variation ((hu l hll).differentiableAt (by simp))
    (hY.sub_const r) (hasDerivAt_const θ (0:ℝ)) hl
  have heb := hit_variation ((hu b hbb).differentiableAt (by simp))
    (hY.add_const r) (hasDerivAt_const θ (0:ℝ)) hb
  rw [(second_hasDerivAt ((hu l hll).differentiableAt (by simp))).unique hzdl,
    (hY.hasDerivAt.sub_const r).deriv] at hel
  rw [(second_hasDerivAt ((hu b hbb).differentiableAt (by simp))).unique hzdb,
    (hY.hasDerivAt.add_const r).deriv] at heb
  apply positive_displacement hac hzc
    (fun y hy => ?_) (fun y hy => hpos _ (arch_interior_pos ha hy)) ha0 hb0
    (show first u (θ,l) = deriv Y θ*l by linarith)
    (show first u (θ,b) = deriv Y θ*b by linarith)
  convert scalar_ode_variation (hu y hy) (hΦ.differentiable (by simp) _) (he y hy) using 1
  ring

end QuinticLienard.ParameterVariation

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.QuadraticVariation
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
namespace QuinticLienard.QuadraticVariation
open ScalarArcs ArcFamilies PolynomialModel QuadraticCoordinates WidthCoordinates
  PartialCalculus ParameterVariation

lemma profile_zero (p : ℝ × ℝ) : profile (p,0) = 0 := by simp [profile]

lemma direction_positive {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ω γ) {θ r : ℝ}
    (hr : 0 < r)
    (hpos : ∀ x, 0 < x → 0 < first (fun q : ℝ × ℝ => profile (γ q.1,q.2)) (θ,x)) :
    0 < deriv (fun s => H (γ s,r)) θ := by
  let Y : ℝ → ℝ := fun s => H (γ s,r)
  let Φ : ℝ × ℝ → ℝ := fun q => profile (γ q.1,q.2)
  have hΦ : ContDiff ℝ ω Φ := profile_contDiff.comp
    ((hγ.comp contDiff_fst).prodMk contDiff_snd)
  have hY : DifferentiableAt ℝ Y θ := by
    have hh := (H_analytic (d := (γ θ).1) (k := (γ θ).2) hr).comp θ
      (hγ.contDiffAt.prodMk contDiffAt_const)
    exact hh.differentiableAt (by simp)
  obtain ⟨u,huc,hud,hue,hua⟩ := FixedWidthFamilies.witness profile profile_contDiff model_local_flow
    (h := 0) hγ.contDiffAt hr
  have hu : IsArch (fun x => Φ (θ,x)) (fun y => u (θ,y)) 0
      (peakAtWidth profile ((γ θ,0),r)) (Y θ-r) (Y θ+r) := by
    simpa only [Y,H,profile_zero,add_zero] using hua.self_of_nhds
  have hd : ∀ y ∈ Icc (Y θ-r) (Y θ+r), ContDiffAt ℝ ω u (θ,y) := by
    simpa only [Y,H,profile_zero,add_zero] using hud
  have he : ∀ y ∈ Icc (Y θ-r) (Y θ+r), ∀ᶠ q in 𝓝 (θ,y),
      HasDerivAt (fun s => u (q.1,s)) (Φ (q.1,u q)-q.2) q.2 := by
    simpa only [Y,H,profile_zero,add_zero] using hue
  have hl : ∀ᶠ s in 𝓝 θ, u (s,Y s-r) = 0 := by
    filter_upwards [hua] with s hs
    simpa only [Y,H,profile_zero,add_zero] using hs.lower
  have hb : ∀ᶠ s in 𝓝 θ, u (s,Y s+r) = 0 := by
    filter_upwards [hua] with s hs
    simpa only [Y,H,profile_zero,add_zero] using hs.upper
  exact midpoint_positive hΦ (fun s => profile_zero (γ s)) hY hr hu hd he hl hb hpos

lemma slope_first (d k x : ℝ) :
    first (fun q : ℝ × ℝ => profile ((q.1,k),q.2)) (d,x) = x := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => profile ((q.1,k),q.2)) (d,x) := by
    have hh : ContDiff ℝ ω (fun q : ℝ × ℝ => profile ((q.1,k),q.2)) :=
      profile_contDiff.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
    exact hh.differentiable (by simp) _
  apply (first_hasDerivAt hd).unique
  simpa [profile] using! ((hasDerivAt_id d).mul_const x).add_const (k/2*x^2)

lemma curvature_first (d k x : ℝ) :
    first (fun q : ℝ × ℝ => profile ((d,q.1),q.2)) (k,x) = x^2/2 := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => profile ((d,q.1),q.2)) (k,x) := by
    have hh : ContDiff ℝ ω (fun q : ℝ × ℝ => profile ((d,q.1),q.2)) :=
      profile_contDiff.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
    exact hh.differentiable (by simp) _
  apply (first_hasDerivAt hd).unique
  have hh : HasDerivAt (fun s => d*x+s/2*x^2) ((1/2)*x^2) k := by
    simpa using! (((hasDerivAt_id k).div_const 2).mul_const (x^2)).const_add (d*x)
  have he : (1/2:ℝ)*x^2 = x^2/2 := by ring
  rw [he] at hh
  simpa only [profile] using! hh

theorem P_pos {d k r : ℝ} (hr : 0 < r) : 0 < P ((d,k),r) := by
  rw [←(P_hasDerivAt (d := d) (k := k) hr).deriv]
  apply direction_positive (contDiff_id.prodMk contDiff_const) hr
  intro x hx
  change 0 < first (fun q : ℝ × ℝ => profile ((q.1,k),q.2)) (d,x)
  simpa only [slope_first] using hx

theorem Q_pos {d k r : ℝ} (hr : 0 < r) : 0 < Q ((d,k),r) := by
  rw [←(Q_hasDerivAt (d := d) (k := k) hr).deriv]
  apply direction_positive (contDiff_const.prodMk contDiff_id) hr
  intro x hx
  change 0 < first (fun q : ℝ × ℝ => profile ((d,q.1),q.2)) (k,x)
  rw [curvature_first]
  exact div_pos (sq_pos_of_pos hx) (by norm_num)

end QuinticLienard.QuadraticVariation

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ZeroVariation
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
namespace QuinticLienard.ParameterVariation
open ScalarArcs PartialCalculus ArchVariation

theorem zero_profile_variation {Φ u : ℝ × ℝ → ℝ} {Y B : ℝ → ℝ} {θ r t δ : ℝ}
    (hΦ : ContDiff ℝ ω Φ) (hzero : ∀ x, Φ (θ,x) = 0)
    (hY : DifferentiableAt ℝ Y θ) (hY0 : Y θ = 0) (hr : 0 < r)
    (ha : IsArch (fun x => Φ (θ,x)) (fun y => u (θ,y)) 0 t (-r) r)
    (hu : ∀ y ∈ Icc (-r) r, ContDiffAt ℝ ω u (θ,y))
    (he : ∀ y ∈ Icc (-r) r, ∀ᶠ q in 𝓝 (θ,y),
      HasDerivAt (fun s => u (q.1,s)) (Φ (q.1,u q)-q.2) q.2)
    (hl : ∀ᶠ s in 𝓝 θ, u (s,Y s-r) = 0)
    (hb : ∀ᶠ s in 𝓝 θ, u (s,Y s+r) = 0)
    (hB : ∀ y ∈ Icc (-r) r,
      HasDerivAt B (first Φ (θ,(r^2-y^2)/2)) y)
    (hBv : B r-B (-r) = 2*r*δ) : deriv Y θ = δ := by
  have hll : -r ∈ Icc (-r) r := ⟨le_rfl,by linarith⟩
  have hbb : r ∈ Icc (-r) r := ⟨by linarith,le_rfl⟩
  have hu0 : EqOn (fun y => u (θ,y)) (fun y => (r^2-y^2)/2) (Icc (-r) r) := by
    refine eq_of_hasDerivAt_eq_on_Icc ha.continuous.continuousOn (by fun_prop)
      (d := fun y => -y) ?_ ?_ hll (by simpa using ha.lower)
    · intro y hy
      simpa only [hzero,zero_sub] using ha.equation y hy
    · intro y _
      convert ((hasDerivAt_const y (r^2)).sub ((hasDerivAt_id y).pow 2)).div_const 2 using 1 <;>
        (first | rfl | (dsimp; ring))
  have hz (y : ℝ) (hy : y ∈ Icc (-r) r) :
      HasDerivAt (fun s => first u (θ,s)) (first Φ (θ,(r^2-y^2)/2)) y := by
    have hs : second Φ (θ,u (θ,y)) = 0 := by
      apply (second_hasDerivAt (hΦ.differentiable (by simp) _)).unique
      simpa only [hzero] using hasDerivAt_const (u (θ,y)) (0:ℝ)
    have hh := scalar_ode_variation (hu y hy) (hΦ.differentiable (by simp) _) (he y hy)
    have hv : u (θ,y) = (r^2-y^2)/2 := hu0 hy
    rw [hs,zero_mul,add_zero,hv] at hh
    exact hh
  have hzc : ContinuousOn (fun y => first u (θ,y)) (Icc (-r) r) := by
    intro y hy
    exact ((first_contDiffAt (hu y hy)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hBc : ContinuousOn B (Icc (-r) r) := fun y hy => (hB y hy).continuousAt.continuousWithinAt
  have hv := eq_of_hasDerivAt_eq_on_Icc hzc (hBc.add continuousOn_const) hz
    (fun y hy => (hB y hy).add_const (first u (θ,-r)-B (-r))) hll (by dsimp; ring)
  have hend := hv hbb
  dsimp at hend
  have hel := hit_variation (by simpa only [hY0,zero_sub] using
      (hu (-r) hll).differentiableAt (by simp))
    (hY.sub_const r) (hasDerivAt_const θ (0:ℝ)) hl
  have heb := hit_variation (by simpa only [hY0,zero_add] using
      (hu r hbb).differentiableAt (by simp))
    (hY.add_const r) (hasDerivAt_const θ (0:ℝ)) hb
  have hesl : second u (θ,-r) = r := by
    apply (second_hasDerivAt ((hu (-r) hll).differentiableAt (by simp))).unique
    simpa only [hzero,sub_neg_eq_add,zero_add] using ha.equation (-r) hll
  have hesb : second u (θ,r) = -r := by
    apply (second_hasDerivAt ((hu r hbb).differentiableAt (by simp))).unique
    simpa only [hzero,zero_sub] using ha.equation r hbb
  simp only [hY0,zero_sub,zero_add,(hY.hasDerivAt.sub_const r).deriv,
    (hY.hasDerivAt.add_const r).deriv,hesl,hesb] at hel heb
  nlinarith

end QuinticLienard.ParameterVariation

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.QuadraticZero
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

namespace QuinticLienard.QuadraticVariation
open ScalarArcs ArcFamilies PolynomialModel QuadraticCoordinates WidthCoordinates
  PartialCalculus ParameterVariation

lemma zero_direction {γ : ℝ → ℝ × ℝ} (hγ : ContDiff ℝ ω γ) {θ r δ : ℝ}
    (hγ0 : γ θ = (0,0)) (hr : 0 < r) {B : ℝ → ℝ}
    (hB : ∀ y ∈ Icc (-r) r, HasDerivAt B
      (first (fun q : ℝ × ℝ => profile (γ q.1,q.2)) (θ,(r^2-y^2)/2)) y)
    (hBv : B r-B (-r) = 2*r*δ) : deriv (fun s => H (γ s,r)) θ = δ := by
  let Y : ℝ → ℝ := fun s => H (γ s,r)
  let Φ : ℝ × ℝ → ℝ := fun q => profile (γ q.1,q.2)
  have hΦ : ContDiff ℝ ω Φ := profile_contDiff.comp
    ((hγ.comp contDiff_fst).prodMk contDiff_snd)
  have hz : Y θ = 0 := by simpa only [Y,hγ0] using (zero_data hr).2
  have hY : DifferentiableAt ℝ Y θ := by
    have hh := (H_analytic (d := (γ θ).1) (k := (γ θ).2) hr).comp θ
      (hγ.contDiffAt.prodMk contDiffAt_const)
    exact hh.differentiableAt (by simp)
  obtain ⟨u,huc,hud,hue,hua⟩ := FixedWidthFamilies.witness profile profile_contDiff model_local_flow
    (θ := θ) (h := 0) hγ.contDiffAt hr
  have huv : midpointAtWidth profile ((γ θ,0),r) = 0 := hz
  have hu : IsArch (fun x => Φ (θ,x)) (fun y => u (θ,y)) 0
      (peakAtWidth profile ((γ θ,0),r)) (-r) r := by
    simpa only [huv,profile_zero,add_zero,zero_sub,zero_add] using hua.self_of_nhds
  have hd : ∀ y ∈ Icc (-r) r, ContDiffAt ℝ ω u (θ,y) := by
    simpa only [huv,profile_zero,add_zero,zero_sub,zero_add] using hud
  have he : ∀ y ∈ Icc (-r) r, ∀ᶠ q in 𝓝 (θ,y),
      HasDerivAt (fun s => u (q.1,s)) (Φ (q.1,u q)-q.2) q.2 := by
    simpa only [huv,profile_zero,add_zero,zero_sub,zero_add] using hue
  apply zero_profile_variation hΦ (by intro x; simp [Φ,hγ0,profile]) hY hz hr hu hd he
    (by filter_upwards [hua] with s hs; simpa only [Y,H,profile_zero,add_zero] using hs.lower)
    (by filter_upwards [hua] with s hs; simpa only [Y,H,profile_zero,add_zero] using hs.upper) hB hBv

lemma P_zero {r : ℝ} (hr : 0 < r) : P ((0,0),r) = r^2/3 := by
  rw [←(P_hasDerivAt (d := 0) (k := 0) hr).deriv]
  apply zero_direction (contDiff_id.prodMk contDiff_const) (θ := 0) rfl hr
    (B := fun y => r^2*y/2-y^3/6)
  · intro y hy
    change HasDerivAt _ (first (fun q : ℝ × ℝ => profile ((q.1,0),q.2)) (0,_)) y
    rw [slope_first]
    convert (((hasDerivAt_id y).const_mul (r^2)).div_const 2).sub
      (((hasDerivAt_id y).pow 3).div_const 6) using 1 <;>
        (first | rfl | (dsimp; ring))
  · ring

lemma Q_zero {r : ℝ} (hr : 0 < r) : Q ((0,0),r) = r^4/15 := by
  rw [←(Q_hasDerivAt (d := 0) (k := 0) hr).deriv]
  apply zero_direction (contDiff_const.prodMk contDiff_id) (θ := 0) rfl hr
    (B := fun y => r^4*y/8-r^2*y^3/12+y^5/40)
  · intro y hy
    change HasDerivAt _ (first (fun q : ℝ × ℝ => profile ((0,q.1),q.2)) (0,_)) y
    rw [curvature_first]
    convert ((((hasDerivAt_id y).const_mul (r^4)).div_const 8).sub
      ((((hasDerivAt_id y).pow 3).const_mul (r^2)).div_const 12)).add
      (((hasDerivAt_id y).pow 5).div_const 40) using 1 <;>
        (first | rfl | (dsimp; ring))
  · ring

end QuinticLienard.QuadraticVariation

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.QuadraticDerivatives
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
namespace QuinticLienard.QuadraticCoordinates
open PolynomialModel PartialCalculus

lemma R_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => P ((d,k),s)) (R ((d,k),r)) r := by
  simpa [R,direction] using!
    ((P_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r (d,k)).prodMk (hasDerivAt_id r))
lemma S_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Q ((d,k),s)) (S ((d,k),r)) r := by
  simpa [S,direction] using!
    ((Q_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r (d,k)).prodMk (hasDerivAt_id r))

lemma P_scaling (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    P ((d,k),r) = r^2*P ((d*r,k*r^3),1) := by
  have hright := ((P_hasDerivAt (d := d*r) (k := k*r^3) (by norm_num : (0:ℝ)<1)).comp d
    ((hasDerivAt_id d).mul_const r)).const_mul r
  have he : (fun s => H ((s,k),r)) = (fun s => r*H ((s*r,k*r^3),1)) := by
    ext s
    exact scaling s k hr
  have hu := (P_hasDerivAt (d := d) (k := k) hr).unique (he ▸ hright)
  convert hu using 1; ring

lemma Q_scaling (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    Q ((d,k),r) = r^4*Q ((d*r,k*r^3),1) := by
  have hright := ((Q_hasDerivAt (d := d*r) (k := k*r^3) (by norm_num : (0:ℝ)<1)).comp k
    ((hasDerivAt_id k).mul_const (r^3))).const_mul r
  have he : (fun s => H ((d,s),r)) = (fun s => r*H ((d*r,s*r^3),1)) := by
    ext s
    exact scaling d s hr
  have hu := (Q_hasDerivAt (d := d) (k := k) hr).unique (he ▸ hright)
  convert hu using 1; ring

lemma Rr_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => R ((d,k),s)) (Rr ((d,k),r)) r := by
  simpa [Rr,direction] using!
    ((R_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r (d,k)).prodMk (hasDerivAt_id r))
lemma Sr_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => S ((d,k),s)) (Sr ((d,k),r)) r := by
  simpa [Sr,direction] using!
    ((S_analytic (d := d) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r (d,k)).prodMk (hasDerivAt_id r))

lemma PN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω PN q := by
  apply (P_analytic (d := q.1.1*q.2) (k := q.1.2*q.2^3) (by norm_num : (0:ℝ)<1)).comp q
  fun_prop
lemma QN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω QN q := by
  apply (Q_analytic (d := q.1.1*q.2) (k := q.1.2*q.2^3) (by norm_num : (0:ℝ)<1)).comp q
  fun_prop
lemma PNr_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω PNr q := direction_contDiffAt (PN_analytic q) _
lemma QNr_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω QNr q := direction_contDiffAt (QN_analytic q) _
lemma PNrr_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω PNrr q := direction_contDiffAt (PNr_analytic q) _
lemma QNrr_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω QNrr q := direction_contDiffAt (QNr_analytic q) _

lemma slice_r {f : (ℝ × ℝ) × ℝ → ℝ} {q : (ℝ × ℝ) × ℝ}
    (hf : DifferentiableAt ℝ f q) :
    HasDerivAt (fun s => f (q.1,s)) (direction ((0,0),1) f q) q.2 := by
  simpa [direction] using! hf.hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))

lemma PNr_hasDerivAt (d k r : ℝ) :
    HasDerivAt (fun s => PN ((d,k),s)) (PNr ((d,k),r)) r :=
  slice_r (q := ((d,k),r)) ((PN_analytic ((d,k),r)).differentiableAt (by simp))
lemma QNr_hasDerivAt (d k r : ℝ) :
    HasDerivAt (fun s => QN ((d,k),s)) (QNr ((d,k),r)) r :=
  slice_r (q := ((d,k),r)) ((QN_analytic ((d,k),r)).differentiableAt (by simp))
lemma PNrr_hasDerivAt (d k r : ℝ) :
    HasDerivAt (fun s => PNr ((d,k),s)) (PNrr ((d,k),r)) r :=
  slice_r (q := ((d,k),r)) ((PNr_analytic ((d,k),r)).differentiableAt (by simp))
lemma QNrr_hasDerivAt (d k r : ℝ) :
    HasDerivAt (fun s => QNr ((d,k),s)) (QNrr ((d,k),r)) r :=
  slice_r (q := ((d,k),r)) ((QNr_analytic ((d,k),r)).differentiableAt (by simp))

lemma R_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    R ((d,k),r) = 2*r*PN ((d,k),r)+r^2*PNr ((d,k),r) := by
  have hd := ((hasDerivAt_id r).pow 2).mul (PNr_hasDerivAt d k r)
  have he : (fun s => P ((d,k),s)) =ᶠ[𝓝 r] (fun s => s^2*PN ((d,k),s)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact P_scaling d k hs
  have hh := (R_hasDerivAt (d := d) (k := k) hr).unique (hd.congr_of_eventuallyEq he)
  convert hh using 1; dsimp; ring

lemma S_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    S ((d,k),r) = 4*r^3*QN ((d,k),r)+r^4*QNr ((d,k),r) := by
  have hd := ((hasDerivAt_id r).pow 4).mul (QNr_hasDerivAt d k r)
  have he : (fun s => Q ((d,k),s)) =ᶠ[𝓝 r] (fun s => s^4*QN ((d,k),s)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact Q_scaling d k hs
  have hh := (S_hasDerivAt (d := d) (k := k) hr).unique (hd.congr_of_eventuallyEq he)
  convert hh using 1; dsimp; ring

lemma Rr_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    Rr ((d,k),r) = 2*PN ((d,k),r)+4*r*PNr ((d,k),r)+r^2*PNrr ((d,k),r) := by
  have hd := (((hasDerivAt_id r).const_mul 2).mul (PNr_hasDerivAt d k r)).add
    (((hasDerivAt_id r).pow 2).mul (PNrr_hasDerivAt d k r))
  have he : (fun s => R ((d,k),s)) =ᶠ[𝓝 r]
      (fun s => 2*s*PN ((d,k),s)+s^2*PNr ((d,k),s)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact R_scaled d k hs
  have hh := (Rr_hasDerivAt (d := d) (k := k) hr).unique (hd.congr_of_eventuallyEq he)
  convert hh using 1; dsimp; ring

lemma Sr_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    Sr ((d,k),r) = 12*r^2*QN ((d,k),r)+8*r^3*QNr ((d,k),r)+r^4*QNrr ((d,k),r) := by
  have hd := ((((hasDerivAt_id r).pow 3).const_mul 4).mul (QNr_hasDerivAt d k r)).add
    (((hasDerivAt_id r).pow 4).mul (QNrr_hasDerivAt d k r))
  have he : (fun s => S ((d,k),s)) =ᶠ[𝓝 r]
      (fun s => 4*s^3*QN ((d,k),s)+s^4*QNr ((d,k),s)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact S_scaled d k hs
  have hh := (Sr_hasDerivAt (d := d) (k := k) hr).unique (hd.congr_of_eventuallyEq he)
  convert hh using 1; dsimp; ring

lemma W_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    W ((d,k),r) = r^3*WN ((d,k),r) := by
  dsimp [W]
  rw [R_scaled d k hr,S_scaled d k hr,Rr_scaled d k hr,Sr_scaled d k hr]
  dsimp [WN]
  ring

lemma WN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω WN q := by
  unfold WN
  have hP := PN_analytic q
  have hQ := QN_analytic q
  have hPr := PNr_analytic q
  have hQr := QNr_analytic q
  have hPrr := PNrr_analytic q
  have hQrr := QNrr_analytic q
  fun_prop

lemma WN_zero (d k : ℝ) : WN ((d,k),0) = 16/45 := by
  norm_num [WN,PN,QN,QuadraticVariation.P_zero (by norm_num : (0:ℝ)<1),
    QuadraticVariation.Q_zero (by norm_num : (0:ℝ)<1)]

theorem W_positive_near_zero (d k : ℝ) :
    ∀ᶠ q in 𝓝 ((d,k),(0:ℝ)), 0 < q.2 → 0 < W q := by
  have hp : 0 < WN ((d,k),0) := by rw [WN_zero]; norm_num
  filter_upwards [(WN_analytic ((d,k),0)).continuousAt.eventually (eventually_gt_nhds hp)] with q hq hr
  rcases q with ⟨⟨d',k'⟩,r⟩
  rw [W_scaled d' k' hr]
  exact mul_pos (pow_pos hr 3) hq

end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ModelEndpoint
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
namespace QuinticLienard.ModelEndpoint
open ScalarArcs ArcEndpoints CanonicalVariation PolynomialModel WidthCoordinates
  PartialCalculus QuadraticCoordinates

lemma m_pos {d k r : ℝ} (hr : 0 < r) : 0 < m ((d,k),r) := by
  have hh := (abs_lt.mp (H_abs_lt (d := d) (k := k) hr)).2
  dsimp [m]; linarith
lemma n_pos {d k r : ℝ} (hr : 0 < r) : 0 < n ((d,k),r) := by
  have hh := (abs_lt.mp (H_abs_lt (d := d) (k := k) hr)).1
  dsimp [n]; linarith
lemma mr_pos {d k r : ℝ} (hr : 0 < r) : 0 < 1-Hr ((d,k),r) := by
  have hh := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).2
  linarith
lemma ell_pos {d k r : ℝ} (hr : 0 < r) : 0 < ell ((d,k),r) := by
  apply div_pos _ (mr_pos hr)
  have hh := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).1
  linarith

theorem radius_chart {d k r : ℝ} (hr : 0 < r) :
    ∃ ρ : ℝ → ℝ, ContDiffAt ℝ ω ρ (m ((d,k),r)) ∧
      ρ (m ((d,k),r)) = r ∧
      (∀ᶠ s in 𝓝 (m ((d,k),r)), m ((d,k),ρ s)=s) ∧
      HasDerivAt ρ (1/(1-Hr ((d,k),r))) (m ((d,k),r)) := by
  let f : ℝ × ℝ → ℝ := fun q => m ((d,k),q.2)-q.1
  have hf : ContDiffAt ℝ ω f (m ((d,k),r),r) :=
    (contDiffAt_snd.sub ((H_analytic (d := d) (k := k) hr).comp (m ((d,k),r),r)
      (contDiffAt_const.prodMk contDiffAt_snd))).sub
      contDiffAt_fst
  have hd : HasDerivAt (fun s => f (m ((d,k),r),s)) (1-Hr ((d,k),r)) r :=
    ((hasDerivAt_id r).sub (Hr_hasDerivAt hr)).sub_const _
  obtain ⟨ρ,hρ,hρ0,he,_⟩ := transverse_hit hf hd (ne_of_gt (mr_pos hr))
  have he0 : ∀ᶠ s in 𝓝 (m ((d,k),r)), m ((d,k),ρ s)=s := by
    filter_upwards [he] with s hs
    dsimp [f] at hs
    linarith
  have hdρ := (hρ.differentiableAt (by simp)).hasDerivAt
  have hmD : HasDerivAt (fun s => m ((d,k),s)) (1-Hr ((d,k),r))
      (ρ (m ((d,k),r))) := by
    rw [hρ0]
    exact (hasDerivAt_id r).sub (Hr_hasDerivAt hr)
  have hcomp := hmD.comp (m ((d,k),r)) hdρ
  have hder := hcomp.unique ((hasDerivAt_id _).congr_of_eventuallyEq he0)
  have heder : deriv ρ (m ((d,k),r))=1/(1-Hr ((d,k),r)) := by
    apply (eq_div_iff (ne_of_gt (mr_pos hr))).mpr
    simpa only [mul_comm] using hder
  exact ⟨ρ,hρ,hρ0,he0,by simpa only [heder] using hdρ⟩

theorem lower_chart {d k r : ℝ} (hr : 0 < r) : Nonempty (LowerChart d k r) := by
  obtain ⟨ρ,hρ,hρ0,hρeq,hρd⟩ := radius_chart (d := d) (k := k) hr
  let m₀ := m ((d,k),r)
  have hρbase : ρ m₀ = r := hρ0
  let Y : ℝ → ℝ := fun s => n ((d,k),ρ s)
  have hY : ContDiffAt ℝ ω Y m₀ := by
    have hH0 : ContDiffAt ℝ ω H ((d,k),ρ m₀) := by
      rw [hρbase]; exact H_analytic hr
    exact hρ.add (ContDiffAt.comp m₀ (g := H)
      (f := fun s => ((d,k),ρ s)) hH0 (contDiffAt_const.prodMk hρ))
  have hY0 : Y m₀=n ((d,k),r) := by simp only [Y,m₀,hρ0]
  have hYd : HasDerivAt Y (ell ((d,k),r)) m₀ := by
    have hnD : HasDerivAt (fun s => n ((d,k),s)) (1+Hr ((d,k),r)) (ρ m₀) := by
      rw [hρbase]
      exact (hasDerivAt_id r).add (Hr_hasDerivAt hr)
    have hd := hnD.comp m₀ hρd
    convert! hd using 1
    dsimp [ell]
    ring
  let T : ℝ → ℝ := fun s => peakAtWidth profile (((d,k),0),ρ s)
  have hT : ContDiffAt ℝ ω T m₀ := by
    have hT0 : ContDiffAt ℝ ω (peakAtWidth profile) (((d,k),0),ρ m₀) := by
      rw [hρbase]
      exact peak_analytic profile profile_contDiff model_local_flow hr
    exact ContDiffAt.comp m₀ (g := peakAtWidth profile)
      (f := fun s => (((d,k),(0:ℝ)),ρ s)) hT0 (contDiffAt_const.prodMk hρ)
  have hTs : 0 < T m₀ := by
    simpa only [T,m₀,hρ0] using (peak_spec profile profile_contDiff model_local_flow
      (p := (d,k)) (h := 0) hr).1
  obtain ⟨w,hwc,_,hwd,hwe,hwa⟩ := endpoint_witness profile profile_contDiff model_local_flow hTs
  let u : ℝ × ℝ → ℝ := fun q => w (((d,k),T q.1),q.2)
  have hlift (y : ℝ) : ContDiffAt ℝ ω
      (fun q : ℝ × ℝ => (((d,k),T q.1),q.2)) (m₀,y) :=
    (contDiffAt_const.prodMk (hT.comp (m₀,y) contDiffAt_fst)).prodMk contDiffAt_snd
  have href := FixedWidthFamilies.endpoint_formulas profile profile_contDiff model_local_flow
    (p := (d,k)) (h := 0) hr
  have hlower : lowerFamily profile (((d,k),T m₀),0) = -m ((d,k),r) := by
    dsimp only [T]
    rw [hρbase]
    have h0 : profile ((d,k),(0:ℝ)) = 0 := by simp [profile]
    rw [href.1,h0,add_zero]
    dsimp [m,H]; ring
  have hupper : upperFamily profile (((d,k),T m₀),0) = n ((d,k),r) := by
    dsimp only [T]
    rw [hρbase]
    have h0 : profile ((d,k),(0:ℝ)) = 0 := by simp [profile]
    rw [href.2,h0,add_zero]
    exact add_comm _ _
  rw [hlower,hupper] at hwd hwe
  have hua (y : ℝ) (hy : y ∈ Icc (-m ((d,k),r)) (n ((d,k),r))) :
      ContDiffAt ℝ ω u (m₀,y) := (hwd y hy).comp (m₀,y) (hlift y)
  have hue (y : ℝ) (hy : y ∈ Icc (-m ((d,k),r)) (n ((d,k),r))) :
      ∀ᶠ q in 𝓝 (m₀,y), HasDerivAt (fun s => u (q.1,s))
        (d*u q+(k/2)*(u q)^2-q.2) q.2 := by
    filter_upwards [(hlift y).continuousAt.eventually (hwe y hy)] with q hq
    simpa only [profile] using hq
  have harch : ∀ᶠ s in 𝓝 m₀,
      IsArch (fun x => profile ((d,k),x)) (fun y => u (s,y)) 0 (T s) (-s) (Y s) := by
    have hmap : ContinuousAt (fun s => (((d,k),T s),(0:ℝ))) m₀ :=
      (continuousAt_const.prodMk hT.continuousAt).prodMk continuousAt_const
    have hpos : ∀ᶠ s in 𝓝 m₀, 0 < ρ s :=
      continuousAt_const.eventually_lt hρ.continuousAt (by simpa only [hρbase] using hr)
    filter_upwards [hmap.eventually hwa,hpos,hρeq] with s hs hps heq
    have hf := FixedWidthFamilies.endpoint_formulas profile profile_contDiff model_local_flow
      (p := (d,k)) (h := 0) hps
    have hl : lowerFamily profile (((d,k),T s),0) = -s := by
      have h0 : profile ((d,k),(0:ℝ)) = 0 := by simp [profile]
      change ρ s-H ((d,k),ρ s)=s at heq
      change lowerFamily profile (((d,k),T s),0) = -s
      rw [show lowerFamily profile (((d,k),T s),0) =
        H ((d,k),ρ s)+profile ((d,k),0)-ρ s from hf.1,h0]
      linarith
    have hu : upperFamily profile (((d,k),T s),0) = Y s := by
      have h0 : profile ((d,k),(0:ℝ)) = 0 := by simp [profile]
      change upperFamily profile (((d,k),T s),0) = ρ s+H ((d,k),ρ s)
      rw [hf.2,h0,add_zero]
      exact add_comm _ _
    simpa only [hl,hu] using hs
  exact ⟨{ radius := ρ
           upper := Y
           solution := u
           radius_analytic := hρ
           radius_base := hρ0
           radius_relation := hρeq
           radius_derivative := hρd
           upper_def := fun _ => rfl
           upper_analytic := hY
           upper_base := hY0
           upper_derivative := hYd
           solution_continuous := fun s => hwc ((d,k),T s)
           solution_analytic := hua
           equation := hue
           lower_zero := harch.mono (fun _ hs => hs.lower)
           upper_zero := harch.mono (fun _ hs => hs.upper) }⟩

end QuinticLienard.ModelEndpoint

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RiccatiJets
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
namespace QuinticLienard.RiccatiJets
open PartialCalculus

lemma mixed_equation {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ ω f p) (he : second f =ᶠ[𝓝 p] g)
    (hg : HasDerivAt (fun s => g (s,p.2)) a p.1) :
    second (first f) p = a := by
  rw [←mixed_comm hf]
  apply (first_hasDerivAt ((second_contDiffAt hf).differentiableAt (by simp))).unique
  exact hg.congr_of_eventuallyEq ((continuousAt_id.prodMk continuousAt_const).eventually he)

lemma mixed_equation_eventually {f g G : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ ω f p) (he : second f =ᶠ[𝓝 p] g)
    (hg : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => g (s,q.2)) (G q) q.1) :
    second (first f) =ᶠ[𝓝 p] G := by
  filter_upwards [hf.eventually (by simp),he.eventuallyEq_nhds,hg] with q hq heq hgq
  exact mixed_equation hq heq hgq

theorem jets_eventually {u : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {d b : ℝ}
    (hu : ContDiffAt ℝ ω u p)
    (he : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2) :
    (second u =ᶠ[𝓝 p] (fun q => d*u q+b*(u q)^2-q.2)) ∧
    (second (first u) =ᶠ[𝓝 p] (fun q => (d+2*b*u q)*first u q)) ∧
    (second (first (first u)) =ᶠ[𝓝 p]
      (fun q => (d+2*b*u q)*first (first u) q+2*b*(first u q)^2)) ∧
    (second (first (first (first u))) =ᶠ[𝓝 p]
      (fun q => (d+2*b*u q)*first (first (first u)) q+6*b*first u q*first (first u) q)) := by
  have huN : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ ω u q := hu.eventually (by simp)
  have h0 : second u =ᶠ[𝓝 p] (fun q => d*u q+b*(u q)^2-q.2) := by
    filter_upwards [huN,he] with q hq heq
    exact (second_hasDerivAt (hq.differentiableAt (by simp))).unique heq
  have h1 : second (first u) =ᶠ[𝓝 p] (fun q => (d+2*b*u q)*first u q) := by
    apply mixed_equation_eventually hu h0
    filter_upwards [huN] with q hq
    have hd := first_hasDerivAt (hq.differentiableAt (by simp))
    convert! ((hd.const_mul d).add ((hd.pow 2).const_mul b)).sub_const q.2 using 1
    ring
  have h2 : second (first (first u)) =ᶠ[𝓝 p]
      (fun q => (d+2*b*u q)*first (first u) q+2*b*(first u q)^2) := by
    apply mixed_equation_eventually (first_contDiffAt hu) h1
    filter_upwards [huN] with q hq
    have hd := first_hasDerivAt (hq.differentiableAt (by simp))
    have hz := first_hasDerivAt ((first_contDiffAt hq).differentiableAt (by simp))
    convert! (((hd.const_mul (2*b)).const_add d).mul hz) using 1
    ring
  have h3 : second (first (first (first u))) =ᶠ[𝓝 p]
      (fun q => (d+2*b*u q)*first (first (first u)) q+6*b*first u q*first (first u) q) := by
    apply mixed_equation_eventually (first_contDiffAt (first_contDiffAt hu)) h2
    filter_upwards [huN] with q hq
    have hd := first_hasDerivAt (hq.differentiableAt (by simp))
    have hz := first_hasDerivAt ((first_contDiffAt hq).differentiableAt (by simp))
    have ha := first_hasDerivAt ((first_contDiffAt (first_contDiffAt hq)).differentiableAt (by simp))
    convert! ((((hd.const_mul (2*b)).const_add d).mul ha).add
      ((hz.pow 2).const_mul (2*b))) using 1
    ring
  exact ⟨h0,h1,h2,h3⟩

theorem invariant_derivatives {u : ℝ × ℝ → ℝ} {m y d b : ℝ}
    (hu : ContDiffAt ℝ ω u (m,y))
    (he : ∀ᶠ q in 𝓝 (m,y), HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2)
    (hz : first u (m,y) ≠ 0) :
    HasDerivAt (fun s => logJet u (m,s)) (2*b*first u (m,y)) y ∧
    HasDerivAt (fun s => schwarzJet u (m,s)) 0 y := by
  have hj := jets_eventually hu he
  have hd1 := second_hasDerivAt ((first_contDiffAt hu).differentiableAt (by simp))
  have hd2 := second_hasDerivAt ((first_contDiffAt (first_contDiffAt hu)).differentiableAt (by simp))
  have hd3 := second_hasDerivAt ((first_contDiffAt (first_contDiffAt (first_contDiffAt hu))).differentiableAt (by simp))
  rw [hj.2.1.self_of_nhds] at hd1
  rw [hj.2.2.1.self_of_nhds] at hd2
  rw [hj.2.2.2.self_of_nhds] at hd3
  have hA : HasDerivAt (fun s => logJet u (m,s)) (2*b*first u (m,y)) y := by
    have hd := hd2.div hd1 hz
    have hc : ((d+2*b*u (m,y))*first (first u) (m,y)+2*b*(first u (m,y))^2)*first u (m,y)
        - first (first u) (m,y)*((d+2*b*u (m,y))*first u (m,y)) =
        (2*b*first u (m,y))*(first u (m,y))^2 := by ring
    have hv : (((d+2*b*u (m,y))*first (first u) (m,y)+2*b*(first u (m,y))^2)*first u (m,y)
        - first (first u) (m,y)*((d+2*b*u (m,y))*first u (m,y)))/(first u (m,y))^2 =
        2*b*first u (m,y) := by rw [hc]; exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hz)
    simpa only [hv, logJet, Pi.div_apply] using! hd
  refine ⟨hA,?_⟩
  have hd := (hd3.div hd1 hz).sub ((hA.pow 2).const_mul (3/2))
  have hc : (((d+2*b*u (m,y))*first (first (first u)) (m,y)+6*b*first u (m,y)*first (first u) (m,y))*
      first u (m,y)-first (first (first u)) (m,y)*((d+2*b*u (m,y))*first u (m,y)))/
      (first u (m,y))^2 - (3/2)*((2:ℝ)*logJet u (m,y)^(2-1)*(2*b*first u (m,y))) = 0 := by
    dsimp [logJet]
    field_simp
    ring
  convert! hd using 1
  simpa only [Nat.cast_ofNat] using hc.symm

end QuinticLienard.RiccatiJets

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RiccatiDerivatives
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
namespace QuinticLienard.RiccatiJets
open PartialCalculus

lemma deriv_analytic {f : ℝ → ℝ} {t : ℝ} (hf : ContDiffAt ℝ ω f t) :
    ContDiffAt ℝ ω (deriv f) t := hf.derivWithin (by simp)

lemma curve_hasDerivAt {f : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t,Y t)) (hY : DifferentiableAt ℝ Y t) :
    HasDerivAt (fun s => f (s,Y s))
      (first f (t,Y t)+deriv Y t*second f (t,Y t)) t := by
  simpa only [fderiv_pair,one_mul] using!
    hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hY.hasDerivAt)

lemma root_first {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : second u (t,Y t) = d*u (t,Y t)+b*(u (t,Y t))^2-Y t)
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0) :
    first u (t,Y t) = Y t*deriv Y t := by
  have hd := ArchVariation.hit_variation (hu.differentiableAt (by simp))
    (hY.differentiableAt (by simp)) (hasDerivAt_const t (0:ℝ)) hroot
  rw [he,hroot.self_of_nhds] at hd
  nlinarith

lemma root_first_eventually {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : second u =ᶠ[𝓝 (t,Y t)] (fun q => d*u q+b*(u q)^2-q.2))
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0) :
    (fun s => first u (s,Y s)) =ᶠ[𝓝 t] (fun s => Y s*deriv Y s) := by
  have hc := continuousAt_id.prodMk hY.continuousAt
  filter_upwards [hc.eventually (hu.eventually (by simp)), hY.eventually (by simp),
    hc.eventually he,hroot.eventually_nhds] with s hus hYs hes hrs
  exact root_first hus hYs hes hrs

lemma root_second {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : ∀ᶠ q in 𝓝 (t,Y t), HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2)
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0) :
    first (first u) (t,Y t) = (deriv Y t)^2+Y t*deriv (deriv Y) t-d*Y t*(deriv Y t)^2 := by
  have hj := jets_eventually hu he
  have hz := root_first_eventually hu hY hj.1 hroot
  have hd := curve_hasDerivAt ((first_contDiffAt hu).differentiableAt (by simp))
    (hY.differentiableAt (by simp))
  have hr := (hY.differentiableAt (by simp)).hasDerivAt.mul
    ((deriv_analytic hY).differentiableAt (by simp)).hasDerivAt
  have h := hd.unique (hr.congr_of_eventuallyEq hz)
  rw [hj.2.1.self_of_nhds] at h
  dsimp only at h
  have hz0 : first u (t,Y t) = Y t*deriv Y t := hz.self_of_nhds
  rw [hroot.self_of_nhds,hz0] at h
  nlinarith

lemma root_second_eventually {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : ∀ᶠ q in 𝓝 (t,Y t), HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2)
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0) :
    (fun s => first (first u) (s,Y s)) =ᶠ[𝓝 t]
      (fun s => (deriv Y s)^2+Y s*deriv (deriv Y) s-d*Y s*(deriv Y s)^2) := by
  have hc := continuousAt_id.prodMk hY.continuousAt
  filter_upwards [hc.eventually (hu.eventually (by simp)), hY.eventually (by simp),
    hc.eventually he.eventually_nhds,hroot.eventually_nhds] with s hus hYs hes hrs
  exact root_second hus hYs hes hrs

lemma root_third {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : ∀ᶠ q in 𝓝 (t,Y t), HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2)
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0) :
    first (first (first u)) (t,Y t) =
      Y t*deriv (deriv (deriv Y)) t +3*deriv Y t*deriv (deriv Y) t
      -3*d*Y t*deriv Y t*deriv (deriv Y) t-2*d*(deriv Y t)^3
      +d^2*Y t*(deriv Y t)^3-2*b*(Y t)^2*(deriv Y t)^3 := by
  have hj := jets_eventually hu he
  have hz := root_first_eventually hu hY hj.1 hroot
  have ha := root_second_eventually hu hY he hroot
  have hd := curve_hasDerivAt ((first_contDiffAt (first_contDiffAt hu)).differentiableAt (by simp))
    (hY.differentiableAt (by simp))
  have h1 := (hY.differentiableAt (by simp)).hasDerivAt
  have h2 := ((deriv_analytic hY).differentiableAt (by simp)).hasDerivAt
  have h3 := ((deriv_analytic (deriv_analytic hY)).differentiableAt (by simp)).hasDerivAt
  have hr := ((h2.pow 2).add (h1.mul h3)).sub ((h1.const_mul d).mul (h2.pow 2))
  have h := hd.unique (hr.congr_of_eventuallyEq ha)
  rw [hj.2.2.1.self_of_nhds] at h
  dsimp only at h
  have hz0 : first u (t,Y t) = Y t*deriv Y t := hz.self_of_nhds
  have ha0 := ha.self_of_nhds
  dsimp only at ha0
  rw [hroot.self_of_nhds,hz0,ha0] at h
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply] at h
  nlinarith

lemma root_invariants {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : ∀ᶠ q in 𝓝 (t,Y t), HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2)
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0)
    (hy : Y t ≠ 0) (hl : deriv Y t ≠ 0) :
    logJet u (t,Y t) = deriv (deriv Y) t/deriv Y t+deriv Y t/Y t-d*deriv Y t ∧
    schwarzJet u (t,Y t) = schwarzian Y t+
      (deriv Y t)^2*(-2*b*Y t-d^2/2+d/Y t-3/(2*(Y t)^2)) := by
  have hz := (root_first_eventually hu hY (jets_eventually hu he).1 hroot).self_of_nhds
  dsimp only at hz
  have ha := root_second hu hY he hroot
  have hc := root_third hu hY he hroot
  dsimp [logJet,schwarzJet,schwarzian]
  rw [hz,ha,hc]
  constructor <;> field_simp <;> ring

end QuinticLienard.RiccatiJets

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.Riccati
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

open Set Filter MeasureTheory
open scoped Topology

namespace QuinticLienard.Riccati

theorem inverse_square_integral_bound {v vp q : ℝ → ℝ} {ν a S : ℝ}
    (hS : 0 ≤ S) (ha : 0 < a+ν)
    (hv : ∀ s, HasDerivAt v (vp s) s)
    (hvp : ∀ s ∈ Icc 0 S, HasDerivAt vp (q s*v s) s)
    (hpos : ∀ s, 0 < v s) (hq : ∀ s ∈ Icc 0 S, ν^2 ≤ q s)
    (hv0 : v 0 = 1) (hvp0 : vp 0 = a) :
    (∫ s in (0:ℝ)..S, 1/(v s)^2) < 1/(a+ν) := by
  have hc : Continuous v := continuous_iff_continuousAt.mpr (fun s => (hv s).continuousAt)
  have hpc : ContinuousOn vp (Icc 0 S) := fun s hs => (hvp s hs).continuousAt.continuousWithinAt
  let w : ℝ → ℝ := fun s => Real.exp (-ν*s)*(vp s+ν*v s)
  have hwc : ContinuousOn w (Icc 0 S) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hpc.add (continuous_const.mul hc).continuousOn)
  have hwd (s : ℝ) (hs : s ∈ Icc 0 S) :
      HasDerivAt w (Real.exp (-ν*s)*(q s-ν^2)*v s) s := by
    have he := (((hasDerivAt_id s).const_mul (-ν)).exp).mul
      ((hvp s hs).add ((hv s).const_mul ν))
    convert he using 1 <;> (first | rfl | (dsimp; ring))
  have hwm : MonotoneOn w (Icc 0 S) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hwc
      (fun s hs => (hwd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [(hwd s (interior_subset hs)).deriv]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr (hq s (interior_subset hs)))) (hpos s).le
  have hw (s : ℝ) (hs : s ∈ Icc 0 S) : a+ν ≤ w s := by
    have hh := hwm (show (0:ℝ) ∈ Icc 0 S from ⟨le_rfl,hS⟩) hs hs.1
    simpa [w,hv0,hvp0] using hh
  let f : ℝ → ℝ := fun s => 1/(v s)^2
  have hfc : Continuous f := continuous_const.div (hc.pow 2) (fun s => pow_ne_zero _ (ne_of_gt (hpos s)))
  let H : ℝ → ℝ := fun s => (a+ν)*(∫ y in (0:ℝ)..s, f y)+Real.exp (-ν*s)/(v s)
  have hHd (s : ℝ) : HasDerivAt H ((a+ν-w s)/(v s)^2) s := by
    have he := ((hfc.integral_hasStrictDerivAt 0 s).hasDerivAt.const_mul (a+ν)).add
      ((((hasDerivAt_id s).const_mul (-ν)).exp).div (hv s) (ne_of_gt (hpos s)))
    convert he using 1 <;> (first | rfl | (dsimp [H,w,f]; ring))
  have hHc : Continuous H := continuous_iff_continuousAt.mpr (fun s => (hHd s).continuousAt)
  have hHm : AntitoneOn H (Icc 0 S) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hHc.continuousOn
      (fun s _ => (hHd s).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [(hHd s).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hw s (interior_subset hs))) (sq_nonneg _)
  have hHS := hHm (show (0:ℝ) ∈ Icc 0 S from ⟨le_rfl,hS⟩) ⟨hS,le_rfl⟩ hS
  have h0 : H 0 = 1 := by simp [H,hv0]
  rw [h0] at hHS
  have hterm : 0 < Real.exp (-ν*S)/v S := div_pos (Real.exp_pos _) (hpos S)
  have hbound : (a+ν)*(∫ s in (0:ℝ)..S, 1/(v s)^2) < 1 := by
    change (a+ν)*(∫ s in (0:ℝ)..S, f s) < 1
    dsimp [H] at hHS
    linarith
  exact (lt_div_iff₀ ha).mpr (by simpa [mul_comm] using hbound)

lemma multiplier_pos (u : ℝ → ℝ) (b d c y : ℝ) : 0 < multiplier u b d c y :=
  Real.exp_pos _

lemma multiplier_deriv {u : ℝ → ℝ} (hu : Continuous u) (b d c y : ℝ) :
    HasDerivAt (multiplier u b d c)
      (-(b*u y+d/2)*multiplier u b d c y) y := by
  have hc : Continuous (fun s => b*u s+d/2) := (continuous_const.mul hu).add continuous_const
  convert (hc.integral_hasStrictDerivAt c y).hasDerivAt.neg.exp using 1
  · rfl
  · dsimp [multiplier]; ring

theorem multiplier_second_deriv {u : ℝ → ℝ} (b d c : ℝ)
    (hc : Continuous u) (y : ℝ)
    (hu : HasDerivAt u (d*u y+b*(u y)^2-y) y) :
    HasDerivAt (fun y => -(b*u y+d/2)*multiplier u b d c y)
      ((b*y+d^2/4)*multiplier u b d c y) y := by
  have he := (((hu.const_mul b).add_const (d/2)).neg).mul
    (multiplier_deriv hc b d c y)
  exact he.congr_deriv (by first | rfl | (simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply]; ring1) | ring1 | (dsimp; ring1))

theorem quadratic_inverse_square_bound {u : ℝ → ℝ} {b d m n ν : ℝ}
    (hc : Continuous u) (hb : 0 ≤ b) (hmn : 0 ≤ m+n) (hd : d < 0)
    (hν : 0 ≤ ν) (hνsq : ν^2 = d^2/4-b*m) (hu0 : u (-m) = 0)
    (hu : ∀ y ∈ Icc (-m) n, HasDerivAt u (d*u y+b*(u y)^2-y) y) :
    (∫ y in (-m)..n, 1/(multiplier u b d (-m) y)^2) < 1/(ν-d/2) := by
  let V := multiplier u b d (-m)
  let v : ℝ → ℝ := fun s => V (-m+s)
  let vp : ℝ → ℝ := fun s => -(b*u (-m+s)+d/2)*V (-m+s)
  let q : ℝ → ℝ := fun s => b*(-m+s)+d^2/4
  have hv (s : ℝ) : HasDerivAt v (vp s) s := by
    simpa [v,vp,Function.comp_def] using
      (multiplier_deriv hc b d (-m) (-m+s)).comp s ((hasDerivAt_id s).const_add (-m))
  have hvp (s : ℝ) (hs : s ∈ Icc 0 (m+n)) : HasDerivAt vp (q s*v s) s := by
    have hys : -m+s ∈ Icc (-m) n := by constructor <;> linarith [hs.1,hs.2]
    simpa [vp,q,v,Function.comp_def] using
      (multiplier_second_deriv b d (-m) hc (-m+s) (hu _ hys)).comp s
        ((hasDerivAt_id s).const_add (-m))
  have he := inverse_square_integral_bound (v := v) (vp := vp) (q := q)
    (a := -d/2) (ν := ν) hmn (by linarith) hv hvp
    (fun s => multiplier_pos _ _ _ _ _) (fun s hs => by
      dsimp [q]
      rw [hνsq]
      nlinarith [mul_nonneg hb hs.1])
    (by simp [v,V]) (by simp [vp,V,hu0]; ring)
  have hi : (∫ s in (0:ℝ)..(m+n), 1/(v s)^2) =
      ∫ y in (-m)..n, 1/(multiplier u b d (-m) y)^2 := by
    dsimp [v,V]
    have hh := intervalIntegral.integral_comp_add_left
      (f := fun y => 1/(multiplier u b d (-m) y)^2) (a := (0:ℝ)) (b := m+n) (-m)
    have hab : -m+(m+n)=n := by ring
    simpa only [add_zero,hab] using hh
  rw [hi] at he
  convert he using 1; ring

theorem endpoint_variation_bound {u : ℝ → ℝ} {b d m n ν l w : ℝ}
    (hc : Continuous u) (hb : 0 < b) (hm : 0 < m) (hn : 0 < n) (hd : d < 0)
    (hν : 0 ≤ ν) (hνsq : ν^2 = d^2/4-b*m) (hu0 : u (-m) = 0)
    (hu : ∀ y ∈ Icc (-m) n, HasDerivAt u (d*u y+b*(u y)^2-y) y)
    (hw : w = 1/m-l/n+d*(1+l)+2*b*m*
      (∫ y in (-m)..n, 1/(multiplier u b d (-m) y)^2)) :
    w ≤ 1/m-l/n+d*l-2*ν := by
  have hi := quadratic_inverse_square_bound hc hb.le (by linarith) hd hν hνsq hu0 hu
  have hden : 0 < ν-d/2 := by linarith
  have hid : 2*b*m*(1/(ν-d/2)) = -d-2*ν := by
    rw [mul_one_div]
    apply (div_eq_iff (ne_of_gt hden)).mpr
    nlinarith [hνsq]
  have hmul := mul_le_mul_of_nonneg_left hi.le (show 0 ≤ 2*b*m by positivity)
  rw [hid] at hmul
  rw [hw]
  linarith

end QuinticLienard.Riccati

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RiccatiComparison
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
open Set Filter
open scoped Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuinticLienard.RiccatiJets
open PartialCalculus Riccati

lemma neg_deriv : deriv (fun x : ℝ => -x) = fun _ => -1 :=
  funext (fun x => ((hasDerivAt_id x).neg).deriv)

lemma neg_second_deriv : deriv (deriv (fun x : ℝ => -x)) = fun _ => 0 := by
  rw [neg_deriv]
  exact funext (fun x => (hasDerivAt_const x (-1:ℝ)).deriv)

lemma neg_third_deriv : deriv (deriv (deriv (fun x : ℝ => -x))) = fun _ => 0 := by
  rw [neg_second_deriv]
  exact funext (fun x => (hasDerivAt_const x (0:ℝ)).deriv)

theorem parameter_multiplier {u : ℝ × ℝ → ℝ} {m n d b : ℝ}
    (hm : 0 < m) (hn : 0 < n)
    (hc : Continuous (fun y => u (m,y)))
    (hu : ∀ y ∈ Icc (-m) n, ContDiffAt ℝ ω u (m,y))
    (he : ∀ y ∈ Icc (-m) n, ∀ᶠ q in 𝓝 (m,y),
      HasDerivAt (fun s => u (q.1,s)) (d*u q+b*(u q)^2-q.2) q.2)
    (hroot : ∀ᶠ s in 𝓝 m, u (s,-s)=0) :
    ∀ y ∈ Icc (-m) n, first u (m,y) =
      m/(multiplier (fun s => u (m,s)) b d (-m) y)^2 := by
  let V := multiplier (fun s => u (m,s)) b d (-m)
  have hmn : -m ≤ n := by linarith
  have hmI : -m ∈ Icc (-m) n := ⟨le_rfl,hmn⟩
  have hzi := root_first (hu _ hmI) contDiffAt_id.neg
    (jets_eventually (hu _ hmI) (he _ hmI)).1.self_of_nhds hroot
  have hz0 : first u (m,-m)=m := by
    simpa only [neg_deriv,mul_neg_one,neg_neg] using hzi
  let g : ℝ → ℝ := fun y => (V y)^2*first u (m,y)
  have hgd (y : ℝ) (hy : y ∈ Icc (-m) n) : HasDerivAt g 0 y := by
    have hz := second_hasDerivAt ((first_contDiffAt (hu y hy)).differentiableAt (by simp))
    rw [(jets_eventually (hu y hy) (he y hy)).2.1.self_of_nhds] at hz
    have hd := ((multiplier_deriv hc b d (-m) y).pow 2).mul hz
    convert! hd using 1
    dsimp [V]
    ring
  have hgc : ContinuousOn g (Icc (-m) n) :=
    fun y hy => (hgd y hy).continuousAt.continuousWithinAt
  have hconstant := eq_of_hasDerivAt_eq_on_Icc hgc continuousOn_const hgd
    (fun y _ => hasDerivAt_const y m) hmI (by simp [g,V,hz0])
  intro y hy
  have h := hconstant hy
  change (V y)^2*first u (m,y)=m at h
  exact (eq_div_iff (pow_ne_zero 2 (ne_of_gt (multiplier_pos _ _ _ _ _)))).mpr
    (by simpa [V,mul_comm] using h)

theorem endpoint_formulas {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {m d b : ℝ}
    (hm : 0 < m) (hn : 0 < Y m) (hl : 0 < deriv Y m)
    (hc : Continuous (fun y => u (m,y)))
    (hu : ∀ y ∈ Icc (-m) (Y m), ContDiffAt ℝ ω u (m,y))
    (he : ∀ y ∈ Icc (-m) (Y m), ∀ᶠ q in 𝓝 (m,y),
      HasDerivAt (fun s => u (q.1,s)) (d*u q+b*(u q)^2-q.2) q.2)
    (hY : ContDiffAt ℝ ω Y m)
    (hrootL : ∀ᶠ s in 𝓝 m, u (s,-s)=0)
    (hrootR : ∀ᶠ s in 𝓝 m, u (s,Y s)=0) :
    schwarzian Y m =
      2*b*(m+Y m*(deriv Y m)^2)+(d^2/2)*((deriv Y m)^2-1)
      -d*(1/m+(deriv Y m)^2/Y m)
      +(3/2)*((deriv Y m)^2/(Y m)^2-1/m^2) ∧
    deriv (deriv Y) m/deriv Y m =
      1/m-deriv Y m/Y m+d*(1+deriv Y m)+
      2*b*m*(∫ y in (-m)..(Y m), 1/(multiplier (fun s => u (m,s)) b d (-m) y)^2) ∧
    deriv Y m = m/(Y m*(multiplier (fun s => u (m,s)) b d (-m) (Y m))^2) := by
  let V := multiplier (fun s => u (m,s)) b d (-m)
  have hmn : -m ≤ Y m := by linarith
  have hmI : -m ∈ Icc (-m) (Y m) := ⟨le_rfl,hmn⟩
  have hnI : Y m ∈ Icc (-m) (Y m) := ⟨hmn,le_rfl⟩
  have hz := parameter_multiplier hm hn hc hu he hrootL
  have hzpos (y : ℝ) (hy : y ∈ Icc (-m) (Y m)) : 0 < first u (m,y) := by
    rw [hz y hy]
    exact div_pos hm (sq_pos_of_pos (multiplier_pos _ _ _ _ _))
  have hId (y : ℝ) (hy : y ∈ Icc (-m) (Y m)) :=
    invariant_derivatives (hu y hy) (he y hy) (ne_of_gt (hzpos y hy))
  have hBc : ContinuousOn (fun y => schwarzJet u (m,y)) (Icc (-m) (Y m)) :=
    fun y hy => (hId y hy).2.continuousAt.continuousWithinAt
  have hB := eq_of_hasDerivAt_eq_on_Icc hBc continuousOn_const
    (fun y hy => (hId y hy).2) (fun y _ => hasDerivAt_const y (schwarzJet u (m,-m)))
    hmI rfl hnI
  have hinvL := root_invariants (hu _ hmI) (contDiffAt_id.neg)
    (he _ hmI) hrootL (neg_ne_zero.mpr (ne_of_gt hm))
    (show deriv (fun x : ℝ => -x) m ≠ 0 by rw [neg_deriv]; norm_num)
  have hinvR := root_invariants (hu _ hnI) hY (he _ hnI) hrootR
    (ne_of_gt hn) (ne_of_gt hl)
  have hAL : logJet u (m,-m) = 1/m+d := by
    have h := hinvL.1
    rw [neg_second_deriv,neg_deriv] at h
    dsimp only at h
    convert h using 1
    field_simp
    ring
  have hBL : schwarzJet u (m,-m) = 2*b*m-d^2/2-d/m-3/(2*m^2) := by
    have h := hinvL.2
    dsimp [schwarzian] at h
    rw [neg_third_deriv,neg_second_deriv,neg_deriv] at h
    dsimp only at h
    convert h using 1
    field_simp
    ring
  have hS : schwarzian Y m =
      2*b*(m+Y m*(deriv Y m)^2)+(d^2/2)*((deriv Y m)^2-1)
      -d*(1/m+(deriv Y m)^2/Y m)
      +(3/2)*((deriv Y m)^2/(Y m)^2-1/m^2) := by
    dsimp only at hB
    rw [hinvR.2,hBL] at hB
    field_simp at hB ⊢
    nlinarith
  let f : ℝ → ℝ := fun y => 1/(V y)^2
  have hVc : Continuous V := continuous_iff_continuousAt.mpr
    (fun y => (multiplier_deriv hc b d (-m) y).continuousAt)
  have hfc : Continuous f := continuous_const.div (hVc.pow 2)
    (fun y => pow_ne_zero 2 (ne_of_gt (multiplier_pos _ _ _ _ _)))
  let A : ℝ → ℝ := fun y => logJet u (m,y)-2*b*m*(∫ s in (-m)..y, f s)
  have hAd (y : ℝ) (hy : y ∈ Icc (-m) (Y m)) : HasDerivAt A 0 y := by
    have hd := (hId y hy).1.sub ((hfc.integral_hasStrictDerivAt (-m) y).hasDerivAt.const_mul (2*b*m))
    rw [hz y hy] at hd
    convert! hd using 1
    dsimp [f,V]
    ring
  have hAc : ContinuousOn A (Icc (-m) (Y m)) :=
    fun y hy => (hAd y hy).continuousAt.continuousWithinAt
  have hA := eq_of_hasDerivAt_eq_on_Icc hAc continuousOn_const hAd
    (fun y _ => hasDerivAt_const y (logJet u (m,-m))) hmI
    (by simp [A]) hnI
  have hW : deriv (deriv Y) m/deriv Y m =
      1/m-deriv Y m/Y m+d*(1+deriv Y m)+
      2*b*m*(∫ y in (-m)..Y m,1/(V y)^2) := by
    change logJet u (m,Y m)-2*b*m*(∫ s in (-m)..Y m, f s)=logJet u (m,-m) at hA
    rw [hinvR.1,hAL] at hA
    dsimp [f] at hA
    linarith
  refine ⟨hS,hW,?_⟩
  have hzn := (root_first_eventually (hu _ hnI) hY
    (jets_eventually (hu _ hnI) (he _ hnI)).1 hrootR).self_of_nhds
  dsimp only at hzn
  rw [hz _ hnI] at hzn
  have hvn : V (Y m) ≠ 0 := ne_of_gt (multiplier_pos _ _ _ _ _)
  change deriv Y m = m/(Y m*(V (Y m))^2)
  change m/(V (Y m))^2=Y m*deriv Y m at hzn
  field_simp at hzn ⊢
  nlinarith

end QuinticLienard.RiccatiJets

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.EndpointComparison
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
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuinticLienard.ModelEndpoint
open Set Filter
open scoped Topology ContDiff
open PartialCalculus QuadraticCoordinates RiccatiJets

theorem LowerChart.formulas {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    schwarzian c.upper (m ((d,k),r)) =
      k*(m ((d,k),r)+n ((d,k),r)*(ell ((d,k),r))^2)+
      (d^2/2)*((ell ((d,k),r))^2-1)-
      d*(1/m ((d,k),r)+(ell ((d,k),r))^2/n ((d,k),r))+
      (3/2)*((ell ((d,k),r))^2/(n ((d,k),r))^2-1/(m ((d,k),r))^2) ∧
    deriv (deriv c.upper) (m ((d,k),r))/ell ((d,k),r) =
      1/m ((d,k),r)-ell ((d,k),r)/n ((d,k),r)+d*(1+ell ((d,k),r))+
      k*m ((d,k),r)*(∫ y in (-m ((d,k),r))..(n ((d,k),r)),
        1/(Riccati.multiplier (fun s => c.solution (m ((d,k),r),s)) (k/2) d
          (-m ((d,k),r)) y)^2) := by
  have hn : 0 < c.upper (m ((d,k),r)) := by rw [c.upper_base]; exact n_pos hr
  have hl : 0 < deriv c.upper (m ((d,k),r)) := by
    rw [c.upper_derivative.deriv]; exact ell_pos hr
  have hu : ∀ y ∈ Icc (-m ((d,k),r)) (c.upper (m ((d,k),r))),
      ContDiffAt ℝ ω c.solution (m ((d,k),r),y) := by
    rw [c.upper_base]; exact c.solution_analytic
  have he : ∀ y ∈ Icc (-m ((d,k),r)) (c.upper (m ((d,k),r))),
      ∀ᶠ q in 𝓝 (m ((d,k),r),y), HasDerivAt (fun s => c.solution (q.1,s))
        (d*c.solution q+(k/2)*(c.solution q)^2-q.2) q.2 := by
    rw [c.upper_base]; exact c.equation
  have hh := RiccatiJets.endpoint_formulas (m_pos hr) hn hl
    (c.solution_continuous _) hu he c.upper_analytic c.lower_zero c.upper_zero
  rw [c.upper_base,c.upper_derivative.deriv] at hh
  constructor
  · convert hh.1 using 1; ring
  · convert hh.2.1 using 1; ring

theorem LowerChart.variation_bound {d k r ν : ℝ} (hr : 0 < r)
    (hk : 0 < k) (hd : d < 0) (hν : 0 ≤ ν)
    (hνsq : ν^2=d^2/4-(k/2)*m ((d,k),r)) (c : LowerChart d k r) :
    deriv (deriv c.upper) (m ((d,k),r))/ell ((d,k),r) ≤
      1/m ((d,k),r)-ell ((d,k),r)/n ((d,k),r)+d*ell ((d,k),r)-2*ν := by
  have he : ∀ y ∈ Icc (-m ((d,k),r)) (n ((d,k),r)),
      HasDerivAt (fun s => c.solution (m ((d,k),r),s))
        (d*c.solution (m ((d,k),r),y)+(k/2)*(c.solution (m ((d,k),r),y))^2-y) y :=
    fun y hy => (c.equation y hy).self_of_nhds
  have hz : c.solution (m ((d,k),r),-m ((d,k),r))=0 := c.lower_zero.self_of_nhds
  have hf := (c.formulas hr).2
  have hv := Riccati.endpoint_variation_bound (c.solution_continuous _)
    (show 0 < k/2 by linarith) (m_pos hr) (n_pos hr) hd hν hνsq hz he
    (show deriv (deriv c.upper) (m ((d,k),r))/ell ((d,k),r) =
      1/m ((d,k),r)-ell ((d,k),r)/n ((d,k),r)+d*(1+ell ((d,k),r))+
      2*(k/2)*m ((d,k),r)*(∫ y in (-m ((d,k),r))..(n ((d,k),r)),
        1/(Riccati.multiplier (fun s => c.solution (m ((d,k),r),s)) (k/2) d
          (-m ((d,k),r)) y)^2) by convert hf using 1; ring)
  exact hv

end QuinticLienard.ModelEndpoint

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.QuadraticSlices
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
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open ScalarArcs CanonicalVariation PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus

lemma fderiv_model (f : (ℝ × ℝ) × ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) (a b c : ℝ) :
    fderiv ℝ f q ((a,b),c) = a*direction ((1,0),0) f q+
      b*direction ((0,1),0) f q+c*direction ((0,0),1) f q := by
  have he : ((a,b),c) = a • (((1,0),0) : (ℝ × ℝ) × ℝ)+
      b • (((0,1),0) : (ℝ × ℝ) × ℝ)+c • (((0,0),1) : (ℝ × ℝ) × ℝ) := by
    ext <;> simp
  rw [he,map_add,map_add,map_smul,map_smul,map_smul]
  rfl

lemma slice_d {f : (ℝ × ℝ) × ℝ → ℝ} {d k r : ℝ}
    (hf : DifferentiableAt ℝ f ((d,k),r)) :
    HasDerivAt (fun s => f ((s,k),r)) (direction ((1,0),0) f ((d,k),r)) d := by
  simpa [direction] using! hf.hasFDerivAt.comp_hasDerivAt d
    (((hasDerivAt_id d).prodMk (hasDerivAt_const d k)).prodMk (hasDerivAt_const d r))
lemma slice_k {f : (ℝ × ℝ) × ℝ → ℝ} {d k r : ℝ}
    (hf : DifferentiableAt ℝ f ((d,k),r)) :
    HasDerivAt (fun s => f ((d,s),r)) (direction ((0,1),0) f ((d,k),r)) k := by
  simpa [direction] using! hf.hasFDerivAt.comp_hasDerivAt k
    (((hasDerivAt_const k d).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))

lemma v_translation (d k h : ℝ) {r : ℝ} (hr : 0 < r) :
    v profile (d,k) (h,r) = Hr ((d+k*h,k),r) := by
  have he : (fun s => M profile (d,k) (h,s)) =ᶠ[𝓝 r]
      (fun s => H ((d+k*h,k),s)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact translation d k h hs
  exact (second_hasDerivAt ((M_analytic profile profile_contDiff model_local_flow
    (p := (d,k)) (h := h) hr).differentiableAt (by simp))).unique
      ((Hr_hasDerivAt hr).congr_of_eventuallyEq he)

lemma height_derivative (d k h : ℝ) {r : ℝ} (hr : 0 < r) :
    first (M profile (d,k)) (h,r) = k*P ((d+k*h,k),r) := by
  have he : (fun s => M profile (d,k) (s,r)) =
      (fun s => H ((d+k*s,k),r)) := funext (fun s => translation d k s hr)
  have hd := (P_hasDerivAt (d := d+k*h) (k := k) hr).comp h
    (((hasDerivAt_id h).const_mul k).const_add d)
  have hh := (first_hasDerivAt ((M_analytic profile profile_contDiff model_local_flow
    (p := (d,k)) (h := h) hr).differentiableAt (by simp))).unique
      (hd.congr_of_eventuallyEq (Eventually.of_forall (fun s => congrFun he s)))
  simpa only [mul_one,mul_comm] using hh

lemma width_identity {d k r : ℝ} (hr : 0 < r) :
    k*P ((d,k),r)+d=(r*Hr ((d,k),r)+H ((d,k),r))/gap ((d,k),r) := by
  have ht := transport_midpoint profile profile_contDiff model_local_flow
    (p := (d,k)) (h := 0) hr
  rw [height_derivative d k 0 hr,translation d k 0 hr,v_translation d k 0 hr] at ht
  have hder : deriv (fun u => profile ((d,k),u)) 0=d := by
    have hh := (((hasDerivAt_id (0:ℝ)).const_mul d).add
      (((hasDerivAt_id (0:ℝ)).pow 2).const_mul (k/2))).deriv
    simpa [profile] using! hh
  simp only [mul_zero,add_zero,hder] at ht
  dsimp [gap]
  have hg := ne_of_gt (H_gap_pos (d := d) (k := k) hr)
  field_simp [hg] at ht ⊢
  nlinarith [ht]

lemma euler_identity {d k r : ℝ} (hr : 0 < r) :
    r*Hr ((d,k),r)-H ((d,k),r)=d*P ((d,k),r)+3*k*Q ((d,k),r) := by
  have hm : HasDerivAt (fun s : ℝ => ((d*s,k*s^3),(1:ℝ)))
      ((d,3*k*r^2),0) r := by
    convert! (((hasDerivAt_id r).const_mul d).prodMk
      (((hasDerivAt_id r).pow 3).const_mul k)).prodMk (hasDerivAt_const r (1:ℝ)) using 1
    ext <;> dsimp <;> ring
  have hd := (hasDerivAt_id r).mul
    (((H_analytic (d := d*r) (k := k*r^3) (by norm_num : (0:ℝ)<1)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt r hm)
  have he : (fun s => H ((d,k),s)) =ᶠ[𝓝 r] (fun s => s*H ((d*s,k*s^3),1)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact scaling d k hs
  have hc := (Hr_hasDerivAt (d := d) (k := k) hr).unique
    (hd.congr_of_eventuallyEq he)
  rw [fderiv_model] at hc
  change Hr ((d,k),r)=1*H ((d*r,k*r^3),1)+r*(d*P ((d*r,k*r^3),1)+
    (3*k*r^2)*Q ((d*r,k*r^3),1)+0*Hr ((d*r,k*r^3),1)) at hc
  rw [scaling d k hr,P_scaling d k hr,Q_scaling d k hr]
  nlinarith [hc]

lemma Hr_d_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun z => Hr ((z,k),r)) (R ((d,k),r)) d := by
  have hh := slice_d ((Hr_analytic (d := d) (k := k) hr).differentiableAt (by simp))
  have he : direction ((1,0),0) Hr ((d,k),r) = R ((d,k),r) :=
    direction_comm (H_analytic hr) _ _
  rw [he] at hh
  exact hh

lemma Hr_k_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun z => Hr ((d,z),r)) (S ((d,k),r)) k := by
  have hh := slice_k ((Hr_analytic (d := d) (k := k) hr).differentiableAt (by simp))
  have he : direction ((0,1),0) Hr ((d,k),r) = S ((d,k),r) :=
    direction_comm (H_analytic hr) _ _
  rw [he] at hh
  exact hh

lemma Hrr_hasDerivAt {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Hr ((d,k),s)) (Hrr ((d,k),r)) r :=
  slice_r ((Hr_analytic hr).differentiableAt (by simp))

lemma v_height_derivative (d k h : ℝ) {r : ℝ} (hr : 0 < r) :
    first (v profile (d,k)) (h,r) = k*R ((d+k*h,k),r) := by
  have he : (fun s => v profile (d,k) (s,r)) =
      (fun s => Hr ((d+k*s,k),r)) := funext (fun s => v_translation d k s hr)
  have hd := (Hr_d_hasDerivAt (d := d+k*h) (k := k) hr).comp h
    (((hasDerivAt_id h).const_mul k).const_add d)
  have hh := (first_hasDerivAt ((v_analytic profile profile_contDiff model_local_flow
    (p := (d,k)) (h := h) hr).differentiableAt (by simp))).unique
      (hd.congr_of_eventuallyEq (Eventually.of_forall (fun s => congrFun he s)))
  simpa only [mul_one,mul_comm] using hh

lemma v_width_derivative (d k h : ℝ) {r : ℝ} (hr : 0 < r) :
    second (v profile (d,k)) (h,r) = Hrr ((d+k*h,k),r) := by
  have he : (fun s => v profile (d,k) (h,s)) =ᶠ[𝓝 r]
      (fun s => Hr ((d+k*h,k),s)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact v_translation d k h hs
  exact (second_hasDerivAt ((v_analytic profile profile_contDiff model_local_flow
    (p := (d,k)) (h := h) hr).differentiableAt (by simp))).unique
      ((Hrr_hasDerivAt hr).congr_of_eventuallyEq he)

lemma transport_Hr {d k r : ℝ} (hr : 0 < r) :
    k*R ((d,k),r)-alpha ((d,k),r)*Hrr ((d,k),r) =
      -2*H ((d,k),r)*r*(1-(Hr ((d,k),r))^2)/(gap ((d,k),r))^2 := by
  have ht := transport_v profile profile_contDiff model_local_flow
    (p := (d,k)) (h := 0) hr
  rw [v_height_derivative d k 0 hr,v_width_derivative d k 0 hr,
    translation d k 0 hr,v_translation d k 0 hr] at ht
  simpa only [mul_zero,add_zero,alpha,gap] using ht

end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.BaseTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.WidthTransport
open ScalarArcs CanonicalVariation WidthCoordinates PartialCalculus
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : ArcFamilies.State P, ∃ f : ArcFamilies.State P × ℝ → ArcFamilies.State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (ArcFamilies.field Φ (f q)) q.2)
include hΦ hloc

theorem base_width_deriv {p : P} {t r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => baseAtWidth Φ ((p,t),s))
      (-(r^2-(M Φ p (baseAtWidth Φ ((p,t),r),r))^2)/r) r := by
  let h := baseAtWidth Φ ((p,t),r)
  have hs := base_spec Φ hΦ hloc (p := p) (t := t) hr
  let f : ℝ → ℝ := fun h => widthFamily Φ ((p,t),h)
  let g : ℝ → ℝ := fun s => baseAtWidth Φ ((p,t),s)
  have hg : DifferentiableAt ℝ g r :=
    ((base_analytic Φ hΦ hloc hr).comp r
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hf := width_base_deriv Φ hΦ hloc (p := p) hs.1
  have hm := midpoint_reparam Φ hΦ hloc (p := p) hs.1
  rw [hs.2] at hm hf
  rw [←hm] at hf
  have he : (f ∘ g) =ᶠ[𝓝 r] id := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hsr
    exact (base_spec Φ hΦ hloc hsr).2
  have hc := (hf.comp r hg.hasDerivAt).unique
    ((hasDerivAt_id r).congr_of_eventuallyEq he)
  have hgap := ne_of_gt (M_gap_pos Φ hΦ hloc (p := p) (h := h) hr)
  have hg' : deriv g r = -(r^2-M Φ p (h,r)^2)/r := by
    change (-r / (r^2-M Φ p (h,r)^2))*deriv g r = 1 at hc
    field_simp [hgap, ne_of_gt hr] at hc ⊢
    nlinarith [hc]
  simpa only [hg'] using hg.hasDerivAt

end QuinticLienard.WidthTransport

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.BaseSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ArchSymmetries
open ScalarArcs ArcFamilies CanonicalVariation WidthCoordinates
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)

include hΦ hloc

theorem base_affine {p q : P} {t r c H C : ℝ} (hr : 0 < r) (hc : 0 < c)
    (he : ∀ x, Φ (q,H+c^2*x) = C+c*Φ (p,x)) :
    baseAtWidth Φ ((q,H+c^2*t),c*r) = H+c^2*baseAtWidth Φ ((p,t),r) := by
  have hs := base_spec Φ hΦ hloc (p := p) (t := t) hr
  have hw := width_affine Φ hΦ hs.1 hc he
  rw [hs.2] at hw
  exact base_eq Φ hΦ hloc (mul_pos hc hr)
    (by nlinarith [sq_pos_of_pos hc]) hw

end QuinticLienard.ArchSymmetries

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.Characteristic
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
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open ScalarArcs CanonicalVariation PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus QuadraticCoordinates ArchSymmetries

lemma base_analytic {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : ContDiffAt ℝ ω base q :=
  (WidthCoordinates.base_analytic profile profile_contDiff model_local_flow hr).comp q
    ((contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd)
lemma J_analytic {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : ContDiffAt ℝ ω J q := by
  unfold J
  have hb := base_analytic hr
  fun_prop
lemma A_analytic {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : ContDiffAt ℝ ω A q := by
  exact ((H_analytic (d := J q) (k := q.1.2) hr).comp q
    (((J_analytic hr).prodMk contDiffAt_fst.snd).prodMk contDiffAt_snd)).div
      contDiffAt_snd (ne_of_gt hr)
lemma D_analytic {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : ContDiffAt ℝ ω D q :=
  (Hr_analytic (d := J q) (k := q.1.2) hr).comp q
    (((J_analytic hr).prodMk contDiffAt_fst.snd).prodMk contDiffAt_snd)

lemma Jz_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => J ((s,k),r)) (Jz ((z,k),r)) z :=
  slice_d ((J_analytic hr).differentiableAt (by simp))
lemma Jk_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => J ((z,s),r)) (Jk ((z,k),r)) k :=
  slice_k ((J_analytic hr).differentiableAt (by simp))
lemma Az_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => A ((s,k),r)) (Az ((z,k),r)) z :=
  slice_d ((A_analytic hr).differentiableAt (by simp))
lemma Ak_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => A ((z,s),r)) (Ak ((z,k),r)) k :=
  slice_k ((A_analytic hr).differentiableAt (by simp))
lemma Dz_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => D ((s,k),r)) (Dz ((z,k),r)) z :=
  slice_d ((D_analytic hr).differentiableAt (by simp))
lemma Dk_hasDerivAt {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => D ((z,s),r)) (Dk ((z,k),r)) k :=
  slice_k ((D_analytic hr).differentiableAt (by simp))

lemma A_abs_lt {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : |A q| < 1 := by
  dsimp [A]
  rw [abs_div,abs_of_pos hr,div_lt_one hr]
  exact H_abs_lt hr
lemma D_abs_lt {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : |D q| < 1 := Hr_abs_lt hr
lemma A_gap_pos {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : 0 < 1-(A q)^2 := by
  have ht := sq_lt_sq₀ (abs_nonneg (A q)) (by norm_num : (0:ℝ) ≤ 1) |>.mpr (A_abs_lt hr)
  nlinarith [sq_abs (A q)]
lemma D_gap_pos {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : 0 < 1-(D q)^2 := by
  have ht := sq_lt_sq₀ (abs_nonneg (D q)) (by norm_num : (0:ℝ) ≤ 1) |>.mpr (D_abs_lt hr)
  nlinarith [sq_abs (D q)]

lemma base_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => base ((z,k),s)) (-r*(1-(A ((z,k),r))^2)) r := by
  have hb := base_width_deriv profile profile_contDiff model_local_flow
    (p := (z,k)) (t := 0) hr
  rw [translation z k _ hr] at hb
  convert! hb using 1
  dsimp only [J,A,base]
  field_simp [ne_of_gt hr]

lemma J_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => J ((z,k),s)) (-k*r*(1-(A ((z,k),r))^2)) r := by
  convert! (base_deriv (z := z) (k := k) hr).const_mul k |>.const_add z using 1
  ring

lemma A_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => A ((z,k),s))
      (J ((z,k),r)*(1-(A ((z,k),r))^2)-2*A ((z,k),r)/r) r := by
  have hd := (((H_analytic (d := J ((z,k),r)) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (f := fun s => ((J ((z,k),s),k),s)) r
    (((J_deriv (z := z) (k := k) hr).prodMk (hasDerivAt_const r k)).prodMk (hasDerivAt_id r))).div
      (hasDerivAt_id r) (ne_of_gt hr)
  rw [fderiv_model] at hd
  have ht := width_identity (d := J ((z,k),r)) (k := k) hr
  change k*P ((J ((z,k),r),k),r)+J ((z,k),r)=
    (r*Hr ((J ((z,k),r),k),r)+H ((J ((z,k),r),k),r))/(r^2-H ((J ((z,k),r),k),r)^2) at ht
  have hg := ne_of_gt (H_gap_pos (d := J ((z,k),r)) (k := k) hr)
  convert! hd using 1
  dsimp [A,P,Hr,Q,direction] at ht ⊢
  field_simp [ne_of_gt hr,hg] at ht ⊢
  nlinarith [ht]

lemma D_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => D ((z,k),s))
      (2*A ((z,k),r)*(1-(D ((z,k),r))^2)/(r*(1-(A ((z,k),r))^2))) r := by
  have hd := (Hr_analytic (d := J ((z,k),r)) (k := k) hr).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp_hasDerivAt (f := fun s => ((J ((z,k),s),k),s)) r
    (((J_deriv (z := z) (k := k) hr).prodMk (hasDerivAt_const r k)).prodMk (hasDerivAt_id r))
  rw [fderiv_model] at hc
  have hR : direction ((1,0),0) Hr ((J ((z,k),r),k),r)=R ((J ((z,k),r),k),r) :=
    direction_comm (H_analytic hr) _ _
  rw [hR] at hc
  have ht := transport_Hr (d := J ((z,k),r)) (k := k) hr
  have hg := ne_of_gt (H_gap_pos (d := J ((z,k),r)) (k := k) hr)
  have ha := ne_of_gt (A_gap_pos (q := ((z,k),r)) hr)
  convert! hc using 1
  dsimp [A,D,Hrr,alpha,gap] at ht ⊢
  field_simp [ne_of_gt hr,hg] at ht ⊢
  nlinarith [ht]

end QuinticLienard.ReferenceCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CharacteristicScaling
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
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open ScalarArcs CanonicalVariation PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus QuadraticCoordinates ArchSymmetries

lemma base_translation (z k t : ℝ) {r : ℝ} (hr : 0 < r) :
    baseAtWidth profile (((z,k),t),r) = t+baseAtWidth profile (((z+k*t,k),0),r) := by
  have hh := base_affine profile profile_contDiff model_local_flow
    (p := (z+k*t,k)) (q := (z,k)) (t := 0) (H := t)
    (C := z*t+k/2*t^2) hr (show 0 < (1:ℝ) by norm_num)
    (by intro x; dsimp [profile]; ring)
  simpa using hh

lemma J_reparam {z k r : ℝ} (hr : 0 < r) (hk : k ≠ 0) :
    J ((z,k),r)=k*baseAtWidth profile (((0,k),z/k),r) := by
  have hh := base_translation 0 k (z/k) hr
  simp only [zero_add,mul_div_cancel₀ _ hk] at hh
  rw [hh]
  dsimp [J,base]
  field_simp

lemma Jz_pos {z k r : ℝ} (hr : 0 < r) : 0 < Jz ((z,k),r) := by
  by_cases hk : k = 0
  · subst k
    have he : (fun s => J ((s,0),r))=id := by ext s; simp [J]
    have hh := (Jz_hasDerivAt (z := z) (k := 0) hr).unique (he ▸ hasDerivAt_id z)
    rw [hh]; norm_num
  · have hb : DifferentiableAt ℝ (fun t => baseAtWidth profile (((0,k),t),r)) (z/k) :=
      ((WidthCoordinates.base_analytic profile profile_contDiff model_local_flow hr).comp (z/k)
        ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
    have hc := (hb.hasDerivAt.comp z ((hasDerivAt_id z).div_const k)).const_mul k
    have he : (fun s => J ((s,k),r))=(fun s => k*baseAtWidth profile (((0,k),s/k),r)) :=
      funext (fun s => J_reparam hr hk)
    have hh := (Jz_hasDerivAt (z := z) (k := k) hr).unique (he ▸ hc)
    have hp := base_peak_deriv_pos profile profile_contDiff model_local_flow
      (p := (0,k)) (t := z/k) hr
    rw [hh]
    convert hp using 1
    field_simp

lemma Az_formula {z k r : ℝ} (hr : 0 < r) :
    Az ((z,k),r) = P ((J ((z,k),r),k),r)*Jz ((z,k),r)/r := by
  have hc := ((P_hasDerivAt (d := J ((z,k),r)) (k := k) hr).comp z
    (Jz_hasDerivAt (z := z) (k := k) hr)).div_const r
  exact (Az_hasDerivAt hr).unique hc

lemma Ak_formula {z k r : ℝ} (hr : 0 < r) :
    Ak ((z,k),r) = (P ((J ((z,k),r),k),r)*Jk ((z,k),r)+Q ((J ((z,k),r),k),r))/r := by
  have hc := ((H_analytic (d := J ((z,k),r)) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
    (f := fun s => ((J ((z,s),r),s),r)) k
    (((Jk_hasDerivAt (z := z) (k := k) hr).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
  have hh := (Ak_hasDerivAt (z := z) (k := k) hr).unique (hc.div_const r)
  rw [fderiv_model] at hh
  simpa [P,Q,mul_comm] using hh

lemma Dz_formula {z k r : ℝ} (hr : 0 < r) :
    Dz ((z,k),r) = R ((J ((z,k),r),k),r)*Jz ((z,k),r) := by
  have hc := (Hr_d_hasDerivAt (d := J ((z,k),r)) (k := k) hr).comp z
    (Jz_hasDerivAt (z := z) (k := k) hr)
  exact (Dz_hasDerivAt hr).unique hc

lemma Dk_formula {z k r : ℝ} (hr : 0 < r) :
    Dk ((z,k),r) = R ((J ((z,k),r),k),r)*Jk ((z,k),r)+S ((J ((z,k),r),k),r) := by
  have hc := ((Hr_analytic (d := J ((z,k),r)) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
    (f := fun s => ((J ((z,s),r),s),r)) k
    (((Jk_hasDerivAt (z := z) (k := k) hr).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
  have hh := (Dk_hasDerivAt (z := z) (k := k) hr).unique hc
  rw [fderiv_model] at hh
  have hR : direction ((1,0),0) Hr ((J ((z,k),r),k),r)=R ((J ((z,k),r),k),r) :=
    direction_comm (H_analytic hr) _ _
  have hS : direction ((0,1),0) Hr ((J ((z,k),r),k),r)=S ((J ((z,k),r),k),r) :=
    direction_comm (H_analytic hr) _ _
  simpa [hR,hS,mul_comm] using hh

lemma Az_pos {z k r : ℝ} (hr : 0 < r) : 0 < Az ((z,k),r) := by
  rw [Az_formula hr]
  exact div_pos (mul_pos (QuadraticVariation.P_pos hr) (Jz_pos hr)) hr

end QuinticLienard.ReferenceCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.MixedDerivatives
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
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus

lemma mixed_z_radius {f fr : (ℝ × ℝ) × ℝ → ℝ} {z k r b : ℝ}
    (hf : ∀ q, 0 < q.2 → ContDiffAt ℝ ω f q) (hr : 0 < r)
    (hfr : ∀ a, HasDerivAt (fun s => f ((a,k),s)) (fr ((a,k),r)) r)
    (hb : HasDerivAt (fun a => fr ((a,k),r)) b z) :
    HasDerivAt (fun s => direction ((1,0),0) f ((z,k),s)) b r := by
  have he : (fun a => direction ((0,0),1) f ((a,k),r)) = (fun a => fr ((a,k),r)) := by
    ext a
    exact (slice_r ((hf ((a,k),r) hr).differentiableAt (by simp))).unique (hfr a)
  have hcross := (slice_d ((direction_contDiffAt (hf ((z,k),r) hr) ((0,0),1)).differentiableAt
    (by simp))).unique (he ▸ hb)
  have hh := slice_r ((direction_contDiffAt (hf ((z,k),r) hr) ((1,0),0)).differentiableAt (by simp))
  rw [←direction_comm (hf ((z,k),r) hr) ((1,0),0) ((0,0),1),hcross] at hh
  exact hh

lemma mixed_k_radius {f fr : (ℝ × ℝ) × ℝ → ℝ} {z k r b : ℝ}
    (hf : ∀ q, 0 < q.2 → ContDiffAt ℝ ω f q) (hr : 0 < r)
    (hfr : ∀ a, HasDerivAt (fun s => f ((z,a),s)) (fr ((z,a),r)) r)
    (hb : HasDerivAt (fun a => fr ((z,a),r)) b k) :
    HasDerivAt (fun s => direction ((0,1),0) f ((z,k),s)) b r := by
  have he : (fun a => direction ((0,0),1) f ((z,a),r)) = (fun a => fr ((z,a),r)) := by
    ext a
    exact (slice_r ((hf ((z,a),r) hr).differentiableAt (by simp))).unique (hfr a)
  have hcross := (slice_k ((direction_contDiffAt (hf ((z,k),r) hr) ((0,0),1)).differentiableAt
    (by simp))).unique (he ▸ hb)
  have hh := slice_r ((direction_contDiffAt (hf ((z,k),r) hr) ((0,1),0)).differentiableAt (by simp))
  rw [←direction_comm (hf ((z,k),r) hr) ((0,1),0) ((0,0),1),hcross] at hh
  exact hh

end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CharacteristicJets
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
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open PartialCalculus QuadraticCoordinates

lemma Az_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Az ((z,k),s))
      ((1-(A ((z,k),r))^2)*Jz ((z,k),r)+C ((z,k),r)*Az ((z,k),r)) r := by
  apply mixed_z_radius (f := A)
    (fr := fun q => J q*(1-(A q)^2)-2*A q/q.2) (fun _ hp => A_analytic hp) hr
    (fun a => A_deriv hr)
  convert! ((Jz_hasDerivAt (z := z) (k := k) hr).mul
    (((Az_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1)).sub
      (((Az_hasDerivAt (z := z) (k := k) hr).const_mul 2).div_const r) using 1
  dsimp [C]
  ring

lemma Ak_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Ak ((z,k),s))
      ((1-(A ((z,k),r))^2)*Jk ((z,k),r)+C ((z,k),r)*Ak ((z,k),r)) r := by
  apply mixed_k_radius (f := A)
    (fr := fun q => J q*(1-(A q)^2)-2*A q/q.2) (fun _ hp => A_analytic hp) hr
    (fun a => A_deriv hr)
  convert! ((Jk_hasDerivAt (z := z) (k := k) hr).mul
    (((Ak_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1)).sub
      (((Ak_hasDerivAt (z := z) (k := k) hr).const_mul 2).div_const r) using 1
  dsimp [C]
  ring

lemma E_z_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => E ((s,k),r)) (K ((z,k),r)*Az ((z,k),r)) z := by
  convert! ((Az_hasDerivAt (z := z) (k := k) hr).const_mul 2).div
    ((((Az_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1).const_mul r)
      (ne_of_gt (mul_pos hr (A_gap_pos (q := ((z,k),r)) hr))) using 1
  dsimp [E,K]
  field_simp
  ring

lemma E_k_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => E ((z,s),r)) (K ((z,k),r)*Ak ((z,k),r)) k := by
  convert! ((Ak_hasDerivAt (z := z) (k := k) hr).const_mul 2).div
    ((((Ak_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1).const_mul r)
      (ne_of_gt (mul_pos hr (A_gap_pos (q := ((z,k),r)) hr))) using 1
  dsimp [E,K]
  field_simp
  ring

lemma D_deriv' {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => D ((z,k),s)) (E ((z,k),r)*(1-(D ((z,k),r))^2)) r := by
  convert D_deriv (z := z) (k := k) hr using 1
  dsimp [E]
  ring

lemma Dz_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Dz ((z,k),s))
      (K ((z,k),r)*Az ((z,k),r)*(1-(D ((z,k),r))^2)-
        2*E ((z,k),r)*D ((z,k),r)*Dz ((z,k),r)) r := by
  apply mixed_z_radius (f := D) (fr := fun q => E q*(1-(D q)^2))
    (fun _ hp => D_analytic hp) hr (fun a => D_deriv' hr)
  convert! (E_z_deriv (z := z) (k := k) hr).mul
    (((Dz_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1) using 1
  dsimp only [Pi.pow_apply]
  ring

lemma Dk_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Dk ((z,k),s))
      (K ((z,k),r)*Ak ((z,k),r)*(1-(D ((z,k),r))^2)-
        2*E ((z,k),r)*D ((z,k),r)*Dk ((z,k),r)) r := by
  apply mixed_k_radius (f := D) (fr := fun q => E q*(1-(D q)^2))
    (fun _ hp => D_analytic hp) hr (fun a => D_deriv' hr)
  convert! (E_k_deriv (z := z) (k := k) hr).mul
    (((Dk_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1) using 1
  dsimp only [Pi.pow_apply]
  ring

lemma U_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => U ((z,k),s)) (K ((z,k),r)*Az ((z,k),r)) r := by
  convert! (Dz_deriv (z := z) (k := k) hr).div
    (((D_deriv' (z := z) (k := k) hr).pow 2).const_sub 1)
      (ne_of_gt (D_gap_pos (q := ((z,k),r)) hr)) using 1
  dsimp only [Pi.pow_apply]
  field_simp [ne_of_gt (D_gap_pos (q := ((z,k),r)) hr)]
  ring

lemma V_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => V ((z,k),s)) (K ((z,k),r)*Ak ((z,k),r)) r := by
  convert! (Dk_deriv (z := z) (k := k) hr).div
    (((D_deriv' (z := z) (k := k) hr).pow 2).const_sub 1)
      (ne_of_gt (D_gap_pos (q := ((z,k),r)) hr)) using 1
  dsimp only [Pi.pow_apply]
  field_simp [ne_of_gt (D_gap_pos (q := ((z,k),r)) hr)]
  ring

lemma T_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => T ((z,k),s))
      (-(1-(A ((z,k),r))^2)*Q ((J ((z,k),r),k),r)*Jz ((z,k),r)/
        (r*(Az ((z,k),r))^2)) r := by
  convert! (Ak_deriv (z := z) (k := k) hr).div (Az_deriv (z := z) (k := k) hr)
    (ne_of_gt (Az_pos (z := z) (k := k) hr)) using 1
  have h1 := Az_formula (z := z) (k := k) hr
  have h2 := Ak_formula (z := z) (k := k) hr
  rw [h1,h2]
  field_simp
  ring

lemma B_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => B ((z,k),s))
      ((1-(A ((z,k),r))^2)*Q ((J ((z,k),r),k),r)*Jz ((z,k),r)/
        (r*(Az ((z,k),r))^2)*U ((z,k),r)) r := by
  convert! (V_deriv (z := z) (k := k) hr).sub
    ((T_deriv (z := z) (k := k) hr).mul (U_deriv (z := z) (k := k) hr)) using 1
  dsimp [B,T]
  field_simp [ne_of_gt (Az_pos (z := z) (k := k) hr)]
  ring

lemma B_formula {z k r : ℝ} (hr : 0 < r) :
    B ((z,k),r) = G ((J ((z,k),r),k),r)/(P ((J ((z,k),r),k),r)*(1-(D ((z,k),r))^2)) := by
  dsimp only [B,V,T,U]
  rw [Dk_formula hr,Dz_formula hr,Az_formula hr,Ak_formula hr]
  dsimp [G]
  field_simp [ne_of_gt (QuadraticVariation.P_pos (d := J ((z,k),r)) (k := k) hr),
    ne_of_gt (Jz_pos (z := z) (k := k) hr),ne_of_gt hr]
  ring

end QuinticLienard.ReferenceCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RadiusLimits
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
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates

lemma RN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω RN q := by
  unfold RN
  have h1 := PN_analytic q
  have h2 := PNr_analytic q
  fun_prop
lemma GN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω GN q := by
  unfold GN
  have h1 := PN_analytic q
  have h2 := PNr_analytic q
  have h3 := QN_analytic q
  have h4 := QNr_analytic q
  fun_prop
lemma RN_zero (d k : ℝ) : RN ((d,k),0)=2/3 := by
  norm_num [RN,PN,QuadraticVariation.P_zero (by norm_num : (0:ℝ)<1)]
lemma GN_zero (d k : ℝ) : GN ((d,k),0)=2/45 := by
  norm_num [GN,PN,QN,QuadraticVariation.P_zero (by norm_num : (0:ℝ)<1),
    QuadraticVariation.Q_zero (by norm_num : (0:ℝ)<1)]
lemma G_scaled (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    G ((d,k),r)=r^5*GN ((d,k),r) := by
  dsimp [G]
  rw [R_scaled d k hr,S_scaled d k hr,P_scaling d k hr,Q_scaling d k hr]
  dsimp [GN,PN,QN]
  ring
lemma R_G_positive_near_zero (d k : ℝ) :
    ∀ᶠ q in 𝓝 ((d,k),(0:ℝ)), 0 < q.2 → 0 < R q ∧ 0 < G q := by
  have hp : 0 < RN ((d,k),0) := by rw [RN_zero]; norm_num
  have hq : 0 < GN ((d,k),0) := by rw [GN_zero]; norm_num
  filter_upwards [(RN_analytic ((d,k),0)).continuousAt.eventually (eventually_gt_nhds hp),
    (GN_analytic ((d,k),0)).continuousAt.eventually (eventually_gt_nhds hq)] with q h1 h2 hr
  rcases q with ⟨⟨d',k'⟩,r⟩
  constructor
  · rw [R_scaled d' k' hr]
    have hh := mul_pos hr h1
    dsimp [RN] at hh
    nlinarith only [hh]
  · rw [G_scaled d' k' hr]
    exact mul_pos (pow_pos hr 5) h2

end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.BaseLimits
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
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open ScalarArcs CanonicalVariation PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus QuadraticCoordinates ArchSymmetries

lemma base_bounds {z k r : ℝ} (hr : 0 < r) : -r^2/2 ≤ base ((z,k),r) ∧ base ((z,k),r) < 0 := by
  have hs := base_spec profile profile_contDiff model_local_flow (p := (z,k)) (t := 0) hr
  have hh := height_bound profile profile_contDiff model_local_flow (p := (z,k)) hs.1
  rw [hs.2] at hh
  exact ⟨by dsimp [base]; linarith,hs.1⟩

lemma base_tendsto_zero (z k : ℝ) : Tendsto (fun r => base ((z,k),r)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun r : ℝ => -r^2/2) (h := fun _ : ℝ => (0:ℝ))
  · simpa using! (((tendsto_id.mono_left inf_le_left).pow 2).neg.div_const (2:ℝ) :
      Tendsto (fun r : ℝ => -r^2/2) (𝓝[>] (0:ℝ)) (𝓝 (-0^2/2)))
  · exact tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (base_bounds (z := z) (k := k) hr).1
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (base_bounds (z := z) (k := k) hr).2.le

lemma model_tendsto (z k : ℝ) :
    Tendsto (fun r => ((J ((z,k),r),k),r)) (𝓝[>] (0:ℝ)) (𝓝 ((z,k),(0:ℝ))) := by
  have hj : Tendsto (fun r => J ((z,k),r)) (𝓝[>] (0:ℝ)) (𝓝 z) := by
    simpa [J] using (tendsto_const_nhds.add (tendsto_const_nhds.mul (base_tendsto_zero z k)))
  exact (hj.prodMk_nhds tendsto_const_nhds).prodMk_nhds (tendsto_id.mono_left inf_le_left)

lemma U_B_positive_near_zero (z k : ℝ) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < U ((z,k),r) ∧ 0 < B ((z,k),r) := by
  filter_upwards [(model_tendsto z k).eventually (R_G_positive_near_zero z k),
    self_mem_nhdsWithin] with r hh hr
  obtain ⟨hR,hG⟩ := hh hr
  constructor
  · dsimp only [U]
    rw [Dz_formula hr]
    exact div_pos (mul_pos hR (Jz_pos hr)) (D_gap_pos hr)
  · rw [B_formula hr]
    exact div_pos hG (mul_pos (QuadraticVariation.P_pos hr) (D_gap_pos hr))

lemma K_pos {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : 0 < K q := by
  dsimp [K]
  exact div_pos (mul_pos (by norm_num) (by positivity))
    (mul_pos hr (sq_pos_of_pos (A_gap_pos hr)))

lemma U_pos {z k r : ℝ} (hr : 0 < r) : 0 < U ((z,k),r) := by
  have hm : MonotoneOn (fun s => U ((z,k),s)) (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun s hs => (U_deriv hs).continuousAt.continuousWithinAt)
      (fun s hs => (U_deriv (interior_subset (s := Ioi 0) hs)).differentiableAt.differentiableWithinAt)
    intro s hs
    have hs' : 0 < s := interior_subset hs
    rw [(U_deriv (z := z) (k := k) hs').deriv]
    exact (mul_pos (K_pos hs') (Az_pos hs')).le
  have he : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s ∧ s < r ∧ 0 < U ((z,k),s) := by
    filter_upwards [U_B_positive_near_zero z k,self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono inf_le_left] with s hs hpos hlt
    exact ⟨hpos,hlt,hs.1⟩
  obtain ⟨s,hs,hlt,hU⟩ := he.exists
  exact hU.trans_le (hm hs hr hlt.le)

lemma B_pos {z k r : ℝ} (hr : 0 < r) : 0 < B ((z,k),r) := by
  have hm : MonotoneOn (fun s => B ((z,k),s)) (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun s hs => (B_deriv hs).continuousAt.continuousWithinAt)
      (fun s hs => (B_deriv (interior_subset (s := Ioi 0) hs)).differentiableAt.differentiableWithinAt)
    intro s hs
    have hs' : 0 < s := interior_subset hs
    rw [(B_deriv (z := z) (k := k) hs').deriv]
    exact (mul_pos (div_pos (mul_pos (mul_pos (A_gap_pos hs')
      (QuadraticVariation.Q_pos hs')) (Jz_pos hs'))
      (mul_pos hs' (sq_pos_of_pos (Az_pos hs')))) (U_pos hs')).le
  have he : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s ∧ s < r ∧ 0 < B ((z,k),s) := by
    filter_upwards [U_B_positive_near_zero z k,self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono inf_le_left] with s hs hpos hlt
    exact ⟨hpos,hlt,hs.2⟩
  obtain ⟨s,hs,hlt,hB⟩ := he.exists
  exact hB.trans_le (hm hs hr hlt.le)

lemma J_surjective (d k : ℝ) {r : ℝ} (hr : 0 < r) : ∃ z : ℝ, J ((z,k),r)=d := by
  let t := peakAtWidth profile (((d,k),0),r)
  have hs := peak_spec profile profile_contDiff model_local_flow (p := (d,k)) (h := 0) hr
  have he : baseAtWidth profile (((d,k),t),r)=0 :=
    base_eq profile profile_contDiff model_local_flow hr hs.1 hs.2
  have ht := base_translation d k t hr
  refine ⟨d+k*t,?_⟩
  dsimp [J,base]
  rw [he] at ht
  linear_combination -k*ht

end QuinticLienard.ReferenceCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RadiusSigns
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
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.QuadraticCoordinates

theorem R_pos {d k r : ℝ} (hr : 0 < r) : 0 < R ((d,k),r) := by
  obtain ⟨z,hz⟩ := ReferenceCharacteristic.J_surjective d k hr
  have hu := ReferenceCharacteristic.U_pos (z := z) (k := k) hr
  dsimp only [ReferenceCharacteristic.U] at hu
  rw [ReferenceCharacteristic.Dz_formula hr,hz] at hu
  have hm := (div_pos_iff_of_pos_right (ReferenceCharacteristic.D_gap_pos (q := ((z,k),r)) hr)).mp hu
  exact (mul_pos_iff_of_pos_right (ReferenceCharacteristic.Jz_pos (z := z) (k := k) hr)).mp hm

theorem G_pos {d k r : ℝ} (hr : 0 < r) : 0 < G ((d,k),r) := by
  obtain ⟨z,hz⟩ := ReferenceCharacteristic.J_surjective d k hr
  have hb := ReferenceCharacteristic.B_pos (z := z) (k := k) hr
  rw [ReferenceCharacteristic.B_formula hr,hz] at hb
  exact (div_pos_iff_of_pos_right (mul_pos (QuadraticVariation.P_pos hr)
    (ReferenceCharacteristic.D_gap_pos (q := ((z,k),r)) hr))).mp hb

end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RegionBarrier
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
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology
namespace QuinticLienard.RegionBarrier

lemma last_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ c ∈ Ico a b, f c=0 ∧ ∀ t ∈ Ioc c b, 0 < f t := by
  let S := Icc a b ∩ f ⁻¹' {0}
  have hclose : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcomp : IsCompact S := isCompact_Icc.of_isClosed_subset hclose inter_subset_left
  obtain ⟨x,hx,hx0⟩ := intermediate_value_Icc hab.le hf (show (0:ℝ) ∈ Icc (f a) (f b) from ⟨ha.le,hb.le⟩)
  have hne : S.Nonempty := ⟨x,hx,hx0⟩
  obtain ⟨c,hc,hmax⟩ := hcomp.exists_isMaxOn hne continuousOn_id
  have hc0 : f c=0 := hc.2
  have hcb : c < b := lt_of_le_of_ne hc.1.2 (by intro h; rw [h] at hc0; linarith)
  refine ⟨c,⟨hc.1.1,hcb⟩,hc0,?_⟩
  intro t ht
  by_contra! hnt
  have hft := hf.mono (Icc_subset_Icc (hc.1.1.trans ht.1.le) le_rfl)
  obtain ⟨x,hx,hx0⟩ := intermediate_value_Icc ht.2 hft (show (0:ℝ) ∈ Icc (f t) (f b) from ⟨hnt,hb.le⟩)
  have hxS : x ∈ S := ⟨⟨hc.1.1.trans (ht.1.le.trans hx.1),hx.2⟩,hx0⟩
  have hh := hmax hxS
  exact (ht.1.trans_le hx.1).not_ge hh

lemma no_negative_w_at_positive_slope {h f w C w' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt h (f t) t)
    (hF : ∀ t ∈ Icc a b, HasDerivAt f (C t*w t) t)
    (hW : ∀ t ∈ Icc a b, HasDerivAt w (w' t) t)
    (hC : ∀ t ∈ Icc a b, 0 < C t)
    (hWp : ∀ t ∈ Icc a b, h t < 0 → 0 ≤ f t → 0 < w' t)
    (ha : f a < 0) (hb : h b < 0) (hfb : 0 < f b) : 0 ≤ w b := by
  by_contra! hwb
  obtain ⟨c,hc,hc0,hpos⟩ := last_zero hab
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt) ha hfb
  have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc hc.1 le_rfl
  have hfn (t : ℝ) (ht : t ∈ Icc c b) : 0 ≤ f t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h,hc0]
    · exact (hpos t ⟨h,ht.2⟩).le
  have hmH : MonotoneOn h (Icc c b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc c b)
      (fun t ht => (hH t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hH t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hH t (hsub (interior_subset ht))).deriv]
    exact hfn t (interior_subset ht)
  have hneg (t : ℝ) (ht : t ∈ Icc c b) : h t < 0 :=
    (hmH ht ⟨hc.2.le,le_rfl⟩ ht.2).trans_lt hb
  have hmW : MonotoneOn w (Icc c b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc c b)
      (fun t ht => (hW t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hW t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hW t (hsub (interior_subset ht))).deriv]
    exact (hWp t (hsub (interior_subset ht)) (hneg t (interior_subset ht)) (hfn t (interior_subset ht))).le
  have hmF : StrictAntiOn f (Icc c b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc c b)
      (fun t ht => (hF t (hsub ht)).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hF t (hsub (interior_subset ht))).deriv]
    exact mul_neg_of_pos_of_neg (hC t (hsub (interior_subset ht)))
      ((hmW (interior_subset ht) ⟨hc.2.le,le_rfl⟩ (interior_subset ht).2).trans_lt hwb)
  have hh := hmF ⟨le_rfl,hc.2.le⟩ ⟨hc.2.le,le_rfl⟩ hc.2
  rw [hc0] at hh
  linarith

lemma no_negative_w {h f w C w' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt h (f t) t)
    (hF : ∀ t ∈ Icc a b, HasDerivAt f (C t*w t) t)
    (hW : ∀ t ∈ Icc a b, HasDerivAt w (w' t) t)
    (hC : ∀ t ∈ Icc a b, 0 < C t)
    (hWp : ∀ t ∈ Icc a b, h t < 0 → 0 ≤ f t → 0 < w' t)
    (ha : f a < 0) (hb : h b < 0) (hfb : 0 ≤ f b) : 0 ≤ w b := by
  rcases hfb.eq_or_lt with hfb | hfb
  · by_contra! hwb
    have hbb : b ∈ Icc a b := ⟨hab.le,le_rfl⟩
    have hlim := (hasDerivWithinAt_iff_tendsto_slope' (show b ∉ Iio b by simp)).mp
      ((hF b hbb).hasDerivWithinAt (s := Iio b))
    have hdneg : C b*w b < 0 := mul_neg_of_pos_of_neg (hC b hbb) hwb
    have he : ∀ᶠ t in 𝓝[<] b, a < t ∧ t < b ∧ h t < 0 ∧ w t < 0 ∧ 0 < f t := by
      filter_upwards [(eventually_gt_nhds hab).filter_mono inf_le_left,self_mem_nhdsWithin,
        ((hH b hbb).continuousAt.eventually (eventually_lt_nhds hb)).filter_mono inf_le_left,
        ((hW b hbb).continuousAt.eventually (eventually_lt_nhds hwb)).filter_mono inf_le_left,
        hlim.eventually (eventually_lt_nhds hdneg)] with t hat htb hht hwt hft
      refine ⟨hat,htb,hht,hwt,?_⟩
      have hf0 : f b=0 := hfb.symm
      have hdiv : (f t)/(t-b)<0 := by simpa [slope,vsub_eq_sub,hf0,div_eq_mul_inv,mul_comm] using hft
      have h := (div_lt_iff_of_neg (sub_neg.mpr htb)).mp hdiv
      simpa using h
    obtain ⟨t,hat,htb,hht,hwt,hft⟩ := he.exists
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right htb.le
    exact hwt.not_ge (no_negative_w_at_positive_slope hat
      (fun s hs => hH s (hsub hs)) (fun s hs => hF s (hsub hs))
      (fun s hs => hW s (hsub hs)) (fun s hs => hC s (hsub hs))
      (fun s hs => hWp s (hsub hs)) ha hht hft)
  · exact no_negative_w_at_positive_slope hab hH hF hW hC hWp ha hb hfb
end QuinticLienard.RegionBarrier

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CharacteristicSigns
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
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ReferenceCharacteristic
open QuadraticCoordinates PartialCalculus

lemma monotone_zero_nonneg {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 0))
    (hm : MonotoneOn f (Ioc 0 r)) : 0 ≤ f r := by
  apply le_of_tendsto hf
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hr).filter_mono inf_le_left] with s hs hsr
  exact hm ⟨hs,hsr.le⟩ ⟨hr,le_rfl⟩ hsr.le

lemma strictMono_zero_pos {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 0))
    (hm : StrictMonoOn f (Ioc 0 r)) : 0 < f r := by
  have hhalf : 0 < r/2 := half_pos hr
  have hle : r/2 ≤ r := by linarith
  have hn := monotone_zero_nonneg hhalf hf (hm.monotoneOn.mono (Ioc_subset_Ioc_right hle))
  exact hn.trans_lt (hm ⟨hhalf,hle⟩ ⟨hr,le_rfl⟩ (by linarith))

lemma J_strictAnti {z k : ℝ} (hk : 0 < k) :
    StrictAntiOn (fun r => J ((z,k),r)) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun s hs => (J_deriv hs).continuousAt.continuousWithinAt)
  intro s hs
  have hs' : 0 < s := interior_subset hs
  rw [(J_deriv (z := z) (k := k) hs').deriv]
  have h := mul_pos (mul_pos hk hs') (A_gap_pos (q := ((z,k),s)) hs')
  linarith

lemma AH_tendsto (z k : ℝ) :
    Tendsto (fun r => r^2*A ((z,k),r)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hlow : Tendsto (fun r : ℝ => -r^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using! (((tendsto_id.mono_left inf_le_left).pow 2).neg :
      Tendsto (fun r : ℝ => -r^2) (𝓝[>] (0:ℝ)) (𝓝 (-0^2)))
  have hupp : Tendsto (fun r : ℝ => r^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using! ((tendsto_id.mono_left inf_le_left).pow 2 :
      Tendsto (fun r : ℝ => r^2) (𝓝[>] (0:ℝ)) (𝓝 (0^2)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have h := (abs_lt.mp (A_abs_lt (q := ((z,k),r)) hr)).1
    nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ A ((z,k),r)+1 by linarith)]
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have h := (abs_lt.mp (A_abs_lt (q := ((z,k),r)) hr)).2
    nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ 1-A ((z,k),r) by linarith)]

lemma AH_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => s^2*A ((z,k),s)) (r^2*J ((z,k),r)*(1-A ((z,k),r)^2)) r := by
  have hd := ((hasDerivAt_id r).pow 2).mul (A_deriv (z := z) (k := k) hr)
  convert! hd using 1
  dsimp only [Pi.pow_apply,id_eq]
  field_simp
  ring

lemma A_pos_before {z k r : ℝ} (hk : 0 < k) (_hr : 0 < r)
    (hA : 0 ≤ A ((z,k),r)) {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    0 < A ((z,k),s) := by
  have hj := J_strictAnti (z := z) hk
  have hpos (t : ℝ) (ht : 0 < t) (hjt : 0 ≤ J ((z,k),t)) : 0 < A ((z,k),t) := by
    have hm : StrictMonoOn (fun u => u^2*A ((z,k),u)) (Ioc 0 t) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioc 0 t)
        (fun u hu => (AH_deriv hu.1).continuousAt.continuousWithinAt)
      intro u hu
      rw [interior_Ioc] at hu
      rw [(AH_deriv (z := z) (k := k) hu.1).deriv]
      exact mul_pos (mul_pos (sq_pos_of_pos hu.1)
        (hjt.trans_lt (hj hu.1 ht hu.2))) (A_gap_pos hu.1)
    have hmul : 0 < t^2*A ((z,k),t) := strictMono_zero_pos (f := fun u => u^2*A ((z,k),u)) (r := t) ht (AH_tendsto z k) hm
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos ht)).mp hmul
  by_contra! hnon
  have hjs : J ((z,k),s) < 0 := by
    by_contra! h
    exact (hpos s hs h).not_ge hnon
  have hm : StrictAntiOn (fun u => u^2*A ((z,k),u)) (Icc s r) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc s r)
      (fun u hu => (AH_deriv (hs.trans_le hu.1)).continuousAt.continuousWithinAt)
    intro u hu
    have hu' := interior_subset (s := Icc s r) hu
    have hu0 := hs.trans_le hu'.1
    rw [(AH_deriv (z := z) (k := k) hu0).deriv]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (sq_pos_of_pos hu0)
        ((hj.antitoneOn hs hu0 hu'.1).trans_lt hjs)) (A_gap_pos hu0)
  have hh := hm ⟨le_rfl,hsr.le⟩ ⟨hsr.le,le_rfl⟩ hsr
  have hleft := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) hnon
  have hright := mul_nonneg (sq_nonneg r) hA
  linarith

end QuinticLienard.ReferenceCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.HeightLimits
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

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus
lemma HN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω HN q := by
  apply (H_analytic (by norm_num : (0:ℝ)<1)).comp q
  fun_prop
lemma DN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω DN q := by
  unfold DN
  have h1 := HN_analytic q
  have h2 := PN_analytic q
  have h3 := QN_analytic q
  fun_prop
lemma HN_zero (d k : ℝ) : HN ((d,k),0)=0 := by
  simpa [HN] using (zero_data (by norm_num : (0:ℝ)<1)).2
lemma DN_zero (d k : ℝ) : DN ((d,k),0)=0 := by simp [DN,HN_zero]
lemma Hr_DN {d k r : ℝ} (hr : 0 < r) : Hr ((d,k),r)=DN ((d,k),r) := by
  have he := euler_identity (d := d) (k := k) hr
  rw [scaling d k hr,P_scaling d k hr,Q_scaling d k hr] at he
  dsimp [DN,HN,PN,QN]
  apply (mul_left_cancel₀ (ne_of_gt hr))
  nlinarith only [he]
lemma HN_deriv_zero (d k : ℝ) : HasDerivAt (fun r => HN ((d,k),r)) (d/3) 0 := by
  have hm : HasDerivAt (fun s : ℝ => ((d*s,k*s^3),(1:ℝ))) ((d,0),0) 0 := by
    convert! (((hasDerivAt_id (0:ℝ)).const_mul d).prodMk
      (((hasDerivAt_id (0:ℝ)).pow 3).const_mul k)).prodMk (hasDerivAt_const (0:ℝ) (1:ℝ)) using 1
    norm_num [id_eq]
  have hH : HasFDerivAt H (fderiv ℝ H ((0,0),1)) ((d*0,k*0^3),1) := by
    simpa using ((H_analytic (d := 0) (k := 0) (by norm_num : (0:ℝ)<1)).differentiableAt (by simp)).hasFDerivAt
  have hd := hH.comp_hasDerivAt (f := fun s : ℝ => ((d*s,k*s^3),(1:ℝ))) 0 hm
  rw [fderiv_model] at hd
  change HasDerivAt (fun r => HN ((d,k),r))
    (d*P ((0,0),1)+0*Q ((0,0),1)+0*Hr ((0,0),1)) 0 at hd
  simpa [QuadraticVariation.P_zero (by norm_num : (0:ℝ)<1),div_eq_mul_inv] using hd
lemma DN_deriv_zero (d k : ℝ) : HasDerivAt (fun r => DN ((d,k),r)) (2*d/3) 0 := by
  have hd := ((HN_deriv_zero d k).add
    (((hasDerivAt_id (0:ℝ)).const_mul d).mul (PNr_hasDerivAt d k 0))).add
      ((((hasDerivAt_id (0:ℝ)).pow 3).const_mul (3*k)).mul (QNr_hasDerivAt d k 0))
  convert! hd using 1
  dsimp [DN,Pi.pow_apply,id_eq]
  norm_num [PN,QuadraticVariation.P_zero (by norm_num : (0:ℝ)<1)]
  ring
lemma Hr_negative_near_zero {d k : ℝ} (hd : d < 0) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), Hr ((d,k),r) < 0 := by
  have ht := (DN_deriv_zero d k).hasDerivWithinAt (s := Ioi 0)
  have hlim := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp ht
  have hn : (2:ℝ)*d/3 < 0 := by linarith
  filter_upwards [hlim.eventually (eventually_lt_nhds hn),self_mem_nhdsWithin] with r hh hr
  rw [Hr_DN hr]
  have hh' : DN ((d,k),r)/r < 0 := by
    simpa [slope,DN_zero,vsub_eq_sub,div_eq_mul_inv,mul_comm] using hh
  have h := (div_lt_iff₀ hr).mp hh'
  simpa using h
end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CharacteristicLimit
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

namespace QuinticLienard.ReferenceCharacteristic
open QuadraticCoordinates
lemma D_tendsto_zero (z k : ℝ) :
    Tendsto (fun r => D ((z,k),r)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have ht := (DN_analytic ((z,k),0)).continuousAt.tendsto.comp (model_tendsto z k)
  rw [DN_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (Hr_DN hr).symm
end QuinticLienard.ReferenceCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.Schwarzian
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

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ModelEndpoint
open PartialCalculus QuadraticCoordinates RiccatiJets

lemma Hrr_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω Hrr ((d,k),r) :=
  direction_contDiffAt (Hr_analytic hr) _
lemma w_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω w ((d,k),r) := by
  have h1 : 1+Hr ((d,k),r) ≠ 0 := by
    have hh := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).1
    linarith
  exact (contDiffAt_const.mul (Hrr_analytic hr)).div
    (((contDiffAt_const.sub (Hr_analytic hr)).pow 2).mul
      (contDiffAt_const.add (Hr_analytic hr)))
    (mul_ne_zero (pow_ne_zero _ (ne_of_gt (mr_pos hr))) h1)
lemma ell_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => ell ((d,k),s)) (2*Hrr ((d,k),r)/(1-Hr ((d,k),r))^2) r := by
  convert! ((hasDerivAt_const r (1:ℝ)).add (Hrr_hasDerivAt hr)).div
    ((hasDerivAt_const r (1:ℝ)).sub (Hrr_hasDerivAt hr)) (ne_of_gt (mr_pos hr)) using 1
  dsimp
  ring

lemma LowerChart.radius_deriv_eventually {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    ∀ᶠ s in 𝓝 (m ((d,k),r)), 0 < c.radius s ∧
      HasDerivAt c.radius (1/(1-Hr ((d,k),c.radius s))) s := by
  have hp : ∀ᶠ s in 𝓝 (m ((d,k),r)), 0 < c.radius s :=
    continuousAt_const.eventually_lt c.radius_analytic.continuousAt (by rw [c.radius_base]; exact hr)
  filter_upwards [hp,c.radius_analytic.eventually (by simp),c.radius_relation.eventually_nhds] with s hs ha he
  have hd := (ha.differentiableAt (by simp)).hasDerivAt
  have heder := (((hasDerivAt_id (c.radius s)).sub (Hr_hasDerivAt hs)).comp s hd).unique
    ((hasDerivAt_id s).congr_of_eventuallyEq he)
  have heq : deriv c.radius s=1/(1-Hr ((d,k),c.radius s)) := by
    apply (eq_div_iff (ne_of_gt (mr_pos hs))).mpr
    simpa only [mul_comm] using heder
  exact ⟨hs,by simpa only [heq] using hd⟩

lemma LowerChart.upper_deriv_eventually {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    ∀ᶠ s in 𝓝 (m ((d,k),r)), deriv c.upper s=ell ((d,k),c.radius s) := by
  filter_upwards [c.radius_deriv_eventually hr] with s hs
  have hd := ((hasDerivAt_id (c.radius s)).add (Hr_hasDerivAt (d := d) (k := k) hs.1)).comp s hs.2
  have hd' : HasDerivAt c.upper (ell ((d,k),c.radius s)) s := by
    convert! hd.congr_of_eventuallyEq (Eventually.of_forall c.upper_def) using 1
    dsimp [ell]
    ring
  exact hd'.deriv

lemma LowerChart.second_deriv_eventually {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    ∀ᶠ s in 𝓝 (m ((d,k),r)), deriv (deriv c.upper) s=
      2*Hrr ((d,k),c.radius s)/(1-Hr ((d,k),c.radius s))^3 := by
  filter_upwards [c.radius_deriv_eventually hr,(c.upper_deriv_eventually hr).eventually_nhds] with s hs he
  have hd := ((ell_deriv hs.1).comp s hs.2).congr_of_eventuallyEq he
  rw [hd.deriv]
  field_simp

lemma LowerChart.log_deriv_eventually {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    ∀ᶠ s in 𝓝 (m ((d,k),r)), deriv (deriv c.upper) s/deriv c.upper s=w ((d,k),c.radius s) := by
  filter_upwards [c.radius_deriv_eventually hr,c.upper_deriv_eventually hr,c.second_deriv_eventually hr] with s hs h1 h2
  rw [h1,h2]
  have hn := ne_of_gt (mr_pos (d := d) (k := k) hs.1)
  dsimp [w,ell]
  field_simp

lemma LowerChart.log_deriv {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    deriv (deriv c.upper) (m ((d,k),r))/ell ((d,k),r)=w ((d,k),r) := by
  have hh := (c.log_deriv_eventually hr).self_of_nhds
  rwa [c.upper_derivative.deriv,c.radius_base] at hh

lemma LowerChart.schwarzian {d k r : ℝ} (hr : 0 < r) (c : LowerChart d k r) :
    schwarzian c.upper (m ((d,k),r))=sch ((d,k),r) := (c.formulas hr).1

lemma log_deriv_hasDerivAt {Y : ℝ → ℝ} {s : ℝ} (hY : ContDiffAt ℝ ω Y s) (hl : deriv Y s ≠ 0) :
    HasDerivAt (fun t => deriv (deriv Y) t/deriv Y t)
      (schwarzian Y s+(1/2)*(deriv (deriv Y) s/deriv Y s)^2) s := by
  have hd := ((deriv_analytic (deriv_analytic hY)).differentiableAt (by simp)).hasDerivAt.div
    ((deriv_analytic hY).differentiableAt (by simp)).hasDerivAt hl
  convert! hd using 1
  dsimp [schwarzian]
  field_simp
  ring

lemma w_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => w ((d,k),s))
      ((1-Hr ((d,k),r))*(sch ((d,k),r)+(1/2)*(w ((d,k),r))^2)) r := by
  obtain ⟨c⟩ := lower_chart (d := d) (k := k) hr
  have hd := slice_r (q := ((d,k),r)) ((w_analytic hr).differentiableAt (by simp))
  have hdρ := c.radius_derivative
  have hd0 : HasDerivAt (fun s => w ((d,k),s)) (direction ((0,0),1) w ((d,k),r)) (c.radius (m ((d,k),r))) := by
    rw [c.radius_base]; exact hd
  have hc := hd0.comp (m ((d,k),r)) hdρ
  have hwρ : HasDerivAt (fun s => w ((d,k),c.radius s))
      (direction ((0,0),1) w ((d,k),r)*(1/(1-Hr ((d,k),r)))) (m ((d,k),r)) := by
    simpa only [c.radius_base] using! hc
  have hl := ne_of_gt (ell_pos (d := d) (k := k) hr)
  have hYl : deriv c.upper (m ((d,k),r)) ≠ 0 := by rwa [c.upper_derivative.deriv]
  have he := hwρ.unique ((log_deriv_hasDerivAt c.upper_analytic hYl).congr_of_eventuallyEq
    (Filter.EventuallyEq.symm (c.log_deriv_eventually hr)))
  rw [c.schwarzian hr,c.upper_derivative.deriv,c.log_deriv hr] at he
  have hfinal : direction ((0,0),1) w ((d,k),r)=
      (1-Hr ((d,k),r))*(sch ((d,k),r)+(1/2)*(w ((d,k),r))^2) := by
    have hn := ne_of_gt (mr_pos (d := d) (k := k) hr)
    field_simp at he
    nlinarith only [he]
  simpa only [hfinal] using hd

end QuinticLienard.ModelEndpoint

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CharacteristicPositive
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

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ReferenceCharacteristic
lemma D_pos_of_A_nonneg {z k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hA : 0 ≤ A ((z,k),r)) : 0 < D ((z,k),r) := by
  apply strictMono_zero_pos hr (D_tendsto_zero z k)
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 r)
    (fun s hs => (D_deriv hs.1).continuousAt.continuousWithinAt)
  intro s hs
  rw [interior_Ioc] at hs
  rw [(D_deriv (z := z) (k := k) hs.1).deriv]
  exact div_pos (mul_pos (mul_pos (by norm_num) (A_pos_before hk hr hA hs.1 hs.2))
    (D_gap_pos hs.1)) (mul_pos hs.1 (A_gap_pos hs.1))
end QuinticLienard.ReferenceCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.HeightSigns
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

namespace QuinticLienard.ModelEndpoint
open PartialCalculus QuadraticCoordinates
lemma d_neg_of_H_neg {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hH : H ((d,k),r) < 0) : d < 0 := by
  have hmd : StrictMono (fun d => H ((d,k),r)) := by
    apply strictMono_of_deriv_pos
    intro a; rw [(P_hasDerivAt hr).deriv]; exact QuadraticVariation.P_pos hr
  have hmk : StrictMono (fun k => H ((0,k),r)) := by
    apply strictMono_of_deriv_pos
    intro a; rw [(Q_hasDerivAt hr).deriv]; exact QuadraticVariation.Q_pos hr
  have hH0 : 0 < H ((0,k),r) := by
    have hh := hmk hk
    simpa only [(zero_data hr).2] using hh
  by_contra! hd
  have hh := hmd.monotone hd
  exact hH.not_ge (hH0.le.trans hh)

lemma Hr_pos_of_H_nonneg {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hH : 0 ≤ H ((d,k),r)) : 0 < Hr ((d,k),r) := by
  obtain ⟨z,hz⟩ := ReferenceCharacteristic.J_surjective d k hr
  have hA : 0 ≤ ReferenceCharacteristic.A ((z,k),r) := by
    dsimp [ReferenceCharacteristic.A]
    rw [hz]
    exact div_nonneg hH hr.le
  simpa only [ReferenceCharacteristic.D,hz] using ReferenceCharacteristic.D_pos_of_A_nonneg hk hr hA

lemma w_pos_of_H_nonneg {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hH : 0 ≤ H ((d,k),r)) : 0 < w ((d,k),r) := by
  have ha : 0 < alpha ((d,k),r) := div_pos hr (H_gap_pos hr)
  have ht := transport_Hr (d := d) (k := k) hr
  have hgap : 0 < 1-(Hr ((d,k),r))^2 := by
    have hh := abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)
    nlinarith [sq_nonneg (Hr ((d,k),r))]
  have hnon : -2*H ((d,k),r)*r*(1-(Hr ((d,k),r))^2)/(gap ((d,k),r))^2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hH) hr.le) hgap.le)
      (sq_nonneg _)
  have hpr := mul_pos hk (R_pos (d := d) (k := k) hr)
  have hHrr : 0 < Hrr ((d,k),r) :=
    pos_of_mul_pos_right (by linarith : 0 < alpha ((d,k),r)*Hrr ((d,k),r)) ha.le
  have hplus : 0 < 1+Hr ((d,k),r) := by
    have hh := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).1
    linarith
  exact div_pos (mul_pos (by norm_num) hHrr) (mul_pos (sq_pos_of_pos (mr_pos hr)) hplus)

lemma sch_pos_of_H_neg_Hr_nonneg {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hH : H ((d,k),r) < 0) (hHr : 0 ≤ Hr ((d,k),r)) : 0 < sch ((d,k),r) := by
  have hd := d_neg_of_H_neg hk hr hH
  have hm := m_pos (d := d) (k := k) hr
  have hn := n_pos (d := d) (k := k) hr
  have hmn : n ((d,k),r) < m ((d,k),r) := by dsimp [m,n]; linarith
  have hl : 1 ≤ ell ((d,k),r) := by
    apply (le_div_iff₀ (mr_pos hr)).mpr
    linarith
  have hl2 : 1 ≤ (ell ((d,k),r))^2 := by nlinarith
  have hbase : 0 ≤ (ell ((d,k),r))^2/(n ((d,k),r))^2-1/(m ((d,k),r))^2 := by
    have hsq : (n ((d,k),r))^2 ≤ (m ((d,k),r))^2 := sq_le_sq₀ hn.le hm.le |>.mpr hmn.le
    have hh : (1:ℝ)/(m ((d,k),r))^2 ≤ (ell ((d,k),r))^2/(n ((d,k),r))^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hm) (sq_pos_of_pos hn)).mpr
      nlinarith [mul_nonneg (sq_nonneg (m ((d,k),r))) (sub_nonneg.mpr hl2)]
    linarith
  have hkn : 0 < k*(m ((d,k),r)+n ((d,k),r)*(ell ((d,k),r))^2) := by positivity
  have hd2 : 0 ≤ d^2/2*((ell ((d,k),r))^2-1) := mul_nonneg (by positivity) (by linarith)
  have hdp : 0 ≤ -d*(1/m ((d,k),r)+(ell ((d,k),r))^2/n ((d,k),r)) := mul_nonneg (neg_nonneg.mpr hd.le) (by positivity)
  dsimp only [sch,Prod.fst] at *
  nlinarith

lemma w_nonneg_of_H_neg_Hr_nonneg {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hH : H ((d,k),r) < 0) (hHr : 0 ≤ Hr ((d,k),r)) : 0 ≤ w ((d,k),r) := by
  have hd := d_neg_of_H_neg hk hr hH
  obtain ⟨a,ha0,har,ha⟩ : ∃ a : ℝ, 0 < a ∧ a < r ∧ Hr ((d,k),a) < 0 := by
    have he : ∀ᶠ a in 𝓝[>] (0:ℝ), 0 < a ∧ a < r ∧ Hr ((d,k),a) < 0 := by
      filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hr).filter_mono inf_le_left,
        Hr_negative_near_zero (k := k) hd] with a ha0 har ha
      exact ⟨ha0,har,ha⟩
    exact he.exists
  let C : ℝ → ℝ := fun s => (1-Hr ((d,k),s))^2*(1+Hr ((d,k),s))/2
  have hC (s : ℝ) (hs : 0 < s) : 0 < C s := by
    have hm := mr_pos (d := d) (k := k) hs
    have hp : 0 < 1+Hr ((d,k),s) := by
      have ht := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hs)).1
      linarith
    dsimp [C]; positivity
  apply RegionBarrier.no_negative_w har
    (fun s hs => Hr_hasDerivAt (ha0.trans_le hs.1))
    (C := C) (w' := fun s => (1-Hr ((d,k),s))*(sch ((d,k),s)+(1/2)*(w ((d,k),s))^2))
    _ (fun s hs => w_deriv (ha0.trans_le hs.1)) (fun s hs => hC s (ha0.trans_le hs.1)) _ ha hH hHr
  · intro s hs
    convert! Hrr_hasDerivAt (d := d) (k := k) (ha0.trans_le hs.1) using 1
    dsimp [C,w]
    have hm := mr_pos (d := d) (k := k) (ha0.trans_le hs.1)
    have hp : 0 < 1+Hr ((d,k),s) := by
      have ht := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) (ha0.trans_le hs.1))).1
      linarith
    field_simp [ne_of_gt hm,ne_of_gt hp]
  · intro s hs hHs hHrs
    have hsch := sch_pos_of_H_neg_Hr_nonneg hk (ha0.trans_le hs.1) hHs hHrs
    exact mul_pos (mr_pos (ha0.trans_le hs.1)) (by nlinarith [sq_nonneg (w ((d,k),s))])
end QuinticLienard.ModelEndpoint

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ModelAlgebra
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

namespace QuinticLienard.ModelAlgebra

lemma A_pos {z l : ℝ} (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) : 0 < A z l := by
  have hz1 : 0 < z - 1 := by linarith
  have hA : A z l = (1-l)*(3*(z-1)+1) +
      l * (z-1) * (2*(z-1)^2+3*(z-1)+3) := by unfold A; ring
  rw [hA]
  positivity

lemma J_pos {z l : ℝ} (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) : 0 < J z l := by
  have hz1 : 0 < z - 1 := by linarith
  have hz2 : 0 < z + 1 := by linarith
  have hJ : J z l = (1-l)*((z-1)^2+4*(z-1)+1) +
      l * (2*(z-1)*(z+1)*((z-1)^2+(z-1)+1)) := by unfold J; ring
  rw [hJ]
  positivity

lemma wStar_normalized (z l : ℝ) :
    wStar z 1 l = 2*(l*z^3*(z-2)+2*z-1) / (z^2*(z+1)) := by
  unfold wStar
  congr 1 <;> ring

lemma wStar_pos {z l : ℝ} (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) :
    0 < wStar z 1 l := by
  have hz0 : 0 < z := by linarith
  have hz1 : 0 < z - 1 := by linarith
  have hz2 : 0 < z + 1 := by linarith
  rw [wStar_normalized]
  have heq : l*z^3*(z-2)+2*z-1 =
      (1-l)*(2*(z-1)+1)+l*(z-1)^3*(z+1) := by ring
  rw [heq]
  positivity

lemma baseline {z l : ℝ} (hz : 0 < z) :
    dStar z 1 l (wStar z 1 l) (S₀ z l) =
      (z-1)/(2*z^4) * A z l * T z l := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z + 1 ≠ 0 := by positivity
  unfold dStar S₀ A T
  rw [wStar_normalized]
  field_simp
  ring

lemma delta_factor {z l : ℝ} (hz : 0 < z) :
    1/z-l-wStar z 1 l = -(z-1)/((z+1)*z^2) * T z l := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z + 1 ≠ 0 := by positivity
  rw [wStar_normalized]
  unfold T
  field_simp
  ring

lemma derivative_at_wStar {z l : ℝ} (hz : 0 < z) :
    (1-2/z+l*(2*z-1)) + (z+1)*wStar z 1 l = J z l / z^2 := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z + 1 ≠ 0 := by positivity
  rw [wStar_normalized]
  unfold J
  field_simp
  ring

lemma dStar_mono_from_wStar {z l w S : ℝ}
    (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) (hw : wStar z 1 l ≤ w) :
    dStar z 1 l (wStar z 1 l) S ≤ dStar z 1 l w S := by
  have hz0 : 0 < z := by linarith
  have hz1 : 0 < z + 1 := by linarith
  have hp : 0 < 1-2/z+l*(2*z-1)+(z+1)*wStar z 1 l := by
    rw [derivative_at_wStar hz0]
    exact div_pos (J_pos hz hl hl1) (sq_pos_of_pos hz0)
  have heq : dStar z 1 l w S - dStar z 1 l (wStar z 1 l) S =
      (w-wStar z 1 l) * ((1-2/z+l*(2*z-1)+(z+1)*wStar z 1 l) +
        (z+1)/2*(w-wStar z 1 l)) := by unfold dStar; ring
  have hw0 : 0 ≤ w-wStar z 1 l := sub_nonneg.mpr hw
  have : 0 ≤ dStar z 1 l w S - dStar z 1 l (wStar z 1 l) S := by
    rw [heq]
    positivity
  linarith

lemma schwarzian_improvement (z l b d : ℝ) :
    schwarzian z 1 l b d - S₀ z l =
      (2*b*z-d^2/2)+l^2*(2*b+d^2/2-d)-d/z := by
  unfold schwarzian S₀
  simp only [div_one, one_pow, one_div]
  ring

lemma schwarzian_last (z l b d : ℝ) :
    schwarzian z 1 l b d =
      (2*b*z-d^2/2)+l^2*(2*b+d^2/2-d+3/2)-d/z-3/(2*z^2) := by
  unfold schwarzian
  simp only [div_one, one_pow]
  ring

lemma riccati_consequence {z l b d w : ℝ}
    (hl : 0 < l) (hd : d < 0) (hw : wStar z 1 l ≤ w)
    (hR : w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z)) :
    2*Real.sqrt (d^2/4-b*z) < 1/z-l-wStar z 1 l := by
  have hdl : d*l < 0 := mul_neg_of_neg_of_pos hd hl
  linarith

lemma last_case_nonneg_T {z l b d w : ℝ}
    (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) (hb : 0 < b) (hd : d < 0)
    (hw : wStar z 1 l ≤ w) (hT : 0 ≤ T z l)
    (hRic : 4*b*z ≤ d^2 →
      w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z)) :
    0 < dStar z 1 l w (schwarzian z 1 l b d) := by
  have hz0 : 0 < z := by linarith
  have hz1 : 0 < z - 1 := by linarith
  have hdelta : 1/z-l-wStar z 1 l ≤ 0 := by
    rw [delta_factor hz0]
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    · exact hT
  have hd2 : d^2 < 4*b*z := by
    by_contra! h
    have hstrict := riccati_consequence hl hd hw (hRic h)
    have hs := Real.sqrt_nonneg (d^2/4-b*z)
    linarith
  have hbase : 0 ≤ dStar z 1 l (wStar z 1 l) (S₀ z l) := by
    rw [baseline hz0]
    exact mul_nonneg (mul_nonneg (by positivity) (A_pos hz hl hl1).le) hT
  have hS : 0 < schwarzian z 1 l b d - S₀ z l := by
    rw [schwarzian_improvement]
    have ht1 : 0 < 2*b*z-d^2/2 := by linarith
    have ht2 : 0 ≤ l^2*(2*b+d^2/2-d) := by
      apply mul_nonneg (sq_nonneg _)
      nlinarith only [sq_nonneg d, hb, hd]
    have ht3 : 0 < -(d/z) := by
      simpa only [neg_div] using div_pos (neg_pos.mpr hd) hz0
    linarith
  have heq : dStar z 1 l (wStar z 1 l) (schwarzian z 1 l b d) =
      dStar z 1 l (wStar z 1 l) (S₀ z l) +
        (z-1)*(schwarzian z 1 l b d - S₀ z l) := by unfold dStar; ring
  have hpos : 0 < dStar z 1 l (wStar z 1 l) (schwarzian z 1 l b d) := by
    rw [heq]
    exact add_pos_of_nonneg_of_pos hbase (mul_pos hz1 hS)
  exact hpos.trans_le (dStar_mono_from_wStar hz hl hl1 hw)

lemma negative_T_estimates {z l : ℝ} (hz : 1 < z) (hl : 0 < l)
    (hT : T z l < 0) : 2 < z ∧ 2+3*l < z := by
  have hz0 : 0 < z := by linarith
  have hzpow : 0 < z^2 := sq_pos_of_pos hz0
  have ht : 0 < l*z^2*(2*z-1) := mul_pos (mul_pos hl hzpow) (by linarith)
  have hTwo : 2 < z := by unfold T at hT; nlinarith only [hT, ht]
  have hSquare : 4 < z^2 := by nlinarith only [hTwo]
  have hrest : 0 < z^2*(2*z-1)-3 := by
    have : 0 < z^2*(2*z-4) := mul_pos hzpow (by linarith)
    nlinarith only [this, hSquare]
  have hprod : 0 < l * (z^2*(2*z-1)-3) := mul_pos hl hrest
  exact ⟨hTwo, by unfold T at hT; nlinarith only [hT, hprod]⟩

lemma slope_estimate {z l d : ℝ} (hz : 0 < z) (hl : 0 < l)
    (hzl : 2 + 3*l < z) (hX : d < (l/z-1)/(1+l)) : 2 < -d*z := by
  have hl1 : 0 < 1+l := by linarith
  have h1 : d*(1+l) < l/z-1 := (lt_div_iff₀ hl1).mp hX
  have h2 := mul_lt_mul_of_pos_right h1 hz
  have heq : (l/z-1)*z = l-z := by field_simp
  rw [heq] at h2
  have hh : (2+d*z)*(1+l) < 0 := by nlinarith only [h2, hzl]
  have hneg : 2+d*z < 0 := by
    by_contra hn
    have hnonneg := mul_nonneg (le_of_not_gt hn) hl1.le
    linarith only [hnonneg, hh]
  linarith

lemma last_case_neg_T {z l b d w : ℝ}
    (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) (hb : 0 < b) (hd : d < 0)
    (hw : wStar z 1 l ≤ w) (hT : T z l < 0)
    (hX : d < (l/z-1)/(1+l))
    (hRic : 4*b*z ≤ d^2 →
      w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z)) :
    0 < dStar z 1 l w (schwarzian z 1 l b d) := by
  have hz0 : 0 < z := by linarith
  have hzsq : 0 < z^2 := sq_pos_of_pos hz0
  obtain ⟨hz2, hzl⟩ := negative_T_estimates hz hl hT
  have hdz : 2 < -d*z := slope_estimate hz0 hl hzl hX
  have hddiv : 2/z^2 < -d/z := by
    have heq : -d/z = (-d*z)/z^2 := by field_simp
    rw [heq]
    exact div_lt_div_of_pos_right hdz hzsq
  have hfirst : -(1/(2*z^2)) < 2*b*z-d^2/2 := by
    by_cases hnonneg : 0 ≤ 2*b*z-d^2/2
    · have : 0 < 1/(2*z^2) := by positivity
      linarith
    · have hlarge : 4*b*z ≤ d^2 := by linarith
      have hrad : 0 ≤ d^2/4-b*z := by linarith
      have hroot := Real.sq_sqrt hrad
      have hroot0 := Real.sqrt_nonneg (d^2/4-b*z)
      have hstrict := riccati_consequence hl hd hw (hRic hlarge)
      have hws := wStar_pos hz hl hl1
      have hupper : 2*Real.sqrt (d^2/4-b*z) < 1/z := by linarith
      have hrecip : 0 < 1/z := by positivity
      have hsquare : 4*(Real.sqrt (d^2/4-b*z))^2 < (1/z)^2 := by
        nlinarith only [sq_nonneg (2*Real.sqrt (d^2/4-b*z)-1/z),
          mul_pos (by linarith : 0 < 1/z-2*Real.sqrt (d^2/4-b*z))
            (by linarith : 0 < 1/z+2*Real.sqrt (d^2/4-b*z))]
      have heq : (1/z)^2 = 1/z^2 := by ring
      rw [heq] at hsquare
      have heq2 : 1/(2*z^2) = (1/z^2)/2 := by ring
      rw [heq2]
      nlinarith only [hsquare, hroot]
  have hS : 0 < schwarzian z 1 l b d := by
    rw [schwarzian_last]
    have hterm : 0 ≤ l^2*(2*b+d^2/2-d+3/2) := by
      apply mul_nonneg (sq_nonneg _)
      nlinarith only [sq_nonneg d, hb, hd]
    have heq : 3/(2*z^2) = -(1/(2*z^2))+2/z^2 := by ring
    rw [heq]
    simp only [neg_div] at hddiv
    linarith
  have hwpos : 0 < w := (wStar_pos hz hl hl1).trans_le hw
  have hcoeff : 0 < 1-2/z+l*(2*z-1) := by
    have hdiv : 2/z < 1 := (div_lt_one hz0).mpr hz2
    have : 0 < l*(2*z-1) := mul_pos hl (by linarith)
    linarith
  unfold dStar
  simp only [mul_one, div_one]
  have : 0 < z-1 := by linarith
  positivity

lemma last_case {z l b d w : ℝ}
    (hz : 1 < z) (hl : 0 < l) (hl1 : l < 1) (hb : 0 < b) (hd : d < 0)
    (hw : wStar z 1 l ≤ w)
    (hX : d < (l/z-1)/(1+l))
    (hRic : 4*b*z ≤ d^2 →
      w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z)) :
    0 < dStar z 1 l w (schwarzian z 1 l b d) := by
  rcases le_or_gt 0 (T z l) with hT | hT
  · exact last_case_nonneg_T hz hl hl1 hb hd hw hT hRic
  · exact last_case_neg_T hz hl hl1 hb hd hw hT hX hRic

lemma wStar_neg {z l : ℝ} (hz : 0 < z) (hz1 : z < 1) (hl : 1 ≤ l) :
    wStar z 1 l < 0 := by
  rw [wStar_normalized]
  have ht : z^3*(z-2) < 0 := mul_neg_of_pos_of_neg (pow_pos hz _) (by linarith)
  have hb : l*z^3*(z-2) ≤ z^3*(z-2) := by
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) ht.le]
  have heq : z^3*(z-2)+2*z-1 = (z-1)^3*(z+1) := by ring
  have hbase : z^3*(z-2)+2*z-1 < 0 := by
    rw [heq]
    exact mul_neg_of_neg_of_pos ((show Odd (3 : ℕ) by decide).pow_neg (by linarith)) (by positivity)
  apply div_neg_of_neg_of_pos _ (by positivity)
  linarith

lemma equal_endpoints_pos {l w S : ℝ} (hl : 1 < l) (hw : 0 < w) :
    0 < dStar 1 1 l w S := by
  have heq : dStar 1 1 l w S = (l-1)*w+w^2 := by unfold dStar; ring
  rw [heq]
  exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hw) (sq_nonneg _)

lemma schwarzian_pos_of_one_le {z l b d : ℝ}
    (hz : 1 < z) (hl : 1 ≤ l) (hb : 0 < b) (hd : d < 0) :
    0 < schwarzian z 1 l b d := by
  have hz0 : 0 < z := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hl2 : 1 ≤ l^2 := by nlinarith
  have hz2 : 1 < z^2 := by nlinarith
  have hiz : 1/z^2 < 1 := (div_lt_one (sq_pos_of_pos hz0)).mpr hz2
  have hi : 0 < 1/z+l^2 := add_pos_of_pos_of_nonneg (one_div_pos.mpr hz0) (sq_nonneg _)
  have h1 : 0 < 2*b*(z+l^2) := mul_pos (by positivity) (by positivity)
  have h2 : 0 ≤ d^2/2*(l^2-1) := mul_nonneg (by positivity) (by linarith)
  have h3 : 0 < -d*(1/z+l^2) := mul_pos (neg_pos.mpr hd) hi
  have h4 : 0 < (3:ℝ)/2*(l^2-1/z^2) := mul_pos (by norm_num) (by linarith)
  unfold schwarzian
  simp only [one_pow, div_one]
  linarith

lemma second_case {z l b d w : ℝ}
    (hz : 1 < z) (hl : 1 ≤ l) (hb : 0 < b) (hd : d < 0) (hw : 0 ≤ w) :
    0 < dStar z 1 l w (schwarzian z 1 l b d) := by
  have hz0 : 0 < z := by linarith
  have hlow : l*(2*z-1) ≥ 2*z-1 := by
    have := mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ 2*z-1 by linarith)
    nlinarith only [this]
  have hi : 2/z < 2 := (div_lt_iff₀ hz0).mpr (by linarith)
  have hcoeff : 0 < 1-2/z+l*(2*z-1) := by linarith
  have hS := schwarzian_pos_of_one_le hz hl hb hd
  unfold dStar
  simp only [div_one, mul_one]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos (by linarith) hS) (mul_nonneg hcoeff.le hw))
    (mul_nonneg (by positivity) (sq_nonneg _))

end QuinticLienard.ModelAlgebra

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.EndpointAlgebra
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

namespace QuinticLienard.EndpointAlgebra
open ModelAlgebra

lemma determinant {m n l w s : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    X1 m n l w*Z2 m n l w s-Z1 m n l w*X2 m n l w s =
      l^2*(m+n)^2/(m^2*n^2*(1+l)^3)*dStar m n l w s := by
  dsimp [X1,X2,Z1,Z2,dStar]
  field_simp
  ring

lemma gamma_identity {m n l w s : ℝ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hl : 1+l ≠ 0) (hmn : m+n ≠ 0) :
    (m-n)*(gamma2 m n l w s*X1 m n l w-gamma1 m n l w*X2 m n l w s)-
      l*(m+n)^2/((1+l)*m^2*n^2)*(wStar m n l-w)*X1 m n l w =
      l^2*(m+n)^2*(m^2+n^2)/((1+l)^3*m^4*n^4)*dStar m n l w s := by
  dsimp [gamma2,gamma1,N0,N1,N2,X1,X2,Z1,Z2,wStar,dStar]
  field_simp
  ring

lemma gamma_factor {m n l w s : ℝ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hl : 1+l ≠ 0) (hmn : m+n ≠ 0) (hneq : m ≠ n)
    (hx : X1 m n l w ≠ 0) (hd : dStar m n l w s=0) :
    gamma2 m n l w s-X2 m n l w s/X1 m n l w*gamma1 m n l w =
      l*(m+n)^2/((1+l)*m^2*n^2)*(wStar m n l-w)/(m-n) := by
  have hh := gamma_identity (w := w) (s := s) hm hn hl hmn
  rw [hd,mul_zero] at hh
  have hdiff : m-n ≠ 0 := sub_ne_zero.mpr hneq
  apply (eq_div_iff hdiff).mpr
  field_simp [hx] at *
  nlinarith only [hh]

end QuinticLienard.EndpointAlgebra

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RealAnalysis
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

open Set Filter
open scoped Topology

namespace QuinticLienard.RealAnalysis

lemma deriv_nonpos_of_left_min {f : ℝ → ℝ} {a c v : ℝ} (hac : a < c)
    (hd : HasDerivAt f v c) (hmin : ∀ x ∈ Icc a c, f c ≤ f x) : v ≤ 0 := by
  have ht : Tendsto (slope f c) (𝓝[<] c) (𝓝 v) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono c (by intro x hx; exact ne_of_lt hx))
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsLT hac] with x hx
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr (hmin x (Ioo_subset_Icc_self hx))) (sub_nonpos.mpr hx.2.le)

lemma positive_of_deriv_pos_at_zero {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (ha : 0 ≤ f a) (hzero : ∀ x ∈ Icc a b, f x = 0 → 0 < f' x) : 0 < f b := by
  have hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x := by
    apply image_le_of_deriv_right_lt_deriv_boundary' continuousOn_const
      (fun x _ ↦ (hasDerivAt_const x (0:ℝ)).hasDerivWithinAt) ha hf
      (fun x hx ↦ (hf' x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    intro x hx heq
    exact hzero x (Ico_subset_Icc_self hx) heq.symm
  have hn := hnonneg b ⟨hab.le, le_rfl⟩
  by_contra! hh
  have hb0 : f b = 0 := le_antisymm hh hn
  have hd := deriv_nonpos_of_left_min hab (hf' b ⟨hab.le, le_rfl⟩)
    (fun x hx ↦ hb0 ▸ hnonneg x hx)
  exact (not_lt_of_ge hd) (hzero b ⟨hab.le, le_rfl⟩ hb0)

end QuinticLienard.RealAnalysis

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.EndpointScaling
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
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.EndpointAlgebra

lemma X_reparam {M N L : ℝ → ℝ} {x m n l w a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => X (M t) (N t) (L t)) (X1 m n l w*a) x := by
  have hm' : M x ≠ 0 := by rwa [hMv]
  have hn' : N x ≠ 0 := by rwa [hNv]
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hd := ((hL.div hM hm').sub ((hasDerivAt_const x (1:ℝ)).div hN hn')).div
    (hL.const_add 1) hl'
  convert! hd using 1
  simp only [Pi.div_apply,Pi.sub_apply,hMv,hNv,hLv]
  dsimp [X1,Z1]
  field_simp
  ring

lemma Z_reparam {M N L : ℝ → ℝ} {x m n l w a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => Z (M t) (N t) (L t)) (Z1 m n l w*a) x := by
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hd := ((hL.mul hM).sub hN).div (hL.const_add 1) hl'
  convert! hd using 1
  simp only [Pi.sub_apply,Pi.mul_apply,hMv,hNv,hLv]
  dsimp [Z1]
  field_simp
  ring

lemma N0_reparam {M N L : ℝ → ℝ} {x m n l w a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hm : m ≠ 0) (hn : n ≠ 0) :
    HasDerivAt (fun t => N0 (M t) (N t) (L t)) (N1 m n l w*a) x := by
  have hm' : M x ≠ 0 := by rwa [hMv]
  have hn' : N x ≠ 0 := by rwa [hNv]
  have hd := (hL.div (hM.pow 2) (pow_ne_zero _ hm')).add
    ((hasDerivAt_const x (1:ℝ)).div (hN.pow 2) (pow_ne_zero _ hn'))
  convert! hd using 1
  simp only [Pi.pow_apply,hMv,hNv,hLv]
  dsimp [N1]
  field_simp
  ring

lemma gamma_reparam {M N L : ℝ → ℝ} {x m n l w a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => gamma (M t) (N t) (L t)) (gamma1 m n l w*a) x := by
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hd := (N0_reparam hM hN hL hMv hNv hLv hm hn).div (hL.const_add 1) hl'
  convert! hd using 1
  simp only [hMv,hNv,hLv]
  dsimp [gamma1]
  field_simp

lemma Z1_reparam {M N L W : ℝ → ℝ} {x m n l w s a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hW : HasDerivAt W ((s+(1/2)*w^2)*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hWv : W x=w) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => Z1 (M t) (N t) (L t) (W t)) (Z2 m n l w s*a) x := by
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hd := (((hL.mul hW).mul (hM.add hN)).div
    ((hL.const_add 1).pow 2) (pow_ne_zero _ hl'))
  convert! hd using 1
  simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply,hMv,hNv,hLv,hWv]
  dsimp [Z2]
  field_simp
  ring

lemma X1_reparam {M N L W : ℝ → ℝ} {x m n l w s a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hW : HasDerivAt W ((s+(1/2)*w^2)*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hWv : W x=w)
    (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => X1 (M t) (N t) (L t) (W t)) (X2 m n l w s*a) x := by
  have hm' : M x ≠ 0 := by rwa [hMv]
  have hn' : N x ≠ 0 := by rwa [hNv]
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hB := ((hasDerivAt_const x (1:ℝ)).div (hN.pow 2) (pow_ne_zero _ hn')).sub
    ((hasDerivAt_const x (1:ℝ)).div (hM.pow 2) (pow_ne_zero _ hm'))
  have hd := ((hL.mul hB).div (hL.const_add 1) hl').add
    ((Z1_reparam hM hN hL hW hMv hNv hLv hWv hl).div (hM.mul hN) (mul_ne_zero hm' hn'))
  convert! hd using 1
  simp only [Pi.div_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,hMv,hNv,hLv,hWv]
  dsimp [X2]
  field_simp
  ring

lemma N1_reparam {M N L W : ℝ → ℝ} {x m n l w s a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hW : HasDerivAt W ((s+(1/2)*w^2)*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hWv : W x=w) (hm : m ≠ 0) (hn : n ≠ 0) :
    HasDerivAt (fun t => N1 (M t) (N t) (L t) (W t)) (N2 m n l w s*a) x := by
  have hm' : M x ≠ 0 := by rwa [hMv]
  have hn' : N x ≠ 0 := by rwa [hNv]
  have hd := (((hL.mul hW).div (hM.pow 2) (pow_ne_zero _ hm')).sub
    ((hL.const_mul 2).div (hM.pow 3) (pow_ne_zero _ hm'))).sub
      ((hL.const_mul 2).div (hN.pow 3) (pow_ne_zero _ hn'))
  convert! hd using 1
  simp only [Pi.mul_apply,Pi.pow_apply,hMv,hNv,hLv,hWv]
  dsimp [N2]
  field_simp
  ring

lemma gamma1_reparam {M N L W : ℝ → ℝ} {x m n l w s a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hW : HasDerivAt W ((s+(1/2)*w^2)*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hWv : W x=w)
    (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => gamma1 (M t) (N t) (L t) (W t)) (gamma2 m n l w s*a) x := by
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hd := ((N1_reparam hM hN hL hW hMv hNv hLv hWv hm hn).div (hL.const_add 1) hl').sub
    ((((N0_reparam hM hN hL hMv hNv hLv hm hn).mul hL).mul hW).div
      ((hL.const_add 1).pow 2) (pow_ne_zero _ hl'))
  convert! hd using 1
  simp only [Pi.mul_apply,Pi.pow_apply,hMv,hNv,hLv,hWv]
  dsimp [gamma2]
  field_simp
  ring
end QuinticLienard.EndpointAlgebra

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.EndpointJets
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

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ModelEndpoint
open PartialCalculus QuadraticCoordinates

lemma endpoint_identities {d k r : ℝ} (hr : 0 < r) :
    EndpointAlgebra.X (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))=k*P ((d,k),r)+d ∧
    EndpointAlgebra.Z (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))=d*P ((d,k),r)+3*k*Q ((d,k),r) ∧
    EndpointAlgebra.gamma (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))=QuadraticCoordinates.gamma ((d,k),r) := by
  have hm := ne_of_gt (m_pos (d := d) (k := k) hr)
  have hn := ne_of_gt (n_pos (d := d) (k := k) hr)
  have hv := ne_of_gt (mr_pos (d := d) (k := k) hr)
  have hg := ne_of_gt (H_gap_pos (d := d) (k := k) hr)
  dsimp only [m,n] at hm hn
  constructor
  · rw [width_identity hr]
    dsimp [EndpointAlgebra.X,m,n,ell,gap]
    field_simp
    ring
  constructor
  · rw [← euler_identity hr]
    dsimp [EndpointAlgebra.Z,m,n,ell]
    field_simp
    ring
  · dsimp [EndpointAlgebra.gamma,QuadraticCoordinates.gamma,m,n,ell,gap]
    field_simp
    ring

lemma m_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => m ((d,k),s)) (1-Hr ((d,k),r)) r :=
  (hasDerivAt_id r).sub (Hr_hasDerivAt hr)
lemma n_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => n ((d,k),s)) (ell ((d,k),r)*(1-Hr ((d,k),r))) r := by
  convert! (hasDerivAt_id r).add (Hr_hasDerivAt (d := d) (k := k) hr) using 1
  dsimp [ell]
  field_simp [ne_of_gt (mr_pos (d := d) (k := k) hr)]
lemma ell_deriv_scaled {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => ell ((d,k),s)) (ell ((d,k),r)*w ((d,k),r)*(1-Hr ((d,k),r))) r := by
  have hm := ne_of_gt (mr_pos (d := d) (k := k) hr)
  have hp : 1+Hr ((d,k),r) ≠ 0 := by
    have hh := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).1
    linarith
  convert! ell_deriv (d := d) (k := k) hr using 1
  dsimp [ell,w]
  field_simp
lemma w_deriv_scaled {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => w ((d,k),s)) ((sch ((d,k),r)+(1/2)*(w ((d,k),r))^2)*(1-Hr ((d,k),r))) r := by
  simpa only [mul_comm] using w_deriv (d := d) (k := k) hr

lemma endpoint_first_derivs {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => EndpointAlgebra.X (m ((d,k),s)) (n ((d,k),s)) (ell ((d,k),s)))
      (Xj ((d,k),r)*(1-Hr ((d,k),r))) r ∧
    HasDerivAt (fun s => EndpointAlgebra.Z (m ((d,k),s)) (n ((d,k),s)) (ell ((d,k),s)))
      (Zj ((d,k),r)*(1-Hr ((d,k),r))) r ∧
    HasDerivAt (fun s => EndpointAlgebra.gamma (m ((d,k),s)) (n ((d,k),s)) (ell ((d,k),s)))
      (gj ((d,k),r)*(1-Hr ((d,k),r))) r := by
  have hm := ne_of_gt (m_pos (d := d) (k := k) hr)
  have hn := ne_of_gt (n_pos (d := d) (k := k) hr)
  have hl : 1+ell ((d,k),r) ≠ 0 := by have := ell_pos (d := d) (k := k) hr; positivity
  exact ⟨EndpointAlgebra.X_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr) rfl rfl rfl hm hn hl,
    EndpointAlgebra.Z_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr) rfl rfl rfl hl,
    EndpointAlgebra.gamma_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr) rfl rfl rfl hm hn hl⟩

lemma endpoint_second_derivs {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Xj ((d,k),s)) (Xjj ((d,k),r)*(1-Hr ((d,k),r))) r ∧
    HasDerivAt (fun s => Zj ((d,k),s)) (Zjj ((d,k),r)*(1-Hr ((d,k),r))) r ∧
    HasDerivAt (fun s => gj ((d,k),s)) (gjj ((d,k),r)*(1-Hr ((d,k),r))) r := by
  have hm := ne_of_gt (m_pos (d := d) (k := k) hr)
  have hn := ne_of_gt (n_pos (d := d) (k := k) hr)
  have hl : 1+ell ((d,k),r) ≠ 0 := by have := ell_pos (d := d) (k := k) hr; positivity
  exact ⟨EndpointAlgebra.X1_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr)
      (w_deriv_scaled hr) rfl rfl rfl rfl hm hn hl,
    EndpointAlgebra.Z1_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr)
      (w_deriv_scaled hr) rfl rfl rfl rfl hl,
    EndpointAlgebra.gamma1_reparam (m_deriv hr) (n_deriv hr) (ell_deriv_scaled hr)
      (w_deriv_scaled hr) rfl rfl rfl rfl hm hn hl⟩

lemma gamma_analytic {d k r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ ω QuadraticCoordinates.gamma ((d,k),r) := by
  unfold QuadraticCoordinates.gamma gap
  have hH := H_analytic (d := d) (k := k) hr
  have hHr := Hr_analytic (d := d) (k := k) hr
  fun_prop (disch := exact pow_ne_zero _ (ne_of_gt (H_gap_pos hr)))
lemma gr_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω gr ((d,k),r) :=
  direction_contDiffAt (gamma_analytic hr) _
lemma gr_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => QuadraticCoordinates.gamma ((d,k),s)) (gr ((d,k),r)) r :=
  slice_r ((gamma_analytic hr).differentiableAt (by simp))
lemma grr_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => gr ((d,k),s)) (grr ((d,k),r)) r :=
  slice_r ((gr_analytic hr).differentiableAt (by simp))

lemma first_jets {d k r : ℝ} (hr : 0 < r) :
    Xj ((d,k),r)*(1-Hr ((d,k),r))=k*R ((d,k),r) ∧
    Zj ((d,k),r)*(1-Hr ((d,k),r))=d*R ((d,k),r)+3*k*S ((d,k),r) ∧
    gj ((d,k),r)*(1-Hr ((d,k),r))=gr ((d,k),r) := by
  have he : ∀ᶠ s in 𝓝 r, 0 < s := eventually_gt_nhds hr
  have h1 := (endpoint_first_derivs (d := d) (k := k) hr).1
  have h2 := (endpoint_first_derivs (d := d) (k := k) hr).2.1
  have h3 := (endpoint_first_derivs (d := d) (k := k) hr).2.2
  constructor
  · have ht := (((R_hasDerivAt (d := d) (k := k) hr).const_mul k).add_const d).congr_of_eventuallyEq
      (he.mono (fun s hs => (endpoint_identities (d := d) (k := k) hs).1))
    exact h1.unique ht
  constructor
  · have ht := (((R_hasDerivAt (d := d) (k := k) hr).const_mul d).add
      ((S_hasDerivAt (d := d) (k := k) hr).const_mul (3*k))).congr_of_eventuallyEq
      (he.mono (fun s hs => (endpoint_identities (d := d) (k := k) hs).2.1))
    exact h2.unique ht
  · exact h3.unique ((gr_deriv (d := d) (k := k) hr).congr_of_eventuallyEq
      (he.mono (fun s hs => (endpoint_identities (d := d) (k := k) hs).2.2)))

lemma second_jets {d k r : ℝ} (hr : 0 < r) :
    Xjj ((d,k),r)*(1-Hr ((d,k),r))^2-Xj ((d,k),r)*Hrr ((d,k),r)=k*Rr ((d,k),r) ∧
    Zjj ((d,k),r)*(1-Hr ((d,k),r))^2-Zj ((d,k),r)*Hrr ((d,k),r)=d*Rr ((d,k),r)+3*k*Sr ((d,k),r) ∧
    gjj ((d,k),r)*(1-Hr ((d,k),r))^2-gj ((d,k),r)*Hrr ((d,k),r)=grr ((d,k),r) := by
  have he : ∀ᶠ s in 𝓝 r, 0 < s := eventually_gt_nhds hr
  have hm := (Hrr_hasDerivAt (d := d) (k := k) hr).const_sub 1
  have h1 := ((endpoint_second_derivs (d := d) (k := k) hr).1.mul hm).unique
    (((Rr_hasDerivAt (d := d) (k := k) hr).const_mul k).congr_of_eventuallyEq
      (he.mono (fun s hs => (first_jets (d := d) (k := k) hs).1)))
  have h2 := ((endpoint_second_derivs (d := d) (k := k) hr).2.1.mul hm).unique
    ((((Rr_hasDerivAt (d := d) (k := k) hr).const_mul d).add
      ((Sr_hasDerivAt (d := d) (k := k) hr).const_mul (3*k))).congr_of_eventuallyEq
      (he.mono (fun s hs => (first_jets (d := d) (k := k) hs).2.1)))
  have h3 := ((endpoint_second_derivs (d := d) (k := k) hr).2.2.mul hm).unique
    ((grr_deriv (d := d) (k := k) hr).congr_of_eventuallyEq
      (he.mono (fun s hs => (first_jets (d := d) (k := k) hs).2.2)))
  constructor
  · nlinarith only [h1]
  constructor
  · nlinarith only [h2]
  · nlinarith only [h3]

lemma Xj_pos {d k r : ℝ} (hk : 0 < k) (hr : 0 < r) : 0 < Xj ((d,k),r) := by
  have h := (first_jets (d := d) (k := k) hr).1
  exact pos_of_mul_pos_left (h.symm ▸ mul_pos hk (R_pos hr)) (mr_pos hr).le

lemma determinant_W {d k r : ℝ} (hr : 0 < r) :
    (Xj ((d,k),r)*Zjj ((d,k),r)-Zj ((d,k),r)*Xjj ((d,k),r))*(1-Hr ((d,k),r))^3=
      3*k^2*W ((d,k),r) := by
  obtain ⟨hx,hz,_⟩ := first_jets (d := d) (k := k) hr
  obtain ⟨hxx,hzz,_⟩ := second_jets (d := d) (k := k) hr
  dsimp only [W]
  linear_combination (Zjj ((d,k),r)*(1-Hr ((d,k),r))^2-Hrr ((d,k),r)*Zj ((d,k),r))*hx +
    (-Xjj ((d,k),r)*(1-Hr ((d,k),r))^2+Hrr ((d,k),r)*Xj ((d,k),r))*hz +
    k*R ((d,k),r)*hzz-(d*R ((d,k),r)+3*k*S ((d,k),r))*hxx
end QuinticLienard.ModelEndpoint

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.SchwarzianScaling
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

namespace QuinticLienard.ModelAlgebra
lemma zero_sign_conditional {z l b d w : ℝ}
    (hz : 0 < z) (hl : 0 < l) (hb : 0 < b)
    (hSmall : z ≤ 1 → 1 < l ∧ 0 < w)
    (hLarge : 1 < z → d < 0)
    (hSlope : 1 < z → 1 ≤ l → 0 ≤ w)
    (hX : d < (l/z-1)/(1+l))
    (hRic : 1 < z → 4*b*z ≤ d^2 → w ≤ 1/z-l+d*l-2*Real.sqrt (d^2/4-b*z))
    (hZero : dStar z 1 l w (schwarzian z 1 l b d) = 0) :
    z ≠ 1 ∧ 0 < (wStar z 1 l-w)/(z-1) := by
  rcases lt_trichotomy z 1 with hlt | rfl | hgt
  · obtain ⟨hl1, hw⟩ := hSmall hlt.le
    refine ⟨ne_of_lt hlt, div_pos_of_neg_of_neg ?_ (by linarith)⟩
    have hstar := wStar_neg hz hlt hl1.le
    linarith
  · obtain ⟨hl1, hw⟩ := hSmall le_rfl
    have := equal_endpoints_pos (S := schwarzian 1 1 l b d) hl1 hw
    simp only [hZero, lt_self_iff_false] at this
  · have hd := hLarge hgt
    have hl1 : l < 1 := by
      by_contra! hl1
      have := second_case hgt hl1 hb hd (hSlope hgt hl1)
      linarith
    have hw : w < wStar z 1 l := by
      by_contra! hw
      have := last_case hgt hl hl1 hb hd hw hX (hRic hgt)
      linarith
    exact ⟨ne_of_gt hgt, div_pos (sub_pos.mpr hw) (by linarith)⟩

lemma schwarzian_scaling {m n l b d : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) :
    schwarzian (m/n) 1 l (n^3*b) (n*d)=n^2*schwarzian m n l b d := by
  dsimp [schwarzian]
  field_simp
lemma dStar_scaling {m n l w s : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) :
    dStar (m/n) 1 l (n*w) (n^2*s)=n*dStar m n l w s := by
  dsimp [dStar]
  field_simp
lemma wStar_scaling {m n l : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) (hs : m+n ≠ 0) :
    wStar (m/n) 1 l=n*wStar m n l := by
  dsimp [wStar]
  field_simp
lemma X_scaling {m n l : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    (l/(m/n)-1)/(1+l)=n*((l/m-1/n)/(1+l)) := by
  field_simp

lemma zero_sign_unscaled {m n l b d w : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hl : 0 < l) (hb : 0 < b)
    (hSmall : m ≤ n → 1 < l ∧ 0 < w)
    (hLarge : n < m → d < 0)
    (hSlope : n < m → 1 ≤ l → 0 ≤ w)
    (hX : d < (l/m-1/n)/(1+l))
    (hRic : n < m → 4*b*m ≤ d^2 → w ≤ 1/m-l/n+d*l-2*Real.sqrt (d^2/4-b*m))
    (hZero : dStar m n l w (schwarzian m n l b d) = 0) :
    m ≠ n ∧ 0 < (wStar m n l-w)/(m-n) := by
  have hz := div_pos hm hn
  have hlt : 1 < m/n ↔ n < m := by simpa using (lt_div_iff₀ hn : 1 < m/n ↔ 1*n < m)
  have hle : m/n ≤ 1 ↔ m ≤ n := by simpa using (div_le_iff₀ hn : m/n ≤ 1 ↔ m ≤ 1*n)
  have hs : m+n ≠ 0 := ne_of_gt (add_pos hm hn)
  have hln : 1+l ≠ 0 := by positivity
  have hsmall : m/n ≤ 1 → 1 < l ∧ 0 < n*w := by
    intro h
    exact ⟨(hSmall (hle.mp h)).1,mul_pos hn (hSmall (hle.mp h)).2⟩
  have hlarge : 1 < m/n → n*d < 0 := fun h => mul_neg_of_pos_of_neg hn (hLarge (hlt.mp h))
  have hslope : 1 < m/n → 1 ≤ l → 0 ≤ n*w :=
    fun h hl1 => mul_nonneg hn.le (hSlope (hlt.mp h) hl1)
  have hx : n*d < (l/(m/n)-1)/(1+l) := by
    rw [X_scaling (ne_of_gt hm) (ne_of_gt hn) hln]
    exact mul_lt_mul_of_pos_left hX hn
  have hric : 1 < m/n → 4*(n^3*b)*(m/n) ≤ (n*d)^2 →
      n*w ≤ 1/(m/n)-l+n*d*l-2*Real.sqrt ((n*d)^2/4-(n^3*b)*(m/n)) := by
    intro hz1 hdisc
    have he : 4*(n^3*b)*(m/n)=n^2*(4*b*m) := by field_simp
    have he2 : (n*d)^2=n^2*d^2 := by ring
    rw [he,he2] at hdisc
    have hd := (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp hdisc
    have hh := mul_le_mul_of_nonneg_left (hRic (hlt.mp hz1) hd) hn.le
    have hroot : Real.sqrt ((n*d)^2/4-(n^3*b)*(m/n))=n*Real.sqrt (d^2/4-b*m) := by
      have heq : (n*d)^2/4-(n^3*b)*(m/n)=n^2*(d^2/4-b*m) := by field_simp
      rw [heq,Real.sqrt_mul (sq_nonneg n),Real.sqrt_sq hn.le]
    rw [hroot]
    convert! hh using 1
    field_simp
  have hzero : dStar (m/n) 1 l (n*w) (schwarzian (m/n) 1 l (n^3*b) (n*d))=0 := by
    rw [schwarzian_scaling (ne_of_gt hm) (ne_of_gt hn),dStar_scaling (ne_of_gt hm) (ne_of_gt hn),hZero,mul_zero]
  obtain ⟨hne,hpos⟩ := zero_sign_conditional hz hl (mul_pos (pow_pos hn _) hb)
    hsmall hlarge hslope hx hric hzero
  have hmn : m ≠ n := by intro h; apply hne; rw [h,div_self (ne_of_gt hn)]
  refine ⟨hmn,?_⟩
  have heq : (wStar (m/n) 1 l-n*w)/(m/n-1)=n^2*((wStar m n l-w)/(m-n)) := by
    rw [wStar_scaling (ne_of_gt hm) (ne_of_gt hn) hs]
    field_simp
  rw [heq] at hpos
  exact pos_of_mul_pos_right hpos (sq_nonneg n)
end QuinticLienard.ModelAlgebra

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.EndpointSigns
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

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ModelEndpoint
open PartialCalculus QuadraticCoordinates

lemma sch_eq {d k r : ℝ} : sch ((d,k),r)=
    ModelAlgebra.schwarzian (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r)) (k/2) d := by
  dsimp [sch,ModelAlgebra.schwarzian]
  ring

lemma actual_zero_sign {d k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hZero : ModelAlgebra.dStar (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))
      (w ((d,k),r)) (sch ((d,k),r))=0) :
    m ((d,k),r) ≠ n ((d,k),r) ∧
      0 < (ModelAlgebra.wStar (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))-w ((d,k),r))/
        (m ((d,k),r)-n ((d,k),r)) := by
  have hm := m_pos (d := d) (k := k) hr
  have hn := n_pos (d := d) (k := k) hr
  have hl := ell_pos (d := d) (k := k) hr
  apply ModelAlgebra.zero_sign_unscaled hm hn hl (show 0 < k/2 by linarith)
  · intro hmn
    have hH : 0 ≤ H ((d,k),r) := by dsimp [m,n] at hmn; linarith
    have hHr := Hr_pos_of_H_nonneg hk hr hH
    refine ⟨?_,w_pos_of_H_nonneg hk hr hH⟩
    exact (lt_div_iff₀ (mr_pos hr)).mpr (by linarith)
  · intro hnm
    apply d_neg_of_H_neg hk hr
    dsimp [m,n] at hnm
    linarith
  · intro hnm hl1
    have hH : H ((d,k),r) < 0 := by dsimp [m,n] at hnm; linarith
    have hHr : 0 ≤ Hr ((d,k),r) := by
      have hh := (le_div_iff₀ (mr_pos (d := d) (k := k) hr)).mp hl1
      linarith
    exact w_nonneg_of_H_neg_Hr_nonneg hk hr hH hHr
  · change d < EndpointAlgebra.X (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))
    rw [(endpoint_identities hr).1]
    have hh := mul_pos hk (QuadraticVariation.P_pos (d := d) (k := k) hr)
    linarith
  · intro hnm hdisc
    have hH : H ((d,k),r) < 0 := by dsimp [m,n] at hnm; linarith
    have hd := d_neg_of_H_neg hk hr hH
    obtain ⟨c⟩ := lower_chart (d := d) (k := k) hr
    have hh := c.variation_bound hr hk hd (Real.sqrt_nonneg (d^2/4-(k/2)*m ((d,k),r)))
      (Real.sq_sqrt (show 0 ≤ d^2/4-(k/2)*m ((d,k),r) by linarith))
    rwa [c.log_deriv hr] at hh
  · rwa [← sch_eq]

lemma dStar_zero_of_W_zero {d k r : ℝ} (hr : 0 < r) (hW : W ((d,k),r)=0) :
    ModelAlgebra.dStar (m ((d,k),r)) (n ((d,k),r)) (ell ((d,k),r))
      (w ((d,k),r)) (sch ((d,k),r))=0 := by
  have hm := m_pos (d := d) (k := k) hr
  have hn := n_pos (d := d) (k := k) hr
  have hl := ell_pos (d := d) (k := k) hr
  have hln : 1+ell ((d,k),r) ≠ 0 := by positivity
  have hh := determinant_W (d := d) (k := k) hr
  rw [hW,mul_zero] at hh
  have hd : Xj ((d,k),r)*Zjj ((d,k),r)-Zj ((d,k),r)*Xjj ((d,k),r)=0 :=
    (mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ (ne_of_gt (mr_pos hr)))
  rw [Xj,Xjj,Zj,Zjj,EndpointAlgebra.determinant (ne_of_gt hm) (ne_of_gt hn) hln] at hd
  exact (mul_eq_zero.mp hd).resolve_left (ne_of_gt (by positivity))

lemma gamma_zero_sign {d k r : ℝ} (hk : 0 < k) (hr : 0 < r) (hW : W ((d,k),r)=0) :
    0 < gjj ((d,k),r)-Xjj ((d,k),r)/Xj ((d,k),r)*gj ((d,k),r) := by
  have hm := m_pos (d := d) (k := k) hr
  have hn := n_pos (d := d) (k := k) hr
  have hl := ell_pos (d := d) (k := k) hr
  have hln : 1+ell ((d,k),r) ≠ 0 := by positivity
  have hmn : m ((d,k),r)+n ((d,k),r) ≠ 0 := ne_of_gt (add_pos hm hn)
  have hd := dStar_zero_of_W_zero hr hW
  obtain ⟨hne,hpos⟩ := actual_zero_sign hk hr hd
  have hf := EndpointAlgebra.gamma_factor (ne_of_gt hm) (ne_of_gt hn) hln hmn hne
    (ne_of_gt (Xj_pos hk hr)) hd
  change 0 < EndpointAlgebra.gamma2 _ _ _ _ _ - EndpointAlgebra.X2 _ _ _ _ _ /
    EndpointAlgebra.X1 _ _ _ _ * EndpointAlgebra.gamma1 _ _ _ _
  rw [hf, mul_div_assoc]
  exact mul_pos (by positivity) hpos

lemma gamma_source_sign {d k r : ℝ} (hk : 0 < k) (hr : 0 < r) (hW : W ((d,k),r)=0) :
    0 < grr ((d,k),r)-Rr ((d,k),r)/R ((d,k),r)*gr ((d,k),r) := by
  have ha := mr_pos (d := d) (k := k) hr
  have hR := R_pos (d := d) (k := k) hr
  have hX := Xj_pos (d := d) hk hr
  obtain ⟨hx,_,hg⟩ := first_jets (d := d) (k := k) hr
  obtain ⟨hxx,_,hgg⟩ := second_jets (d := d) (k := k) hr
  have heq : grr ((d,k),r)-Rr ((d,k),r)/R ((d,k),r)*gr ((d,k),r)=
      (1-Hr ((d,k),r))^2*(gjj ((d,k),r)-Xjj ((d,k),r)/Xj ((d,k),r)*gj ((d,k),r)) := by
    apply (mul_right_inj' (ne_of_gt (mul_pos hR hX))).mp
    field_simp
    linear_combination -R ((d,k),r)*Xj ((d,k),r)*hgg +
      Xj ((d,k),r)*Rr ((d,k),r)*hg +
      gj ((d,k),r)*R ((d,k),r)*hxx -
      gj ((d,k),r)*Rr ((d,k),r)*hx
  rw [heq]
  exact mul_pos (sq_pos_of_pos ha) (gamma_zero_sign hk hr hW)
end QuinticLienard.ModelEndpoint

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CurvatureJets
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

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus ModelEndpoint
lemma alpha_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω alpha ((d,k),r) := by
  unfold alpha gap
  have hH := H_analytic (d := d) (k := k) hr
  fun_prop (disch := exact ne_of_gt (H_gap_pos hr))
lemma ar_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω ar ((d,k),r) :=
  direction_contDiffAt (alpha_analytic hr) _
lemma ar_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => alpha ((d,k),s)) (ar ((d,k),r)) r :=
  slice_r ((alpha_analytic hr).differentiableAt (by simp))
lemma arr_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => ar ((d,k),s)) (arr ((d,k),r)) r :=
  slice_r ((ar_analytic hr).differentiableAt (by simp))
lemma Rr_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω Rr ((d,k),r) :=
  direction_contDiffAt (R_analytic hr) _
lemma Sr_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω Sr ((d,k),r) :=
  direction_contDiffAt (S_analytic hr) _
lemma W_analytic {d k r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ω W ((d,k),r) :=
  ((R_analytic hr).mul (Sr_analytic hr)).sub ((S_analytic hr).mul (Rr_analytic hr))

lemma transport_P {d k r : ℝ} (hr : 0 < r) :
    transport P ((d,k),r)=gamma ((d,k),r)*P ((d,k),r)-1 := by
  have hp := slice_d ((P_analytic (d := d) (k := k) hr).differentiableAt (by simp))
  have hH := P_hasDerivAt (d := d) (k := k) hr
  have hg := ne_of_gt (H_gap_pos (d := d) (k := k) hr)
  have ht := (((Hr_d_hasDerivAt (d := d) (k := k) hr).const_mul r).add hH).div
    ((hasDerivAt_const d (r^2)).sub (hH.pow 2)) hg
  have he : (fun s => k*P ((s,k),r)+s) =ᶠ[𝓝 d]
      (fun s => (r*Hr ((s,k),r)+H ((s,k),r))/(r^2-(H ((s,k),r))^2)) :=
    Eventually.of_forall (fun s => width_identity (d := s) (k := k) hr)
  have hh := ((hp.const_mul k).add (hasDerivAt_id d)).unique (ht.congr_of_eventuallyEq he)
  dsimp [transport,alpha,gamma,gap]
  change k*direction ((1,0),0) P ((d,k),r)-r/(r^2-H ((d,k),r)^2)*R ((d,k),r)=_
  dsimp at hh
  norm_num only [Nat.cast_ofNat, show 2-1=1 from rfl, pow_one] at hh
  field_simp [hg] at hh ⊢
  nlinarith only [hh]

lemma transport_Q {d k r : ℝ} (hr : 0 < r) :
    transport Q ((d,k),r)=gamma ((d,k),r)*Q ((d,k),r)-P ((d,k),r) := by
  have hp := slice_k ((P_analytic (d := d) (k := k) hr).differentiableAt (by simp))
  have hH := Q_hasDerivAt (d := d) (k := k) hr
  have hg := ne_of_gt (H_gap_pos (d := d) (k := k) hr)
  have ht := (((Hr_k_hasDerivAt (d := d) (k := k) hr).const_mul r).add hH).div
    ((hasDerivAt_const k (r^2)).sub (hH.pow 2)) hg
  have he : (fun s => s*P ((d,s),r)+d) =ᶠ[𝓝 k]
      (fun s => (r*Hr ((d,s),r)+H ((d,s),r))/(r^2-(H ((d,s),r))^2)) :=
    Eventually.of_forall (fun s => width_identity (d := d) (k := s) hr)
  have hh := (((hasDerivAt_id k).mul hp).add_const d).unique (ht.congr_of_eventuallyEq he)
  have hc : direction ((0,1),0) P ((d,k),r)=direction ((1,0),0) Q ((d,k),r) :=
    direction_comm (H_analytic hr) _ _
  rw [hc] at hh
  dsimp [transport,alpha,gamma,gap]
  change k*direction ((1,0),0) Q ((d,k),r)-r/(r^2-H ((d,k),r)^2)*S ((d,k),r)=_
  dsimp at hh
  norm_num only [Nat.cast_ofNat, show 2-1=1 from rfl, pow_one] at hh
  field_simp [hg] at hh ⊢
  nlinarith only [hh]

lemma transport_deriv {f : (ℝ × ℝ) × ℝ → ℝ} {d k r : ℝ} (hr : 0 < r)
    (hf : ContDiffAt ℝ ω f ((d,k),r)) :
    HasDerivAt (fun s => transport f ((d,k),s))
      (transport (direction ((0,0),1) f) ((d,k),r)-ar ((d,k),r)*direction ((0,0),1) f ((d,k),r)) r := by
  have hfd := direction_contDiffAt hf (((1,0),0) : (ℝ × ℝ) × ℝ)
  have hfr := direction_contDiffAt hf (((0,0),1) : (ℝ × ℝ) × ℝ)
  have hd := ((slice_r (hfd.differentiableAt (by simp))).const_mul k).sub
    ((ar_deriv (d := d) (k := k) hr).mul (slice_r (hfr.differentiableAt (by simp))))
  have hc := direction_comm hf (((0,0),1) : (ℝ × ℝ) × ℝ) (((1,0),0) : (ℝ × ℝ) × ℝ)
  convert! hd using 1
  dsimp [transport]
  rw [hc]
  ring

lemma transport_R {d k r : ℝ} (hr : 0 < r) :
    transport R ((d,k),r)=(gamma ((d,k),r)+ar ((d,k),r))*R ((d,k),r)+gr ((d,k),r)*P ((d,k),r) := by
  have hh := (transport_deriv hr (P_analytic (d := d) (k := k) hr)).unique
    ((((gr_deriv hr).mul (R_hasDerivAt hr)).sub_const 1).congr_of_eventuallyEq
      ((eventually_gt_nhds hr).mono (fun s hs => transport_P (d := d) (k := k) hs)))
  change transport R ((d,k),r)-ar ((d,k),r)*R ((d,k),r)=_ at hh
  nlinarith only [hh]
lemma transport_S {d k r : ℝ} (hr : 0 < r) :
    transport S ((d,k),r)=(gamma ((d,k),r)+ar ((d,k),r))*S ((d,k),r)+gr ((d,k),r)*Q ((d,k),r)-R ((d,k),r) := by
  have hh := (transport_deriv hr (Q_analytic (d := d) (k := k) hr)).unique
    ((((gr_deriv hr).mul (S_hasDerivAt hr)).sub (R_hasDerivAt hr)).congr_of_eventuallyEq
      ((eventually_gt_nhds hr).mono (fun s hs => transport_Q (d := d) (k := k) hs)))
  change transport S ((d,k),r)-ar ((d,k),r)*S ((d,k),r)=_ at hh
  nlinarith only [hh]
lemma transport_Rr {d k r : ℝ} (hr : 0 < r) :
    transport Rr ((d,k),r)=(gamma ((d,k),r)+2*ar ((d,k),r))*Rr ((d,k),r)+
      (2*gr ((d,k),r)+arr ((d,k),r))*R ((d,k),r)+grr ((d,k),r)*P ((d,k),r) := by
  have hh := (transport_deriv hr (R_analytic (d := d) (k := k) hr)).unique
    (((((gr_deriv hr).add (arr_deriv hr)).mul (Rr_hasDerivAt hr)).add
      ((grr_deriv hr).mul (R_hasDerivAt hr))).congr_of_eventuallyEq
      ((eventually_gt_nhds hr).mono (fun s hs => transport_R (d := d) (k := k) hs)))
  change transport Rr ((d,k),r)-ar ((d,k),r)*Rr ((d,k),r)=_ at hh
  dsimp at hh
  nlinarith only [hh]
lemma transport_Sr {d k r : ℝ} (hr : 0 < r) :
    transport Sr ((d,k),r)=(gamma ((d,k),r)+2*ar ((d,k),r))*Sr ((d,k),r)+
      (2*gr ((d,k),r)+arr ((d,k),r))*S ((d,k),r)+grr ((d,k),r)*Q ((d,k),r)-Rr ((d,k),r) := by
  have hh := (transport_deriv hr (S_analytic (d := d) (k := k) hr)).unique
    ((((((gr_deriv hr).add (arr_deriv hr)).mul (Sr_hasDerivAt hr)).add
      ((grr_deriv hr).mul (S_hasDerivAt hr))).sub (Rr_hasDerivAt hr)).congr_of_eventuallyEq
      ((eventually_gt_nhds hr).mono (fun s hs => transport_S (d := d) (k := k) hs)))
  change transport Sr ((d,k),r)-ar ((d,k),r)*Sr ((d,k),r)=_ at hh
  dsimp at hh
  nlinarith only [hh]

lemma direction_mul_sub {f g h j : (ℝ × ℝ) × ℝ → ℝ} {q : (ℝ × ℝ) × ℝ}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q)
    (hh : DifferentiableAt ℝ h q) (hj : DifferentiableAt ℝ j q) (v : (ℝ × ℝ) × ℝ) :
    direction v (fun q => f q*g q-h q*j q) q=
      direction v f q*g q+f q*direction v g q-direction v h q*j q-h q*direction v j q := by
  change (fderiv ℝ (f*g-h*j) q) v=_
  rw [fderiv_sub (hf.mul hg) (hh.mul hj),fderiv_mul hf hg,fderiv_mul hh hj]
  dsimp only [direction]
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul]
  ring

lemma transport_W {d k r : ℝ} (hr : 0 < r) :
    transport W ((d,k),r)=(2*gamma ((d,k),r)+3*ar ((d,k),r))*W ((d,k),r)+
      gr ((d,k),r)*(P ((d,k),r)*Sr ((d,k),r)-Q ((d,k),r)*Rr ((d,k),r))-
      grr ((d,k),r)*G ((d,k),r) := by
  have hR := (R_analytic (d := d) (k := k) hr).differentiableAt (by simp)
  have hS := (S_analytic (d := d) (k := k) hr).differentiableAt (by simp)
  have hRr := (Rr_analytic (d := d) (k := k) hr).differentiableAt (by simp)
  have hSr := (Sr_analytic (d := d) (k := k) hr).differentiableAt (by simp)
  have he : transport W ((d,k),r)=transport R ((d,k),r)*Sr ((d,k),r)+R ((d,k),r)*transport Sr ((d,k),r)-
      transport S ((d,k),r)*Rr ((d,k),r)-S ((d,k),r)*transport Rr ((d,k),r) := by
    dsimp only [transport]
    rw [show W = (fun q => R q*Sr q-S q*Rr q) from rfl]
    rw [direction_mul_sub hR hSr hS hRr,direction_mul_sub hR hSr hS hRr]
    ring
  rw [he,transport_R hr,transport_S hr,transport_Rr hr,transport_Sr hr]
  dsimp [W,G]
  ring
end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CurvatureComparison
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

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus ModelEndpoint

lemma transport_W_at_zero {d k r : ℝ} (hr : 0 < r) (hW : W ((d,k),r)=0) :
    transport W ((d,k),r) = -G ((d,k),r)*(grr ((d,k),r)-Rr ((d,k),r)/R ((d,k),r)*gr ((d,k),r)) := by
  have hR := ne_of_gt (R_pos (d := d) (k := k) hr)
  rw [transport_W hr,hW,mul_zero,zero_add]
  dsimp only [W] at hW
  dsimp only [G]
  field_simp
  linear_combination gr ((d,k),r)*P ((d,k),r)*hW

lemma characteristic_deriv {f : (ℝ × ℝ) × ℝ → ℝ} {z k r : ℝ} (hr : 0 < r)
    (hf : ContDiffAt ℝ ω f ((ReferenceCharacteristic.J ((z,k),r),k),r)) :
    HasDerivAt (fun s => f ((ReferenceCharacteristic.J ((z,k),s),k),s))
      (-transport f ((ReferenceCharacteristic.J ((z,k),r),k),r)/
        alpha ((ReferenceCharacteristic.J ((z,k),r),k),r)) r := by
  have hd := (hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (f := fun s => ((ReferenceCharacteristic.J ((z,k),s),k),s)) r
    (((ReferenceCharacteristic.J_deriv (z := z) (k := k) hr).prodMk (hasDerivAt_const r k)).prodMk (hasDerivAt_id r))
  rw [fderiv_model] at hd
  convert! hd using 1
  have hg := ne_of_gt (H_gap_pos (d := ReferenceCharacteristic.J ((z,k),r)) (k := k) hr)
  dsimp [transport,alpha,ReferenceCharacteristic.A,gap]
  field_simp [ne_of_gt hr,hg]
  ring

lemma W_pos_of_curvature_pos {d k r : ℝ} (hk : 0 < k) (hr : 0 < r) : 0 < W ((d,k),r) := by
  obtain ⟨z,hz⟩ := ReferenceCharacteristic.J_surjective d k hr
  have he : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s ∧ s < r ∧
      0 < W ((ReferenceCharacteristic.J ((z,k),s),k),s) := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hr).filter_mono inf_le_left,
      (ReferenceCharacteristic.model_tendsto z k).eventually (W_positive_near_zero z k)] with s hs hsr hW
    exact ⟨hs,hsr,hW hs⟩
  obtain ⟨a,ha,har,hWa⟩ := he.exists
  have hd (s : ℝ) (hs : s ∈ Icc a r) :=
    characteristic_deriv (ha.trans_le hs.1) (W_analytic (d := ReferenceCharacteristic.J ((z,k),s)) (k := k) (ha.trans_le hs.1))
  have hpos := RealAnalysis.positive_of_deriv_pos_at_zero har
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt) hd hWa.le (by
      intro s hs hzero
      have hs0 := ha.trans_le hs.1
      rw [transport_W_at_zero hs0 hzero,neg_mul,neg_neg]
      exact div_pos (mul_pos (G_pos hs0) (gamma_source_sign hk hs0 hzero))
        (div_pos hs0 (H_gap_pos hs0)))
  simpa only [hz] using hpos

lemma P_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : P ((-d,-k),r)=P ((d,k),r) := by
  have h1 := (P_hasDerivAt (d := -d) (k := -k) hr).comp d (hasDerivAt_neg d)
  have h2 := (P_hasDerivAt (d := d) (k := k) hr).neg
  have hh := h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall (fun s => reflection s k hr)))
  linarith
lemma Q_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : Q ((-d,-k),r)=Q ((d,k),r) := by
  have h1 := (Q_hasDerivAt (d := -d) (k := -k) hr).comp k (hasDerivAt_neg k)
  have h2 := (Q_hasDerivAt (d := d) (k := k) hr).neg
  have hh := h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall (fun s => reflection d s hr)))
  linarith
lemma R_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : R ((-d,-k),r)=R ((d,k),r) := by
  exact (R_hasDerivAt hr).unique ((R_hasDerivAt hr).congr_of_eventuallyEq
    ((eventually_gt_nhds hr).mono (fun s hs => P_reflection d k hs)))
lemma S_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : S ((-d,-k),r)=S ((d,k),r) := by
  exact (S_hasDerivAt hr).unique ((S_hasDerivAt hr).congr_of_eventuallyEq
    ((eventually_gt_nhds hr).mono (fun s hs => Q_reflection d k hs)))
lemma Rr_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : Rr ((-d,-k),r)=Rr ((d,k),r) := by
  exact (Rr_hasDerivAt hr).unique ((Rr_hasDerivAt hr).congr_of_eventuallyEq
    ((eventually_gt_nhds hr).mono (fun s hs => R_reflection d k hs)))
lemma Sr_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : Sr ((-d,-k),r)=Sr ((d,k),r) := by
  exact (Sr_hasDerivAt hr).unique ((Sr_hasDerivAt hr).congr_of_eventuallyEq
    ((eventually_gt_nhds hr).mono (fun s hs => S_reflection d k hs)))
lemma W_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) : W ((-d,-k),r)=W ((d,k),r) := by
  simp only [W,R_reflection d k hr,S_reflection d k hr,Rr_reflection d k hr,Sr_reflection d k hr]

lemma W_nonneg {d k r : ℝ} (hr : 0 < r) : 0 ≤ W ((d,k),r) := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have hh := W_pos_of_curvature_pos (d := -d) (neg_pos.mpr hk) hr
    simpa only [W_reflection d k hr] using hh.le
  · have ht : Tendsto (fun a : ℝ => W ((d,a),r)) (𝓝[>] (0:ℝ)) (𝓝 (W ((d,0),r))) :=
      (((W_analytic (d := d) (k := 0) hr).continuousAt).comp (f := fun a : ℝ => ((d,a),r))
        ((continuousAt_const.prodMk continuousAt_id).prodMk continuousAt_const)).tendsto.mono_left inf_le_left
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (W_pos_of_curvature_pos (d := d) ha hr).le
  · exact (W_pos_of_curvature_pos hk hr).le

lemma G_deriv {d k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => G ((d,k),s)) (P ((d,k),r)*Sr ((d,k),r)-Q ((d,k),r)*Rr ((d,k),r)) r := by
  convert! ((R_hasDerivAt hr).mul (Sr_hasDerivAt hr)).sub
    ((S_hasDerivAt hr).mul (Rr_hasDerivAt hr)) using 1
  ring

theorem model_inequality {d k r : ℝ} (hr : 0 < r) :
    deriv (fun s => R ((d,k),s)/G ((d,k),s)) r ≤ 0 := by
  have hG := G_pos (d := d) (k := k) hr
  have hd := ((Rr_hasDerivAt (d := d) (k := k) hr).div (G_deriv hr) (ne_of_gt hG))
  change deriv ((fun s => R ((d,k),s)) / (fun s => G ((d,k),s))) r ≤ 0
  rw [hd.deriv]
  have he : Rr ((d,k),r)*G ((d,k),r)-R ((d,k),r)*(P ((d,k),r)*Sr ((d,k),r)-Q ((d,k),r)*Rr ((d,k),r))=
      -P ((d,k),r)*W ((d,k),r) := by dsimp [G,W]; ring
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (QuadraticVariation.P_pos hr).le) (W_nonneg hr)) (sq_nonneg _)
end QuinticLienard.QuadraticCoordinates

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

theorem midpointAtWidth_abs_lt {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    |midpointAtWidth Φ ((p,h),r)| < r := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  have hb := midpoint_abs_lt_width (positive_arch_exists hφ hhpos hs.1)
  change |midpointAtWidth Φ ((p,h),r)| < widthFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) at hb
  rwa [hs.2] at hb

end QuinticLienard.PositiveWidth

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveTransport
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
namespace QuinticLienard.PositiveTransport
open ScalarArcs ArcEndpoints ArcFamilies PositiveVariation PositiveWidth PartialCalculus
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

theorem M_abs_lt {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) : |M Φ p (h,r)| < r :=
  midpointAtWidth_abs_lt Φ hΦ hloc hhpos hr

end QuinticLienard.PositiveTransport

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
-- module Solutions.OAIQW_QuinticLienard.ActualFitTransport
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
namespace QuinticLienard.QuinticFit
open ScaledProfile PartialCalculus QuadraticCoordinates
lemma M_abs_lt (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : |M a (h,r)|<r :=
  PositiveTransport.M_abs_lt _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr
end QuinticLienard.QuinticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CurvatureTransport
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
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus
lemma G_analytic {d k r : ℝ} (hr : 0<r) : ContDiffAt ℝ ω G ((d,k),r) :=
  ((P_analytic hr).mul (S_analytic hr)).sub ((Q_analytic hr).mul (R_analytic hr))
lemma C_analytic {d k r : ℝ} (hr : 0<r) : ContDiffAt ℝ ω C ((d,k),r) :=
  (R_analytic hr).div (G_analytic hr) (G_pos hr).ne'
lemma Cr_nonpos {d k r : ℝ} (hr : 0<r) : Cr ((d,k),r)≤0 := by
  have hd := slice_r ((C_analytic (d:=d) (k:=k) hr).differentiableAt (by simp))
  change direction ((0,0),1) C ((d,k),r)≤0
  rw [←hd.deriv]
  exact model_inequality hr
end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveBase
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
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveWidth
open ScalarArcs ArcEndpoints ArcFamilies PositiveVariation
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma base_spec {p : P} {t r : ℝ} (he : Admissible Φ ((p,t),r)) :
    0<baseAtWidth Φ ((p,t),r) ∧ baseAtWidth Φ ((p,t),r)<t ∧
    widthFamily Φ ((p,t),baseAtWidth Φ ((p,t),r))=r :=
  Classical.epsilon_spec he
end QuinticLienard.PositiveWidth

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ActualCharacteristic
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
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuinticFit
lemma base_spec {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    0<b a t r ∧ b a t r<t ∧ PositiveWidth.widthFamily (QuinticProfile.profile a) ((0,t),b a t r)=r :=
  PositiveWidth.base_spec _ he
lemma radius_pos {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : 0<r :=
  (base_spec he).2.2 ▸ PositiveWidth.width_pos _ (fun _ h => QuinticProfile.analytic a h) (base_spec he).1 (base_spec he).2.1
lemma m_abs_lt {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : |m a t r|<r :=
  M_abs_lt a (base_spec he).1 (radius_pos he)
lemma g_pos {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : 0<g a t r :=
  sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos (radius_pos he)] using m_abs_lt he))
end QuinticLienard.ActualCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CurvaturePositive
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
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuadraticCoordinates
lemma feed_nonneg_oai {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) : 0≤feed a t r := by
  dsimp only [feed]
  exact mul_nonneg_of_nonpos_of_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (div_pos (g_pos he) (radius_pos he)).le (Cr_nonpos (radius_pos he)))
    (sub_nonpos.mpr (fitted_slope_lt he hthird).le)
end QuinticLienard.ActualCharacteristic

end OAI
end

theorem solution : type_of% @OAI.QuinticLienard.ActualCharacteristic.feed_nonneg_oai := @OAI.QuinticLienard.ActualCharacteristic.feed_nonneg_oai
