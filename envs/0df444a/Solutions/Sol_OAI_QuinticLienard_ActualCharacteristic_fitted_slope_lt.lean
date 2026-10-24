-- Prove2me | solution 1 for OAI.QuinticLienard.ActualCharacteristic.fitted_slope_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T18:13:22.087785+00:00
-- url     : https://prove2.me/submissions/71f1745d-f521-4fc7-b770-c2d841d6fb21

import Mathlib
import Definitions.Def_OAIQWQL000

section
-- module Solutions.OAIQW_QuinticLienard.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

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

lemma PN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω PN q := by
  apply (P_analytic (d := q.1.1*q.2) (k := q.1.2*q.2^3) (by norm_num : (0:ℝ)<1)).comp q
  fun_prop
lemma QN_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω QN q := by
  apply (Q_analytic (d := q.1.1*q.2) (k := q.1.2*q.2^3) (by norm_num : (0:ℝ)<1)).comp q
  fun_prop
lemma PNr_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω PNr q := direction_contDiffAt (PN_analytic q) _
lemma QNr_analytic (q : (ℝ × ℝ) × ℝ) : ContDiffAt ℝ ω QNr q := direction_contDiffAt (QN_analytic q) _

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

end QuinticLienard.QuadraticCoordinates

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
-- module Solutions.OAIQW_QuinticLienard.QuadraticFit
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
namespace QuinticLienard.QuadraticFit
open PartialCalculus QuadraticCoordinates ArcEndpoints

lemma midpoint_strictMono (k : ℝ) {r : ℝ} (hr : 0 < r) :
    StrictMono (fun d => H ((d,k),r)) := by
  apply strictMono_of_deriv_pos
  intro d
  rw [(P_hasDerivAt hr).deriv]
  exact QuadraticVariation.P_pos hr

lemma midpoint_above (k : ℝ) {r M : ℝ} (hr : 0 < r) (hM : M < r) :
    ∃ d, M < H ((d,k),r) := by
  by_contra! hn
  let h₀ := H (((0:ℝ),k),r)
  have hh₀ := abs_lt.mp (H_abs_lt (d := 0) (k := k) hr)
  let c := (r-M)*(r+h₀)
  have hc : 0 < c := mul_pos (sub_pos.mpr hM) (by dsimp [h₀]; linarith [hh₀.1])
  let B := 2*r/c+|k|+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlen : 0 < 2*r+1 := by linarith
  have hab : B < B+(2*r+1) := lt_add_of_pos_right _ hlen
  obtain ⟨d,hd,he⟩ := exists_hasDerivAt_eq_slope
    (fun x => H ((x,k),r)) (fun x => P ((x,k),r)) hab
    (fun x _ => (P_hasDerivAt hr).continuousAt.continuousWithinAt)
    (fun x _ => P_hasDerivAt hr)
  have hp := QuadraticVariation.P_pos (d := d) (k := k) hr
  have hp1 : P ((d,k),r) < 1 := by
    rw [he]
    apply (div_lt_one (by linarith : 0 < B+(2*r+1)-B)).mpr
    have ha := (abs_lt.mp (H_abs_lt (d := B) (k := k) hr)).1
    have hb := (abs_lt.mp (H_abs_lt (d := B+(2*r+1)) (k := k) hr)).2
    linarith
  have hd0 : 0 < d := hB.trans hd.1
  have hlo : h₀ ≤ H ((d,k),r) := (midpoint_strictMono k hr).monotone hd0.le
  have hhi := hn d
  have hgap : c ≤ r^2-H ((d,k),r)^2 := by
    have hh := (abs_lt.mp (H_abs_lt (d := d) (k := k) hr)).1
    have hm := mul_le_mul (show r-M ≤ r-H ((d,k),r) by linarith)
      (show r+h₀ ≤ r+H ((d,k),r) by linarith)
      (show 0 ≤ r+h₀ by dsimp [h₀]; linarith [hh₀.1])
      (show 0 ≤ r-H ((d,k),r) by linarith)
    dsimp [c]
    nlinarith [hm]
  have hkp : -|k| ≤ k*P ((d,k),r) := by
    have h₁ := mul_le_mul_of_nonneg_right (neg_abs_le k) hp.le
    have h₂ := mul_le_mul_of_nonneg_left hp1.le (abs_nonneg k)
    nlinarith
  have hlow : 2*r/c < d+k*P ((d,k),r) := by
    dsimp [B] at hd
    linarith [hd.1]
  have hsum : 0 < d+k*P ((d,k),r) := (div_pos (by linarith) hc).trans hlow
  have hm₁ := (div_lt_iff₀ hc).mp hlow
  have hm₂ := mul_le_mul_of_nonneg_left hgap hsum.le
  have heq := width_identity (d := d) (k := k) hr
  have hGN := ne_of_gt (H_gap_pos (d := d) (k := k) hr)
  have heq' : (d+k*P ((d,k),r))*(r^2-H ((d,k),r)^2)=r*Hr ((d,k),r)+H ((d,k),r) := by
    apply (eq_div_iff hGN).mp
    simpa only [add_comm,gap] using heq
  have hh := (abs_lt.mp (H_abs_lt (d := d) (k := k) hr)).2
  have hv := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).2
  have hh₁ := mul_lt_mul_of_pos_left hv hr
  nlinarith [hm₁,hm₂,heq']

lemma midpoint_below (k : ℝ) {r M : ℝ} (hr : 0 < r) (hM : -r < M) :
    ∃ d, H ((d,k),r) < M := by
  obtain ⟨d,hd⟩ := midpoint_above (-k) hr (show -M < r by linarith)
  refine ⟨-d,?_⟩
  have he := reflection d (-k) hr
  simp only [neg_neg] at he
  rw [he]
  linarith

lemma midpoint_exists {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    ∃ d, H ((d,k),r)=M := by
  obtain ⟨a,ha⟩ := midpoint_below k hr (abs_lt.mp hM).1
  obtain ⟨b,hb⟩ := midpoint_above k hr (abs_lt.mp hM).2
  have hab : a < b := (midpoint_strictMono k hr).lt_iff_lt.mp (ha.trans hb)
  obtain ⟨d,_,hd⟩ := intermediate_value_Icc hab.le
    (fun x _ => (P_hasDerivAt hr).continuousAt.continuousWithinAt) ⟨ha.le,hb.le⟩
  exact ⟨d,hd⟩

lemma slope_spec {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    H ((slope ((k,r),M),k),r)=M := by
  have he := midpoint_exists (k := k) hr hM
  simp only [slope,dite_eq_left he]
  exact he.choose_spec

lemma slope_eq {k r M d : ℝ} (hr : 0 < r) (hM : |M| < r)
    (hd : H ((d,k),r)=M) : slope ((k,r),M)=d :=
  (midpoint_strictMono k hr).injective ((slope_spec hr hM).trans hd.symm)

lemma slope_analytic {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    ContDiffAt ℝ ω slope ((k,r),M) := by
  let d := slope ((k,r),M)
  let f : (ℝ × ℝ) × ℝ → ℝ := fun q => H ((q.2,q.1.1),q.1.2)
  have hf : ContDiffAt ℝ ω f ((k,r),d) :=
    (H_analytic (d := d) (k := k) hr).comp (g := H) (f := fun q : (ℝ × ℝ) × ℝ => ((q.2,q.1.1),q.1.2)) ((k,r),d)
      ((contDiffAt_snd.prodMk contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)
  have hd : HasDerivAt (fun s => f ((k,r),s)) (P ((d,k),r)) d := P_hasDerivAt hr
  obtain ⟨Y,hY,hY₀,he⟩ := level_hit hf hd (slope_spec hr hM)
    (ne_of_gt (QuadraticVariation.P_pos hr))
  apply hY.congr_of_eventuallyEq
  have hpos : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((k,r),M), 0 < q.1.2 :=
    continuousAt_const.eventually_lt continuousAt_fst.snd hr
  have habs : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((k,r),M), |q.2| < q.1.2 :=
    continuousAt_snd.abs.eventually_lt continuousAt_fst.snd hM
  filter_upwards [he,hpos,habs] with q hq hqr hqM
  exact slope_eq hqr hqM hq

end QuinticLienard.QuadraticFit

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
lemma analytic {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) {q : Dom} (hq : 0<q.2) :
    ContDiffAt ℝ ω (Φ a c) q := (Expr a c).eval_analytic (regular hc hq)
lemma local_flow (a : Fin 6 → ℝ) {c : ℝ} (hc : 0<c) (x : State Params) (hx : 0<x.2.1) :
    ∃ f : State Params × ℝ → State Params, ContDiffAt ℝ ω f (x,0) ∧
      ∀ᶠ q in 𝓝 (x,(0:ℝ)), f (q.1,0)=q.1 ∧
        HasDerivAt (fun s => f (q.1,s)) (field (Φ a c) (f q)) q.2 :=
  algebraic_profile_flow (Expr a c) x (regular hc hx)
end QuinticLienard.ScaledProfile

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScaledExpansion
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
open SmoothFlow.AlgebraicExpr
lemma polynomial_taylor (a : Fin 6 → ℝ) (x z : ℝ) :
    poly a z-poly a x=c₁ a x*(z-x)+c₂ a x*(z-x)^2+c₃ a x*(z-x)^3+c₄ a x*(z-x)^4+a 5*(z-x)^5 := by
  dsimp [poly,c₁,c₂,c₃,c₄]
  ring
lemma rational_taylor (b₁ b₂ b₃ b₄ b₅ : ℝ) {x z δ : ℝ} (hx : x≠0) (hxz : z+x≠0)
    (hδ : δ=(z-x)*(z+x)/2) :
    b₁*(z-x)+b₂*(z-x)^2+b₃*(z-x)^3+b₄*(z-x)^4+b₅*(z-x)^5 =
      b₁/x*δ+(2*b₂/x^2-b₁/x^3)*δ^2/2+
      δ^3*(-2*(b₂-b₁/(2*x))*(z+3*x)/(x^2*(z+x)^3)+8*b₃/(z+x)^3+
        16*b₄*δ/(z+x)^4+32*b₅*δ^2/(z+x)^5) := by
  rw [hδ]
  field_simp
  ring
lemma expansion (a : Fin 6 → ℝ) {x z δ : ℝ} (hx : x≠0) (hxz : z+x≠0)
    (hδ : δ=(z-x)*(z+x)/2) :
    poly a z-poly a x=c₁ a x/x*δ+(2*c₂ a x/x^2-c₁ a x/x^3)*δ^2/2+δ^3*rem a x z δ := by
  rw [polynomial_taylor]
  exact rational_taylor _ _ _ _ _ hx hxz hδ
lemma actual_scaling (a : Fin 6 → ℝ) {c u r t : ℝ} (hc : 0<c) (hr : 0<r) (ht : 0<t) :
    poly a (Real.sqrt (2*(c+u^2+r^2*t)))-poly a (Real.sqrt (2*(c+u^2+r^2))) =
      r*Φ a c (((u,r),r^5),t) := by
  let q : Dom := (((u,r),r^5),t)
  let x := (X c).eval q
  let z := (Z c).eval q
  let δ := Δ.eval q
  have hx : 0<x := X_pos hc q
  have hz : 0<z := Z_pos hc ht
  have hxx : x^2=2*(c+u^2+r^2) := by
    dsimp [x,q]
    simp only [X,eval_sqrt,eval_mul,eval_const,eval_add,eval_pow,eval_A,eval_ρ]
    exact Real.sq_sqrt (by positivity)
  have hzz : z^2=2*(c+u^2+r^2*t) := by
    dsimp [z,q]
    simp only [Z,eval_sqrt,eval_mul,eval_const,eval_add,eval_pow,eval_A,eval_ρ,eval_s]
    exact Real.sq_sqrt (by positivity)
  have hδ : δ=(z-x)*(z+x)/2 := by
    have he : δ=r^2*(t-1) := by simp [δ,Δ,q]
    rw [he]
    nlinarith only [hxx,hzz]
  have hE := expansion a hx.ne' (add_pos hz hx).ne' hδ
  have hex : x=Real.sqrt (2*(c+u^2+r^2)) := by simp [x,X,q]
  have hez : z=Real.sqrt (2*(c+u^2+r^2*t)) := by simp [z,Z,q]
  rw [←hex,←hez,hE]
  change _=r*(Expr a c).eval q
  simp only [Expr,K,B,η,eval_add,eval_mul,eval_sub,eval_div,eval_pow,eval_const,
    eval_ρ,eval_s,eval_ε,eval_C₁,eval_C₂,eval_Rem]
  change _=r*(r*(c₁ a x/x)*(t-1)+r^3*(2*c₂ a x/x^2-c₁ a x/x^3)*(t-1)^2/2+
    r^5*((t-1)^3*rem a x z δ))
  have he : δ=r^2*(t-1) := by simp [δ,Δ,q]
  rw [he]
  ring
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

theorem midpoint_analytic {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    ContDiffAt ℝ ω (midpointFamily Φ) ((p,t),h) := by
  obtain ⟨hl,hr⟩ := endpoints Φ hΦ hloc (p := p) hhpos hht
  exact ((hr.add hl).div_const 2).sub
    ((hΦ (p,h) hhpos).comp ((p,t),h) (contDiffAt_fst.fst.prodMk contDiffAt_snd))

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

theorem peak_analytic {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    ContDiffAt ℝ ω (peakAtWidth Φ) ((p,h),r) := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  let W : (P × ℝ) × ℝ → ℝ := fun q => widthFamily Φ ((q.1.1,q.2),q.1.2)
  have hwd : ContDiffAt ℝ ω W ((p,h),t) :=
    (width_analytic Φ hΦ hloc hhpos hs.1).comp ((p,h),t)
      ((contDiffAt_fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)
  have hwtd : DifferentiableAt ℝ (fun s => W ((p,h),s)) t :=
    (hwd.comp t (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hdpos : 0 < deriv (fun s => W ((p,h),s)) t :=
    (peak_width_midpoint_bounds Φ hΦ hloc hhpos hs.1).1
  obtain ⟨Y,hY,hY0,he⟩ := level_hit hwd hwtd.hasDerivAt hs.2 hdpos.ne'
  have hlt : ∀ᶠ q in 𝓝 ((p,h),r), q.1.2 < Y q :=
    continuousAt_fst.snd.eventually_lt hY.continuousAt (by simpa only [hY0] using hs.1)
  have hpos : ∀ᶠ q : (P × ℝ) × ℝ in 𝓝 ((p,h),r), 0 < q.2 :=
    continuousAt_const.eventually_lt continuousAt_snd hr
  have hbase : ∀ᶠ q : (P × ℝ) × ℝ in 𝓝 ((p,h),r), 0<q.1.2 :=
    continuousAt_const.eventually_lt continuousAt_fst.snd hhpos
  apply hY.congr_of_eventuallyEq
  filter_upwards [he,hlt,hpos,hbase] with q hq hltq hposq hbq
  exact peak_eq Φ hΦ hloc hposq hbq hltq hq

theorem midpointAtWidth_analytic {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    ContDiffAt ℝ ω (midpointAtWidth Φ) ((p,h),r) := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  exact (midpoint_analytic Φ hΦ hloc hhpos hs.1).comp ((p,h),r)
    ((contDiffAt_fst.fst.prodMk (peak_analytic Φ hΦ hloc hhpos hr)).prodMk contDiffAt_fst.snd)

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

theorem peak_width_deriv {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    HasDerivAt (fun s => peakAtWidth Φ ((p,h),s))
      (1/deriv (fun t => widthFamily Φ ((p,t),h)) (peakAtWidth Φ ((p,h),r))) r := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  let f : ℝ → ℝ := fun t => widthFamily Φ ((p,t),h)
  let g : ℝ → ℝ := fun s => peakAtWidth Φ ((p,h),s)
  have hf : DifferentiableAt ℝ f t :=
    ((width_analytic Φ hΦ hloc hhpos hs.1).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ g r :=
    ((peak_analytic Φ hΦ hloc hhpos hr).comp r
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have he : (f ∘ g) =ᶠ[𝓝 r] id := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact (peak_spec Φ hΦ hloc hhpos hs).2
  have hc := (hf.hasDerivAt.comp r hg.hasDerivAt).unique
    ((hasDerivAt_id r).congr_of_eventuallyEq he)
  have hp : 0 < deriv f t := (peak_width_midpoint_bounds Φ hΦ hloc hhpos hs.1).1
  have heq : deriv g r = 1/deriv f t := by
    apply (eq_div_iff hp.ne').mpr
    simpa only [mul_comm] using hc
  simpa only [heq] using hg.hasDerivAt

theorem midpoint_width_deriv_abs_lt {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    |deriv (fun s => midpointAtWidth Φ ((p,h),s)) r| < 1 := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  let m : ℝ → ℝ := fun t => midpointFamily Φ ((p,t),h)
  have hm : DifferentiableAt ℝ m t :=
    ((midpoint_analytic Φ hΦ hloc hhpos hs.1).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hc := hm.hasDerivAt.comp r (peak_width_deriv Φ hΦ hloc hhpos hr)
  have hder : deriv (fun s => midpointAtWidth Φ ((p,h),s)) r =
      deriv m t / deriv (fun t => widthFamily Φ ((p,t),h)) t := by
    simpa only [Function.comp_def,mul_one_div,midpointAtWidth,m,t] using! hc.deriv
  rw [hder]
  exact (peak_width_midpoint_bounds Φ hΦ hloc (p := p) hhpos hs.1).2

theorem midpoint_base_deriv {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    HasDerivAt (fun s => midpointFamily Φ ((p,t),s))
      (midpointFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) -
        deriv (fun u => Φ (p,u)) h) h := by
  obtain ⟨hl,hr⟩ := base_derivatives Φ hΦ hloc (p := p) hhpos hht
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  have hdφ := (((hΦ (p,h) hhpos).comp h (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)).hasDerivAt
  have hu := chosen_arch (positive_arch_exists hφ hhpos hht)
  have hlne : Φ (p,h)-lowerFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hu.lower_transverse)
  have hrne : Φ (p,h)-upperFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_lt (sub_neg.mpr hu.upper_transverse)
  have hqne := ne_of_gt (gap_pos Φ hΦ (p := p) hhpos hht)
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

theorem M_analytic {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    ContDiffAt ℝ ω (M Φ p) (h,r) :=
  (midpointAtWidth_analytic Φ hΦ hloc hhpos hr).comp (h,r)
    ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)

theorem v_analytic {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    ContDiffAt ℝ ω (v Φ p) (h,r) := second_contDiffAt (M_analytic Φ hΦ hloc hhpos hr)

theorem M_abs_lt {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) : |M Φ p (h,r)| < r :=
  midpointAtWidth_abs_lt Φ hΦ hloc hhpos hr

theorem v_abs_lt {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) : |v Φ p (h,r)| < 1 := by
  have he := (second_hasDerivAt ((M_analytic Φ hΦ hloc (p := p) (h := h) hhpos hr).differentiableAt
    (by simp))).deriv
  change deriv (fun s => midpointAtWidth Φ ((p,h),s)) r = v Φ p (h,r) at he
  rw [←he]
  exact midpoint_width_deriv_abs_lt Φ hΦ hloc hhpos hr

theorem M_gap_pos {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) : 0 < r^2-(M Φ p (h,r))^2 :=
  sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos hr] using M_abs_lt Φ hΦ hloc (p := p) (h := h) hhpos hr))

theorem midpoint_reparam {p : P} {h t : ℝ} (hhpos : 0<h) (hht : h < t) :
    M Φ p (h,widthFamily Φ ((p,t),h)) = midpointFamily Φ ((p,t),h) := by
  dsimp [M,midpointAtWidth]
  rw [peak_eq Φ hΦ hloc (width_pos Φ hΦ (p := p) hhpos hht) hhpos hht rfl]

theorem transport_midpoint {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    first (M Φ p) (h,r) - r/(r^2-(M Φ p (h,r))^2)*v Φ p (h,r) =
      M Φ p (h,r)/(r^2-(M Φ p (h,r))^2)-deriv (fun u => Φ (p,u)) h := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hM := M_analytic Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hw := width_base_deriv Φ hΦ hloc (p := p) hhpos hs.1
  have hm := midpoint_base_deriv Φ hΦ hloc (p := p) hhpos hs.1
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
    filter_upwards [continuousAt_id.eventually_lt continuousAt_const (peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr).1,
      continuousAt_const.eventually_lt continuousAt_id hhpos] with s hs hsp
    exact midpoint_reparam Φ hΦ hloc hsp hs
  have hcoeff := hcomp.unique (hm.congr_of_eventuallyEq he)
  rw [fderiv_pair] at hcoeff
  change first (M Φ p) (h,r) - r/(r^2-M Φ p (h,r)^2)*second (M Φ p) (h,r) = _
  convert hcoeff using 1
  ring

theorem transport_midpoint_cross {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    (r^2-M Φ p (h,r)^2)*first (M Φ p) (h,r) - r*v Φ p (h,r) =
      M Φ p (h,r) - (r^2-M Φ p (h,r)^2)*deriv (fun u => Φ (p,u)) h := by
  have ht := transport_midpoint Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hq := ne_of_gt (M_gap_pos Φ hΦ hloc (p := p) (h := h) hhpos hr)
  field_simp [hq] at ht
  nlinarith [ht]

theorem transport_v {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    first (v Φ p) (h,r) - r/(r^2-M Φ p (h,r)^2)*second (v Φ p) (h,r) =
      -2*M Φ p (h,r)*r*(1-v Φ p (h,r)^2)/(r^2-M Φ p (h,r)^2)^2 := by
  have hMa := M_analytic Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hMd := second_hasDerivAt (hMa.differentiableAt (by simp))
  change HasDerivAt (fun s => M Φ p (h,s)) (v Φ p (h,r)) r at hMd
  have hvd := second_hasDerivAt ((v_analytic Φ hΦ hloc (p := p) (h := h) hhpos hr).differentiableAt (by simp))
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
    exact transport_midpoint_cross Φ hΦ hloc hhpos hs
  have hc := hleft.unique (hright.congr_of_eventuallyEq he)
  have ht := transport_midpoint_cross Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hq := ne_of_gt (M_gap_pos Φ hΦ hloc (p := p) (h := h) hhpos hr)
  dsimp only [id] at hc
  field_simp [hq]
  linear_combination (r^2-M Φ p (h,r)^2)*hc -
    (2*r-2*M Φ p (h,r)*v Φ p (h,r))*ht

end QuinticLienard.PositiveTransport

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ConditionalFit
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
namespace QuinticLienard.QuadraticFit
open PartialCalculus QuadraticCoordinates ReferenceCharacteristic

lemma slope_curvature_deriv {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    HasDerivAt (fun a => slope ((a,r),M))
      (-Q ((slope ((k,r),M),k),r)/P ((slope ((k,r),M),k),r)) k := by
  have hs := ((slope_analytic hr hM).comp (f := fun a : ℝ => ((a,r),M)) k
    ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hprod := (H_analytic (d := slope ((k,r),M)) (k := k) hr).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f := fun a => ((slope ((a,r),M),a),r)) k
      ((hs.hasDerivAt.prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
  have he := hprod.unique ((hasDerivAt_const k M).congr_of_eventuallyEq
    (Eventually.of_forall (fun a => slope_spec (k := a) hr hM)))
  rw [fderiv_model] at he
  have hP := ne_of_gt (QuadraticVariation.P_pos (d := slope ((k,r),M)) (k := k) hr)
  have hd : deriv (fun a => slope ((a,r),M)) k = -Q ((slope ((k,r),M),k),r)/P ((slope ((k,r),M),k),r) := by
    dsimp only [P,Q,Hr] at hP ⊢
    field_simp [hP]
    simp only [one_mul,zero_mul,add_zero,Function.comp_def] at he
    linarith
  rw [←hd]
  exact hs.hasDerivAt

lemma conditionalV_analytic {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    ContDiffAt ℝ ω conditionalV ((k,r),M) :=
  (Hr_analytic (d := slope ((k,r),M)) (k := k) hr).comp
    (f := fun q : (ℝ × ℝ) × ℝ => ((slope q,q.1.1),q.1.2)) ((k,r),M)
    (((slope_analytic hr hM).prodMk contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)

lemma conditionalV_deriv {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    HasDerivAt (fun a => conditionalV ((a,r),M))
      (G ((slope ((k,r),M),k),r)/P ((slope ((k,r),M),k),r)) k := by
  have h := (Hr_analytic (d := slope ((k,r),M)) (k := k) hr).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f := fun a => ((slope ((a,r),M),a),r)) k
      (((slope_curvature_deriv hr hM).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
  rw [fderiv_model] at h
  have hR := direction_comm (H_analytic (d := slope ((k,r),M)) (k := k) hr) ((1,0),0) ((0,0),1)
  have hS := direction_comm (H_analytic (d := slope ((k,r),M)) (k := k) hr) ((0,1),0) ((0,0),1)
  change direction ((1,0),0) Hr _=R _ at hR
  change direction ((0,1),0) Hr _=S _ at hS
  convert! h using 1
  rw [hR,hS]
  dsimp only [G]
  field_simp [ne_of_gt (QuadraticVariation.P_pos (d := slope ((k,r),M)) (k := k) hr)]
  ring

lemma conditionalV_strictMono {r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    StrictMono (fun k => conditionalV ((k,r),M)) := by
  apply strictMono_of_deriv_pos
  intro k
  rw [(conditionalV_deriv hr hM).deriv]
  exact div_pos (G_pos hr) (QuadraticVariation.P_pos hr)

lemma reference_midpoint_exists {k r A₀ : ℝ} (hr : 0 < r) (hA : |A₀| < 1) :
    ∃ z, A ((z,k),r)=A₀ := by
  have hm : |r*A₀|<r := by rw [abs_mul,abs_of_pos hr]; nlinarith
  obtain ⟨d,hd⟩ := midpoint_exists (k := k) hr hm
  obtain ⟨z,hz⟩ := J_surjective d k hr
  refine ⟨z,?_⟩
  dsimp only [A]
  rw [hz,hd]
  field_simp

lemma reference_midpoint_strictMono (k : ℝ) {r : ℝ} (hr : 0 < r) :
    StrictMono (fun z => A ((z,k),r)) := by
  apply strictMono_of_deriv_pos
  intro z
  rw [(Az_hasDerivAt hr).deriv]
  exact Az_pos hr

lemma label_spec {k r A₀ : ℝ} (hr : 0 < r) (hA : |A₀| < 1) :
    A ((label ((k,r),A₀),k),r)=A₀ := by
  have he := reference_midpoint_exists (k := k) hr hA
  simp only [label,dite_eq_left he]
  exact he.choose_spec

lemma label_eq {k r A₀ z : ℝ} (hr : 0 < r) (hA : |A₀| < 1)
    (hz : A ((z,k),r)=A₀) : label ((k,r),A₀)=z :=
  (reference_midpoint_strictMono k hr).injective ((label_spec hr hA).trans hz.symm)

lemma label_analytic {k r A₀ : ℝ} (hr : 0 < r) (hA : |A₀| < 1) :
    ContDiffAt ℝ ω label ((k,r),A₀) := by
  let z := label ((k,r),A₀)
  let f : (ℝ × ℝ) × ℝ → ℝ := fun q => A ((q.2,q.1.1),q.1.2)
  have hf : ContDiffAt ℝ ω f ((k,r),z) :=
    (A_analytic (q := ((z,k),r)) hr).comp (g := A)
      (f := fun q : (ℝ × ℝ) × ℝ => ((q.2,q.1.1),q.1.2)) ((k,r),z)
      ((contDiffAt_snd.prodMk contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)
  obtain ⟨Y,hY,hY₀,he⟩ := ArcEndpoints.level_hit hf (Az_hasDerivAt hr)
    (label_spec hr hA) (ne_of_gt (Az_pos hr))
  apply hY.congr_of_eventuallyEq
  have hpos : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((k,r),A₀), 0 < q.1.2 :=
    continuousAt_const.eventually_lt continuousAt_fst.snd hr
  have habs : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((k,r),A₀), |q.2| < 1 :=
    continuousAt_snd.abs.eventually_lt continuousAt_const hA
  filter_upwards [he,hpos,habs] with q hq hqr hqA
  exact label_eq hqr hqA hq

lemma label_curvature_deriv {k r A₀ : ℝ} (hr : 0 < r) (hA : |A₀| < 1) :
    HasDerivAt (fun a => label ((a,r),A₀)) (-T ((label ((k,r),A₀),k),r)) k := by
  have hs := ((label_analytic hr hA).comp (f := fun a : ℝ => ((a,r),A₀)) k
    ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hprod := (A_analytic (q := ((label ((k,r),A₀),k),r)) hr).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f := fun a => ((label ((a,r),A₀),a),r)) k
      ((hs.hasDerivAt.prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
  have he := hprod.unique ((hasDerivAt_const k A₀).congr_of_eventuallyEq
    (Eventually.of_forall (fun a => label_spec (k := a) hr hA)))
  rw [fderiv_model] at he
  have hP := ne_of_gt (Az_pos (z := label ((k,r),A₀)) (k := k) hr)
  have hd : deriv (fun a => label ((a,r),A₀)) k = -T ((label ((k,r),A₀),k),r) := by
    dsimp only [T,Az,Ak] at hP ⊢
    field_simp [hP]
    simp only [one_mul,zero_mul,add_zero,Function.comp_def] at he
    linarith
  rw [←hd]
  exact hs.hasDerivAt

lemma T_strictAnti (z k : ℝ) : StrictAntiOn (fun s => T ((z,k),s)) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun s hs => (T_deriv hs).continuousAt.continuousWithinAt)
  intro s hs
  have hs' : 0 < s := interior_subset hs
  rw [(T_deriv (z := z) (k := k) hs').deriv]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (A_gap_pos hs'))
      (QuadraticVariation.Q_pos hs')) (Jz_pos hs'))
    (mul_pos hs' (sq_pos_of_pos (Az_pos hs')))

lemma conditionalA_deriv {k r A₀ s : ℝ} (hr : 0 < r) (hA : |A₀| < 1) (hs : 0 < s) :
    HasDerivAt (fun a => A ((label ((a,r),A₀),a),s))
      (Az ((label ((k,r),A₀),k),s)*(T ((label ((k,r),A₀),k),s)-T ((label ((k,r),A₀),k),r))) k := by
  have h := (A_analytic (q := ((label ((k,r),A₀),k),s)) hs).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f := fun a => ((label ((a,r),A₀),a),s)) k
      (((label_curvature_deriv hr hA).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k s))
  rw [fderiv_model] at h
  convert! h using 1
  have h₁ := ne_of_gt (Az_pos (z := label ((k,r),A₀)) (k := k) hs)
  have h₂ := ne_of_gt (Az_pos (z := label ((k,r),A₀)) (k := k) hr)
  dsimp only [T,Az,Ak] at h₁ h₂ ⊢
  field_simp [h₁,h₂]
  ring

lemma conditionalA_strictMono {r A₀ s : ℝ} (hr : 0 < r) (hA : |A₀| < 1)
    (hs : 0 < s) (hsr : s < r) : StrictMono (fun k => A ((label ((k,r),A₀),k),s)) := by
  apply strictMono_of_deriv_pos
  intro k
  rw [(conditionalA_deriv hr hA hs).deriv]
  exact mul_pos (Az_pos hs) (sub_pos.mpr (T_strictAnti _ _ hs hr hsr))
end QuinticLienard.QuadraticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.HyperbolicCoordinate
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
namespace QuinticLienard

lemma angle_analytic {x : ℝ} (hx : |x| < 1) : ContDiffAt ℝ ω angle x := by
  have h := abs_lt.mp hx
  apply ContDiffAt.div_const
  apply ContDiffAt.sub
  · exact (contDiffAt_const.add contDiffAt_id).log (by dsimp only [id_eq]; linarith [h.1,h.2])
  · exact (contDiffAt_const.sub contDiffAt_id).log (by dsimp only [id_eq]; linarith [h.1,h.2])

lemma angle_deriv {x : ℝ} (hx : |x| < 1) : HasDerivAt angle (1/(1-x^2)) x := by
  have h := abs_lt.mp hx
  have h₁ : 1+x ≠ 0 := by linarith
  have h₂ : 1-x ≠ 0 := by linarith
  have h₃ : 1-x^2 ≠ 0 := by nlinarith [mul_pos (show 0 < 1+x by linarith) (show 0 < 1-x by linarith)]
  convert! (((hasDerivAt_id x).const_add 1).log h₁).sub
    (((hasDerivAt_id x).const_sub 1).log h₂) |>.div_const 2 using 1
  dsimp only [id_eq]
  field_simp [h₁,h₂,h₃]
  ring

lemma angle_strictMono : StrictMonoOn angle (Ioo (-1) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun x hx => (angle_deriv (abs_lt.mpr hx)).continuousAt.continuousWithinAt)
  intro x hx
  have hx' := interior_subset (s := Ioo (-1) 1) hx
  rw [(angle_deriv (abs_lt.mpr hx')).deriv]
  exact div_pos one_pos (by nlinarith [mul_pos (sub_pos.mpr hx'.2) (show 0 < 1+x by linarith [hx'.1])])
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.FitAngles
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

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuinticLienard.ReferenceCharacteristic
open QuadraticCoordinates PartialCalculus
lemma E_analytic {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : ContDiffAt ℝ ω E q := by
  apply ContDiffAt.div
  · exact contDiffAt_const.mul (A_analytic hr)
  · exact contDiffAt_snd.mul (contDiffAt_const.sub ((A_analytic hr).pow 2))
  · exact ne_of_gt (mul_pos hr (A_gap_pos hr))
lemma θ_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => θ ((z,k),s)) (J ((z,k),r)-E ((z,k),r)) r := by
  change HasDerivAt (fun s => angle (A ((z,k),s))) _ r
  have h := (angle_deriv (A_abs_lt (q := ((z,k),r)) hr)).comp (h := fun s => A ((z,k),s)) r (A_deriv (z := z) (k := k) hr)
  convert! h using 1
  dsimp only [E]
  field_simp [ne_of_gt (A_gap_pos (q := ((z,k),r)) hr),ne_of_gt hr]
lemma L_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => L ((z,k),s)) (E ((z,k),r)) r := by
  change HasDerivAt (fun s => angle (D ((z,k),s))) _ r
  have h := (angle_deriv (D_abs_lt (q := ((z,k),r)) hr)).comp (h := fun s => D ((z,k),s)) r (D_deriv' (z := z) (k := k) hr)
  convert! h using 1
  field_simp [ne_of_gt (D_gap_pos (q := ((z,k),r)) hr)]
lemma L_tendsto_zero (z k : ℝ) :
    Tendsto (fun r => L ((z,k),r)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  simpa only [angle_zero,Function.comp_def,L] using ((angle_analytic (by norm_num : |(0:ℝ)|<1)).continuousAt.tendsto.comp (D_tendsto_zero z k))
lemma E_continuousOn (z k : ℝ) : ContinuousOn (fun s => E ((z,k),s)) (Ioi 0) :=
  fun x hs => ((E_analytic (q := ((z,k),x)) hs).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
lemma J_continuousOn (z k : ℝ) : ContinuousOn (fun s => J ((z,k),s)) (Ioi 0) :=
  fun _ hs => (J_deriv hs).continuousAt.continuousWithinAt
lemma integral_E {z k a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, E ((z,k),s))=L ((z,k),b)-L ((z,k),a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    rw [uIcc_of_le hab] at hs
    exact L_deriv (ha.trans_le hs.1)
  · exact ((E_continuousOn z k).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
lemma integral_J {z k a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, J ((z,k),s)) = θ ((z,k),b)-θ ((z,k),a)+(∫ s in a..b, E ((z,k),s)) := by
  have hJ : IntervalIntegrable (fun s => J ((z,k),s)) volume a b := ((J_continuousOn z k).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
  have hE : IntervalIntegrable (fun s => E ((z,k),s)) volume a b := ((E_continuousOn z k).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => θ ((z,k),s)) (f' := fun s => J ((z,k),s)-E ((z,k),s))
    (a := a) (b := b) (fun s hs => θ_deriv (ha.trans_le ((uIcc_of_le hab) ▸ hs).1)) (hJ.sub hE)
  rw [intervalIntegral.integral_sub hJ hE] at he
  linarith
end QuinticLienard.ReferenceCharacteristic

namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates ReferenceCharacteristic
lemma conditionalE_strictMono {r A₀ s : ℝ} (hr : 0 < r) (hA : |A₀| < 1)
    (hs : 0 < s) (hsr : s < r) : StrictMono (fun k => E ((label ((k,r),A₀),k),s)) := by
  apply strictMono_of_deriv_pos
  intro k
  let a' := Az ((label ((k,r),A₀),k),s)*(T ((label ((k,r),A₀),k),s)-T ((label ((k,r),A₀),k),r))
  have hd := conditionalA_deriv (k := k) hr hA hs
  have he : HasDerivAt (fun k => E ((label ((k,r),A₀),k),s))
      (K ((label ((k,r),A₀),k),s)*a') k := by
    convert! (hd.const_mul 2).div (((hd.pow 2).const_sub 1).const_mul s)
      (ne_of_gt (mul_pos hs (A_gap_pos (q := ((label ((k,r),A₀),k),s)) hs))) using 1
    dsimp only [E,K,a',Pi.pow_apply]
    field_simp [ne_of_gt hs,ne_of_gt (A_gap_pos (q := ((label ((k,r),A₀),k),s)) hs)]
    ring
  rw [he.deriv]
  exact mul_pos (K_pos hs) (mul_pos (Az_pos hs) (sub_pos.mpr (T_strictAnti _ _ hs hr hsr)))

lemma L_difference_nonneg {r A₀ k₁ k₂ s : ℝ} (hr : 0 < r) (hA : |A₀| < 1)
    (hk : k₁ ≤ k₂) (hs : 0 < s) (hsr : s ≤ r) :
    0 ≤ L ((label ((k₂,r),A₀),k₂),s)-L ((label ((k₁,r),A₀),k₁),s) := by
  apply monotone_zero_nonneg hs
    (by simpa using (L_tendsto_zero (label ((k₂,r),A₀)) k₂).sub (L_tendsto_zero (label ((k₁,r),A₀)) k₁))
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 s)
    (fun t ht => ((L_deriv ht.1).sub (L_deriv ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => ((L_deriv (interior_subset ht).1).sub (L_deriv (interior_subset ht).1)).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [interior_Ioc] at ht
  rw [((L_deriv (z := label ((k₂,r),A₀)) (k := k₂) ht.1).sub (L_deriv ht.1)).deriv]
  exact sub_nonneg.mpr ((conditionalE_strictMono hr hA ht.1 (ht.2.trans_le hsr)).monotone hk)

lemma integral_E_difference_bound {r A₀ k₁ k₂ a b : ℝ} (hr : 0 < r) (hA : |A₀| < 1)
    (hk : k₁ ≤ k₂) (ha : 0 < a) (hab : a ≤ b) (hbr : b ≤ r) :
    0 ≤ (∫ s in a..b, E ((label ((k₂,r),A₀),k₂),s)-E ((label ((k₁,r),A₀),k₁),s)) ∧
    (∫ s in a..b, E ((label ((k₂,r),A₀),k₂),s)-E ((label ((k₁,r),A₀),k₁),s)) ≤
      L ((label ((k₂,r),A₀),k₂),r)-L ((label ((k₁,r),A₀),k₁),r) := by
  have hE (k : ℝ) : IntervalIntegrable (fun s => E ((label ((k,r),A₀),k),s)) volume a b := ((E_continuousOn (label ((k,r),A₀)) k).mono
    (fun t (ht : t ∈ Icc a b) => ha.trans_le ht.1)).intervalIntegrable_of_Icc hab
  have hmono : MonotoneOn (fun t => L ((label ((k₂,r),A₀),k₂),t)-L ((label ((k₁,r),A₀),k₁),t)) (Ioc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 r)
      (fun t ht => ((L_deriv ht.1).sub (L_deriv ht.1)).continuousAt.continuousWithinAt)
      (fun t ht => ((L_deriv (interior_subset ht).1).sub (L_deriv (interior_subset ht).1)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [interior_Ioc] at ht
    rw [((L_deriv (z := label ((k₂,r),A₀)) (k := k₂) ht.1).sub (L_deriv ht.1)).deriv]
    exact sub_nonneg.mpr ((conditionalE_strictMono hr hA ht.1 ht.2).monotone hk)
  rw [intervalIntegral.integral_sub (hE k₂) (hE k₁),integral_E ha hab,integral_E ha hab]
  have h₁ := hmono ⟨ha,hab.trans hbr⟩ ⟨ha.trans_le hab,hbr⟩ hab
  have h₂ := hmono ⟨ha.trans_le hab,hbr⟩ ⟨hr,le_rfl⟩ hbr
  have h₃ := L_difference_nonneg hr hA hk ha (hab.trans hbr)
  constructor <;> linarith
end QuinticLienard.QuadraticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.MonotoneIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter Metric
open Set Filter
open Set Filter MeasureTheory
open scoped Topology ContDiff

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace QuinticLienard.RealAnalysis

theorem ae_bddAbove_of_integral_bounded {α : Type uα} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {C : ℝ}
    (hf : ∀ n, Integrable (f n) μ)
    (hn : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f n x)
    (hm : ∀ᵐ x ∂μ, Monotone (fun n => f n x))
    (hI : ∀ n, (∫ x, f n x ∂μ) ≤ C) :
    ∀ᵐ x ∂μ, BddAbove (Set.range (fun n => f n x)) := by
  let F : ℕ → α → ℝ≥0∞ := fun n x => ENNReal.ofReal (f n x)
  have hFm : ∀ n, AEMeasurable (F n) μ := fun n => (hf n).aemeasurable.ennreal_ofReal
  have hFM : ∀ᵐ x ∂μ, Monotone (fun n => F n x) := by
    filter_upwards [hm] with x hx n m hnm
    exact ENNReal.ofReal_le_ofReal (hx hnm)
  have hfin : (∫⁻ x, ⨆ n, F n x ∂μ) < ⊤ := by
    rw [lintegral_iSup' hFm hFM]
    apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
    apply iSup_le
    intro n
    rw [←ofReal_integral_eq_lintegral_ofReal (hf n) (hn.mono (fun x hx => hx n))]
    exact ENNReal.ofReal_le_ofReal (hI n)
  filter_upwards [ae_lt_top' (AEMeasurable.iSup hFm) hfin.ne,hn] with x hx hxn
  refine ⟨(⨆ n, F n x).toReal,?_⟩
  rintro y ⟨n,rfl⟩
  have ht := ENNReal.toReal_mono hx.ne (le_iSup (fun n => F n x) n)
  simpa only [F,ENNReal.toReal_ofReal (hxn n)] using ht

end QuinticLienard.RealAnalysis

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AngleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology ENNReal

open Set Filter MeasureTheory
open scoped Topology
namespace QuinticLienard.RealAnalysis
lemma rate_inverse_identity {s a : ℝ} (hs : 0 < s) (ha : |a|<1) :
    1/(1-a)=s*(2*a/(s*(1-a^2)))+1/(1+a) := by
  have ha' := abs_lt.mp ha
  have h₁ : 1-a ≠ 0 := by linarith
  have h₂ : 1+a ≠ 0 := by linarith
  have h₃ : 1-a^2 ≠ 0 := by nlinarith [mul_pos (show 0 < 1-a by linarith) (show 0 < 1+a by linarith)]
  field_simp [ne_of_gt hs,h₁,h₂,h₃]
  ring
lemma bddAbove_angle_of_rate {s : ℝ} (hs : 0 < s) {u : ℕ → ℝ}
    (hu : ∀ n, |u n|<1) (hm : Monotone u)
    (hB : BddAbove (range (fun n => 2*u n/(s*(1-(u n)^2))))) :
    BddAbove (range (fun n => angle (u n))) := by
  obtain ⟨B,hB⟩ := hB
  let C := s*max B 0+1/(1+u 0)+1
  have hlow : 0 < 1+u 0 := by linarith [(abs_lt.mp (hu 0)).1]
  have hC : 1 < C := by
    dsimp only [C]
    have := mul_nonneg hs.le (le_max_right B 0)
    linarith [one_div_pos.mpr hlow]
  have ht : 1-1/C ∈ Ioo (-1:ℝ) 1 := by
    have h₁ := one_div_pos.mpr (show 0 < C by linarith)
    have h₂ := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) hC
    norm_num only [div_one] at h₂
    constructor <;> linarith
  refine ⟨angle (1-1/C),?_⟩
  rintro y ⟨n,rfl⟩
  apply angle_strictMono.monotoneOn (abs_lt.mp (hu n)) ht
  have hrange := hB (mem_range_self n)
  have hi := one_div_le_one_div_of_le hlow (show 1+u 0 ≤ 1+u n by linarith [hm (Nat.zero_le n)])
  have hc : 1/(1-u n) ≤ C := by
    rw [rate_inverse_identity hs (hu n)]
    have hmul := mul_le_mul_of_nonneg_left (hrange.trans (le_max_left B 0)) hs.le
    dsimp only [C]
    linarith
  have hden : 0 < 1-u n := by linarith [(abs_lt.mp (hu n)).2]
  have hc' : 1/C ≤ 1-u n := by
    have hprod := (div_le_iff₀ hden).mp hc
    apply (div_le_iff₀ (show 0 < C by linarith)).mpr
    nlinarith
  linarith

lemma exists_mem_Ioo_of_ae {l u a b : ℝ} {p : ℝ → Prop}
    (hab : a < b) (hsub : Ioo a b ⊆ Ioc l u)
    (hp : ∀ᵐ s ∂volume.restrict (Ioc l u), p s) : ∃ s ∈ Ioo a b, p s := by
  apply Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioo a b) ≠ 0 by rw [Real.volume_Ioo]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)))
  exact hp.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))

lemma uniform_integral_pos_of_reciprocal {a b B : ℝ} (hab : a < b) {g : ℕ → ℝ → ℝ}
    (hg : ∀ n, ContinuousOn (g n) (Icc a b))
    (hp : ∀ n x, x ∈ Icc a b → 0 < g n x)
    (hB : ∀ n, (∫ x in a..b, 1/(g n x)) ≤ B) :
    ∃ ε > 0, ∀ n, ε ≤ ∫ x in a..b, g n x := by
  have hi (n : ℕ) : IntervalIntegrable (fun x => 1/(g n x)) volume a b :=
    (continuousOn_const.div (hg n) (fun x hx => ne_of_gt (hp n x hx))).intervalIntegrable_of_Icc hab.le
  have hB0 : 0 ≤ B := (intervalIntegral.integral_nonneg hab.le
    (fun x hx => le_of_lt (one_div_pos.mpr (hp 0 x hx)))).trans (hB 0)
  let δ := (b-a)/(B+1)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hab) (by linarith)
  have hδB : δ*B ≤ b-a := by
    have he : δ*(B+1)=b-a := by dsimp only [δ]; field_simp
    nlinarith
  refine ⟨δ*(b-a),mul_pos hδ (sub_pos.mpr hab),?_⟩
  intro n
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) : 2*δ ≤ g n x+δ^2*(1/g n x) := by
    apply (mul_le_mul_iff_left₀ (hp n x hx)).mp
    have he : (g n x+δ^2*(1/g n x))*g n x=(g n x)^2+δ^2 := by
      field_simp [ne_of_gt (hp n x hx)]
    rw [he]
    nlinarith [sq_nonneg (g n x-δ)]
  have hineq := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
    (((hg n).intervalIntegrable_of_Icc hab.le).add ((hi n).const_mul (δ^2))) hpoint
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add
    ((hg n).intervalIntegrable_of_Icc hab.le) ((hi n).const_mul (δ^2)),intervalIntegral.integral_const_mul] at hineq
  simp only [smul_eq_mul] at hineq
  have hbound := mul_le_mul_of_nonneg_left (hB n) (sq_nonneg δ)
  have hbound' := mul_le_mul_of_nonneg_left hδB hδ.le
  nlinarith
end QuinticLienard.RealAnalysis

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.FitProperness
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
open Set Filter
open scoped Topology ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates ReferenceCharacteristic RealAnalysis

lemma seqA_abs {r M s : ℝ} (n : ℕ) (hs : 0 < s) : |seqA r M n s|<1 := A_abs_lt hs
lemma seqA_mono {r M s : ℝ} (hr : 0 < r) (hM : |M|<1) (hs : 0 < s) (hsr : s < r) :
    Monotone (fun n => seqA r M n s) := by
  intro n m hnm
  exact (conditionalA_strictMono hr hM hs hsr).monotone (by exact_mod_cast Nat.add_le_add_right hnm 1)
lemma seqE_mono {r M s : ℝ} (hr : 0 < r) (hM : |M|<1) (hs : 0 < s) (hsr : s < r) :
    Monotone (fun n => seqE r M n s) := by
  intro n m hnm
  exact (conditionalE_strictMono hr hM hs hsr).monotone (by exact_mod_cast Nat.add_le_add_right hnm 1)
lemma seqθ_lower {r M s : ℝ} (hr : 0 < r) (hM : |M|<1) (hs : 0 < s) (hsr : s < r) (n : ℕ) :
    seqθ r M 0 s ≤ seqθ r M n s :=
  angle_strictMono.monotoneOn (abs_lt.mp (seqA_abs 0 hs)) (abs_lt.mp (seqA_abs n hs))
    (seqA_mono hr hM hs hsr (Nat.zero_le n))
lemma seqE_continuousOn (r M : ℝ) (n : ℕ) : ContinuousOn (seqE r M n) (Ioi 0) := E_continuousOn _ _
lemma seqJ_continuousOn (r M : ℝ) (n : ℕ) : ContinuousOn (seqJ r M n) (Ioi 0) := J_continuousOn _ _
lemma seqA_continuousOn (r M : ℝ) (n : ℕ) : ContinuousOn (seqA r M n) (Ioi 0) := by
  intro s hs
  exact (A_deriv (z := label ((((n:ℝ)+1),r),M)) (k := (n:ℝ)+1) hs).continuousAt.continuousWithinAt
lemma seqg_continuousOn (r M : ℝ) (n : ℕ) : ContinuousOn (seqg r M n) (Ioi 0) :=
  continuousOn_id.mul (continuousOn_const.sub ((seqA_continuousOn r M n).pow 2))
lemma seqg_pos {r M s : ℝ} (n : ℕ) (hs : 0 < s) : 0 < seqg r M n s :=
  mul_pos hs (A_gap_pos hs)
lemma seqE_integrable {r M a b : ℝ} (n : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (seqE r M n) volume a b :=
  ((seqE_continuousOn r M n).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
lemma seqJ_integrable {r M a b : ℝ} (n : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (seqJ r M n) volume a b :=
  ((seqJ_continuousOn r M n).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
lemma seqE_integral_bounds {r M C a b : ℝ} (hr : 0 < r) (hM : |M|<1)
    (hC : ∀ n, seqL r M n r ≤ C) (ha : 0 < a) (hab : a ≤ b) (hbr : b ≤ r) (n : ℕ) :
    (∫ s in a..b, seqE r M 0 s) ≤ (∫ s in a..b, seqE r M n s) ∧
    (∫ s in a..b, seqE r M n s) ≤ (∫ s in a..b, seqE r M 0 s)+C-seqL r M 0 r := by
  have h := integral_E_difference_bound (k₁ := ((0:ℕ):ℝ)+1) (k₂ := (n:ℝ)+1) hr hM
    (by simp only [Nat.cast_zero]; linarith [Nat.cast_nonneg (α := ℝ) n]) ha hab hbr
  change 0 ≤ (∫ s in a..b, seqE r M n s-seqE r M 0 s) ∧
    (∫ s in a..b, seqE r M n s-seqE r M 0 s) ≤ seqL r M n r-seqL r M 0 r at h
  rw [intervalIntegral.integral_sub (seqE_integrable n ha hab) (seqE_integrable 0 ha hab)] at h
  constructor <;> linarith [h.1,h.2,hC n]

lemma seqθ_ae_bdd {r M C a b : ℝ} (hr : 0 < r) (hM : |M|<1)
    (hC : ∀ n, seqL r M n r ≤ C) (ha : 0 < a) (hab : a ≤ b) (hbr : b < r) :
    ∀ᵐ s ∂volume.restrict (Ioc a b), BddAbove (range (fun n => seqθ r M n s)) := by
  have hmem : ∀ᵐ s ∂volume.restrict (Ioc a b), s ∈ Ioc a b := ae_restrict_mem measurableSet_Ioc
  have hbd := ae_bddAbove_of_integral_bounded
    (μ := volume.restrict (Ioc a b)) (f := fun n s => seqE r M n s-seqE r M 0 s)
    (C := C-seqL r M 0 r)
    (fun n => ((seqE_integrable n ha hab).sub (seqE_integrable 0 ha hab)).1)
    (hmem.mono (fun s hs n => sub_nonneg.mpr (seqE_mono hr hM (ha.trans hs.1) (hs.2.trans_lt hbr) (Nat.zero_le n))))
    (hmem.mono (fun s hs n m hnm => sub_le_sub_right (seqE_mono hr hM (ha.trans hs.1) (hs.2.trans_lt hbr) hnm) _))
    (by intro n; rw [←intervalIntegral.integral_of_le hab,intervalIntegral.integral_sub
        (seqE_integrable n ha hab) (seqE_integrable 0 ha hab)]
        have h := (seqE_integral_bounds hr hM hC ha hab hbr.le n).2
        linarith)
  filter_upwards [hbd,hmem] with s hs hsm
  have hrates : BddAbove (range (fun n => 2*seqA r M n s/(s*(1-(seqA r M n s)^2)))) := by
    obtain ⟨B,hB⟩ := hs
    refine ⟨B+seqE r M 0 s,?_⟩
    rintro y ⟨n,rfl⟩
    have h := hB (mem_range_self n)
    change 2*seqA r M n s/(s*(1-(seqA r M n s)^2))-seqE r M 0 s ≤ B at h
    linarith
  exact bddAbove_angle_of_rate (ha.trans hsm.1) (fun n => seqA_abs n (ha.trans hsm.1))
    (seqA_mono hr hM (ha.trans hsm.1) (hsm.2.trans_lt hbr)) hrates

lemma seqg_uniform_integral_pos {r M C a b : ℝ} (hr : 0 < r) (hM : |M|<1)
    (hC : ∀ n, seqL r M n r ≤ C) (ha : 0 < a) (hab : a < b) (hbr : b < r) :
    ∃ ε > 0, ∀ n, ε ≤ ∫ s in a..b, seqg r M n s := by
  let q : ℝ → ℝ := fun s => 1/(s*(1+seqA r M 0 s))
  have hq : ContinuousOn q (Icc a b) := by
    apply continuousOn_const.div
      (continuousOn_id.mul (continuousOn_const.add ((seqA_continuousOn r M 0).mono (fun _ hs => ha.trans_le hs.1))))
    intro s hs
    apply ne_of_gt (mul_pos (ha.trans_le hs.1) _)
    change 0 < 1+seqA r M 0 s
    linarith [(abs_lt.mp (seqA_abs (r := r) (M := M) 0 (ha.trans_le hs.1))).1]
  apply uniform_integral_pos_of_reciprocal hab
    (fun n => (seqg_continuousOn r M n).mono (fun _ hs => ha.trans_le hs.1))
    (fun n s hs => seqg_pos n (ha.trans_le hs.1))
    (B := ((∫ s in a..b, seqE r M 0 s)+C-seqL r M 0 r)/2+(∫ s in a..b, q s))
  intro n
  have h₁ := seqE_integrable (r := r) (M := M) n ha hab.le
  have h₂ : IntervalIntegrable q volume a b := hq.intervalIntegrable_of_Icc hab.le
  have hg : IntervalIntegrable (fun s => 1/seqg r M n s) volume a b :=
    (continuousOn_const.div ((seqg_continuousOn r M n).mono (fun _ hs => ha.trans_le hs.1))
      (fun s hs => ne_of_gt (seqg_pos n (ha.trans_le hs.1)))).intervalIntegrable_of_Icc hab.le
  have hpoint (s : ℝ) (hs : s ∈ Icc a b) : 1/seqg r M n s ≤ seqE r M n s/2+q s := by
    have hs0 := ha.trans_le hs.1
    have hin : 0 < 1+seqA r M n s := by linarith [(abs_lt.mp (seqA_abs (r := r) (M := M) n hs0)).1]
    have hi0 : 0 < 1+seqA r M 0 s := by linarith [(abs_lt.mp (seqA_abs (r := r) (M := M) 0 hs0)).1]
    have hgap : 0 < 1-(seqA r M n s)^2 := A_gap_pos hs0
    have hid : 1/seqg r M n s=seqE r M n s/2+1/(s*(1+seqA r M n s)) := by
      change 1/(s*(1-(seqA r M n s)^2))= (2*seqA r M n s/(s*(1-(seqA r M n s)^2)))/2+1/(s*(1+seqA r M n s))
      field_simp [ne_of_gt hs0,ne_of_gt hin,ne_of_gt hgap]
      ring
    rw [hid]
    have hinv : 1/(s*(1+seqA r M n s)) ≤ 1/(s*(1+seqA r M 0 s)) := one_div_le_one_div_of_le (mul_pos hs0 hi0)
      (mul_le_mul_of_nonneg_left (by linarith [seqA_mono hr hM hs0 (hs.2.trans_lt hbr) (Nat.zero_le n)]) hs0.le)
    dsimp only [q]
    linarith
  have hle := intervalIntegral.integral_mono_on hab.le hg ((h₁.div_const 2).add h₂) hpoint
  rw [intervalIntegral.integral_add (h₁.div_const 2) h₂,intervalIntegral.integral_div] at hle
  linarith [(seqE_integral_bounds hr hM hC ha hab.le hbr.le n).2]

lemma seqJ_drop {r M a b : ℝ} (n : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    seqJ r M n a-seqJ r M n b=((n:ℝ)+1)*(∫ s in a..b, seqg r M n s) := by
  have hg : IntervalIntegrable (seqg r M n) volume a b :=
    ((seqg_continuousOn r M n).mono (fun _ hs => ha.trans_le hs.1)).intervalIntegrable_of_Icc hab
  have hd (s : ℝ) (hs : s ∈ uIcc a b) : HasDerivAt (seqJ r M n) (-((n:ℝ)+1)*seqg r M n s) s := by
    have h := J_deriv (z := label ((((n:ℝ)+1),r),M)) (k := (n:ℝ)+1) (ha.trans_le (((uIcc_of_le hab) ▸ hs).1))
    convert! h using 1
    dsimp only [seqg,seqA]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hg.const_mul (-((n:ℝ)+1)))
  rw [intervalIntegral.integral_const_mul] at he
  linarith

theorem seqL_not_bddAbove {r M : ℝ} (hr : 0 < r) (hM : |M|<1) :
    ¬ BddAbove (range (fun n => seqL r M n r)) := by
  rintro ⟨_root_.OAI.QuinticLienard.ReferenceCharacteristic.C,hC⟩
  have hCn (n : ℕ) : seqL r M n r ≤ _root_.OAI.QuinticLienard.ReferenceCharacteristic.C := hC (mem_range_self n)
  have hgood := seqθ_ae_bdd hr hM hCn (show 0<r/4 by positivity)
    (show r/4 ≤ 3*r/4 by linarith) (show 3*r/4<r by linarith)
  obtain ⟨b,hb,hθb⟩ := exists_mem_Ioo_of_ae (a := r/3) (b := 5*r/12)
    (by linarith) (by intro s hs; constructor <;> linarith [hs.1,hs.2]) hgood
  obtain ⟨c,hc,hθc⟩ := exists_mem_Ioo_of_ae (a := 7*r/12) (b := 2*r/3)
    (by linarith) (by intro s hs; constructor <;> linarith [hs.1,hs.2]) hgood
  obtain ⟨Bθb,hBθb⟩ := hθb
  obtain ⟨Bθc,hBθc⟩ := hθc
  let a := r/4
  let d := 3*r/4
  have ha : 0<a := by dsimp [a]; positivity
  have hab : a<b := by dsimp [a]; linarith [hb.1]
  have hbc : b<c := by linarith [hb.2,hc.1]
  have hcd : c<d := by dsimp [d]; linarith [hc.2]
  have hdr : d<r := by dsimp [d]; linarith
  let U := Bθb-seqθ r M 0 a+(∫ s in a..b, seqE r M 0 s)+_root_.OAI.QuinticLienard.ReferenceCharacteristic.C-seqL r M 0 r
  let V := seqθ r M 0 d-Bθc+(∫ s in c..d, seqE r M 0 s)
  have hupper (n : ℕ) : seqJ r M n b ≤ U/(b-a) := by
    have he : (∫ s in a..b, seqJ r M n s)=seqθ r M n b-seqθ r M n a+(∫ s in a..b, seqE r M n s) := integral_J ha hab.le
    have hI := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
      (seqJ_integrable n ha hab.le) (fun s hs =>
        (J_strictAnti (z := label ((((n:ℝ)+1),r),M)) (by positivity : (0:ℝ)<(n:ℝ)+1)).antitoneOn
          (ha.trans_le hs.1) (ha.trans hab) hs.2)
    rw [intervalIntegral.integral_const] at hI
    simp only [smul_eq_mul] at hI
    change (b-a)*seqJ r M n b ≤ (∫ s in a..b, seqJ r M n s) at hI
    apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
    have hLow := seqθ_lower hr hM ha (hab.trans (hbc.trans (hcd.trans hdr))) n
    have hHigh := hBθb (mem_range_self n)
    have hEB := (seqE_integral_bounds hr hM hCn ha hab.le (hbc.trans (hcd.trans hdr)).le n).2
    dsimp only [U]
    nlinarith
  have hlower (n : ℕ) : V/(d-c) ≤ seqJ r M n c := by
    have hc0 := ha.trans (hab.trans hbc)
    have he : (∫ s in c..d, seqJ r M n s)=seqθ r M n d-seqθ r M n c+(∫ s in c..d, seqE r M n s) := integral_J hc0 hcd.le
    have hI := intervalIntegral.integral_mono_on hcd.le (seqJ_integrable n hc0 hcd.le)
      intervalIntegrable_const (fun s hs =>
        (J_strictAnti (z := label ((((n:ℝ)+1),r),M)) (by positivity : (0:ℝ)<(n:ℝ)+1)).antitoneOn
          hc0 (hc0.trans_le hs.1) hs.1)
    rw [intervalIntegral.integral_const] at hI
    simp only [smul_eq_mul] at hI
    change (∫ s in c..d, seqJ r M n s) ≤ (d-c)*seqJ r M n c at hI
    apply (div_le_iff₀ (sub_pos.mpr hcd)).mpr
    have hLow := seqθ_lower hr hM (hc0.trans hcd) hdr n
    have hHigh := hBθc (mem_range_self n)
    have hEB := (seqE_integral_bounds hr hM hCn hc0 hcd.le hdr.le n).1
    dsimp only [V]
    nlinarith
  obtain ⟨ε,hε,hbound⟩ := seqg_uniform_integral_pos hr hM hCn (ha.trans hab) hbc (hcd.trans hdr)
  obtain ⟨n,hn⟩ := exists_nat_gt ((U/(b-a)-V/(d-c))/ε)
  have hmul := mul_le_mul_of_nonneg_left (hbound n) (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
  rw [←seqJ_drop n (ha.trans hab) hbc.le] at hmul
  have hn' := (div_lt_iff₀ hε).mp hn
  nlinarith [hupper n,hlower n]
end QuinticLienard.QuadraticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.GlobalFit
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
open Set Filter
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates ReferenceCharacteristic

lemma label_model_slope {r M k : ℝ} (hr : 0 < r) (hM : |M|<r) :
    J ((label ((k,r),M/r),k),r)=slope ((k,r),M) := by
  have hA : |M/r|<1 := by rw [abs_div,abs_of_pos hr]; exact (div_lt_one hr).mpr hM
  apply (slope_eq hr hM _).symm
  have hh := label_spec (k := k) hr hA
  change H ((J ((label ((k,r),M/r),k),r),k),r)/r=M/r at hh
  exact (div_left_inj' (ne_of_gt hr)).mp hh

lemma label_L_eq {r M k : ℝ} (hr : 0 < r) (hM : |M|<r) :
    L ((label ((k,r),M/r),k),r)=angle (conditionalV ((k,r),M)) := by
  dsimp only [L,D,conditionalV]
  rw [label_model_slope hr hM]

lemma slope_reflection {r M k : ℝ} (hr : 0 < r) (hM : |M|<r) :
    slope ((-k,r),-M)=-slope ((k,r),M) := by
  apply slope_eq hr (by simpa only [abs_neg] using hM)
  rw [reflection _ _ hr,slope_spec hr hM]

lemma Hr_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    Hr ((-d,-k),r)=-Hr ((d,k),r) := by
  apply (Hr_hasDerivAt hr).unique
  exact (Hr_hasDerivAt hr).neg.congr_of_eventuallyEq
    ((eventually_gt_nhds hr).mono (fun s hs => reflection d k hs))

lemma conditionalV_reflection {r M k : ℝ} (hr : 0 < r) (hM : |M|<r) :
    conditionalV ((-k,r),-M)=-conditionalV ((k,r),M) := by
  dsimp only [conditionalV]
  rw [slope_reflection hr hM,Hr_reflection _ _ hr]

lemma conditionalV_gt {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    ∃ k, v < conditionalV ((k,r),M) := by
  by_contra! h
  apply seqL_not_bddAbove hr (show |M/r|<1 by rw [abs_div,abs_of_pos hr]; exact (div_lt_one hr).mpr hM)
  refine ⟨angle v,?_⟩
  rintro y ⟨n,rfl⟩
  change L ((label ((((n:ℝ)+1,r),M/r)),(n:ℝ)+1),r) ≤ angle v
  rw [label_L_eq hr hM]
  apply angle_strictMono.monotoneOn (abs_lt.mp (Hr_abs_lt hr)) (abs_lt.mp hv) (h _)

lemma conditionalV_lt {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    ∃ k, conditionalV ((k,r),M)<v := by
  obtain ⟨k,hk⟩ := conditionalV_gt (M := -M) (v := -v) hr (by simpa only [abs_neg] using hM) (by simpa only [abs_neg] using hv)
  refine ⟨-k,?_⟩
  have he := conditionalV_reflection (k := k) (M := -M) hr (by simpa only [abs_neg] using hM)
  simp only [neg_neg] at he
  rw [he]
  linarith

lemma conditionalV_exists {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    ∃ k, conditionalV ((k,r),M)=v := by
  obtain ⟨a,ha⟩ := conditionalV_lt hr hM hv
  obtain ⟨b,hb⟩ := conditionalV_gt hr hM hv
  have hab : a < b := (conditionalV_strictMono hr hM).lt_iff_lt.mp (ha.trans hb)
  have hc : Continuous (fun k => conditionalV ((k,r),M)) := by
    apply continuous_iff_continuousAt.mpr
    intro k
    exact ((conditionalV_analytic hr hM).comp (f := fun k : ℝ => ((k,r),M)) k
      ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)).continuousAt
  obtain ⟨k,_,hk⟩ := intermediate_value_Icc hab.le hc.continuousOn ⟨ha.le,hb.le⟩
  exact ⟨k,hk⟩

lemma fitK_spec {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    conditionalV ((fitK ((r,M),v),r),M)=v := by
  have he := conditionalV_exists hr hM hv
  simp only [fitK,dite_eq_left he]
  exact he.choose_spec
lemma fit_spec {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    H ((fitD ((r,M),v),fitK ((r,M),v)),r)=M ∧
    Hr ((fitD ((r,M),v),fitK ((r,M),v)),r)=v :=
  ⟨slope_spec hr hM,fitK_spec hr hM hv⟩
lemma fitK_eq {r M v k : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1)
    (hk : conditionalV ((k,r),M)=v) : fitK ((r,M),v)=k :=
  (conditionalV_strictMono hr hM).injective ((fitK_spec hr hM hv).trans hk.symm)
lemma fit_unique {r M v d k : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1)
    (hd : H ((d,k),r)=M) (hk : Hr ((d,k),r)=v) :
    fitD ((r,M),v)=d ∧ fitK ((r,M),v)=k := by
  have hs := slope_eq (k := k) hr hM hd
  have he : conditionalV ((k,r),M)=v := by dsimp only [conditionalV]; rw [hs,hk]
  have hfit := fitK_eq hr hM hv he
  refine ⟨?_,hfit⟩
  dsimp only [fitD]
  rw [hfit,hs]

lemma fitK_analytic {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    ContDiffAt ℝ ω fitK ((r,M),v) := by
  let k := fitK ((r,M),v)
  let f : (ℝ × ℝ) × ℝ → ℝ := fun q => conditionalV ((q.2,q.1.1),q.1.2)
  have hf : ContDiffAt ℝ ω f ((r,M),k) :=
    (conditionalV_analytic (k := k) hr hM).comp
      (f := fun q : (ℝ × ℝ) × ℝ => ((q.2,q.1.1),q.1.2)) ((r,M),k)
      ((contDiffAt_snd.prodMk contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)
  obtain ⟨Y,hY,hY₀,he⟩ := ArcEndpoints.level_hit hf (conditionalV_deriv hr hM)
    (fitK_spec hr hM hv) (ne_of_gt (div_pos (G_pos hr) (QuadraticVariation.P_pos hr)))
  apply hY.congr_of_eventuallyEq
  have hp : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((r,M),v), 0 < q.1.1 :=
    continuousAt_const.eventually_lt continuousAt_fst.fst hr
  have hm : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((r,M),v), |q.1.2|<q.1.1 :=
    continuousAt_fst.snd.abs.eventually_lt continuousAt_fst.fst hM
  have hv' : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((r,M),v), |q.2|<1 :=
    continuousAt_snd.abs.eventually_lt continuousAt_const hv
  filter_upwards [he,hp,hm,hv'] with q hq hqr hqM hqv
  exact fitK_eq hqr hqM hqv hq
lemma fitD_analytic {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    ContDiffAt ℝ ω fitD ((r,M),v) :=
  (slope_analytic (k := fitK ((r,M),v)) hr hM).comp
    (f := fun q : (ℝ × ℝ) × ℝ => ((fitK q,q.1.1),q.1.2)) ((r,M),v)
    (((fitK_analytic hr hM hv).prodMk contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)
end QuinticLienard.QuadraticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveSymmetries
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
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ArchSymmetries
open ScalarArcs
lemma IsArch.affineOn {φ ψ u : ℝ → ℝ} {h t a b c H C : ℝ}
    (hu : IsArch φ u h t a b) (hht : h<t) (hc : 0<c)
    (he : ∀ x ∈ Icc h t, ψ (H+c^2*x)=C+c*φ x) :
    IsArch ψ (fun y => H+c^2*u ((y-C)/c))
      (H+c^2*h) (H+c^2*t) (C+c*a) (C+c*b) := by
  let χ : ℝ → ℝ := fun x => C+c*φ ((x-H)/c^2)
  have hc2 : c^2≠0 := pow_ne_zero 2 hc.ne'
  have hx (x : ℝ) : (H+c^2*x-H)/c^2=x := by field_simp; ring
  have ha := IsArch.affine hu (ψ:=χ) (H:=H) (C:=C) hc (by intro x; dsimp [χ]; rw [hx])
  apply ha.congr_profile (by nlinarith [sq_pos_of_pos hc])
  intro x hx
  have hm : (x-H)/c^2 ∈ Icc h t := by
    constructor
    · exact (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith [hx.1])
    · exact (div_le_iff₀ (sq_pos_of_pos hc)).mpr (by nlinarith [hx.2])
  have hid : H+c^2*((x-H)/c^2)=x := by field_simp; ring
  simpa only [hid] using he ((x-H)/c^2) hm
end QuinticLienard.ArchSymmetries

namespace QuinticLienard.PositiveWidth
open ScalarArcs ArcFamilies
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc
omit hloc [FiniteDimensional ℝ P] in
lemma profile_C1 (p : P) : ContDiffOn ℝ 1 (fun x => Φ (p,x)) (Ioi 0) := by
  intro x hx
  exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
lemma midpoint_of_arch {p : P} {h t a b r : ℝ} {u : ℝ → ℝ}
    (hu : IsArch (fun x => Φ (p,x)) u h t a b) (hh : 0<h) (hht : h<t)
    (hr : 0<r) (hw : (b-a)/2=r) :
    midpointAtWidth Φ ((p,h),r)=(b+a)/2-Φ (p,h) := by
  have hc := canonical_of_positive_arch hu (profile_C1 Φ hΦ p) hh hht
  have hwidth : widthFamily Φ ((p,t),h)=r := by
    dsimp [widthFamily,width]
    rw [hc.1,hc.2]
    exact hw
  rw [midpointAtWidth,peak_eq Φ hΦ hloc hr hh hht hwidth]
  dsimp [midpointFamily,ScalarArcs.midpoint]
  rw [hc.1,hc.2]

lemma midpoint_quadratic {p : P} {h r d k : ℝ} (hh : 0<h) (hr : 0<r)
    (he : ∀ x, Φ (p,h+x)=Φ (p,h)+d*x+k*x^2/2) :
    midpointAtWidth Φ ((p,h),r)=QuadraticCoordinates.H ((d,k),r) := by
  let T := WidthCoordinates.peakAtWidth PolynomialModel.profile ((((d,k),0),r))
  have hs := WidthCoordinates.peak_spec PolynomialModel.profile PolynomialModel.profile_contDiff
    PolynomialModel.model_local_flow (p:=(d,k)) (h:=0) hr
  have ha := chosen_arch (entire_arch_exists
    (ArchSymmetries.profile_C1 PolynomialModel.profile PolynomialModel.profile_contDiff (d,k)) hs.1)
  have hb := ArchSymmetries.IsArch.affine ha (ψ:=fun x => Φ (p,x)) (H:=h) (C:=Φ (p,h))
    (by norm_num : (0:ℝ)<1) (by intro x; simpa only [one_pow,one_mul,PolynomialModel.profile] using (he x).trans (by ring))
  simp only [one_pow,one_mul,add_zero] at hb
  have hw : ((Φ (p,h)+upper (fun x => PolynomialModel.profile ((d,k),x)) 0 T)-
      (Φ (p,h)+lower (fun x => PolynomialModel.profile ((d,k),x)) 0 T))/2=r := by
    have hh := hs.2
    change (upper (fun x => PolynomialModel.profile ((d,k),x)) 0 T-
      lower (fun x => PolynomialModel.profile ((d,k),x)) 0 T)/2=r at hh
    linarith only [hh]
  have hm := midpoint_of_arch Φ hΦ hloc hb hh (by change h<h+T; linarith [hs.1]) hr hw
  rw [hm]
  dsimp [QuadraticCoordinates.H,WidthCoordinates.midpointAtWidth,WidthCoordinates.midpointFamily,
    ScalarArcs.midpoint,T,PolynomialModel.profile]
  ring
end QuinticLienard.PositiveWidth

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.FitSmall
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
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus QuadraticVariation
lemma Hr_zero {r : ℝ} (hr : 0<r) : Hr ((0,0),r)=0 := by
  apply (Hr_hasDerivAt hr).unique ((hasDerivAt_const r (0:ℝ)).congr_of_eventuallyEq ?_)
  filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
  exact (zero_data hs).2
end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveFit
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
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveFit
open ScalarArcs ArcFamilies PositiveWidth PartialCalculus QuadraticFit
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc
lemma m_analytic {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    ContDiffAt ℝ ω (m Φ h) (p,r) :=
  (midpointAtWidth_analytic Φ hΦ hloc hh hr).comp (p,r)
    ((contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd)
lemma n_analytic {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    ContDiffAt ℝ ω (n Φ h) (p,r) := direction_contDiffAt (m_analytic Φ hΦ hloc hh hr) _
lemma m_hasDerivAt {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    HasDerivAt (fun s => m Φ h (p,s)) (n Φ h (p,r)) r := by
  exact ((m_analytic Φ hΦ hloc (p:=p) hh hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_const r p).prodMk (hasDerivAt_id r))
lemma m_abs_lt {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) : |m Φ h (p,r)|<r :=
  midpointAtWidth_abs_lt Φ hΦ hloc hh hr
lemma n_abs_lt {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) : |n Φ h (p,r)|<1 := by
  rw [←(m_hasDerivAt Φ hΦ hloc hh hr).deriv]
  exact PositiveTransport.midpoint_width_deriv_abs_lt Φ hΦ hloc hh hr
lemma d_analytic {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    ContDiffAt ℝ ω (d Φ h r) p :=
  (fitD_analytic hr (m_abs_lt Φ hΦ hloc hh hr) (n_abs_lt Φ hΦ hloc hh hr)).comp p
    ((contDiffAt_const.prodMk ((m_analytic Φ hΦ hloc hh hr).comp p
      (contDiffAt_id.prodMk contDiffAt_const))).prodMk
      ((n_analytic Φ hΦ hloc hh hr).comp p (contDiffAt_id.prodMk contDiffAt_const)))
lemma k_analytic {p : P} {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    ContDiffAt ℝ ω (k Φ h r) p :=
  (fitK_analytic hr (m_abs_lt Φ hΦ hloc hh hr) (n_abs_lt Φ hΦ hloc hh hr)).comp p
    ((contDiffAt_const.prodMk ((m_analytic Φ hΦ hloc hh hr).comp p
      (contDiffAt_id.prodMk contDiffAt_const))).prodMk
      ((n_analytic Φ hΦ hloc hh hr).comp p (contDiffAt_id.prodMk contDiffAt_const)))
lemma fit_quadratic {p : P} {h r D K : ℝ} (hh : 0<h) (hr : 0<r)
    (he : ∀ x, Φ (p,h+x)=Φ (p,h)+D*x+K*x^2/2) :
    d Φ h r p=D ∧ k Φ h r p=K := by
  have hm : ∀ s, 0<s → m Φ h (p,s)=QuadraticCoordinates.H ((D,K),s) :=
    fun s hs => midpoint_quadratic Φ hΦ hloc hh hs he
  have hn : n Φ h (p,r)=QuadraticCoordinates.Hr ((D,K),r) := by
    apply (m_hasDerivAt Φ hΦ hloc hh hr).unique
    apply (QuadraticCoordinates.Hr_hasDerivAt hr).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact hm s hs
  exact fit_unique hr (m_abs_lt Φ hΦ hloc hh hr) (n_abs_lt Φ hΦ hloc hh hr) (hm r hr).symm hn.symm

end QuinticLienard.PositiveFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScaledCoefficients
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
namespace QuinticLienard.ScaledProfile
open SmoothFlow.AlgebraicExpr PartialCalculus ArcFamilies
lemma third_formula (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    third a h=3*(a 1-a 3*(root h)^2+5*a 5*(root h)^4)/(root h)^5 := by
  have hx : 0<root h := Real.sqrt_pos.mpr (by positivity)
  dsimp [third,rem,c₁,c₂,c₃,c₄]
  field_simp
  ring
lemma epsilon_zero (a : Fin 6 → ℝ) (c u r t : ℝ) :
    Φ a c (((u,r),0),t)=r*slope a (c+u^2+r^2)*(t-1)+
      r^3*curvature a (c+u^2+r^2)*(t-1)^2/2 := by
  simp [Φ,Expr,K,B,X,slope,curvature,root]
lemma fitSlope_analytic {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) (p : Params) :
    ContDiffAt ℝ ω (fitSlope a c) p :=
  PositiveFit.d_analytic (Φ a c) (fun _ h => analytic hc h) (local_flow a hc) (by norm_num) (by norm_num)
lemma fitCurvature_analytic {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) (p : Params) :
    ContDiffAt ℝ ω (fitCurvature a c) p :=
  PositiveFit.k_analytic (Φ a c) (fun _ h => analytic hc h) (local_flow a hc) (by norm_num) (by norm_num)
lemma fit_epsilon_zero {a : Fin 6 → ℝ} {c : ℝ} (hc : 0<c) (u r : ℝ) :
    fitSlope a c ((u,r),0)=r*slope a (c+u^2+r^2) ∧
    fitCurvature a c ((u,r),0)=r^3*curvature a (c+u^2+r^2) := by
  apply PositiveFit.fit_quadratic (Φ a c) (fun _ h => analytic hc h) (local_flow a hc)
    (by norm_num) (by norm_num)
  intro x
  rw [epsilon_zero,epsilon_zero]
  ring
end QuinticLienard.ScaledProfile

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
-- module Solutions.OAIQW_QuinticLienard.PositiveScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uQ

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
namespace QuinticLienard.PositiveWidth
open ScalarArcs ArcFamilies
variable {P : Type uP} {Q : Type uQ} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    (Ψ : Q × ℝ → ℝ) (hΨ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Ψ q)
    (hlocal : ∀ x : State Q, 0<x.2.1 → ∃ f : State Q × ℝ → State Q,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Ψ (f q)) q.2)
include hΦ hloc hΨ hlocal
lemma fixed_width_scaling {p : P} {q : Q} {b H c C r : ℝ}
    (hb : 0<b) (hh : 0<H+c^2*b) (hc : 0<c) (hr : 0<r)
    (he : ∀ x, 0<x → Ψ (q,H+c^2*x)=C+c*Φ (p,x)) :
    midpointAtWidth Ψ ((q,H+c^2*b),c*r)=c*midpointAtWidth Φ ((p,b),r) := by
  let T := peakAtWidth Φ ((p,b),r)
  have hs := peak_spec Φ hΦ hloc (p:=p) hb hr
  have ha := chosen_arch (positive_arch_exists (profile_C1 Φ hΦ p) hb hs.1)
  have haf := ArchSymmetries.IsArch.affineOn ha (ψ:=fun x => Ψ (q,x)) (H:=H) (C:=C) hs.1 hc
    (fun x hx => he x (lt_of_lt_of_le hb hx.1))
  have hw : ((C+c*upper (fun x => Φ (p,x)) b T)-(C+c*lower (fun x => Φ (p,x)) b T))/2=c*r := by
    have hw := hs.2
    change (upper (fun x => Φ (p,x)) b T-lower (fun x => Φ (p,x)) b T)/2=r at hw
    calc
      _ = c*((upper (fun x => Φ (p,x)) b T-lower (fun x => Φ (p,x)) b T)/2) := by ring
      _ = c*r := by rw [hw]
  have hm := midpoint_of_arch Ψ hΨ hlocal haf hh (by nlinarith [sq_pos_of_pos hc,hs.1]) (mul_pos hc hr) hw
  rw [hm,he b hb]
  dsimp [midpointAtWidth,midpointFamily,ScalarArcs.midpoint,T]
  ring
lemma fixed_width_derivative_scaling {p : P} {q : Q} {b H c C r : ℝ}
    (hb : 0<b) (hh : 0<H+c^2*b) (hc : 0<c) (hr : 0<r)
    (he : ∀ x, 0<x → Ψ (q,H+c^2*x)=C+c*Φ (p,x)) :
    PositiveFit.n Ψ (H+c^2*b) (q,c*r)=PositiveFit.n Φ b (p,r) := by
  have hd := (PositiveFit.m_hasDerivAt Ψ hΨ hlocal (p:=q) hh (mul_pos hc hr)).comp r
    ((hasDerivAt_id r).const_mul c)
  have hs := (PositiveFit.m_hasDerivAt Φ hΦ hloc (p:=p) hb hr).const_mul c
  have hev : (fun s => PositiveFit.m Ψ (H+c^2*b) (q,c*s)) =ᶠ[𝓝 r]
      (fun s => c*PositiveFit.m Φ b (p,s)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact fixed_width_scaling Φ hΦ hloc Ψ hΨ hlocal hb hh hc hs he
  have hd' := hd.unique (hs.congr_of_eventuallyEq hev)
  apply mul_right_cancel₀ hc.ne'
  calc
    _ = c*PositiveFit.n Φ b (p,r) := by simpa only [mul_one] using hd'
    _ = PositiveFit.n Φ b (p,r)*c := mul_comm _ _
end QuinticLienard.PositiveWidth

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ModelScaling
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
namespace QuinticLienard.QuadraticCoordinates
open PolynomialModel ArchSymmetries WidthCoordinates
lemma scaling_width (d k : ℝ) {r s : ℝ} (hr : 0<r) (hs : 0<s) :
    H ((d,k),r*s)=r*H ((r*d,r^3*k),s) := by
  have hh := (fixed_width_affine profile profile_contDiff model_local_flow
    (p := (r*d,r^3*k)) (q := (d,k)) (h:=0) (H:=0) (C:=0) hs hr
    (by intro x; dsimp [profile]; ring)).2
  simpa [H] using hh
lemma Hr_scaling (d k : ℝ) {r s : ℝ} (hr : 0<r) (hs : 0<s) :
    Hr ((d,k),r*s)=Hr ((r*d,r^3*k),s) := by
  have hd := (Hr_hasDerivAt (d:=d) (k:=k) (mul_pos hr hs)).comp s
    ((hasDerivAt_id s).const_mul r)
  have he := (Hr_hasDerivAt (d:=r*d) (k:=r^3*k) hs).const_mul r
  have hev : (fun t => H ((d,k),r*t)) =ᶠ[𝓝 s] (fun t => r*H ((r*d,r^3*k),t)) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hs] with t ht
    exact scaling_width d k hr ht
  have hc := hd.unique (he.congr_of_eventuallyEq hev)
  apply mul_right_cancel₀ hr.ne'
  calc
    _ = r*Hr ((r*d,r^3*k),s) := by simpa only [mul_one] using hc
    _ = _ := mul_comm _ _
end QuinticLienard.QuadraticCoordinates
namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates
lemma fit_scaled {r M v : ℝ} (hr : 0<r) (hM : |M|<r) (hv : |v|<1) :
    fitD ((1,M/r),v)=r*fitD ((r,M),v) ∧ fitK ((1,M/r),v)=r^3*fitK ((r,M),v) := by
  have hMr : |M/r|<1 := by rw [abs_div,abs_of_pos hr]; exact (div_lt_one hr).mpr hM
  have hs := fit_spec hr hM hv
  have hh := scaling_width (fitD ((r,M),v)) (fitK ((r,M),v)) hr (by norm_num : (0:ℝ)<1)
  have hh' : H ((r*fitD ((r,M),v),r^3*fitK ((r,M),v)),1)=M/r := by
    rw [mul_one,hs.1] at hh
    apply (eq_div_iff hr.ne').mpr
    simpa only [mul_comm] using hh.symm
  have hh'' := Hr_scaling (fitD ((r,M),v)) (fitK ((r,M),v)) hr (by norm_num : (0:ℝ)<1)
  rw [mul_one,hs.2] at hh''
  exact fit_unique (by norm_num) hMr hv hh' hh''.symm
end QuinticLienard.QuadraticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.FiberQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uα

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

open Set Filter Asymptotics
open scoped Topology ContDiff
namespace QuinticLienard.SmallWidth
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma fiber_quotient_tendsto {f : P × ℝ → ℝ} {p₀ : P} {D : (P × ℝ) →L[ℝ] ℝ}
    (hf : HasStrictFDerivAt f D (p₀,(0:ℝ))) {α : Type uα} {l : Filter α}
    {p : α → P} {t : α → ℝ} (hp : Tendsto p l (𝓝 p₀)) (ht : Tendsto t l (𝓝 0))
    (hne : ∀ᶠ z in l, t z≠0) :
    Tendsto (fun z => (f (p z,t z)-f (p z,(0:ℝ)))/t z) l (𝓝 (D (0,1))) := by
  have hmap : Tendsto (fun z => ((p z,t z),(p z,(0:ℝ)))) l (𝓝 ((p₀,(0:ℝ)),(p₀,(0:ℝ)))) :=
    (hp.prodMk_nhds ht).prodMk_nhds (hp.prodMk_nhds tendsto_const_nhds)
  have ho := hf.isLittleO.comp_tendsto hmap
  have he (z : α) : D ((p z,t z)-(p z,(0:ℝ)))=t z*D (0,1) := by
    rw [show (p z,t z)-(p z,(0:ℝ))=t z • (0,1) by ext <;> simp]
    simp only [map_smul,smul_eq_mul]
  have ho' : (fun z => f (p z,t z)-f (p z,(0:ℝ))-t z*D (0,1)) =o[l] t := by
    apply Asymptotics.isLittleO_iff.mpr
    intro c hc
    filter_upwards [ho.bound hc] with z hz
    simp only [Function.comp_apply] at hz
    rw [he z] at hz
    simpa only [Prod.mk_sub_mk,sub_self,sub_zero,
      Prod.norm_def,norm_zero,max_eq_right (norm_nonneg (t z))] using hz
  have hh := ho'.tendsto_div_nhds_zero.add_const (D (0,1))
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hne] with z hz
  field_simp [hz]
  ring

end QuinticLienard.SmallWidth

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScaledActual
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
open ScaledProfile
lemma scaled_fit {a : Fin 6 → ℝ} {c u r : ℝ} (hc : 0<c) (hr : 0<r) :
    fitSlope a c ((u,r),r^5)=r*lambda a (c+u^2+r^2,r) ∧
    fitCurvature a c ((u,r),r^5)=r^3*kappa a (c+u^2+r^2,r) := by
  have hh : 0<c+u^2+r^2 := by positivity
  have he (x : ℝ) (hx : 0<x) : QuinticProfile.profile a (0,c+u^2+r^2*x) =
      poly a (root (c+u^2+r^2))+r*Φ a c (((u,r),r^5),x) := by
    have hs := actual_scaling a (u:=u) hc hr hx
    change _-_=_ at hs
    dsimp [QuinticProfile.profile,root]
    linarith only [hs]
  have hm := PositiveWidth.fixed_width_scaling (Φ a c) (fun _ h => analytic hc h) (local_flow a hc)
    (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a)
    (p:=((u,r),r^5)) (q:=0) (b:=1) (H:=c+u^2) (c:=r) (r:=1) (C:=poly a (root (c+u^2+r^2)))
    (by norm_num) (by simpa using hh) hr (by norm_num) (by simpa using he)
  have hn := PositiveWidth.fixed_width_derivative_scaling (Φ a c) (fun _ h => analytic hc h) (local_flow a hc)
    (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a)
    (p:=((u,r),r^5)) (q:=0) (b:=1) (H:=c+u^2) (c:=r) (r:=1) (C:=poly a (root (c+u^2+r^2)))
    (by norm_num) (by simpa using hh) hr (by norm_num) (by simpa using he)
  simp only [mul_one] at hm hn
  have hM := PositiveFit.m_abs_lt (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have hv := PositiveFit.n_abs_lt (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have hs := QuadraticFit.fit_scaled hr hM hv
  have hm' : PositiveFit.m (QuinticProfile.profile a) (c+u^2+r^2) (0,r)/r =
      PositiveFit.m (Φ a c) 1 (((u,r),r^5),1) := by
    change PositiveWidth.midpointAtWidth _ _ /r = PositiveWidth.midpointAtWidth _ _
    rw [hm]
    field_simp
  rw [hm',hn] at hs
  simpa only [fitSlope,fitCurvature,lambda,kappa,PositiveFit.d,PositiveFit.k,hn] using hs
lemma pull_analytic (a : Fin 6 → ℝ) {c h r e : ℝ} (hh : c+r^2<h) :
    ContDiffAt ℝ ω (pull a c) ((h,r),e) := by
  have hp : 0<h-c-r^2 := by linarith
  exact (((contDiffAt_fst.fst.sub contDiffAt_const).sub
    (contDiffAt_fst.snd.pow 2)).sqrt (ne_of_gt hp)).prodMk contDiffAt_fst.snd |>.prodMk contDiffAt_snd
lemma pulledSlope_analytic {a : Fin 6 → ℝ} {c h r e : ℝ} (hc : 0<c) (hh : c+r^2<h) :
    ContDiffAt ℝ ω (pulledSlope a c) ((h,r),e) :=
  (fitSlope_analytic hc _).comp _ (pull_analytic a hh)
lemma pulledCurvature_analytic {a : Fin 6 → ℝ} {c h r e : ℝ} (hc : 0<c) (hh : c+r^2<h) :
    ContDiffAt ℝ ω (pulledCurvature a c) ((h,r),e) :=
  (fitCurvature_analytic hc _).comp _ (pull_analytic a hh)
lemma pull_height {c h r : ℝ} (hh : c+r^2≤h) : c+(Real.sqrt (h-c-r^2))^2+r^2=h := by
  rw [Real.sq_sqrt (by linarith)]
  ring
lemma pulled_zero {a : Fin 6 → ℝ} {c h r : ℝ} (hc : 0<c) (hh : c+r^2≤h) :
    pulledSlope a c ((h,r),0)=r*slope a h ∧ pulledCurvature a c ((h,r),0)=r^3*curvature a h := by
  have hs := fit_epsilon_zero (a:=a) hc (Real.sqrt (h-c-r^2)) r
  rw [pull_height hh] at hs
  exact hs
lemma pulled_actual {a : Fin 6 → ℝ} {c h r : ℝ} (hc : 0<c) (hh : c+r^2≤h) (hr : 0<r) :
    pulledSlope a c ((h,r),r^5)=r*lambda a (h,r) ∧
    pulledCurvature a c ((h,r),r^5)=r^3*kappa a (h,r) := by
  have hs := scaled_fit (a:=a) (u:=Real.sqrt (h-c-r^2)) hc hr
  rw [pull_height hh] at hs
  exact hs
end QuinticLienard.QuinticFit

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
lemma root_analytic {h : ℝ} (hh : 0<h) : ContDiffAt ℝ ω root h :=
  (contDiffAt_const.mul contDiffAt_id).sqrt (mul_ne_zero (by norm_num) hh.ne')
lemma root_hasDerivAt {h : ℝ} (hh : 0<h) : HasDerivAt root (1/root h) h := by
  have hd := (Real.hasDerivAt_sqrt (mul_ne_zero (by norm_num : (2:ℝ)≠0) hh.ne')).comp h
    ((hasDerivAt_id h).const_mul 2)
  convert! hd using 1
  simp only [root]
  ring
lemma poly_hasDerivAt (a : Fin 6 → ℝ) (x : ℝ) : HasDerivAt (poly a) (c₁ a x) x := by
  have hd := (hasDerivAt_const x (a 0)).add (((hasDerivAt_id x).const_mul (a 1))) |>.add
    (((hasDerivAt_id x).pow 2).const_mul (a 2)) |>.add
    (((hasDerivAt_id x).pow 3).const_mul (a 3)) |>.add
    (((hasDerivAt_id x).pow 4).const_mul (a 4)) |>.add
    (((hasDerivAt_id x).pow 5).const_mul (a 5))
  convert! hd using 1
  dsimp [c₁]
  ring
lemma c₁_hasDerivAt (a : Fin 6 → ℝ) (x : ℝ) : HasDerivAt (c₁ a) (2*c₂ a x) x := by
  have hd := (hasDerivAt_const x (a 1)).add ((hasDerivAt_id x).const_mul (2*a 2)) |>.add
    (((hasDerivAt_id x).pow 2).const_mul (3*a 3)) |>.add
    (((hasDerivAt_id x).pow 3).const_mul (4*a 4)) |>.add
    (((hasDerivAt_id x).pow 4).const_mul (5*a 5))
  convert! hd using 1
  dsimp [c₂]
  ring
lemma c₂_hasDerivAt (a : Fin 6 → ℝ) (x : ℝ) : HasDerivAt (c₂ a) (3*c₃ a x) x := by
  have hd := (hasDerivAt_const x (a 2)).add ((hasDerivAt_id x).const_mul (3*a 3)) |>.add
    (((hasDerivAt_id x).pow 2).const_mul (6*a 4)) |>.add
    (((hasDerivAt_id x).pow 3).const_mul (10*a 5))
  convert! hd using 1
  dsimp [c₃]
  ring
lemma profile_hasDerivAt (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (fun u => poly a (root u)) (slope a h) h := by
  simpa only [slope,mul_one_div] using! (poly_hasDerivAt a (root h)).comp h (root_hasDerivAt hh)
lemma slope_hasDerivAt (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (slope a) (curvature a h) h := by
  have hx := root_pos hh
  have hd := ((c₁_hasDerivAt a (root h)).comp h (root_hasDerivAt hh)).div (root_hasDerivAt hh) hx.ne'
  convert! hd using 1
  dsimp [curvature]
  field_simp
lemma curvature_hasDerivAt (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) :
    HasDerivAt (curvature a) (third a h) h := by
  have hx := root_pos hh
  have hd := ((((c₂_hasDerivAt a (root h)).comp h (root_hasDerivAt hh)).const_mul 2).div
    ((root_hasDerivAt hh).pow 2) (pow_ne_zero _ hx.ne')).sub
      (((c₁_hasDerivAt a (root h)).comp h (root_hasDerivAt hh)).div
        ((root_hasDerivAt hh).pow 3) (pow_ne_zero _ hx.ne'))
  convert! hd using 1
  rw [third_formula a hh]
  dsimp [c₁,c₂,c₃]
  field_simp
  ring
lemma slope_analytic (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) : ContDiffAt ℝ ω (slope a) h := by
  have hr := root_analytic hh
  change ContDiffAt ℝ ω (fun u => (a 1+2*a 2*root u+3*a 3*(root u)^2+4*a 4*(root u)^3+5*a 5*(root u)^4)/root u) h
  fun_prop (disch:=exact (root_pos hh).ne')
lemma curvature_analytic (a : Fin 6 → ℝ) {h : ℝ} (hh : 0<h) : ContDiffAt ℝ ω (curvature a) h := by
  have hr := root_analytic hh
  change ContDiffAt ℝ ω (fun u => 2*(a 2+3*a 3*root u+6*a 4*(root u)^2+10*a 5*(root u)^3)/(root u)^2-(a 1+2*a 2*root u+3*a 3*(root u)^2+4*a 4*(root u)^3+5*a 5*(root u)^4)/(root u)^3) h
  fun_prop (disch:=exact pow_ne_zero _ (root_pos hh).ne')
end QuinticLienard.ScaledProfile

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
lemma M_analytic (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (M a) (h,r) :=
  PositiveTransport.M_analytic _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr
lemma V_analytic (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : ContDiffAt ℝ ω (V a) (h,r) :=
  PositiveTransport.v_analytic _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr
lemma M_abs_lt (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : |M a (h,r)|<r :=
  PositiveTransport.M_abs_lt _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr
lemma V_abs_lt (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) : |V a (h,r)|<1 :=
  PositiveTransport.v_abs_lt _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr
lemma n_eq_V (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    PositiveFit.n (QuinticProfile.profile a) h (0,r)=V a (h,r) :=
  (PositiveFit.m_hasDerivAt _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh hr).unique
    (second_hasDerivAt ((M_analytic a hh hr).differentiableAt (by simp)))
lemma fit_eq (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    lambda a (h,r)=QuadraticFit.fitD ((r,M a (h,r)),V a (h,r)) ∧
    kappa a (h,r)=QuadraticFit.fitK ((r,M a (h,r)),V a (h,r)) := by
  simp only [lambda,kappa,PositiveFit.d,PositiveFit.k,n_eq_V a hh hr]
  exact ⟨rfl,rfl⟩
lemma spec (a : Fin 6 → ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    H (fit a (h,r))=M a (h,r) ∧ Hr (fit a (h,r))=V a (h,r) := by
  dsimp only [fit]
  rw [(fit_eq a hh hr).1,(fit_eq a hh hr).2]
  exact QuadraticFit.fit_spec hr (M_abs_lt a hh hr) (V_abs_lt a hh hr)
end QuinticLienard.QuinticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScalarComparison
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
open scoped Topology
namespace QuinticLienard.ScalarComparison

lemma weighted_deriv {a E F : ℝ → ℝ} {l r : ℝ} (hlr : l≤r)
    (ha : ContinuousOn a (Icc l r)) :
    ∃ w : ℝ → ℝ, (∀ s, 0<w s) ∧ w l=1 ∧
      ∀ s ∈ Icc l r, HasDerivAt E (-a s*E s+F s) s →
        HasDerivAt (fun s=>w s*E s) (w s*F s) s := by
  let ac : ℝ → ℝ := fun s => a (projIcc l r hlr s)
  have hc : Continuous ac := (continuousOn_iff_continuous_domRestrict.mp ha).comp continuous_projIcc
  let w : ℝ → ℝ := fun s => Real.exp (∫ u in l..s,ac u)
  refine ⟨w,fun s=>Real.exp_pos _,by simp [w],?_⟩
  intro s hs hd
  have hh := ((hc.integral_hasStrictDerivAt l s).hasDerivAt.exp).mul hd
  have he : ac s=a s := by simp only [ac,projIcc_of_mem hlr hs]
  rw [he] at hh
  convert! hh using 1
  dsimp only [w]
  ring
lemma linear_pos {a E F : ℝ → ℝ} {l r : ℝ} (hlr : l<r)
    (ha : ContinuousOn a (Icc l r))
    (hd : ∀ s ∈ Icc l r, HasDerivAt E (-a s*E s+F s) s)
    (hF : ∀ s ∈ Ioo l r, 0<F s) (hE : 0≤E l) : 0<E r := by
  obtain ⟨w,hw,hw0,hwd⟩ := weighted_deriv hlr.le ha
  have hm : StrictMonoOn (fun s=>w s*E s) (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun s hs => (hwd s hs (hd s hs)).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    rw [(hwd s ⟨hs.1.le,hs.2.le⟩ (hd s ⟨hs.1.le,hs.2.le⟩)).deriv]
    exact mul_pos (hw s) (hF s hs)
  have hp := hm ⟨le_rfl,hlr.le⟩ ⟨hlr.le,le_rfl⟩ hlr
  dsimp only at hp
  rw [hw0,one_mul] at hp
  exact (mul_pos_iff_of_pos_left (hw r)).mp (hE.trans_lt hp)

lemma linear_negative_from_zero {a E F : ℝ → ℝ} {r : ℝ} (hr : 0<r)
    (ha : ContinuousOn a (Ioc 0 r)) (hap : ∀ s ∈ Ioc 0 r, 0<a s)
    (hd : ∀ s ∈ Ioc 0 r, HasDerivAt E (-a s*E s+F s) s)
    (hF : ∀ s ∈ Ioo 0 r, F s<0)
    (h0 : Tendsto E (𝓝[>] (0:ℝ)) (𝓝 0)) : E r<0 := by
  have hn (s : ℝ) (hs : s ∈ Ioc 0 r) : E s≤0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0<δ ∧ δ<s ∧ E δ<ε := by
      filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hs.1).filter_mono inf_le_left,
        h0.eventually (eventually_lt_nhds hε)] with δ hδ hδs hEδ
      exact ⟨hδ,hδs,hEδ⟩
    obtain ⟨δ,hδ,hδs,hEδ⟩ := hev.exists
    have hsub : Icc δ s ⊆ Ioc 0 r := fun _ ht=>⟨hδ.trans_le ht.1,ht.2.trans hs.2⟩
    have hb := image_le_of_deriv_right_lt_deriv_boundary
      (fun x hx => (hd x (hsub hx)).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (hsub ⟨hx.1,hx.2.le⟩)).hasDerivWithinAt)
      (B:=fun _=>ε) (B':=fun _=>0) hEδ.le (fun x=>hasDerivAt_const x ε) (by
        intro x hx he
        have hax := hap x (hsub ⟨hx.1,hx.2.le⟩)
        have hfx := hF x ⟨hδ.trans_le hx.1,hx.2.trans_le hs.2⟩
        rw [he]
        nlinarith [mul_pos hax hε]) (show s ∈ Icc δ s from ⟨hδs.le,le_rfl⟩)
    simpa only [zero_add] using hb
  have he := linear_pos (a:=a) (E:=fun s=>-E s) (F:=fun s=>-F s)
    (show r/2<r by linarith)
    (ha.mono (fun s hs=>⟨(half_pos hr).trans_le hs.1,hs.2⟩))
    (fun s hs=>by
      convert! (hd s ⟨(half_pos hr).trans_le hs.1,hs.2⟩).neg using 1
      ring)
    (fun s hs=>neg_pos.mpr (hF s ⟨(half_pos hr).trans hs.1,hs.2⟩))
    (neg_nonneg.mpr (hn (r/2) ⟨half_pos hr,by linarith⟩))
  exact neg_pos.mp he

lemma error_negative_before {a b c E : ℝ → ℝ} {κ r : ℝ} (_hr : 0<r)
    (ha : ContinuousOn a (Ioc 0 r)) (hap : ∀ s ∈ Ioc 0 r,0<a s)
    (hb : ∀ s ∈ Ioc 0 r,0<b s) (hc : StrictAntiOn c (Ioc 0 r))
    (hd : ∀ s ∈ Ioc 0 r,HasDerivAt E (-a s*E s-b s*(c s-κ)) s)
    (h0 : Tendsto E (𝓝[>] (0:ℝ)) (𝓝 0)) (hEr : E r≤0)
    {s : ℝ} (hs : 0<s) (hsr : s<r) : E s<0 := by
  by_cases hcs : κ≤c s
  · apply linear_negative_from_zero hs (ha.mono (Ioc_subset_Ioc_right hsr.le)) (fun x hx=>hap x ⟨hx.1,hx.2.trans hsr.le⟩)
      (F:=fun x=>-b x*(c x-κ))
      (fun x hx=>by simpa only [sub_eq_add_neg,neg_mul] using hd x ⟨hx.1,hx.2.trans hsr.le⟩)
      _ h0
    intro x hx
    have hcx := hc ⟨hx.1,hx.2.le.trans hsr.le⟩ ⟨hs,hsr.le⟩ hx.2
    have hbx := hb x ⟨hx.1,hx.2.le.trans hsr.le⟩
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hbx) (sub_pos.mpr (hcs.trans_lt hcx))
  · by_contra! hEs
    have hp := linear_pos (a:=a) (E:=E) (F:=fun x=>-b x*(c x-κ)) hsr
      (ha.mono (fun x hx=>⟨hs.trans_le hx.1,hx.2⟩))
      (fun x hx=>by simpa only [sub_eq_add_neg,neg_mul] using hd x ⟨hs.trans_le hx.1,hx.2⟩)
      (fun x hx=>by
        have hcx := hc ⟨hs,hsr.le⟩ ⟨hs.trans hx.1,hx.2.le⟩ hx.1
        have hbx := hb x ⟨hs.trans hx.1,hx.2.le⟩
        have hck : c x<κ := hcx.trans (lt_of_not_ge hcs)
        exact mul_pos_of_neg_of_neg (neg_neg_of_pos hbx) (sub_neg.mpr hck)) hEs
    exact (not_lt_of_ge hEr) hp
end QuinticLienard.ScalarComparison

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ActualFitLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

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
namespace QuinticLienard.QuinticFit
open ScaledProfile SmallWidth QuadraticCoordinates
lemma fit_limits {a : Fin 6 → ℝ} {h₀ : ℝ} (hh₀ : 0<h₀)
    {ι : Type uι} {l : Filter ι} {h r : ι → ℝ}
    (hh : Tendsto h l (𝓝 h₀)) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ z in l, 0<r z) :
    Tendsto (fun z => lambda a (h z,r z)) l (𝓝 (slope a h₀)) ∧
    Tendsto (fun z => kappa a (h z,r z)) l (𝓝 (curvature a h₀)) := by
  let c := h₀/2
  have hc : 0<c := by dsimp [c]; linarith
  have hch : c<h₀ := by dsimp [c]; linarith
  have hF := pulledSlope_analytic (a:=a) (h:=h₀) (r:=0) (e:=0) hc (by simpa using hch)
  have hG := pulledCurvature_analytic (a:=a) (h:=h₀) (r:=0) (e:=0) hc (by simpa using hch)
  have he : Tendsto (fun z => (r z)^5) l (𝓝 0) := by simpa using hr.pow 5
  have hn : ∀ᶠ z in l, (r z)^5≠0 := hp.mono (fun _ hz => pow_ne_zero _ hz.ne')
  have hqF := fiber_quotient_tendsto (hF.hasStrictFDerivAt (by simp)) (hh.prodMk_nhds hr) he hn
  have hqG := fiber_quotient_tendsto (hG.hasStrictFDerivAt (by simp)) (hh.prodMk_nhds hr) he hn
  have hlF := (hr.pow 4).mul hqF
  have hlG := (hr.pow 2).mul hqG
  have hb : ∀ᶠ z in l, c+(r z)^2<h z := by
    have ht : Tendsto (fun z => h z-c-(r z)^2) l (𝓝 (h₀-c)) := by
      simpa using (hh.sub tendsto_const_nhds).sub (hr.pow 2)
    filter_upwards [ht.eventually (eventually_gt_nhds (sub_pos.mpr hch))] with z hz
    linarith
  constructor
  · have ht := ((slope_analytic a hh₀).continuousAt.tendsto.comp hh).add hlF
    simp only [zero_pow (by norm_num : (4:ℕ)≠0),zero_mul,add_zero] at ht
    apply ht.congr'
    filter_upwards [hp,hb] with z hz hbz
    dsimp
    rw [(pulled_actual hc hbz.le hz).1,(pulled_zero hc hbz.le).1]
    field_simp
    ring
  · have ht := ((curvature_analytic a hh₀).continuousAt.tendsto.comp hh).add hlG
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,add_zero] at ht
    apply ht.congr'
    filter_upwards [hp,hb] with z hz hbz
    dsimp
    rw [(pulled_actual hc hbz.le hz).2,(pulled_zero hc hbz.le).2]
    field_simp
    ring
lemma normalized_limits {a : Fin 6 → ℝ} {h₀ : ℝ} (hh₀ : 0<h₀)
    {ι : Type uι} {l : Filter ι} {h r : ι → ℝ}
    (hh : Tendsto h l (𝓝 h₀)) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ z in l, 0<r z) :
    Tendsto (fun z => M a (h z,r z)/r z) l (𝓝 0) ∧
    Tendsto (fun z => V a (h z,r z)) l (𝓝 0) := by
  have hf := fit_limits (a:=a) hh₀ hh hr hp
  have hd : Tendsto (fun z => r z*lambda a (h z,r z)) l (𝓝 0) := by simpa using hr.mul hf.1
  have hk : Tendsto (fun z => (r z)^3*kappa a (h z,r z)) l (𝓝 0) := by simpa using (hr.pow 3).mul hf.2
  have ht := (hd.prodMk_nhds hk).prodMk_nhds (tendsto_const_nhds (x:=(1:ℝ)))
  have hM := (H_analytic (d:=0) (k:=0) (by norm_num : (0:ℝ)<1)).continuousAt.tendsto.comp ht
  have hV := (Hr_analytic (d:=0) (k:=0) (by norm_num : (0:ℝ)<1)).continuousAt.tendsto.comp ht
  rw [(zero_data (by norm_num : (0:ℝ)<1)).2] at hM
  rw [Hr_zero (by norm_num : (0:ℝ)<1)] at hV
  constructor
  · apply hM.congr'
    filter_upwards [hp,hh.eventually (eventually_gt_nhds hh₀)] with z hz hhz
    have he := scaling (lambda a (h z,r z)) (kappa a (h z,r z)) hz
    rw [show H ((lambda a (h z,r z),kappa a (h z,r z)),r z)=M a (h z,r z) from (spec a hhz hz).1] at he
    exact (eq_div_iff hz.ne').mpr (by simpa only [Function.comp_apply,mul_comm] using he.symm)
  · apply hV.congr'
    filter_upwards [hp,hh.eventually (eventually_gt_nhds hh₀)] with z hz hhz
    have he := Hr_scaling (lambda a (h z,r z)) (kappa a (h z,r z)) hz (by norm_num : (0:ℝ)<1)
    simpa only [Function.comp_apply,mul_one,show Hr ((lambda a (h z,r z),kappa a (h z,r z)),r z)=V a (h z,r z) from (spec a hhz hz).2] using he.symm
end QuinticLienard.QuinticFit

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
include hΦ hloc
lemma base_eq {p : P} {t h r : ℝ} (hh : 0<h) (hht : h<t)
    (he : widthFamily Φ ((p,t),h)=r) : baseAtWidth Φ ((p,t),r)=h := by
  have hs := base_spec Φ (show Admissible Φ ((p,t),r) from ⟨h,hh,hht,he⟩)
  exact (width_strictAnti_base Φ hΦ hloc p t).injOn ⟨hs.1,hs.2.1⟩ ⟨hh,hht⟩ (hs.2.2.trans he.symm)
lemma base_exists_le {p : P} {t h r : ℝ} (hh : 0<h) (hht : h<t) (hr : 0<r)
    (hle : r≤widthFamily Φ ((p,t),h)) : Admissible Φ ((p,t),r) := by
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  obtain ⟨δ,hδ,hsmall⟩ := width_small_base hφ t (hh.trans hht) hr
  let b := t-min δ (t-h)/2
  have hbh : h<b := by dsimp [b]; linarith [min_le_right δ (t-h)]
  have hbt : b<t := by dsimp [b]; linarith [lt_min hδ (sub_pos.mpr hht)]
  have hwb : widthFamily Φ ((p,t),b)<r := hsmall b (by dsimp [b]; linarith [min_le_left δ (t-h)]) hbt
  have hc : ContinuousOn (fun u => widthFamily Φ ((p,t),u)) (Icc h b) := by
    intro u hu
    exact ((width_analytic Φ hΦ hloc (hh.trans_le hu.1) (hu.2.trans_lt hbt)).comp u
      (contDiffAt_const.prodMk contDiffAt_id)).continuousAt.continuousWithinAt
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc' hbh.le hc ⟨hwb.le,hle⟩
  exact ⟨u,hh.trans_le hu.1,hu.2.trans_lt hbt,he⟩
lemma base_local {p : P} {t r : ℝ} (he : Admissible Φ ((p,t),r)) :
    ContDiffAt ℝ ω (baseAtWidth Φ) ((p,t),r) ∧ ∀ᶠ q in 𝓝 ((p,t),r), Admissible Φ q := by
  let h := baseAtWidth Φ ((p,t),r)
  have hs := base_spec Φ he
  have hwd := width_analytic Φ hΦ hloc (p:=p) hs.1 hs.2.1
  have hd := width_base_deriv Φ hΦ hloc (p:=p) hs.1 hs.2.1
  have hdneg : -widthFamily Φ ((p,t),h) /
      ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (width_pos Φ hΦ hs.1 hs.2.1)) (gap_pos Φ hΦ hs.1 hs.2.1)
  obtain ⟨Y,hY,hY0,hy⟩ := level_hit hwd hd hs.2.2 hdneg.ne
  have hlt : ∀ᶠ q in 𝓝 ((p,t),r), Y q<q.1.2 :=
    hY.continuousAt.eventually_lt continuousAt_fst.snd (by simpa only [hY0] using hs.2.1)
  have hpos : ∀ᶠ q in 𝓝 ((p,t),r), 0<Y q :=
    continuousAt_const.eventually_lt hY.continuousAt (by simpa only [hY0] using hs.1)
  constructor
  · apply hY.congr_of_eventuallyEq
    filter_upwards [hy,hlt,hpos] with q hq htq hpq
    exact base_eq Φ hΦ hloc hpq htq hq
  · filter_upwards [hy,hlt,hpos] with q hq htq hpq
    exact ⟨Y q,hpq,htq,hq⟩
lemma base_analytic {p : P} {t r : ℝ} (he : Admissible Φ ((p,t),r)) :
    ContDiffAt ℝ ω (baseAtWidth Φ) ((p,t),r) := (base_local Φ hΦ hloc he).1
lemma base_width_deriv {p : P} {t r : ℝ} (he : Admissible Φ ((p,t),r)) :
    HasDerivAt (fun s => baseAtWidth Φ ((p,t),s))
      (-(r^2-(midpointFamily Φ ((p,t),baseAtWidth Φ ((p,t),r)))^2)/r) r := by
  let b : ℝ → ℝ := fun s => baseAtWidth Φ ((p,t),s)
  have hs := base_spec Φ he
  have hb := ((base_analytic Φ hΦ hloc he).comp r
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hw := width_base_deriv Φ hΦ hloc (p:=p) hs.1 hs.2.1
  have hc := hw.comp r hb.hasDerivAt
  have hev : (fun s => widthFamily Φ ((p,t),b s)) =ᶠ[𝓝 r] id := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually (base_local Φ hΦ hloc he).2] with s hs
    exact (base_spec Φ hs).2.2
  have heq := (hc.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_id r)
  rw [hs.2.2] at heq
  have hr : 0<r := hs.2.2 ▸ width_pos Φ hΦ hs.1 hs.2.1
  have hg := gap_pos Φ hΦ (p:=p) hs.1 hs.2.1
  rw [hs.2.2] at hg
  convert! hb.hasDerivAt using 1
  field_simp [hr.ne',hg.ne'] at heq ⊢
  nlinarith [heq]
lemma base_midpoint {p : P} {t r : ℝ} (he : Admissible Φ ((p,t),r)) :
    midpointAtWidth Φ ((p,baseAtWidth Φ ((p,t),r)),r)=
      midpointFamily Φ ((p,t),baseAtWidth Φ ((p,t),r)) := by
  have hs := base_spec Φ he
  have hr : 0<r := hs.2.2 ▸ width_pos Φ hΦ hs.1 hs.2.1
  dsimp only [midpointAtWidth]
  rw [peak_eq Φ hΦ hloc hr hs.1 hs.2.1 hs.2.2]
lemma base_tendsto {p : P} {t h : ℝ} (hh : 0<h) (hht : h<t) :
    Tendsto (fun s => baseAtWidth Φ ((p,t),s)) (𝓝[>] (0:ℝ)) (𝓝 t) := by
  have hr := width_pos Φ hΦ (p:=p) hh hht
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), Admissible Φ ((p,t),s) := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hr).filter_mono inf_le_left] with s hs hsr
    exact base_exists_le Φ hΦ hloc hh hht hs hsr.le
  have hl : Tendsto (fun s : ℝ => t-s^2/2) (𝓝[>] (0:ℝ)) (𝓝 t) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 t)).sub
      (((tendsto_id.mono_left inf_le_left : Tendsto (fun s : ℝ => s) (𝓝[>] (0:ℝ)) (𝓝 0)).pow 2).div_const 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [hev] with s hs
    have hb := base_spec Φ hs
    have he := height_bound Φ hΦ hloc (p:=p) hb.1 hb.2.1
    rw [hb.2.2] at he
    linarith
  · filter_upwards [hev] with s hs
    exact (base_spec Φ hs).2.1.le
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
lemma v_abs_lt {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : |v a t r|<1 :=
  V_abs_lt a (base_spec he).1 (radius_pos he)
lemma A_abs_lt {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : |A a t r|<1 := by
  dsimp only [A]
  rw [abs_div,abs_of_pos (radius_pos he)]
  exact (div_lt_one (radius_pos he)).mpr (m_abs_lt he)
lemma g_pos {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : 0<g a t r :=
  sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos (radius_pos he)] using m_abs_lt he))
lemma base_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (b a t) r :=
  (PositiveWidth.base_analytic _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) he).comp r
    (contDiffAt_const.prodMk contDiffAt_id)
lemma adm_eventually {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ∀ᶠ s in 𝓝 r, Adm a t s :=
  (continuousAt_const.prodMk continuousAt_id).eventually
    (PositiveWidth.base_local _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) he).2
lemma point_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (point a t) r :=
  (base_analytic he).prodMk contDiffAt_id
lemma m_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (m a t) r :=
  (M_analytic a (base_spec he).1 (radius_pos he)).comp (f:=point a t) r (point_analytic he)
lemma A_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (A a t) r :=
  (m_analytic he).div contDiffAt_id (radius_pos he).ne'
lemma base_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : HasDerivAt (b a t) (-g a t r/r) r := by
  have hd := PositiveWidth.base_width_deriv _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) he
  have hm := PositiveWidth.base_midpoint _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) he
  change m a t r=_ at hm
  rw [←hm] at hd
  exact hd
lemma along_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) {f : ℝ × ℝ → ℝ}
    (hf : DifferentiableAt ℝ f (point a t r)) :
    HasDerivAt (fun s => f (point a t s)) (-g a t r/r*D a f (point a t r)) r := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt r ((base_deriv he).prodMk (hasDerivAt_id r))
  rw [fderiv_pair] at hd
  convert! hd using 1
  change -g a t r/r*(first f (point a t r)-r/g a t r*second f (point a t r)) = _
  field_simp [(radius_pos he).ne',(g_pos he).ne']
  ring
lemma m_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (m a t) (-m a t r/r+g a t r/r*k a t r) r := by
  have ht := PositiveTransport.transport_midpoint (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) (base_spec he).1 (radius_pos he)
  have hp : HasDerivAt (fun u => QuinticProfile.profile a (0,u)) (ScaledProfile.slope a (b a t r)) (b a t r) := ScaledProfile.profile_hasDerivAt a (base_spec he).1
  rw [hp.deriv] at ht
  change D a (M a) (point a t r)=m a t r/g a t r-k a t r at ht
  have hd := along_deriv he ((M_analytic a (base_spec he).1 (radius_pos he)).differentiableAt (by simp))
  rw [ht] at hd
  convert! hd using 1
  field_simp [(radius_pos he).ne',(g_pos he).ne']
  ring
lemma v_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (v a t) (2*m a t r*(1-(v a t r)^2)/g a t r) r := by
  have ht := PositiveTransport.transport_v (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) (base_spec he).1 (radius_pos he)
  change D a (V a) (point a t r)= -2*m a t r*r*(1-(v a t r)^2)/(g a t r)^2 at ht
  have hd := along_deriv he ((V_analytic a (base_spec he).1 (radius_pos he)).differentiableAt (by simp))
  rw [ht] at hd
  convert! hd using 1
  field_simp [(radius_pos he).ne',(g_pos he).ne']
lemma A_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (A a t) (k a t r*(1-(A a t r)^2)-2*A a t r/r) r := by
  convert! (m_deriv he).div (hasDerivAt_id r) (radius_pos he).ne' using 1
  dsimp only [A,g,id_eq]
  field_simp [(radius_pos he).ne']
  ring
lemma k_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (k a t) (-g a t r/r*c a t r) r := by
  convert! (ScaledProfile.slope_hasDerivAt a (base_spec he).1).comp r (base_deriv he) using 1
  exact mul_comm _ _
lemma c_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (c a t) (-g a t r/r*ScaledProfile.third a (b a t r)) r := by
  convert! (ScaledProfile.curvature_hasDerivAt a (base_spec he).1).comp r (base_deriv he) using 1
  exact mul_comm _ _
lemma L_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : HasDerivAt (L a t) (rate a t r) r := by
  have hd := (angle_deriv (v_abs_lt he)).comp r (v_deriv he)
  convert! hd using 1
  dsimp only [rate,A,g]
  have hv : 1-(v a t r)^2≠0 := by
    have ht := sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1) |>.mpr (v_abs_lt he)
    nlinarith [sq_abs (v a t r)]
  field_simp [(radius_pos he).ne',hv]
lemma adm_le {a : Fin 6 → ℝ} {t r s : ℝ} (he : Adm a t r) (hs : 0<s) (hsr : s≤r) : Adm a t s := by
  have hb := base_spec he
  apply PositiveWidth.base_exists_le _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hb.1 hb.2.1 hs
  rw [hb.2.2]
  exact hsr
lemma base_tendsto {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    Tendsto (b a t) (𝓝[>] (0:ℝ)) (𝓝 t) :=
  PositiveWidth.base_tendsto _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (base_spec he).1 (base_spec he).2.1
lemma small_limits {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    Tendsto (A a t) (𝓝[>] (0:ℝ)) (𝓝 0) ∧ Tendsto (L a t) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    Tendsto (k a t) (𝓝[>] (0:ℝ)) (𝓝 (ScaledProfile.slope a t)) ∧
    Tendsto (c a t) (𝓝[>] (0:ℝ)) (𝓝 (ScaledProfile.curvature a t)) := by
  have ht : 0<t := (base_spec he).1.trans (base_spec he).2.1
  have hl := QuinticFit.normalized_limits (a:=a) ht (base_tendsto he)
    (tendsto_id.mono_left inf_le_left) self_mem_nhdsWithin
  refine ⟨hl.1,?_,(ScaledProfile.slope_analytic a ht).continuousAt.tendsto.comp (base_tendsto he),
    (ScaledProfile.curvature_analytic a ht).continuousAt.tendsto.comp (base_tendsto he)⟩
  change Tendsto (fun s=>angle (V a (b a t s,s))) (𝓝[>] (0:ℝ)) (𝓝 0)
  simpa only [angle_zero,Function.comp_def,id_eq] using
    (angle_analytic (by norm_num : |(0:ℝ)|<1)).continuousAt.tendsto.comp hl.2
end QuinticLienard.ActualCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.FixedSlopeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

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
namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates
lemma slope_scaled {κ r m : ℝ} (hr : 0<r) (hm : |m|<r) :
    slope ((r^3*κ,1),m/r)=r*slope ((κ,r),m) := by
  have hmr : |m/r|<1 := by rw [abs_div,abs_of_pos hr]; exact (div_lt_one hr).mpr hm
  apply slope_eq (by norm_num) hmr
  have hh := scaling_width (slope ((κ,r),m)) κ hr (by norm_num : (0:ℝ)<1)
  rw [mul_one,slope_spec hr hm] at hh
  exact (eq_div_iff hr.ne').mpr (by simpa only [mul_comm] using hh.symm)
end QuinticLienard.QuadraticFit
namespace QuinticLienard.QuinticFit
open QuadraticFit
lemma fixed_slope_limit {a : Fin 6 → ℝ} {h₀ : ℝ} (hh₀ : 0<h₀) (κ : ℝ)
    {ι : Type uι} {l : Filter ι} {h r : ι → ℝ}
    (hh : Tendsto h l (𝓝 h₀)) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ z in l, 0<r z) :
    Tendsto (fun z => slope ((κ,r z),M a (h z,r z))) l (𝓝 (ScaledProfile.slope a h₀)) := by
  have hf := fit_limits (a:=a) hh₀ hh hr hp
  have hn := (normalized_limits (a:=a) hh₀ hh hr hp).1
  have hx : Tendsto (fun z => (((r z)^3*κ,(1:ℝ)),M a (h z,r z)/r z)) l (𝓝 (((0:ℝ),(1:ℝ)),0)) := by
    have h0 : Tendsto (fun z => (r z)^3*κ) l (𝓝 (0:ℝ)) := by simpa using ((hr.pow 3).mul_const κ)
    exact (h0.prodMk_nhds tendsto_const_nhds).prodMk_nhds hn
  have hy : Tendsto (fun z => (((r z)^3*kappa a (h z,r z),(1:ℝ)),M a (h z,r z)/r z)) l (𝓝 (((0:ℝ),(1:ℝ)),0)) := by
    have h0 : Tendsto (fun z => (r z)^3*kappa a (h z,r z)) l (𝓝 (0:ℝ)) := by simpa using ((hr.pow 3).mul hf.2)
    exact (h0.prodMk_nhds tendsto_const_nhds).prodMk_nhds hn
  obtain ⟨K,U,hU,hLip⟩ := ((slope_analytic (k:=0) (by norm_num : (0:ℝ)<1) (by norm_num : |(0:ℝ)|<1)).of_le (by simp : (1:WithTop ℕ∞)≤ω)).exists_lipschitzOnWith
  have hbound : ∀ᶠ z in l,
      |slope ((κ,r z),M a (h z,r z))-lambda a (h z,r z)| ≤
        K*(r z)^2*|κ-kappa a (h z,r z)| := by
    filter_upwards [hp,hh.eventually (eventually_gt_nhds hh₀),hx.eventually hU,hy.eventually hU] with z hz hhz hxz hyz
    have hl := hLip.dist_le_mul _ hxz _ hyz
    have hm := M_abs_lt a hhz hz
    have hs : slope ((kappa a (h z,r z),r z),M a (h z,r z))=lambda a (h z,r z) :=
      slope_eq hz hm (spec a hhz hz).1
    rw [slope_scaled hz hm,slope_scaled hz hm,hs] at hl
    simp only [Prod.dist_eq,dist_self,Real.dist_eq] at hl
    simp only [max_eq_left (abs_nonneg (r z^3*κ-r z^3*kappa a (h z,r z)))] at hl
    rw [←mul_sub,abs_mul,abs_of_pos hz] at hl
    have hd : |r z^3*κ-r z^3*kappa a (h z,r z)|=(r z)^3*|κ-kappa a (h z,r z)| := by
      rw [←mul_sub,abs_mul,abs_of_pos (pow_pos hz 3)]
    rw [hd] at hl
    apply (mul_le_mul_iff_right₀ hz).mp
    nlinarith [hl]
  have hb : Tendsto (fun z => (K:ℝ)*(r z)^2*|κ-kappa a (h z,r z)|) l (𝓝 0) := by
    simpa using ((hr.pow 2).const_mul (K:ℝ)).mul ((tendsto_const_nhds.sub hf.2).abs)
  have he : Tendsto (fun z => slope ((κ,r z),M a (h z,r z))-lambda a (h z,r z)) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound hb)
  simpa only [sub_add_cancel,zero_add] using he.add hf.1
end QuinticLienard.QuinticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ActualError
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
lemma j_analytic {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (j a t κ) r :=
  (QuadraticFit.slope_analytic (k:=κ) (radius_pos he) (m_abs_lt he)).comp
    (f:=fun s=>((κ,s),m a t s)) r ((contDiffAt_const.prodMk contDiffAt_id).prodMk (m_analytic he))
lemma j_spec {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) : H ((j a t κ r,κ),r)=m a t r :=
  QuadraticFit.slope_spec (radius_pos he) (m_abs_lt he)
lemma j_deriv {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) :
    HasDerivAt (j a t κ) (-κ*g a t r/r+coeff a t κ r*err a t κ r) r := by
  have hj := (j_analytic (κ:=κ) he).differentiableAt (by simp)
  have hd := (H_analytic (d:=j a t κ r) (k:=κ) (radius_pos he)).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f:=fun s=>((j a t κ s,κ),s)) r
      ((hj.hasDerivAt.prodMk (hasDerivAt_const r κ)).prodMk (hasDerivAt_id r))
  have hev : (fun s=>H ((j a t κ s,κ),s)) =ᶠ[𝓝 r] m a t := by
    filter_upwards [adm_eventually he] with s hs
    exact j_spec hs
  have hq := hd.unique ((m_deriv he).congr_of_eventuallyEq hev)
  rw [fderiv_model] at hq
  change deriv (j a t κ) r*P ((j a t κ r,κ),r)+0*Q ((j a t κ r,κ),r)+1*Hr ((j a t κ r,κ),r)=_ at hq
  have hw := width_identity (d:=j a t κ r) (k:=κ) (radius_pos he)
  change κ*P ((j a t κ r,κ),r)+j a t κ r=(r*Hr ((j a t κ r,κ),r)+H ((j a t κ r,κ),r))/(r^2-H ((j a t κ r,κ),r)^2) at hw
  rw [j_spec he] at hw
  have hP := (QuadraticVariation.P_pos (d:=j a t κ r) (k:=κ) (radius_pos he)).ne'
  have heq : deriv (j a t κ) r = -κ*g a t r/r+coeff a t κ r*err a t κ r := by
    dsimp only [coeff,err]
    change κ*P ((j a t κ r,κ),r)+j a t κ r=(r*Hr ((j a t κ r,κ),r)+m a t r)/g a t r at hw
    have hw' := (eq_div_iff (g_pos he).ne').mp hw
    have hq' : (deriv (j a t κ) r*P ((j a t κ r,κ),r)+Hr ((j a t κ r,κ),r))*r = -m a t r+g a t r*k a t r := by
      calc
        _ = (-m a t r/r+g a t r/r*k a t r)*r := by
          congr 1
          simpa only [zero_mul,one_mul,add_zero] using hq
        _ = _ := by field_simp [(radius_pos he).ne']
    field_simp [(radius_pos he).ne',hP]
    nlinarith [hw',hq']
  rw [←heq]
  exact hj.hasDerivAt
lemma err_deriv {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) :
    HasDerivAt (err a t κ) (-coeff a t κ r*err a t κ r-g a t r/r*(c a t r-κ)) r := by
  convert! (k_deriv he).sub (j_deriv (κ:=κ) he) using 1
  ring
lemma coeff_pos {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) : 0<coeff a t κ r :=
  div_pos (g_pos he) (mul_pos (radius_pos he) (QuadraticVariation.P_pos (radius_pos he)))
lemma coeff_continuous {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) : ContinuousAt (coeff a t κ) r := by
  have hq : ContinuousAt (fun s=>((j a t κ s,κ),s)) r :=
    (((j_analytic he).continuousAt.prodMk continuousAt_const).prodMk continuousAt_id)
  have hP : ContinuousAt (fun s=>P ((j a t κ s,κ),s)) r :=
    (P_analytic (d:=j a t κ r) (k:=κ) (radius_pos he)).continuousAt.comp (f:=fun s=>((j a t κ s,κ),s)) hq
  exact ((continuousAt_id.pow 2).sub ((m_analytic he).continuousAt.pow 2)).div
    (continuousAt_id.mul hP) (mul_ne_zero (radius_pos he).ne' (QuadraticVariation.P_pos (radius_pos he)).ne')
lemma err_tendsto {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) (κ : ℝ) :
    Tendsto (err a t κ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hj := QuinticFit.fixed_slope_limit (a:=a) ((base_spec he).1.trans (base_spec he).2.1) κ
    (base_tendsto he) (tendsto_id.mono_left inf_le_left) self_mem_nhdsWithin
  change Tendsto (fun s=>k a t s-QuadraticFit.slope ((κ,s),QuinticFit.M a (b a t s,s))) (𝓝[>] (0:ℝ)) (𝓝 0)
  simpa only [sub_self,id_eq] using (small_limits he).2.2.1.sub hj
lemma label_analytic {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (label a t κ) r :=
  (QuadraticFit.label_analytic (k:=κ) (radius_pos he) (A_abs_lt he)).comp
    (f:=fun s=>((κ,s),A a t s)) r ((contDiffAt_const.prodMk contDiffAt_id).prodMk (A_analytic he))
lemma label_spec {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) :
    ReferenceCharacteristic.A ((label a t κ r,κ),r)=A a t r :=
  QuadraticFit.label_spec (radius_pos he) (A_abs_lt he)
lemma label_J {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) :
    ReferenceCharacteristic.J ((label a t κ r,κ),r)=j a t κ r := by
  symm
  apply QuadraticFit.slope_eq (radius_pos he) (m_abs_lt he)
  have hh := label_spec (κ:=κ) he
  change H ((ReferenceCharacteristic.J ((label a t κ r,κ),r),κ),r)/r=m a t r/r at hh
  exact (div_left_inj' (radius_pos he).ne').mp hh
lemma label_deriv {a : Fin 6 → ℝ} {t κ r : ℝ} (he : Adm a t r) :
    HasDerivAt (label a t κ) (err a t κ r*(1-(A a t r)^2)/ReferenceCharacteristic.Az ((label a t κ r,κ),r)) r := by
  have hz := (label_analytic (κ:=κ) he).differentiableAt (by simp)
  have hd := (ReferenceCharacteristic.A_analytic (q:=((label a t κ r,κ),r)) (radius_pos he)).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f:=fun s=>((label a t κ s,κ),s)) r
      ((hz.hasDerivAt.prodMk (hasDerivAt_const r κ)).prodMk (hasDerivAt_id r))
  have hev : (fun s=>ReferenceCharacteristic.A ((label a t κ s,κ),s)) =ᶠ[𝓝 r] A a t := by
    filter_upwards [adm_eventually he] with s hs
    exact label_spec hs
  have hq := hd.unique ((A_deriv he).congr_of_eventuallyEq hev)
  rw [fderiv_model] at hq
  have hs := (ReferenceCharacteristic.A_analytic (q:=((label a t κ r,κ),r)) (radius_pos he)).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_const r (label a t κ r,κ)).prodMk (hasDerivAt_id r))
  have hs' := hs.unique (ReferenceCharacteristic.A_deriv (radius_pos he))
  change direction ((0,0),1) ReferenceCharacteristic.A ((label a t κ r,κ),r)=_ at hs'
  rw [hs',label_spec he,label_J he] at hq
  have hn := (ReferenceCharacteristic.Az_pos (z:=label a t κ r) (k:=κ) (radius_pos he)).ne'
  have heq : deriv (label a t κ) r=err a t κ r*(1-(A a t r)^2)/ReferenceCharacteristic.Az ((label a t κ r,κ),r) := by
    apply (eq_div_iff hn).mpr
    dsimp only [ReferenceCharacteristic.Az,err] at hq ⊢
    linarith
  rw [←heq]
  exact hz.hasDerivAt
end QuinticLienard.ActualCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ActualSlopeComparison
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
lemma c_strictAnti {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) :
    StrictAntiOn (c a t) (Ioc 0 r) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 r)
    (fun s hs => (c_deriv (adm_le he hs.1 hs.2)).continuousAt.continuousWithinAt)
  intro s hs
  have he' := adm_le he (interior_subset hs).1 (interior_subset hs).2
  rw [(c_deriv he').deriv]
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (neg_neg_of_pos (g_pos he')) (radius_pos he'))
    (hthird _ (base_spec he').1)
lemma label_strictAnti_of_error {a : Fin 6 → ℝ} {t r κ : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) (herr : err a t κ r≤0) :
    StrictAntiOn (label a t κ) (Ioc 0 r) := by
  have hn : ∀ {s : ℝ}, 0<s → s<r → err a t κ s<0 := ScalarComparison.error_negative_before (radius_pos he)
    (fun s hs => (coeff_continuous (adm_le he hs.1 hs.2)).continuousWithinAt)
    (fun s hs => coeff_pos (adm_le he hs.1 hs.2))
    (fun s hs => div_pos (g_pos (adm_le he hs.1 hs.2)) hs.1)
    (c_strictAnti he hthird) (fun s hs => err_deriv (adm_le he hs.1 hs.2))
    (err_tendsto he κ) herr
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 r)
    (fun s hs => (label_deriv (adm_le he hs.1 hs.2)).continuousAt.continuousWithinAt)
  intro s hs
  rw [interior_Ioc] at hs
  have he' := adm_le he hs.1 hs.2.le
  rw [(label_deriv (κ:=κ) he').deriv]
  have hg : 0<1-(A a t s)^2 := by
    have hh := sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1) |>.mpr (A_abs_lt he')
    nlinarith [sq_abs (A a t s)]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (hn hs.1 hs.2) hg)
    (ReferenceCharacteristic.Az_pos (radius_pos he'))
lemma j_eq_lambda {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    j a t (QuinticFit.kappa a (point a t r)) r=QuinticFit.lambda a (point a t r) := by
  apply QuadraticFit.slope_eq (radius_pos he) (m_abs_lt he)
  exact (QuinticFit.spec a (base_spec he).1 (radius_pos he)).1
lemma L_matched {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    ReferenceCharacteristic.L ((label a t (QuinticFit.kappa a (point a t r)) r,
      QuinticFit.kappa a (point a t r)),r)=L a t r := by
  dsimp only [ReferenceCharacteristic.L,ReferenceCharacteristic.D,L]
  rw [label_J he,j_eq_lambda he]
  congr 1
  exact (QuinticFit.spec a (base_spec he).1 (radius_pos he)).2
lemma rate_gt_reference {a : Fin 6 → ℝ} {t r κ s : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) (herr : err a t κ r≤0)
    (hs : 0<s) (hsr : s<r) :
    ReferenceCharacteristic.E ((label a t κ r,κ),s)<rate a t s := by
  have hz := label_strictAnti_of_error he hthird herr ⟨hs,hsr.le⟩ ⟨radius_pos he,le_rfl⟩ hsr
  have hm : StrictMono (fun z=>ReferenceCharacteristic.E ((z,κ),s)) := by
    apply strictMono_of_deriv_pos
    intro z
    rw [(ReferenceCharacteristic.E_z_deriv (z:=z) (k:=κ) hs).deriv]
    exact mul_pos (ReferenceCharacteristic.K_pos hs) (ReferenceCharacteristic.Az_pos hs)
  have hh := hm hz
  change _ < 2*ReferenceCharacteristic.A ((label a t κ s,κ),s)/(s*(1-ReferenceCharacteristic.A ((label a t κ s,κ),s)^2)) at hh
  rw [label_spec (adm_le he hs hsr.le)] at hh
  exact hh

theorem fitted_slope_lt_oai {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) :
    QuinticFit.lambda a (point a t r)<k a t r := by
  let κ := QuinticFit.kappa a (point a t r)
  by_contra! hn
  have herr : err a t κ r≤0 := by
    dsimp only [err,κ]
    rw [j_eq_lambda he]
    linarith
  have hp : 0<L a t r-ReferenceCharacteristic.L ((label a t κ r,κ),r) := by
    apply ReferenceCharacteristic.strictMono_zero_pos (f:=fun s=>L a t s-ReferenceCharacteristic.L ((label a t κ r,κ),s)) (radius_pos he)
      (by simpa only [sub_self] using ((small_limits he).2.1.sub
        (ReferenceCharacteristic.L_tendsto_zero (label a t κ r) κ)))
    apply strictMonoOn_of_deriv_pos (convex_Ioc 0 r)
      (fun s hs => ((L_deriv (adm_le he hs.1 hs.2)).sub
        (ReferenceCharacteristic.L_deriv hs.1)).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Ioc] at hs
    rw [((L_deriv (adm_le he hs.1 hs.2.le)).sub
      (ReferenceCharacteristic.L_deriv (z:=label a t κ r) (k:=κ) hs.1)).deriv]
    exact sub_pos.mpr (rate_gt_reference he hthird herr hs.1 hs.2)
  rw [L_matched he,sub_self] at hp
  exact (lt_irrefl 0) hp
end QuinticLienard.ActualCharacteristic

end OAI
end

theorem solution : type_of% @OAI.QuinticLienard.ActualCharacteristic.fitted_slope_lt_oai := @OAI.QuinticLienard.ActualCharacteristic.fitted_slope_lt_oai
