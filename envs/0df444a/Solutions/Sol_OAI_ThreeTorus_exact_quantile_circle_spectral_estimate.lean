-- Prove2me | solution 1 for OAI.ThreeTorus.exact_quantile_circle_spectral_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:09:28.698504+00:00
-- url     : https://prove2.me/submissions/a4888c41-7afe-43fa-9d48-6fc0cead9ca4

import Mathlib
import Definitions.Def_OAIQ13Tt000
import Theorems.Thm_OAI_ThreeTorus_exact_passage_circle_spectral_limit

section
-- module Solutions.OAIQ13_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Averaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-frequency fast averaging on the compact slow circle. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace ThreeTorus

private lemma fast_integral_character (k : ℤ) :
    (∫ z : UnitAddCircle, fourier k z ∂fastHaar) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right hk]
    exact integral_eq_zero_of_add_right_eq_neg (μ := fastHaar)
      (fourier_add_half_inv_index hk (by norm_num))

private lemma fast_integral_mFourier (nu : Fin 2 → ℤ) :
    (∫ z : UnitAddTorus (Fin 2), UnitAddTorus.mFourier nu z ∂fastProduct) =
      if nu = 0 then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin 2))) 0 nu
  simpa only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, mul_one,
    eq_comm, MeasureSpace.pi, instMeasureSpaceUnitAddCircle] using! h

lemma continuous_fastOrbit (n : ℕ) (beta : UnitAddCircle) : Continuous (fastOrbit n beta) := by
  unfold fastOrbit
  fun_prop

private lemma fast_integrable_diag (F : C(UnitAddTorus (Fin 2),ℂ)) (n : ℕ) (beta : UnitAddCircle) :
    Integrable (fun z => F (fastOrbit n beta z)) fastHaar :=
  (F.continuous.comp (continuous_fastOrbit n beta)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private lemma fast_integrable_prod (F : C(UnitAddTorus (Fin 2),ℂ)) :
    Integrable F fastProduct := F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma fast_mFourier_diagonal (nu : Fin 2 → ℤ) (n : ℕ) (beta z : UnitAddCircle) :
    UnitAddTorus.mFourier nu (fastOrbit n beta z) =
      fourier (nu 1) beta * fourier (nu 0+nu 1*(n:ℤ)) z := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two,
    fastOrbit,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [fourier_apply,zsmul_add,smul_smul,AddCircle.toCircle_add,Circle.coe_mul,
    add_zsmul]
  ring

lemma fast_mFourier_limit (nu : Fin 2 → ℤ) (beta : ℕ → UnitAddCircle) :
    Tendsto (fun n => ∫ z, UnitAddTorus.mFourier nu (fastOrbit n (beta n) z) ∂fastHaar)
      atTop (𝓝 (∫ z, UnitAddTorus.mFourier nu z ∂fastProduct)) := by
  classical
  simp_rw [fast_mFourier_diagonal,integral_const_mul,fast_integral_character]
  rw [fast_integral_mFourier]
  by_cases hz : nu = 0
  · subst nu
    simp
  · rw [ite_eq_right hz]
    have hf : ∀ᶠ n : ℕ in atTop, nu 0+nu 1*(n:ℤ) ≠ 0 := by
      by_cases h1 : nu 1 = 0
      · have h0 : nu 0 ≠ 0 := by
          intro h0
          apply hz
          ext i
          fin_cases i <;> assumption
        exact Eventually.of_forall (fun n => by simpa [h1] using h0)
      · have hinj : Function.Injective (fun n : ℕ => nu 0+nu 1*(n:ℤ)) := by
          intro a b hab
          exact_mod_cast mul_left_cancel₀ h1 (add_left_cancel hab)
        have ht := hinj.tendsto_cofinite
        rw [Nat.cofinite_eq_atTop] at ht
        exact ht.eventually (eventually_cofinite_ne 0)
    apply tendsto_const_nhds.congr'
    filter_upwards [hf] with n hn
    simp [hn]

lemma fast_polynomial_limit (F : C(UnitAddTorus (Fin 2),ℂ))
    (hF : F ∈ Submodule.span ℂ (range (UnitAddTorus.mFourier (d := Fin 2))))
    (beta : ℕ → UnitAddCircle) :
    Tendsto (fun n => ∫ z, F (fastOrbit n (beta n) z) ∂fastHaar)
      atTop (𝓝 (∫ z, F z ∂fastProduct)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨nu,rfl⟩ := h
    exact fast_mFourier_limit nu beta
  | zero => simp
  | add F G _ _ ihF ihG =>
    simp only [ContinuousMap.add_apply]
    simp_rw [integral_add (fast_integrable_diag F _ _) (fast_integrable_diag G _ _)]
    rw [integral_add (fast_integrable_prod F) (fast_integrable_prod G)]
    exact ihF.add ihG
  | smul a F _ ih =>
    simp only [ContinuousMap.smul_apply,smul_eq_mul]
    simp_rw [integral_const_mul]
    exact tendsto_const_nhds.mul ih

lemma fast_average_diagonal_dist (F G : C(UnitAddTorus (Fin 2),ℂ))
    (n : ℕ) (beta : UnitAddCircle) :
    dist (∫ z, F (fastOrbit n beta z) ∂fastHaar) (∫ z, G (fastOrbit n beta z) ∂fastHaar) ≤
      dist F G := by
  rw [dist_eq_norm,dist_eq_norm,← integral_sub (fast_integrable_diag F n beta)
    (fast_integrable_diag G n beta)]
  apply (norm_integral_le_of_norm_le_const (C := ‖F-G‖) ?_).trans_eq (by simp)
  exact Eventually.of_forall (fun z => (F-G).norm_coe_le_norm (fastOrbit n beta z))

lemma fast_average_product_dist (F G : C(UnitAddTorus (Fin 2),ℂ)) :
    dist (∫ z, F z ∂fastProduct) (∫ z, G z ∂fastProduct) ≤ dist F G := by
  rw [dist_eq_norm,dist_eq_norm,← integral_sub (fast_integrable_prod F) (fast_integrable_prod G)]
  apply (norm_integral_le_of_norm_le_const (C := ‖F-G‖) ?_).trans_eq (by simp)
  exact Eventually.of_forall (fun z => (F-G).norm_coe_le_norm z)

/-- Fast averaging on the two-torus, uniform over any sequence of offsets.
This is the compact quotient form of source Lemma `fast-average`. -/
lemma fast_average_torus (F : C(UnitAddTorus (Fin 2),ℂ)) (beta : ℕ → UnitAddCircle) :
    Tendsto (fun n => ∫ z, F (fastOrbit n (beta n) z) ∂fastHaar)
      atTop (𝓝 (∫ z, F z ∂fastProduct)) := by
  have hd : F ∈ closure (↑(Submodule.span ℂ (range
      (UnitAddTorus.mFourier (d := Fin 2)))) : Set C(UnitAddTorus (Fin 2),ℂ)) := by
    rw [← Submodule.topologicalClosure_coe,UnitAddTorus.span_mFourier_closure_eq_top]
    trivial
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨G,hG,hdist⟩ := Metric.mem_closure_iff.mp hd (eps/3) (by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (fast_polynomial_limit G hG beta) (eps/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h1 := fast_average_diagonal_dist F G n (beta n)
  have h2 := fast_average_product_dist G F
  have h3 := hN n hn
  have h4 := dist_triangle (∫ z, F (fastOrbit n (beta n) z) ∂fastHaar)
    (∫ z, G (fastOrbit n (beta n) z) ∂fastHaar) (∫ z, F z ∂fastProduct)
  have h5 := dist_triangle (∫ z, G (fastOrbit n (beta n) z) ∂fastHaar)
    (∫ z, G z ∂fastProduct) (∫ z, F z ∂fastProduct)
  rw [dist_comm G F] at h2
  linarith

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Filter Set Function
open scoped Topology BigOperators

lemma continuous_compactRealTorus {H : ℝ × UnitAddCircle → ℂ} (hH : Continuous H)
    {M : ℕ} (hS : ∀ s y, (M:ℝ) ≤ |s| → H (s,y) = 0) :
    Continuous (compactRealTorus H hH M) := by
  apply AddCircle.liftIoc_zero_continuous
  · ext y
    change H ((2*(M:ℝ))*0-M,y) = H ((2*(M:ℝ))*1-M,y)
    rw [show (2*(M:ℝ))*0-M = -(M:ℝ) by ring,
      show (2*(M:ℝ))*1-M = (M:ℝ) by ring]
    rw [hS _ _ (by simp),hS _ _ (by simp)]
  · exact ((ContinuousMap.curry ⟨H,hH⟩).continuous.comp
      ((continuous_const.mul continuous_id).sub continuous_const)).continuousOn

lemma compactRealTorus_coe {H : ℝ × UnitAddCircle → ℂ} (hH : Continuous H)
    (M : ℕ) {x : ℝ} (hx : x ∈ Ioc 0 1) (y : UnitAddCircle) :
    compactRealTorus H hH M (x:UnitAddCircle) y = H ((2*(M:ℝ))*x-M,y) := by
  rw [compactRealTorus,AddCircle.liftIoc_coe_apply (by simpa using hx)]
  rfl

lemma compact_rescale_integral {f : ℝ → ℂ} {M : ℕ} (hM : 0 < M)
    (hS : ∀ s, (M:ℝ) ≤ |s| → f s = 0) :
    (2*(M:ℝ)) • (∫ x in Ioc (0:ℝ) 1, f ((2*(M:ℝ))*x-M)) = ∫ s, f s := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have he := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) f
    (by positivity : 2*(M:ℝ) ≠ 0) (-(M:ℝ))
  simp only [mul_zero,zero_add,mul_one,show 2*(M:ℝ)+ -(M:ℝ) = (M:ℝ) by ring] at he
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  simp_rw [sub_eq_add_neg]
  rw [he,smul_smul,mul_inv_cancel₀ (by positivity : 2*(M:ℝ) ≠ 0),one_smul,
    intervalIntegral.integral_of_le (by linarith : -(M:ℝ) ≤ M)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro s hs
  apply hS
  by_contra hn
  have hh := abs_lt.mp (lt_of_not_ge hn)
  exact hs ⟨hh.1,hh.2.le⟩

lemma circle_fast_rescale (n M : ℕ) (x : ℝ) :
    (((n:ℝ)*((2*(M:ℝ))*x-M) : ℝ):UnitAddCircle) =
      ((n*(2*M):ℕ):ℤ) • (x:UnitAddCircle) := by
  have he : (n:ℝ)*((2*(M:ℝ))*x-M) = ((n*(2*M):ℕ):ℝ)*x-((n*M:ℕ):ℝ) := by
    push_cast
    ring
  rw [he,AddCircle.coe_sub]
  have hz : (((n*M:ℕ):ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨(n*M:ℕ),by simp⟩
  rw [hz,sub_zero]
  simpa only [zsmul_eq_mul,Int.cast_natCast] using
    (AddCircle.coe_zsmul (p := (1:ℝ)) (n := ((n*(2*M):ℕ):ℤ)) (x := x))

lemma compactRealTorus_integral {H : ℝ × UnitAddCircle → ℂ} (hH : Continuous H)
    {M : ℕ} (hM : 0 < M) (hS : ∀ s y, (M:ℝ) ≤ |s| → H (s,y) = 0)
    (n : ℕ) (β : UnitAddCircle) :
    (2*(M:ℝ)) • (∫ x, compactRealTorus H hH M x
      (((n*(2*M):ℕ):ℤ) • x+β) ∂AddCircle.haarAddCircle) =
      ∫ s, H (s,(((n:ℝ)*s:ℝ):UnitAddCircle)+β) := by
  have he := AddCircle.integral_preimage 1 0 (fun x => compactRealTorus H hH M x
    (((n*(2*M):ℕ):ℤ) • x+β))
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] at he
  rw [← he]
  convert compact_rescale_integral (M := M) hM
    (f := fun s => H (s,(((n:ℝ)*s:ℝ):UnitAddCircle)+β)) (fun s hs => hS s _ hs) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [compactRealTorus_coe hH M hx,circle_fast_rescale]

lemma compactRealTorus_marginal {H : ℝ × UnitAddCircle → ℂ} (hH : Continuous H)
    {M : ℕ} (hM : 0 < M) (hS : ∀ s y, (M:ℝ) ≤ |s| → H (s,y) = 0) :
    (2*(M:ℝ)) • (∫ x, ∫ y, compactRealTorus H hH M x y
      ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle) =
      ∫ s, ∫ y, H (s,y) ∂AddCircle.haarAddCircle := by
  have he := AddCircle.integral_preimage 1 0 (fun x => ∫ y, compactRealTorus H hH M x y
    ∂AddCircle.haarAddCircle)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] at he
  rw [← he]
  convert compact_rescale_integral (M := M) hM
    (f := fun s => ∫ y, H (s,y) ∂AddCircle.haarAddCircle)
    (fun s hs => by simp only [hS s _ hs,integral_zero]) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  apply integral_congr_ae
  exact ae_of_all _ (fun y => compactRealTorus_coe hH M hx y)

/-- Source fast averaging on the real frequency axis, for compactly supported
continuous data and every sequence of circle offsets. The frequency parameter
is the actual passage integer, not a synthetic independent variable. -/
lemma fast_average_real_compact {H : ℝ × UnitAddCircle → ℂ} (hH : Continuous H)
    {M : ℕ} (hM : 0 < M) (hS : ∀ s y, (M:ℝ) ≤ |s| → H (s,y) = 0)
    (β : ℕ → UnitAddCircle) :
    Tendsto (fun n : ℕ => ∫ s, H (s,(((n:ℝ)*s:ℝ):UnitAddCircle)+β n)) atTop
      (𝓝 (∫ s, ∫ y, H (s,y) ∂AddCircle.haarAddCircle)) := by
  have hc := continuous_compactRealTorus hH hS
  let G : C(UnitAddTorus (Fin 2),ℂ) := ⟨fun z => compactRealTorus H hH M (z 0) (z 1),
    (hc.comp (continuous_apply 0)).eval (continuous_apply 1)⟩
  have hfreq : Tendsto (fun n : ℕ => n*(2*M)) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n (by omega)) tendsto_id
  have ht := ((fast_average_torus G (fun k => β (k/(2*M)))).comp hfreq).const_smul (2*(M:ℝ))
  have hi : (∫ z, G z ∂(Measure.pi fun _ : Fin 2 => AddCircle.haarAddCircle)) =
      ∫ x, ∫ y, compactRealTorus H hH M x y
      ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
    calc
      _ = ∫ p : UnitAddCircle × UnitAddCircle, compactRealTorus H hH M p.1 p.2
          ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle :=
        (measurePreserving_finTwoArrow AddCircle.haarAddCircle).integral_comp
          MeasurableEquiv.finTwoArrow.measurableEmbedding _
      _ = _ := integral_prod _ (((hc.comp continuous_fst).eval continuous_snd).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have htarget : (2*(M:ℝ)) • (∫ z, G z ∂(Measure.pi fun _ : Fin 2 => AddCircle.haarAddCircle)) =
      ∫ s, ∫ y, H (s,y) ∂AddCircle.haarAddCircle := by
    rw [hi]
    exact compactRealTorus_marginal hH hM hS
  rw [← htarget]
  apply ht.congr'
  filter_upwards [] with n
  change (2*(M:ℝ)) • (∫ x, compactRealTorus H hH M x
    (((n*(2*M):ℕ):ℤ) • x+β (n*(2*M)/(2*M))) ∂AddCircle.haarAddCircle) = _
  rw [Nat.mul_div_left n (by omega : 0 < 2*M)]
  exact compactRealTorus_integral hH hM hS n (β n)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter
open scoped Topology

lemma fast_average_real_compact_real {H : ℝ × UnitAddCircle → ℝ} (hH : Continuous H)
    {M : ℕ} (hM : 0 < M) (hS : ∀ s y, (M:ℝ) ≤ |s| → H (s,y) = 0)
    (β : ℕ → UnitAddCircle) :
    Tendsto (fun n : ℕ => ∫ s, H (s,(((n:ℝ)*s:ℝ):UnitAddCircle)+β n)) atTop
      (𝓝 (∫ s, ∫ y, H (s,y) ∂AddCircle.haarAddCircle)) := by
  have ht := fast_average_real_compact (Complex.continuous_ofReal.comp hH) hM
    (fun s y hs => by simp only [Function.comp_apply,hS s y hs,Complex.ofReal_zero]) β
  simp only [Function.comp_apply,integral_complex_ofReal] at ht
  simpa only [Function.comp_def,Complex.ofReal_re] using
    Complex.continuous_re.continuousAt.tendsto.comp ht

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Jitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cumulative distribution, smooth quantile inverse, and positive smooth neutral jitter laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics

/-! Approximation of a positive smooth law.
The cumulative distribution and its local smooth inverse are constructed from
the positive smooth density, not assumed as an additional hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus

lemma cumulative_sub (ρ : ℝ → ℝ) (hi : Integrable ρ) (x y : ℝ) :
    cumulative ρ y - cumulative ρ x = ∫ t in x..y, ρ t :=
  intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn

lemma cumulative_eq_primitive (ρ : ℝ → ℝ) (hi : Integrable ρ) :
    cumulative ρ = fun y => cumulative ρ 0 + ∫ t in 0..y, ρ t := by
  funext y
  linarith [cumulative_sub ρ hi 0 y]

lemma hasDerivAt_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ) (y : ℝ) :
    HasDerivAt (cumulative ρ) (ρ y) y := by
  rw [cumulative_eq_primitive ρ hi]
  convert (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 y)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add
      (cumulative ρ 0) using 1
  all_goals try with_reducible_and_instances rfl

lemma contDiff_cumulative {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cumulative ρ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun y => (hasDerivAt_cumulative hρ.continuous hi y).differentiableAt, ?_⟩
  have hd : deriv (cumulative ρ) = ρ := funext fun y =>
    (hasDerivAt_cumulative hρ.continuous hi y).deriv
  rw [hd]
  exact hρ

lemma strictMono_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) : StrictMono (cumulative ρ) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_cumulative hc hi) hp

lemma cumulative_atBot {ρ : ℝ → ℝ} :
    Tendsto (cumulative ρ) atBot (𝓝 0) :=
  tendsto_integral_Iic_zero tendsto_id

lemma cumulative_atTop {ρ : ℝ → ℝ} (hi : Integrable ρ) (hm : ∫ y, ρ y = 1) :
    Tendsto (cumulative ρ) atTop (𝓝 1) := by
  change Tendsto (fun y : ℝ => ∫ x in Iic y, ρ x) atTop (𝓝 1)
  simpa only [hm, id_eq] using
    (aecover_Iic (μ := (volume : Measure ℝ)) tendsto_id).integral_tendsto_of_countably_generated hi

lemma cumulative_mem_Ioo {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (y : ℝ) :
    cumulative ρ y ∈ Ioo (0 : ℝ) 1 := by
  have hs := strictMono_cumulative hc hi hp
  constructor
  · exact (hs.monotone.le_of_tendsto cumulative_atBot (y-1)).trans_lt
      (hs (by linarith : y-1 < y))
  · exact (hs (by linarith : y < y+1)).trans_le
      (hs.monotone.ge_of_tendsto (cumulative_atTop hi hm) (y+1))

lemma range_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    range (cumulative ρ) = Ioo (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨y,rfl⟩
    exact cumulative_mem_Ioo hc hi hp hm y
  · intro z hz
    obtain ⟨a,ha⟩ := (cumulative_atBot.eventually (gt_mem_nhds hz.1)).exists
    obtain ⟨b,hb⟩ := ((cumulative_atTop hi hm).eventually (lt_mem_nhds hz.2)).exists
    exact intermediate_value_univ a b
      (continuous_iff_continuousAt.mpr fun y => (hasDerivAt_cumulative hc hi y).continuousAt)
      ⟨ha.le,hb.le⟩

lemma cumulative_quantile {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    cumulative ρ (quantile ρ a) = a := by
  apply invFun_eq
  change a ∈ range (cumulative ρ)
  rw [range_cumulative hc hi hp hm]
  exact ha

lemma quantile_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (y : ℝ) :
    quantile ρ (cumulative ρ y) = y :=
  leftInverse_invFun (strictMono_cumulative hc hi hp).injective y

lemma contDiffAt_invFun_of_deriv_ne_zero {F : ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hinj : Injective F)
    {x d : ℝ} (hd : HasDerivAt F d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFun F) (F x) := by
  let e := hF.contDiffAt.toOpenPartialHomeomorph F (hd.hasFDerivAt_equiv hd0) (by simp)
  have hx : x ∈ e.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = F := rfl
  have hy : F x ∈ e.target := by simpa only [he] using e.map_source hx
  have hs : e.symm (F x) = x := by simpa only [he] using e.left_inv hx
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (F x) := by
    apply e.contDiffAt_symm_deriv hd0 hy
    · simpa only [he, hs] using hd
    · simpa only [he, hs] using hF.contDiffAt (x := x)
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hy] with y hy'
  apply hinj
  have hr : F (e.symm y) = y := by simpa only [he] using e.right_inv hy'
  rw [invFun_eq ⟨e.symm y,hr⟩, hr]

lemma contDiffOn_quantile {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (quantile ρ) (Ioo (0 : ℝ) 1) := by
  intro a ha
  have hh := contDiffAt_invFun_of_deriv_ne_zero (contDiff_cumulative hρ hi)
    (strictMono_cumulative hρ.continuous hi hp).injective
    (hasDerivAt_cumulative hρ.continuous hi (quantile ρ a)) (hp _).ne'
  rw [cumulative_quantile hρ.continuous hi hp hm ha] at hh
  exact hh.contDiffWithinAt

lemma hasDerivAt_quantile {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (quantile ρ) (ρ (quantile ρ a))⁻¹ a := by
  apply HasDerivAt.of_local_left_inverse
    ((contDiffOn_quantile hρ hi hp hm).contDiffAt (isOpen_Ioo.mem_nhds ha)).continuousAt
    (hasDerivAt_cumulative hρ.continuous hi _) (hp _).ne'
  filter_upwards [isOpen_Ioo.mem_nhds ha] with y hy
  exact cumulative_quantile hρ.continuous hi hp hm hy

lemma contDiff_periodize {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (periodize f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R + |x| + 1)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hs : ∀ᶠ y in 𝓝 x, support (fun k : ℤ => f (y+k)) ⊆ (s : Set ℤ) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    intro k hk
    have hy' : |y| < |x| + 1 := by
      have := abs_add_le (y-x) x
      have hy'' : |y-x| < 1 := hy
      simpa only [sub_add_cancel] using this.trans_lt (by linarith : |y-x|+|x| < |x|+1)
    have hk' : |y+(k : ℝ)| ≤ R := by
      simpa only [Real.norm_eq_abs] using hR (y+k) (subset_tsupport f hk)
    have hz : |(k : ℝ)| < (N : ℝ) := calc
      |(k : ℝ)| = |(y+k)-y| := by congr 1; ring
      _ ≤ |y+k| + |y| := abs_sub _ _
      _ < ↑N := by linarith
    have hh : -(N : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ ↑N := (abs_le.mp hz.le)
    show k ∈ Finset.Icc (-(N : ℤ)) N
    rw [Finset.mem_Icc]
    exact_mod_cast hh
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∑ k ∈ s, f (y+k)) :=
    ContDiff.sum fun k _ => hf.comp (contDiff_id.add contDiff_const)
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  exact finsum_eq_sum_of_support_subset _ hy

lemma periodize_eq_on_unit {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : periodize f x = f x := by
  unfold periodize
  convert finsum_eq_single (fun k : ℤ => f (x+k)) 0 ?_ using 1
  · simp
  · intro k hk
    by_contra hn
    have hh := hs (show x+(k : ℝ) ∈ support f from hn)
    have h1 : (-1 : ℝ) < (k : ℝ) := by linarith [hx.2, hh.1]
    have h2 : (k : ℝ) < (1 : ℝ) := by linarith [hx.1, hh.2]
    have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (1 : ℤ) := by exact_mod_cast h2
    omega

lemma periodize_eq_fract {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1) (x : ℝ) :
    periodize f x = f (Int.fract x) := by
  have hh := (periodize_periodic f).sub_zsmul_eq (x := x) ⌊x⌋
  have he : periodize f (Int.fract x) = periodize f x := by
    simpa only [Int.fract, zsmul_eq_mul, mul_one] using hh
  rw [← he]
  exact periodize_eq_on_unit hs ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

lemma contDiff_cutoff_quantile {ρ ξ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1)
    (hξ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ)
    (hs : tsupport ξ ⊆ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => ξ a * quantile ρ a) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  by_cases ha : a ∈ tsupport ξ
  · exact hξ.contDiffAt.mul ((contDiffOn_quantile hρ hi hp hm).contDiffAt
      (isOpen_Ioo.mem_nhds (hs ha)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ha] with b hb
    simp only [Pi.zero_apply] at hb
    simp only [hb, zero_mul]

lemma lawJitter_smooth {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawJitter ρ c) :=
  contDiff_periodize (contDiff_cutoff_quantile hρ hi hp hm c.ξ_smooth c.ξ_support)
    c.ξ_compact.mul_right

lemma lawJitter_eq_quantile {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hδ : 0 < δ) {a : ℝ} (ha : a ∈ Icc δ (1-δ)) :
    lawJitter ρ c a = quantile ρ a := by
  rw [lawJitter, periodize_eq_on_unit, c.ξ_one a ha, one_mul]
  · exact (support_mul_subset_left _ _).trans ((subset_tsupport _).trans c.ξ_support)
  · constructor <;> linarith [ha.1,ha.2]

lemma lawJitter_deriv_pos {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ)
    {a : ℝ} (ha : a ∈ Ioo δ (1-δ)) :
    HasDerivAt (lawJitter ρ c) (ρ (quantile ρ a))⁻¹ a ∧
      0 < (ρ (quantile ρ a))⁻¹ := by
  refine ⟨?_, inv_pos.mpr (hp _)⟩
  apply (hasDerivAt_quantile hρ hi hp hm
    (show a ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [ha.1], by linarith [ha.2]⟩)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  exact lawJitter_eq_quantile c hδ ⟨hb.1.le,hb.2.le⟩

lemma lawPsi_smooth {δ : ℝ} (c : LawCutoffs δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawPsi c) :=
  contDiff_periodize c.ψ_smooth c.ψ_compact

lemma lawPsi_eq {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : lawPsi c a = c.ψ a := by
  apply periodize_eq_on_unit _ ha
  intro x hx
  have hh := c.ψ_support (subset_tsupport _ hx)
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

lemma lawPsi_bounds {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (a : ℝ) :
    0 ≤ lawPsi c a ∧ lawPsi c a ≤ 1 := by
  have hs : support c.ψ ⊆ Ioo (0 : ℝ) 1 := fun x hx => by
    have hh := c.ψ_support (subset_tsupport _ hx)
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  rw [lawPsi, periodize_eq_fract hs]
  exact ⟨c.ψ_nonneg _, c.ψ_le_one _⟩

lemma lawDensity_smooth {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawDensity ρ c) :=
  hρ.mul ((c.ψ_smooth.comp (contDiff_cumulative hρ hi)).pow 2)

lemma lawDensity_bounds {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hp : ∀ y, 0 < ρ y) (y : ℝ) :
    0 ≤ lawDensity ρ c y ∧ lawDensity ρ c y ≤ ρ y := by
  have hh : c.ψ (cumulative ρ y)^2 ≤ 1 := by
    nlinarith [c.ψ_nonneg (cumulative ρ y), c.ψ_le_one (cumulative ρ y)]
  exact ⟨mul_nonneg (hp y).le (sq_nonneg _), by
    simpa only [lawDensity, mul_one] using mul_le_mul_of_nonneg_left hh (hp y).le⟩

lemma lawDensity_compact {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    HasCompactSupport (lawDensity ρ c) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := quantile ρ δ) (b := quantile ρ (1-δ)))
  intro y hy
  have hn : c.ψ (cumulative ρ y) ≠ 0 := by
    intro hh
    exact hy (by simp only [lawDensity, hh, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero])
  have hh := c.ψ_support (subset_tsupport _ hn)
  have hs := strictMono_cumulative hρ.continuous hi hp
  have hleft : cumulative ρ (quantile ρ δ) = δ :=
    cumulative_quantile hρ.continuous hi hp hm ⟨hδ, by linarith⟩
  have hright : cumulative ρ (quantile ρ (1-δ)) = 1-δ :=
    cumulative_quantile hρ.continuous hi hp hm ⟨by linarith, by linarith⟩
  constructor
  · apply hs.le_iff_le.mp
    rw [hleft]
    exact hh.1.le
  · apply hs.le_iff_le.mp
    rw [hright]
    exact hh.2.le

lemma lawDensity_integrable {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) : Integrable (lawDensity ρ c) := by
  apply hi.mono' (lawDensity_smooth c hρ hi).continuous.aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (lawDensity_bounds c hp y).1]
  exact (lawDensity_bounds c hp y).2

lemma integral_lawDensity {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    (∫ y, lawDensity ρ c y) = ∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
  have hh := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (hasDerivAt_cumulative hρ.continuous hi y).hasDerivWithinAt)
    (strictMono_cumulative hρ.continuous hi hp).injective.injOn (fun a => c.ψ a^2)
  rw [image_univ, range_cumulative hρ.continuous hi hp hm, Measure.restrict_univ] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [lawDensity, abs_of_pos (hp y), smul_eq_mul]

lemma integral_cutoff_lower {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    1-4*δ ≤ ∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
  have hs : HasCompactSupport (fun a : ℝ => c.ψ a^2) :=
    c.ψ_compact.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hi : Integrable (fun a : ℝ => c.ψ a^2) :=
    (c.ψ_smooth.continuous.pow 2).integrable_of_hasCompactSupport hs
  calc
    1-4*δ = ∫ a in Icc (2*δ) (1-2*δ), (1 : ℝ) := by
      simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
        Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-2*δ-2*δ)]
      ring
    _ = ∫ a in Icc (2*δ) (1-2*δ), c.ψ a^2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro a ha
      change 1 = c.ψ a^2
      rw [c.ψ_one a ha, one_pow]
    _ ≤ ∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
      apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
      exact Eventually.of_forall fun a ha => ⟨by linarith [ha.1], by linarith [ha.2]⟩

lemma lawDensity_error {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    (∫ y, |ρ y - lawDensity ρ c y|) = 1-∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 ∧
      (∫ y, |ρ y - lawDensity ρ c y|) ≤ 4*δ := by
  have he : (∫ y, |ρ y - lawDensity ρ c y|) = 1-∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
    rw [integral_congr_ae (Eventually.of_forall fun y =>
      abs_of_nonneg (sub_nonneg.mpr (lawDensity_bounds c hp y).2))]
    rw [integral_sub hi (lawDensity_integrable c hρ hi hp), hm,
      integral_lawDensity c hρ hi hp hm]
  refine ⟨he, ?_⟩
  rw [he]
  linarith [integral_cutoff_lower c hδ hδ']

end ThreeTorus

namespace ThreeTorus
open Set Function MeasureTheory
open scoped Topology

lemma continuous_neutralCircleCutoff {δ : ℝ} (c : LawCutoffs δ) :
    Continuous (neutralCircleCutoff c) :=
by
  apply Continuous.quotient_lift
  exact (lawPsi_smooth c).continuous

lemma neutralCircleCutoff_bounds {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ)
    (a : UnitAddCircle) : 0 ≤ neutralCircleCutoff c a ∧ neutralCircleCutoff c a ≤ 1 := by
  induction a using Quotient.inductionOn with
  | h a => exact lawPsi_bounds c hδ a

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

lemma continuous_fourierCoeff_param {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] [LocallyCompactSpace Ω]
    {f : Ω → UnitAddCircle → ℂ} (hf : Continuous f.uncurry) (j : ℤ) :
    Continuous (fun a => fourierCoeff (f a) j) := by
  have hh : Continuous (fun p : Ω × UnitAddCircle => fourier (-j) p.2*f p.1 p.2) :=
    ((fourier (-j)).continuous.comp continuous_snd).mul hf
  simpa only [fourierCoeff,smul_eq_mul,setIntegral_univ] using
    (continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle)
      (f := fun a θ => fourier (-j) θ*f a θ) hh isCompact_univ)

lemma continuous_passageFourierInput {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) :
    Continuous (passageFourierInput m H A).uncurry := by
  exact (hA.comp continuous_swap).mul ((fourier m).continuous.comp (hH.comp continuous_snd))

lemma continuous_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) (j : ℤ) :
    Continuous (exactPassageCoeff m H A j) :=
  continuous_fourierCoeff_param (continuous_passageFourierInput hH hA) j

end ThreeTorus

namespace ThreeTorus

open Function

lemma branchDensity_on {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hg : ∀ x ∈ I, g (J x) = x) {x : ℝ} (hx : x ∈ I) :
    branchDensity I J g D q (J x) = q x/|D x| := by
  simp only [branchDensity,indicator_of_mem (mem_image_of_mem J hx),hg x hx]

lemma contDiffAt_invFunOn_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hinj : InjOn J I) {x d : ℝ} (hx : x ∈ I)
    (hd : HasDerivAt J d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFunOn J I) (J x) := by
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (J x) := by
    apply e.contDiffAt_symm_deriv hd0 hyt
    · simpa only [he,hix] using hd
    · simpa only [he,hix] using hJ.contDiffAt (x := x)
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply hi.continuousAt.eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  have hr : J (e.symm y) = y := by simpa only [he] using e.right_inv hy
  have hp := invFunOn_pos (show y ∈ J '' I from ⟨e.symm y,hyI,hr⟩)
  exact hinj hp.1 hyI (hp.2.trans hr.symm)

lemma isOpen_image_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hd : ∀ x ∈ I, deriv J x ≠ 0) : IsOpen (J '' I) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hdx := (hJ.differentiable (by simp) x).hasDerivAt
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply (e.continuousAt_symm hyt).eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  exact ⟨e.symm y,hyI,by simpa only [he] using e.right_inv hy⟩

lemma support_branchFamily_subset {Ω : Type*} [TopologicalSpace Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ} :
    support (branchFamily I J F) ⊆ (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F := by
  rintro ⟨s,a⟩ hh
  have hs : s ∈ J '' I := by
    by_contra hn
    exact hh (by simp [branchFamily,hn])
  have hp := invFunOn_pos hs
  refine ⟨(invFunOn J I s,a),subset_tsupport F ?_,?_⟩
  · intro hz
    exact hh (by simp [branchFamily,hs,hz])
  · simp only [hp.2]

lemma branchFamily_compact {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) : HasCompactSupport (branchFamily I J F) := by
  apply HasCompactSupport.intro (hc.image (by fun_prop : Continuous (fun p : ℝ × Ω => (J p.1,p.2))))
  intro p hp
  by_contra hn
  exact hp (support_branchFamily_subset hn)

lemma branchFamily_continuous {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × Ω → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : Continuous F) (hc : HasCompactSupport F) (hs : tsupport F ⊆ I ×ˢ univ) :
    Continuous (branchFamily I J F) := by
  classical
  let g := invFunOn J I
  let M := (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F
  have hM : IsCompact M := hc.image (by fun_prop)
  have hzero {p : ℝ × Ω} (hp : p ∉ M) : branchFamily I J F p = 0 :=
    notMem_support.mp (fun hn => hp (support_branchFamily_subset hn))
  have hD : Continuous (deriv J) := hJ.continuous_deriv (by simp)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ M
  · rcases hp with ⟨⟨x,a⟩,hx,rfl⟩
    have hxI : x ∈ I := (hs hx).1
    have hy : J x ∈ J '' I := mem_image_of_mem J hxI
    have hgi := (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)).continuousAt
    have hge : g (J x) = x := by
      exact hinj (invFunOn_pos hy).1 hxI (invFunOn_pos hy).2
    have hgi' : ContinuousAt (fun p : ℝ × Ω => g p.1) (J x,a) :=
      hgi.comp_of_eq continuousAt_fst rfl
    have hin : ContinuousAt (fun p : ℝ × Ω => (g p.1,p.2)) (J x,a) :=
      hgi'.prodMk continuousAt_snd
    have hDen : ContinuousAt (fun p : ℝ × Ω => |deriv J (g p.1)|) (J x,a) :=
      (hD.continuousAt.comp hgi').abs
    have hquot : ContinuousAt (fun p : ℝ × Ω => F (g p.1,p.2) / |deriv J (g p.1)|) (J x,a) := by
      apply (hF.continuousAt.comp hin).div hDen
      simpa only [hge] using abs_ne_zero.mpr (hd x hxI)
    apply hquot.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × Ω in 𝓝 (J x,a), p.1 ∈ J '' I :=
      continuous_fst.continuousAt.eventually ((isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hy)
    filter_upwards [hnear] with p hp
    simp only [branchFamily,ite_eq_left hp,g]
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hzero hq

lemma branchFamily_congr_branch {Ω : Type*} {C I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hIC : I ⊆ C) (hinj : InjOn J C) (hs : support F ⊆ I ×ˢ univ) :
    branchFamily C J F = branchFamily I J F := by
  classical
  funext p
  have him : J '' I ⊆ J '' C := image_mono hIC
  by_cases hp : p.1 ∈ J '' C
  · have hc := invFunOn_pos hp
    by_cases hpi : p.1 ∈ J '' I
    · have hi := invFunOn_pos hpi
      have hinv : invFunOn J C p.1 = invFunOn J I p.1 :=
        hinj hc.1 (hIC hi.1) (hc.2.trans hi.2.symm)
      simp [branchFamily,hp,hpi,hinv]
    · have hz : F (invFunOn J C p.1,p.2) = 0 := by
        by_contra hn
        exact hpi ⟨_, (hs hn).1, hc.2⟩
      simp [branchFamily,hp,hpi,hz]
  · have hpi : p.1 ∉ J '' I := fun h => hp (him h)
    simp [branchFamily,hp,hpi]

open scoped NNReal

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma integrable_circleDensityLift {q : UnitAddCircle → ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (o : ℝ) :
    Integrable (circleDensityLift o q) := by
  have hmp : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  have hi : IntegrableOn (fun x : ℝ => q (x : UnitAddCircle)) (Ioc o (o+1)) :=
    (hmp.integrable_comp hq.aestronglyMeasurable).2 hq
  exact hi.integrable_indicator measurableSet_Ioc

lemma integrable_branchDensity {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : IntegrableOn q I) : Integrable (branchDensity I J g D q) := by
  have he : IntegrableOn (branchDensity I J g D q) (J '' I) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hI hJ hinj]
    apply hq.congr (ae_restrict_of_forall_mem hI (fun x hx => ?_))
    rw [smul_eq_mul,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  have hs : (J '' I).indicator (branchDensity I J g D q) = branchDensity I J g D q := by
    funext y
    by_cases hy : y ∈ J '' I
    · exact indicator_of_mem hy _
    · simp [hy,branchDensity]
  simpa only [hs] using he.integrable_indicator himage

/-- Total variation contracts under the actual temporal-frequency pushforward.
The real L¹ normalization has no factor 1/2. -/
lemma l1_pushforward_contraction {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → ℝ} {g : Y → ℝ} {T : X → Y}
    (hf : Integrable f μ) (hg : Integrable g ν) (hT : Measurable T)
    (hmap : (μ.withDensityᵥ f).map T = ν.withDensityᵥ g) :
    (∫ y, |g y| ∂ν) ≤ ∫ x, |f x| ∂μ := by
  have hv := MeasureTheory.VectorMeasure.variation_map_le (μ := μ.withDensityᵥ f) (φ := T)
  rw [hmap,Measure.variation_withDensityᵥ hg,Measure.variation_withDensityᵥ hf] at hv
  have hh := hv univ
  rw [Measure.map_apply hT MeasurableSet.univ] at hh
  simp only [preimage_univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  have he (z : ℝ) : ‖z‖ₑ = ENNReal.ofReal |z| := Real.enorm_eq_ofReal_abs z
  simp_rw [he] at hh
  rw [← ofReal_integral_eq_lintegral_ofReal hg.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hf.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _))] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => abs_nonneg _))).mp hh

lemma l1_pushforward_difference {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f₁ f₂ : X → ℝ} {g₁ g₂ : Y → ℝ} {T : X → Y}
    (hf₁ : Integrable f₁ μ) (hf₂ : Integrable f₂ μ)
    (hg₁ : Integrable g₁ ν) (hg₂ : Integrable g₂ ν) (hT : Measurable T)
    (h₁ : (μ.withDensityᵥ f₁).map T = ν.withDensityᵥ g₁)
    (h₂ : (μ.withDensityᵥ f₂).map T = ν.withDensityᵥ g₂) :
    (∫ y, |g₁ y-g₂ y| ∂ν) ≤ ∫ x, |f₁ x-f₂ x| ∂μ := by
  apply l1_pushforward_contraction (hf₁.sub hf₂) (hg₁.sub hg₂) hT
  rw [withDensityᵥ_sub hf₁ hf₂,withDensityᵥ_sub hg₁ hg₂]
  have he := map_sub (MeasureTheory.VectorMeasure.mapGm T) (μ.withDensityᵥ f₁) (μ.withDensityᵥ f₂)
  change (μ.withDensityᵥ f₁-μ.withDensityᵥ f₂).map T =
    (μ.withDensityᵥ f₁).map T-(μ.withDensityᵥ f₂).map T at he
  rw [he,h₁,h₂]

lemma integrable_scaledBranchKernel {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : Integrable (branchDensity I J g D q)) {s : ℝ} (hs : s ≠ 0) :
    Integrable (scaledBranchKernel I J g D q s) :=
  ((integrable_comp_div_iff _ hs).2 hq).const_mul _

lemma integrable_unfoldedModeDensity {I : Set ℝ} {J g D q₀ : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q₀) {n j : ℝ} (hn : 0 < n) (hj : j ≠ 0) :
    Integrable (unfoldedModeDensity I J g D q₀ n j) := by
  have hi := integrable_scaledBranchKernel
    (integrable_branchDensity hI himage hJ hinj hg hD (hq.const_mul n).integrableOn)
    (div_ne_zero hj hn.ne')
  change Integrable (fun t => scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [sub_eq_add_neg] using
    (integrable_comp_mul_left_iff (fun x =>
      scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (x+ -j)) hn.ne').2
      (hi.comp_add_right (-j))

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ThreeTorus

lemma passageBranchKernel_formula (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × ℝ → ℝ) (s y : ℝ) :
    passageBranchKernel I J F s y = |s|⁻¹*branchKernel I J F (y/s,s) := by
  simp [passageBranchKernel,affineKernel]

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_family_of_branch {Ω : Type*} {C I : Set ℝ}
    {J : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : ∀ a, support (A a) ⊆ I) :
    (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily I J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
  have he (C : Set ℝ) :
      (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
    funext p
    simp only [stationaryWeight,branchDensity,branchFamily]
    split_ifs with h <;> simp [h]
  rw [he]
  apply branchFamily_congr_branch hIC hi
  intro p hp
  refine ⟨hs p.2 ?_,mem_univ _⟩
  intro hz
  apply hp
  simp [hz]

lemma stationaryWeight_signed_compact_continuous {J : ℝ → ℝ}
    {A : UnitAddCircle → ℝ → ℂ} {l u R : ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (hR : 0 < R) (hi : InjOn J (Icc (l-R) (u+R)))
    (hd : ∀ x ∈ Ioo (l-R) (u+R), deriv J x ≠ 0) :
    Continuous (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) ∧
    HasCompactSupport (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) := by
  let F : ℝ × UnitAddCircle → ℝ := fun p => ‖A p.2 p.1‖^2
  have hF : Continuous F := (hA.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hFs : support F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) := by
    intro p hp
    refine ⟨hs p.2 ?_,mem_univ _⟩
    intro hz
    exact hp (by simp [F,show A p.2 p.1 = 0 from hz])
  have hFt : tsupport F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) :=
    closure_minimal hFs (isClosed_Icc.prod isClosed_univ)
  have hc : HasCompactSupport F :=
    (isCompact_Icc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport F) hFt
  have hsub : Icc l u ⊆ Ioo (l-R) (u+R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  rw [stationaryWeight_family_of_branch Ioo_subset_Icc_self hi (fun a => (hs a).trans hsub)]
  exact ⟨branchFamily_continuous hJ isOpen_Ioo (hi.mono Ioo_subset_Icc_self) hd hF hc
    (fun p hp => ⟨hsub (hFt hp).1,mem_univ _⟩),branchFamily_compact hJ.continuous hc⟩

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma retainedCircleWeight_integrable {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (n : ℕ) (j : ℤ) :
    Integrable (retainedCircleWeight ψ χ c n j) AddCircle.haarAddCircle := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
    ((hc n j).norm.pow 2)

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma scaled_speed_good_branch {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) :
    InjOn (fun x => (m:ℝ)*V x) (Icc (l-R) (u+R)) ∧
      ∀ x ∈ Ioo (l-R) (u+R), deriv (fun x => (m:ℝ)*V x) x ≠ 0 := by
  have hsub : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : InjOn V (Icc (l-R) (u+R)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn
      (fun x hx => hd x (hsub (interior_subset hx)))).injOn
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (mul_left_cancel₀ hm' he)
  · intro x hx
    rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_ne_zero hm' (hd x (hsub (Ioo_subset_Icc_self hx))).ne'

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_support_subset {C K : Set ℝ} {J : ℝ → ℝ} {A : ℝ → ℂ}
    (hA : support A ⊆ K) : support (stationaryWeight C J A) ⊆ J '' K := by
  classical
  intro s hs
  have hsC : s ∈ J '' C := by
    by_contra hn
    exact hs (by simp [stationaryWeight,branchDensity,hn])
  have hp := invFunOn_pos hsC
  refine ⟨invFunOn J C s,hA ?_,hp.2⟩
  intro hz
  exact hs (by simp [stationaryWeight,branchDensity,hsC,show A (invFunOn J C s) = 0 from hz])

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

lemma measurable_periodizedReal {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (periodizedReal q) := by
  exact Measurable.tsum (fun k => hq.comp (measurable_id.add_const (k:ℝ)))

lemma measurable_foldCircleDensity {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (foldCircleDensity q) := by
  exact ((measurable_periodizedReal hq).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc 1 0).measurable

lemma foldCircleDensity_coe {q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    foldCircleDensity q (x : UnitAddCircle) = periodizedReal q x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

lemma integral_real_eq_lattice (q : ℝ → ℝ) (hq : Integrable q) :
    (∫ x, q x) = ∑' k : ℤ, ∫ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' q hq
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma lintegral_real_eq_lattice (q : ℝ → ℝ≥0∞) :
    (∫⁻ x, q x) = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).lintegral_eq_tsum'' q
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma integrableOn_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    IntegrableOn (periodizedReal q) (Ioc 0 1) := by
  refine ⟨(measurable_periodizedReal hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x in Ioc (0:ℝ) 1, ‖periodizedReal q x‖ₑ) ≤
        ∫⁻ x in Ioc (0:ℝ) 1, ∑' k : ℤ, ‖q (x+k)‖ₑ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, ‖q (x+k)‖ₑ :=
      lintegral_tsum (fun k => (hm.comp (measurable_id.add_const (k:ℝ))).enorm.aemeasurable)
    _ = ∫⁻ x, ‖q x‖ₑ := (lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)).symm
    _ < ∞ := hq.hasFiniteIntegral

lemma integral_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ x in Ioc (0:ℝ) 1, periodizedReal q x) = ∫ x, q x := by
  change (∫ x in Ioc (0:ℝ) 1, ∑' k : ℤ, q (x+k)) = ∫ x, q x
  rw [integral_tsum]
  · exact (integral_real_eq_lattice q hq).symm
  · exact fun k => (hm.comp (measurable_id.add_const (k:ℝ))).aestronglyMeasurable
  · rw [← lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)]
    exact hq.hasFiniteIntegral.ne

lemma integrable_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    Integrable (foldCircleDensity q) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun x : ℝ => (x:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  apply (hp.integrable_comp (measurable_foldCircleDensity hm).aestronglyMeasurable).1
  exact (integrableOn_periodizedReal hm hq).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (foldCircleDensity_coe hx).symm))

lemma integral_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ a, foldCircleDensity q a ∂AddCircle.haarAddCircle) = ∫ x, q x := by
  have he := AddCircle.integral_preimage 1 0 (foldCircleDensity q)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,
    one_smul] at he
  rw [← he]
  exact (setIntegral_congr_fun measurableSet_Ioc (fun x hx => foldCircleDensity_coe hx)).trans
    (integral_periodizedReal hm hq)

lemma quotient_add_int (x : ℝ) (k : ℤ) : ((x+k : ℝ):UnitAddCircle) = (x:UnitAddCircle) := by
  have h : ((k:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k,by simp⟩
  rw [AddCircle.coe_add,h,add_zero]

lemma foldCircleDensity_indicator (q : ℝ → ℝ) (s : Set UnitAddCircle) :
    foldCircleDensity (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) =
      s.indicator (foldCircleDensity q) := by
  classical
  funext a
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hx : x ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 a).2
  have ha : (x:UnitAddCircle) = a := (AddCircle.equivIoc 1 0).symm_apply_apply a
  rw [← ha]
  by_cases hs : (x:UnitAddCircle) ∈ s
  · simp only [indicator_of_mem hs,foldCircleDensity_coe hx,periodizedReal]
    apply tsum_congr
    intro k
    exact indicator_of_mem (by simpa only [mem_preimage,quotient_add_int] using hs) q
  · simp only [indicator_of_notMem hs,foldCircleDensity_coe hx,periodizedReal]
    have hz (k : ℤ) : (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) (x+k) = 0 :=
      indicator_of_notMem (by simpa only [mem_preimage,quotient_add_int] using hs) q
    simp only [hz,tsum_zero]

/-- Folding is exactly pushforward under the quotient, not a replacement kernel. -/
lemma foldCircleDensity_pushforward {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    ((volume : Measure ℝ).withDensityᵥ q).map (fun x : ℝ => (x:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ (foldCircleDensity q) := by
  ext s hs
  rw [VectorMeasure.map_apply _ AddCircle.measurable_mk' hs,
    withDensityᵥ_apply hq (AddCircle.measurable_mk' hs),
    withDensityᵥ_apply (integrable_foldCircleDensity hm hq) hs,
    ← integral_indicator (AddCircle.measurable_mk' hs),← integral_indicator hs]
  rw [← foldCircleDensity_indicator]
  exact (integral_foldCircleDensity (hm.indicator (AddCircle.measurable_mk' hs))
    (hq.indicator (AddCircle.measurable_mk' hs))).symm

lemma foldCircleDensity_l1_difference {q r : ℝ → ℝ}
    (hqm : Measurable q) (hqi : Integrable q) (hrm : Measurable r) (hri : Integrable r) :
    (∫ a, |foldCircleDensity q a-foldCircleDensity r a| ∂AddCircle.haarAddCircle) ≤
      ∫ x, |q x-r x| := by
  exact l1_pushforward_difference hqi hri (integrable_foldCircleDensity hqm hqi)
    (integrable_foldCircleDensity hrm hri) AddCircle.measurable_mk'
    (foldCircleDensity_pushforward hqm hqi) (foldCircleDensity_pushforward hrm hri)

lemma periodizedReal_add_int (q : ℝ → ℝ) (x : ℝ) (j : ℤ) :
    periodizedReal q (x+j) = periodizedReal q x := by
  have h := (Equiv.addLeft j).tsum_eq (fun k : ℤ => q (x+k))
  change (∑' k : ℤ, q (x+(j:ℝ)+(k:ℝ))) = ∑' k : ℤ, q (x+(k:ℝ))
  rw [← h]
  apply tsum_congr
  intro k
  congr 1
  change x+(j:ℝ)+(k:ℝ) = x+((j+k:ℤ):ℝ)
  simp only [Int.cast_add,add_assoc]

/-- The displayed lattice formula holds for every real representative. -/
lemma foldCircleDensity_coe_all (q : ℝ → ℝ) (x : ℝ) :
    foldCircleDensity q (x:UnitAddCircle) = ∑' k : ℤ, q (x+k) := by
  let y : ℝ := (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).1
  have hy : y ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).2
  have hxy : (y:UnitAddCircle) = (x:UnitAddCircle) :=
    (AddCircle.equivIoc 1 0).symm_apply_apply (x:UnitAddCircle)
  have hz : ((y-x:ℝ):UnitAddCircle) = 0 := by rw [AddCircle.coe_sub,hxy,sub_self]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 hz
  have he : y = x+(k:ℝ) := by simpa only [zsmul_eq_mul,mul_one] using eq_add_of_sub_eq' hk.symm
  rw [← hxy,foldCircleDensity_coe hy,he,periodizedReal_add_int]
  rfl

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma measurable_branchDensity_smooth {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) :
    Measurable (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let S := J '' I
  let g := S.piecewise (invFunOn J I) (fun _ => 0)
  have hS : IsOpen S := isOpen_image_of_deriv_ne_zero hJ hIo hd
  have hgi : ContinuousOn (invFunOn J I) S := by
    rintro y ⟨x,hx,rfl⟩
    exact (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hx
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hgi.measurable_piecewise continuous_const.continuousOn hS.measurableSet
  have he : branchDensity I J (invFunOn J I) (deriv J) q =
      S.indicator (fun y => q (g y)/|deriv J (g y)|) := by
    funext y
    by_cases hy : y ∈ S
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp [g,hy]
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp only [indicator_of_notMem hy]
  rw [he]
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  exact ((hq.comp hg).div ((hD.continuous.measurable.comp hg).abs)).indicator hS.measurableSet

lemma measurable_circleDensityLift {q : UnitAddCircle → ℝ} (hq : Measurable q) (o : ℝ) :
    Measurable (circleDensityLift o q) :=
  (hq.comp AddCircle.measurable_mk').indicator measurableSet_Ioc

lemma measurable_unfoldedModeDensity {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) (n j : ℝ) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hm := measurable_branchDensity_smooth hJ hIo hinj hd (hq.const_mul n)
  unfold unfoldedModeDensity scaledBranchKernel
  exact (hm.comp ((measurable_const.mul measurable_id).sub_const j |>.div_const (j/n))).const_mul |j/n|⁻¹

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma retained_unfolded_regular {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (o : ℝ) {n : ℕ} (hn : 0 < n) {j : ℤ} (hj : j ≠ 0) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) ∧
    Integrable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) := by
  have hq : Continuous (retainedCircleWeight ψ χ c n j) :=
    ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
      ((hc n j).norm.pow 2)
  exact ⟨measurable_unfoldedModeDensity hJ hIo hinj hd
      (measurable_circleDensityLift hq.measurable o) n j,
    integrable_unfoldedModeDensity hIo.measurableSet
      (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
      (fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt) hinj
      (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
      (integrable_circleDensityLift (retainedCircleWeight_integrable hψ hχ hc n j) o)
      (by exact_mod_cast hn) (by exact_mod_cast hj)⟩

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PositiveLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive Fourier laws, compact integral differentiation, affine densities, and prime-sieve signal laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform

noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
namespace ThreeTorus

lemma integrable_scaledDensity {q : ℝ → ℝ} (hq : Integrable q) {s : ℝ} (hs : s ≠ 0) :
    Integrable (scaledDensity q s) := by
  have hi := ((integrable_comp_mul_left_iff q (inv_ne_zero hs)).2 hq).const_mul |s|⁻¹
  change Integrable (fun y => |s|⁻¹*q (y/s))
  simpa only [div_eq_mul_inv,mul_comm] using hi

lemma integral_scaledDensity {q : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) :
    (∫ y, scaledDensity q s y) = ∫ y, q y := by
  simp only [scaledDensity,div_eq_mul_inv]
  rw [integral_const_mul,Measure.integral_comp_mul_right]
  simp only [inv_inv,smul_eq_mul]
  field_simp

lemma fourierInv_scaledDensity {q : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (v : ℝ) :
    𝓕⁻ (fun y => (scaledDensity q s y : ℂ)) v =
      𝓕⁻ (fun y => (q y : ℂ)) (v*s) := by
  simp only [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul,
    smul_eq_mul]
  let f : ℝ → ℂ := fun x => Complex.exp (((-2*Real.pi*x*(-(v*s))) : ℝ)*Complex.I)*(q x : ℂ)
  have he : ∀ y : ℝ,
      Complex.exp (((-2*Real.pi*y*(-v)) : ℝ)*Complex.I)*(scaledDensity q s y : ℂ) =
        ((|s| : ℝ) : ℂ)⁻¹*f (s⁻¹*y) := by
    intro y
    have harg : -2*Real.pi*(s⁻¹*y)*(-(v*s)) = -2*Real.pi*y*(-v) := by
      field_simp [hs]
    dsimp only [f,scaledDensity]
    rw [harg]
    simp only [div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]
    rw [mul_comm s⁻¹ y]
    ring
  simp_rw [he]
  rw [integral_const_mul,Measure.integral_comp_mul_left]
  simp only [inv_inv,Complex.real_smul]
  have hsC : ((|s| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hs)
  field_simp
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp only [f]
  congr 3
  ring_nf

lemma fourier_scaledDensity {q : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (v : ℝ) :
    𝓕 (fun y => (scaledDensity q s y : ℂ)) v = 𝓕 (fun y => (q y : ℂ)) (v*s) := by
  have hh := fourierInv_scaledDensity (q := q) hs (-v)
  simpa only [Real.fourierInv_eq_fourier_neg,neg_neg,neg_mul,neg_neg] using hh

lemma scaledDensity_quadratic_bound {q : ℝ → ℝ} {C s : ℝ} (hC : 0 ≤ C) (hs : s ≠ 0)
    (hq : ∀ y, |q y| ≤ C/(1+y^2)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y, |scaledDensity q s y| ≤ D/(1+y^2) := by
  let K := 1+2*s^2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨|s|⁻¹*C*K,by positivity,fun y => ?_⟩
  have hsq : y^2 = s^2*(y/s)^2 := by field_simp
  have hbnd : 1+y^2 ≤ K*(1+(y/s)^2) := by
    dsimp [K]
    nlinarith [sq_nonneg s,sq_nonneg (y/s)]
  calc
    |scaledDensity q s y| = |s|⁻¹*|q (y/s)| := by
      simp only [scaledDensity,abs_mul,abs_inv,abs_abs]
    _ ≤ |s|⁻¹*(C/(1+(y/s)^2)) := mul_le_mul_of_nonneg_left (hq _) (by positivity)
    _ ≤ (|s|⁻¹*C*K)/(1+y^2) := by
      rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hbnd (show 0 ≤ |s|⁻¹*C by positivity)]

lemma quadratic_norm_isBigO {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ y, ‖f y‖ ≤ C/(1+y^2)) :
    f =O[cocompact ℝ] (fun y : ℝ => |y| ^ (-(2:ℝ))) := by
  apply IsBigO.of_bound C
  filter_upwards [(isCompact_Icc (a := (-1:ℝ)) (b := 1)).compl_mem_cocompact] with y hy
  have h0 : y ≠ 0 := by intro h; subst y; simp at hy
  have hsq : 0 < y^2 := sq_pos_of_ne_zero h0
  have hr : |y| ^ (-(2:ℝ)) = (y^2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg y),Real.rpow_two,sq_abs]
  rw [hr,Real.norm_eq_abs,abs_of_nonneg (by positivity),← div_eq_mul_inv]
  exact (hf y).trans (div_le_div_of_nonneg_left hC hsq (by nlinarith))

/-- A compact Fourier bandwidth supplies a shared finite series near any nonzero scale. -/
lemma periodization_scaled_finite {q : ℝ → ℝ} (hq : Continuous q)
    {C : ℝ} (hC : 0 ≤ C) (hbnd : ∀ y, |q y| ≤ C/(1+y^2))
    {D ε : ℝ} (hε : 0 < ε) (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0)
    {N : ℕ} (hN : D < N*ε) {s : ℝ} (hs : ε ≤ |s|) (x : ℝ) :
    ∑' n : ℤ, (scaledDensity q s (x+n) : ℂ) =
      ∑ n ∈ Finset.Icc (-(N:ℤ)) N,
        𝓕 (fun y => (q y : ℂ)) ((n:ℝ)*s)*fourier n (x : UnitAddCircle) := by
  have hs0 : s ≠ 0 := by intro hh; simp [hh] at hs; linarith
  obtain ⟨C',hC',hbound⟩ := scaledDensity_quadratic_bound hC hs0 hbnd
  have hcont : Continuous (scaledDensity q s) :=
    continuous_const.mul (hq.comp (continuous_id.div_const _))
  have hband (n : ℤ) (hn : n ∉ Finset.Icc (-(N:ℤ)) N) :
      𝓕 (fun y => (q y : ℂ)) ((n:ℝ)*s) = 0 := by
    apply hF
    have hn' : (N : ℝ) < |(n:ℝ)| := by
      by_contra! hab
      have hle := abs_le.mp hab
      apply hn
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hle.1,by exact_mod_cast hle.2⟩
    rw [abs_mul]
    exact hN.trans_le (mul_le_mul (le_of_lt hn') hs hε.le (abs_nonneg _))
  have hsumm : Summable (fun n : ℤ => 𝓕 (fun y => (scaledDensity q s y : ℂ)) (n:ℝ)) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(N:ℤ)) N)
    intro n hn
    rw [fourier_scaledDensity hs0]
    exact hband n hn
  have he := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
    (Complex.continuous_ofReal.comp hcont) (b := 2) (by norm_num)
    (quadratic_norm_isBigO hC' (fun y => by
      simpa only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs] using hbound y)) hsumm x
  simp only [Function.comp_def] at he
  erw [he]
  simp_rw [fourier_scaledDensity hs0]
  exact tsum_eq_sum (fun n hn => by rw [hband n hn,zero_mul])

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Transmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Law averaging and weighted errors, folded packet transmission, and concrete signal-circle comparison. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics
open MeasureTheory Set Filter Function

namespace ThreeTorus
open MeasureTheory Set Filter Function Topology
open scoped Topology BigOperators FourierTransform

/-- Compactly supported realized laws have a locally finite scaled lattice sum,
jointly in the nonzero scale and the unfolded circle coordinate. -/
lemma continuousAt_scaled_periodization_compact {q : ℝ → ℝ} (hq : Continuous q)
    (hc : HasCompactSupport q) {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    ContinuousAt (fun v : ℝ × ℝ => periodizedReal (scaledDensity q v.1) v.2) p := by
  classical
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  let R' := max 1 R
  have hR' : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨N,hN⟩ := exists_nat_gt ((|p.1|+1)*R'+|p.2|+1)
  let S : Finset ℤ := Finset.Icc (-(N:ℤ)) N
  have hn : ∀ᶠ v : ℝ × ℝ in 𝓝 p,
      |v.1| < |p.1|+1 ∧ |v.2| < |p.2|+1 ∧ v.1 ≠ 0 := by
    filter_upwards [((continuous_abs.comp continuous_fst).tendsto p).eventually
      (eventually_lt_nhds (by linarith : |p.1| < |p.1|+1)),
      ((continuous_abs.comp continuous_snd).tendsto p).eventually
      (eventually_lt_nhds (by linarith : |p.2| < |p.2|+1)),
      continuous_fst.continuousAt.eventually_ne hp] with v hv hx hs
    exact ⟨hv,hx,hs⟩
  have he : ∀ᶠ v : ℝ × ℝ in 𝓝 p,
      periodizedReal (scaledDensity q v.1) v.2 = ∑ k ∈ S, scaledDensity q v.1 (v.2+k) := by
    filter_upwards [hn] with v hv
    apply tsum_eq_sum
    intro k hk
    by_cases hqk : q ((v.2+k)/v.1) = 0
    · simp [scaledDensity,hqk]
    have hqr : |(v.2+k)/v.1| ≤ R' := by
      exact (hR _ (subset_tsupport q hqk)).trans (le_max_right _ _)
    have hxk : |v.2+(k:ℝ)| ≤ |v.1| * R' := by
      rw [abs_div] at hqr
      exact (div_le_iff₀ (abs_pos.mpr hv.2.2)).mp hqr |>.trans_eq (mul_comm _ _)
    have hh : |(k:ℝ)| < (N:ℝ) := calc
      |(k:ℝ)| = |(v.2+k)-v.2| := by congr 1; ring
      _ ≤ |v.2+(k:ℝ)|+|v.2| := abs_sub _ _
      _ < (|p.1|+1)*R'+|p.2|+1 := by nlinarith [hxk,hv.1,hv.2.1]
      _ < (N:ℝ) := hN
    have hkm : k ∈ S := by
      apply Finset.mem_Icc.mpr
      have := abs_le.mp hh.le
      exact_mod_cast this
    exact False.elim (hk hkm)
  have hfin : ContinuousAt (fun v : ℝ × ℝ => ∑ k ∈ S, scaledDensity q v.1 (v.2+k)) p := by
    apply tendsto_finsetSum
    intro k _
    exact (continuousAt_fst.abs.inv₀ (abs_ne_zero.mpr hp)).mul
      (hq.continuousAt.comp (((continuousAt_snd.add_const (k:ℝ)).div continuousAt_fst hp)))
  exact hfin.congr_of_eventuallyEq he

/-- Compact bandwidth gives local joint continuity of the ideal law's folded density. -/
lemma continuousAt_scaled_periodization_bandlimited {q : ℝ → ℝ} (hq : Continuous q)
    (hqi : Integrable q) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |q y| ≤ C/(1+y^2))
    {D : ℝ} (hF : ∀ v, D < |v| → 𝓕 (fun y => (q y : ℂ)) v = 0)
    {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    ContinuousAt (fun v : ℝ × ℝ => periodizedReal (scaledDensity q v.1) v.2) p := by
  let ε := |p.1|/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (D/ε)
  have hN' : D < (N:ℝ)*ε := (div_lt_iff₀ hε).mp hN
  let S := Finset.Icc (-(N:ℤ)) N
  let F : ℝ → ℂ := 𝓕 (fun y => (q y : ℂ))
  have hFc : Continuous F := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hqi.ofReal
  have hn : ∀ᶠ v : ℝ × ℝ in 𝓝 p, ε ≤ |v.1| := by
    have hε' : ε < |p.1| := by dsimp [ε]; linarith [abs_pos.mpr hp]
    exact (((continuous_abs.comp continuous_fst).tendsto p).eventually
      (eventually_gt_nhds hε')).mono (fun _ h => h.le)
  have hfin : Continuous (fun v : ℝ × ℝ =>
      (∑ k ∈ S, F ((k:ℝ)*v.1)*fourier k (v.2:UnitAddCircle)).re) := by
    apply Complex.continuous_re.comp
    apply continuous_finsetSum
    intro k _
    exact (hFc.comp (continuous_const.mul continuous_fst)).mul
      ((fourier k).continuous.comp ((AddCircle.continuous_mk' 1).comp continuous_snd))
  apply hfin.continuousAt.congr_of_eventuallyEq
  filter_upwards [hn] with v hv
  have he := periodization_scaled_finite hq hC hb hε hF hN' hv v.2
  rw [← Complex.ofReal_tsum] at he
  exact congrArg Complex.re he

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function Topology
open scoped Topology BigOperators FourierTransform

lemma continuous_weighted_fold_difference {w q r : ℝ → ℝ}
    (hw : Continuous w) (hw0 : 0 ∉ tsupport w)
    (hq : Continuous q) (hqc : HasCompactSupport q)
    (hr : Continuous r) (hri : Integrable r) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, |r y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (r y : ℂ)) v = 0) :
    Continuous (fun p : ℝ × UnitAddCircle => w p.1 *
      |foldCircleDensity (scaledDensity q p.1) p.2-
        foldCircleDensity (scaledDensity r p.1) p.2|) := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1:ℝ))).continuous_lift_prod_right
  simp_rw [foldCircleDensity_coe_all]
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 = 0
  · have hz : w =ᶠ[𝓝 p.1] 0 := by
      rw [hp]
      exact notMem_tsupport_iff_eventuallyEq.mp hw0
    apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hz] with v hv
    simp only [Pi.zero_apply] at hv
    simp only [hv,zero_mul]
  · exact (hw.continuousAt.comp continuousAt_fst).mul
      ((continuousAt_scaled_periodization_compact hq hqc hp).sub
        (continuousAt_scaled_periodization_bandlimited hr hri hC hb hF hp)).abs

/-- Scaling and folding are contractions for the total variation distance of
real densities, including subprobability densities and negative scales. -/
lemma scaled_fold_l1_difference {q r : ℝ → ℝ} (hqm : Measurable q) (hqi : Integrable q)
    (hrm : Measurable r) (hri : Integrable r) {s : ℝ} (hs : s ≠ 0) :
    (∫ y, |foldCircleDensity (scaledDensity q s) y-foldCircleDensity (scaledDensity r s) y|
      ∂AddCircle.haarAddCircle) ≤ ∫ x, |q x-r x| := by
  have hqm' : Measurable (scaledDensity q s) :=
    measurable_const.mul (hqm.comp (measurable_id.div_const s))
  have hrm' : Measurable (scaledDensity r s) :=
    measurable_const.mul (hrm.comp (measurable_id.div_const s))
  have he : (fun x => |scaledDensity q s x-scaledDensity r s x|) =
      scaledDensity (fun x => |q x-r x|) s := by
    ext x
    simp only [scaledDensity,← mul_sub,abs_mul,abs_inv,abs_abs]
  exact (foldCircleDensity_l1_difference hqm' (integrable_scaledDensity hqi hs)
    hrm' (integrable_scaledDensity hri hs)).trans_eq (by rw [he,integral_scaledDensity hs])

/-- Exact fast law comparison, with the missing mass of the
realized subprobability included. All arbitrary offsets are allowed. -/
theorem weighted_fold_law_average {w q r : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : 0 ∉ tsupport w)
    (hwn : ∀ s, 0 ≤ w s)
    (hq : Continuous q) (hqc : HasCompactSupport q)
    (hr : Continuous r) (hri : Integrable r) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, |r y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (r y : ℂ)) v = 0)
    (β : ℕ → UnitAddCircle) :
    Tendsto (fun n : ℕ => ∫ s, w s *
      |foldCircleDensity (scaledDensity q s) ((((n:ℝ)*s:ℝ):UnitAddCircle)+β n)-
        foldCircleDensity (scaledDensity r s) ((((n:ℝ)*s:ℝ):UnitAddCircle)+β n)|) atTop
      (𝓝 (∫ s, w s * ∫ y,
        |foldCircleDensity (scaledDensity q s) y-foldCircleDensity (scaledDensity r s) y|
          ∂AddCircle.haarAddCircle)) ∧
    (∫ s, w s * ∫ y,
      |foldCircleDensity (scaledDensity q s) y-foldCircleDensity (scaledDensity r s) y|
        ∂AddCircle.haarAddCircle) ≤ (∫ s, w s) * ∫ x, |q x-r x| := by
  constructor
  · have hH := continuous_weighted_fold_difference hw hw0 hq hqc hr hri hC hb hF
    obtain ⟨R,hR0,hR⟩ := hwc.isBounded.exists_pos_norm_le
    obtain ⟨M,hM⟩ := exists_nat_gt R
    have hM0 : 0 < M := by exact_mod_cast hR0.trans hM
    have hs : ∀ s y, (M:ℝ) ≤ |s| →
        w s * |foldCircleDensity (scaledDensity q s) y-foldCircleDensity (scaledDensity r s) y| = 0 := by
      intro s y hs
      have hz : w s = 0 := by
        by_contra hn
        have hh := hR s (subset_tsupport w hn)
        simp only [Real.norm_eq_abs] at hh
        linarith
      rw [hz,zero_mul]
    simpa only [integral_const_mul] using fast_average_real_compact_real hH hM0 hs β
  · have hwi : Integrable w := hw.integrable_of_hasCompactSupport hwc
    rw [← integral_mul_const]
    apply integral_mono_of_nonneg
      (Eventually.of_forall (fun s => mul_nonneg (hwn s) (integral_nonneg (fun _ => abs_nonneg _))))
      (hwi.mul_const _)
    filter_upwards [] with s
    by_cases hs : s = 0
    · subst s
      have hwz : w 0 = 0 := image_eq_zero_of_notMem_tsupport hw0
      simp only [hwz,zero_mul,le_refl]
    · exact mul_le_mul_of_nonneg_left (scaled_fold_l1_difference hq.measurable
        (hq.integrable_of_hasCompactSupport hqc) hr.measurable hri hs) (hwn s)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function Topology
open scoped Topology BigOperators FourierTransform

lemma continuous_weighted_fold_of_local {w q : ℝ → ℝ}
    (hw : Continuous w) (hw0 : 0 ∉ tsupport w)
    (hq : ∀ p : ℝ × ℝ, p.1 ≠ 0 →
      ContinuousAt (fun v : ℝ × ℝ => periodizedReal (scaledDensity q v.1) v.2) p) :
    Continuous (fun p : ℝ × UnitAddCircle => w p.1 * foldCircleDensity (scaledDensity q p.1) p.2) := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1:ℝ))).continuous_lift_prod_right
  simp_rw [foldCircleDensity_coe_all]
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 = 0
  · have hz : w =ᶠ[𝓝 p.1] 0 := by
      rw [hp]
      exact notMem_tsupport_iff_eventuallyEq.mp hw0
    apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hz] with v hv
    simp only [Pi.zero_apply] at hv
    simp only [hv,zero_mul]
  · exact (hw.continuousAt.comp continuousAt_fst).mul (hq p hp)

lemma continuous_weighted_fold_compact {w q : ℝ → ℝ}
    (hw : Continuous w) (hw0 : 0 ∉ tsupport w) (hq : Continuous q) (hqc : HasCompactSupport q) :
    Continuous (fun p : ℝ × UnitAddCircle => w p.1 * foldCircleDensity (scaledDensity q p.1) p.2) :=
  continuous_weighted_fold_of_local hw hw0 (fun _ hp => continuousAt_scaled_periodization_compact hq hqc hp)

lemma continuous_fast_circle (n : ℕ) (β : UnitAddCircle) :
    Continuous (fun s : ℝ => (((n:ℝ)*s:ℝ):UnitAddCircle)+β) :=
  ((AddCircle.continuous_mk' 1).comp (continuous_const.mul continuous_id)).add_const β

lemma continuous_weighted_fast_compact {w q : ℝ → ℝ}
    (hw : Continuous w) (hw0 : 0 ∉ tsupport w) (hq : Continuous q) (hqc : HasCompactSupport q)
    (n : ℕ) (β : UnitAddCircle) :
    Continuous (fun s : ℝ => w s *foldCircleDensity (scaledDensity q s)
      ((((n:ℝ)*s:ℝ):UnitAddCircle)+β)) :=
  (continuous_weighted_fold_compact hw hw0 hq hqc).comp
    (continuous_id.prodMk (continuous_fast_circle n β))

lemma foldCircleDensity_mul_circle (w : ℝ → ℝ) (g : UnitAddCircle → ℝ) (z : UnitAddCircle) :
    foldCircleDensity (fun s => w s*g (s:UnitAddCircle)) z = foldCircleDensity w z*g z := by
  induction z using Quotient.inductionOn with | h x =>
    simp only [foldCircleDensity_coe_all,quotient_add_int,tsum_mul_right]

lemma fast_circle_coe (n : ℕ) (s : ℝ) :
    (((n:ℝ)*s:ℝ):UnitAddCircle) = (n:ℤ) • (s:UnitAddCircle) := by
  simpa only [zsmul_eq_mul,Int.cast_natCast] using
    (AddCircle.coe_zsmul (p := (1:ℝ)) (n := (n:ℤ)) (x := s))

lemma foldCircleDensity_mul_fast (w : ℝ → ℝ) (g : UnitAddCircle → ℝ)
    (n : ℕ) (β z : UnitAddCircle) :
    foldCircleDensity (fun s => w s*g ((((n:ℝ)*s:ℝ):UnitAddCircle)+β)) z =
      foldCircleDensity w z*g ((n:ℤ) • z+β) := by
  simp_rw [fast_circle_coe]
  exact foldCircleDensity_mul_circle w (fun z => g ((n:ℤ) • z+β)) z

/-- Quantitative transfer from an ideal folded law to a realized compact law.
The phase may have any prescribed offset at every passage integer. -/
theorem realized_fold_signal_estimate {w q r : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : 0 ∉ tsupport w)
    (hwn : ∀ s, 0 ≤ w s)
    (hq : Continuous q) (hqc : HasCompactSupport q)
    (hr : Continuous r) (hri : Integrable r) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, |r y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (r y : ℂ)) v = 0)
    {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
    (hideal : ∀ s ∈ support w, ∀ y, |foldCircleDensity (scaledDensity r s) y-g y| ≤ ε)
    (β : ℕ → UnitAddCircle) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (∫ z,
      |foldCircleDensity (fun s => w s*foldCircleDensity (scaledDensity q s)
        ((((n:ℝ)*s:ℝ):UnitAddCircle)+β n)) z-
        foldCircleDensity w z*g ((n:ℤ) • z+β n)| ∂AddCircle.haarAddCircle) <
      (∫ s, w s)*(∫ x, |q x-r x|) + (∫ s, w s)*ε + η := by
  have hav := weighted_fold_law_average hw hwc hw0 hwn hq hqc hr hri hC hb hF β
  have hlim : (∫ s, w s * ∫ y,
      |foldCircleDensity (scaledDensity q s) y-foldCircleDensity (scaledDensity r s) y|
        ∂AddCircle.haarAddCircle) < (∫ s, w s)*(∫ x, |q x-r x|)+η :=
    lt_of_le_of_lt hav.2 (lt_add_of_pos_right _ hη)
  filter_upwards [hav.1.eventually (eventually_lt_nhds hlim)] with n hn
  let y : ℝ → UnitAddCircle := fun s => (((n:ℝ)*s:ℝ):UnitAddCircle)+β n
  have hy : Continuous y := continuous_fast_circle n (β n)
  let R : ℝ → ℝ := fun s => w s*foldCircleDensity (scaledDensity q s) (y s)
  let G : ℝ → ℝ := fun s => w s*g (y s)
  let E : ℝ → ℝ := fun s => w s*
    |foldCircleDensity (scaledDensity q s) (y s)-foldCircleDensity (scaledDensity r s) (y s)|
  have hRc : Continuous R := continuous_weighted_fast_compact hw hw0 hq hqc n (β n)
  have hRi : Integrable R := hRc.integrable_of_hasCompactSupport hwc.mul_right
  have hGc : Continuous G := hw.mul (hg.comp hy)
  have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hwc.mul_right
  have hEc : Continuous E :=
    (continuous_weighted_fold_difference hw hw0 hq hqc hr hri hC hb hF).comp
      (continuous_id.prodMk hy)
  have hEi : Integrable E := hEc.integrable_of_hasCompactSupport hwc.mul_right
  have hwi : Integrable w := hw.integrable_of_hasCompactSupport hwc
  have hpt (s : ℝ) : |R s-G s| ≤ E s+w s*ε := by
    dsimp only [R,G,E]
    rw [← mul_sub,abs_mul,abs_of_nonneg (hwn s)]
    by_cases hs : w s = 0
    · simp [hs]
    · calc
        _ ≤ w s*(|foldCircleDensity (scaledDensity q s) (y s)-foldCircleDensity (scaledDensity r s) (y s)|+
          |foldCircleDensity (scaledDensity r s) (y s)-g (y s)|) :=
          mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) (hwn s)
        _ ≤ _ := by nlinarith [hideal s hs (y s),hwn s]
  have hbound : (∫ s, |R s-G s|) ≤ (∫ s, E s)+(∫ s, w s)*ε := by
    calc
      _ ≤ ∫ s, E s+w s*ε := integral_mono (hRi.sub hGi).abs (hEi.add (hwi.mul_const ε)) hpt
      _ = _ := by rw [integral_add hEi (hwi.mul_const ε),integral_mul_const]
  have hfold := foldCircleDensity_l1_difference hRc.measurable hRi hGc.measurable hGi
  have heG : ∀ z, foldCircleDensity G z = foldCircleDensity w z*g ((n:ℤ) • z+β n) :=
    foldCircleDensity_mul_fast w g n (β n)
  simp_rw [heG] at hfold
  exact hfold.trans hbound |>.trans_lt (by dsimp only [E,y]; linarith)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma lawJitter_injOn {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : Continuous ρ) (hi : Integrable ρ) (hp : ∀ y, 0 < ρ y)
    (hm : ∫ y, ρ y = 1) (hδ : 0 < δ) : InjOn (lawJitter ρ c) (Ioo δ (1-δ)) := by
  intro a ha b hb he
  rw [lawJitter_eq_quantile c hδ ⟨ha.1.le,ha.2.le⟩,
    lawJitter_eq_quantile c hδ ⟨hb.1.le,hb.2.le⟩] at he
  have he' := congrArg (cumulative ρ) he
  rwa [cumulative_quantile hρ hi hp hm ⟨by linarith [ha.1],by linarith [ha.2]⟩,
    cumulative_quantile hρ hi hp hm ⟨by linarith [hb.1],by linarith [hb.2]⟩] at he'

/-- The inverse-branch Jacobian is exactly the realized quantile density,
not merely some density representing the same measure. -/
lemma lawJitter_branchKernel {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ)
    (w : ℝ → ℝ) (y s : ℝ) :
    branchKernel (Ioo δ (1-δ)) (lawJitter ρ c) (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2) (y,s) =
      w s*lawDensity ρ c y := by
  classical
  by_cases hy : y ∈ lawJitter ρ c '' Ioo δ (1-δ)
  · let a := invFunOn (lawJitter ρ c) (Ioo δ (1-δ)) y
    have ha : a ∈ Ioo δ (1-δ) := (invFunOn_pos hy).1
    have hay : lawJitter ρ c a = y := (invFunOn_pos hy).2
    have hqay : quantile ρ a = y :=
      (lawJitter_eq_quantile c hδ ⟨ha.1.le,ha.2.le⟩).symm.trans hay
    have hca : cumulative ρ y = a := by
      rw [← hqay]
      exact cumulative_quantile hρ.continuous hi hp hm ⟨by linarith [ha.1],by linarith [ha.2]⟩
    have hd : deriv (lawJitter ρ c) a = (ρ y)⁻¹ := by
      simpa only [hqay] using (lawJitter_deriv_pos c hρ hi hp hm hδ ha).1.deriv
    simp only [branchKernel,hy,ite_eq_left]
    change w s*c.ψ a^2/|deriv (lawJitter ρ c) a| = w s*lawDensity ρ c y
    rw [hd,abs_of_pos (inv_pos.mpr (hp y)),div_inv_eq_mul,lawDensity,hca]
    ring
  · have hz : c.ψ (cumulative ρ y) = 0 := by
      by_contra hn
      have ha := c.ψ_support (subset_tsupport c.ψ hn)
      apply hy
      refine ⟨cumulative ρ y,ha,?_⟩
      rw [lawJitter_eq_quantile c hδ ⟨ha.1.le,ha.2.le⟩]
      exact quantile_cumulative hρ.continuous hi hp y
    simp [branchKernel,hy,lawDensity,hz]

lemma lawJitter_passageKernel {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ)
    (w : ℝ → ℝ) (s y : ℝ) :
    passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c)
      (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2) s y =
      w s*scaledDensity (lawDensity ρ c) s y := by
  rw [passageBranchKernel_formula,lawJitter_branchKernel c hρ hi hp hm hδ]
  simp only [scaledDensity]
  ring

lemma lawJitter_fineKernel {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ)
    (w : ℝ → ℝ) (n : ℕ) (s : ℝ) :
    fineResidueKernel (passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c)
      (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2)) 1 0 n s =
      w s*foldCircleDensity (scaledDensity (lawDensity ρ c) s) (((n:ℝ)*s:ℝ):UnitAddCircle) := by
  simp only [fineResidueKernel,lawJitter_passageKernel c hρ hi hp hm hδ,
    Int.cast_zero,sub_zero,Nat.cast_one,mul_one,tsum_mul_left,foldCircleDensity_coe_all]
  congr 1
  have he := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => scaledDensity (lawDensity ρ c) s ((n:ℝ)*s+k))
  simpa only [Equiv.neg_apply,Int.cast_neg,sub_eq_add_neg] using he

lemma stationaryWeight_modulus_independent {A : UnitAddCircle → ℝ → ℂ}
    (hA : ∀ a x, ‖A a x‖ = ‖A 0 x‖) (C : Set ℝ) (V : ℝ → ℝ) (a : UnitAddCircle) :
    stationaryWeight C V (A a) = stationaryWeight C V (A 0) := by
  unfold stationaryWeight
  congr 1
  funext x
  rw [hA a x]

lemma stationaryCutoffLift_modulus_independent {A : UnitAddCircle → ℝ → ℂ}
    (hA : ∀ a x, ‖A a x‖ = ‖A 0 x‖) (C : Set ℝ) (V ψ : ℝ → ℝ) :
    stationaryCutoffLift C V (fun p : ℝ × ℝ => A (p.2:UnitAddCircle) p.1) ψ =
      fun p : ℝ × ℝ => stationaryWeight C V (A 0) p.2*ψ p.1^2 := by
  funext p
  simp only [stationaryCutoffLift,stationaryWeight_modulus_independent hA]
  ring

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma stationaryWeight_nonneg (C : Set ℝ) (V : ℝ → ℝ) (A : ℝ → ℂ) (s : ℝ) :
    0 ≤ stationaryWeight C V A s := by
  classical
  unfold stationaryWeight branchDensity
  simp only [Set.indicator_apply]
  split_ifs <;> positivity

lemma stationaryWeight_tsupport_subset {C K : Set ℝ} {V : ℝ → ℝ} {A : ℝ → ℂ}
    (hV : Continuous V) (hK : IsCompact K) (hA : support A ⊆ K) :
    tsupport (stationaryWeight C V A) ⊆ V '' K :=
  closure_minimal (stationaryWeight_support_subset hA) (hK.image hV).isClosed

lemma stationaryWeight_slice_regular {V : ℝ → ℝ} {m : ℤ}
    {l u R : ℝ} {A : UnitAddCircle → ℝ → ℂ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u) :
    let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A 0)
    Continuous w ∧ HasCompactSupport w ∧ 0 ∉ tsupport w := by
  have hb := scaled_speed_good_branch hm hR hV hdV
  have hc := stationaryWeight_signed_compact_continuous (contDiff_const.mul hV) hA hs hR hb.1 hb.2
  have hv : Continuous (fun x => (m:ℝ)*V x) := continuous_const.mul hV.continuous
  have ht := stationaryWeight_tsupport_subset (C := Icc (l-R) (u+R)) hv isCompact_Icc (hs 0)
  refine ⟨hc.1.comp (continuous_id.prodMk continuous_const),?_,fun hz => h0 (ht hz)⟩
  exact (isCompact_Icc.image hv).of_isClosed_subset (isClosed_tsupport _) ht

/-- Fully realized smooth quantile law: the exact branch kernel has the desired
signal, with both its missing mass and total variation error explicitly included. -/
theorem quantile_fine_signal_estimate {w ρ : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : 0 ∉ tsupport w)
    (hwn : ∀ s, 0 ≤ w s)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
    (hideal : ∀ s ∈ support w, ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g y| ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (∫ z,
      |foldCircleDensity (fineResidueKernel (passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c)
        (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2)) 1 0 n) z-
        foldCircleDensity w z*g ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
      (∫ s, w s)*(4*δ+ε) + η := by
  have hq := (lawDensity_smooth c hρ hi).continuous
  have hqc := lawDensity_compact c hρ hi hp hm hδ hδ'
  have ht := realized_fold_signal_estimate hw hwc hw0 hwn hq hqc hρ.continuous hi hC hb hF
    hg hideal (fun _ => 0) hη
  have he : (∫ y, |lawDensity ρ c y-ρ y|) ≤ 4*δ := by
    simpa only [abs_sub_comm] using (lawDensity_error c hρ hi hp hm hδ hδ').2
  have hn : 0 ≤ ∫ s, w s := integral_nonneg hwn
  filter_upwards [ht] with n ht
  simp only [add_zero] at ht
  have heq : fineResidueKernel (passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c)
      (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2)) 1 0 n =
      fun s => w s*foldCircleDensity (scaledDensity (lawDensity ρ c) s) (((n:ℝ)*s:ℝ):UnitAddCircle) :=
    funext (lawJitter_fineKernel c hρ hi hp hm hδ w n)
  rw [heq]
  apply ht.trans_le
  nlinarith [mul_le_mul_of_nonneg_left he hn]

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma quantileCircleJitter_coe {δ : ℝ} (ρ : ℝ → ℝ) (c : LawCutoffs δ) (a : ℝ) :
    quantileCircleJitter ρ c (a:UnitAddCircle) = lawJitter ρ c a := rfl

lemma continuous_quantileCircleJitter {δ : ℝ} {ρ : ℝ → ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) : Continuous (quantileCircleJitter ρ c) := by
  apply Continuous.quotient_lift
  exact (lawJitter_smooth c hρ hi hp hm).continuous

lemma exactRetainedPacketDensity_integrable
    {I : Set ℝ} {J₀ : ℝ → ℝ} {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) :
    Integrable (exactRetainedPacketDensity I J₀ ψ χ m H A S n) AddCircle.haarAddCircle := by
  have hreg (j : ℤ) (hj : j ∈ S) := retained_unfolded_regular hJ hIo hinj hd hψ hχ
    (fun n j => continuous_exactPassageCoeff (m := m) (hH n) hA j) 0 hn (hS j hj)
  exact integrable_foldCircleDensity
    (Finset.measurable_sum _ (fun j hj => (hreg j hj).1))
    (integrable_finsetSum _ (fun j hj => (hreg j hj).2))

lemma integral_abs_sub_triangle {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g h : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, |f x-h x| ∂μ) ≤ (∫ x, |f x-g x| ∂μ)+(∫ x, |g x-h x| ∂μ) := by
  calc
    _ ≤ ∫ x, |f x-g x|+|g x-h x| ∂μ :=
      integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
        (fun x => abs_sub_le _ _ _)
    _ = _ := integral_add (hf.sub hg).abs (hg.sub hh).abs

/-- Source transmission analytic assembly, for the actual retained signed
coefficients and actual smooth quantile jitter. The law's lost mass is counted.
The model bound has to be established for the ideal law; no passage limit is
assumed. Every sufficiently large integer works. -/
theorem exact_quantile_circle_spectral_estimate_oai
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {Δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+Δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hΔt : Tendsto Δ atTop (𝓝 0))
    (hmod : ∀ a x, ‖A₀ a x‖ = ‖A₀ 0 x‖)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hρm : ∫ y, ρ y = 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ℝ → UnitAddCircle → ℝ}
    (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
    (hideal : ∀ s ∈ support (stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)),
      ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g y| ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ j ∈ S n, j ≠ 0) ∧
      (∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) ∧
      ∀ᶠ n : ℕ in atTop, (∫ z,
        |exactRetainedPacketDensity (Ioo δ (1-δ)) (lawJitter ρ c) (neutralCircleCutoff c)
          χ m H A (S n) n z - foldCircleDensity w z*g ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
        (∫ s, w s)*(4*δ+ε)+η := by
  dsimp only
  let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)
  have hw := stationaryWeight_slice_regular hm hR hV hdV hAc
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) h0
  have hJs := lawJitter_smooth c hρ hi hp hρm
  have hJinj := lawJitter_injOn c hρ.continuous hi hp hρm hδ
  have hJd : ∀ x ∈ Ioo δ (1-δ), deriv (lawJitter ρ c) x ≠ 0 := by
    intro x hx
    obtain ⟨hh,hp⟩ := lawJitter_deriv_pos c hρ hi hp hρm hδ hx
    rw [hh.deriv]
    exact hp.ne'
  have hψs : tsupport c.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
    intro x hx
    have hh := c.ψ_support hx
    exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
  have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), c.ψ x = neutralCircleCutoff c (x:UnitAddCircle) := by
    intro x hx
    exact (lawPsi_eq c hδ ⟨hx.1.le,by simpa using hx.2⟩).symm
  obtain ⟨S,hSN,hST,ht⟩ := exact_passage_circle_spectral_limit hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hΔt hJs isOpen_Ioo hJinj hJd
    (continuous_quantileCircleJitter c hρ hi hp hρm).measurable
    (fun x _ => quantileCircleJitter_coe ρ c x) c.ψ_smooth c.ψ_compact hψs heψ
    (continuous_neutralCircleCutoff c) hχc hcχ hzχ (neutralCircleCutoff_bounds c hδ) hχ hχW
    (by norm_num : 0 < (1:ℕ)) 0
  simp only [Nat.cast_one,mul_one,zero_add] at hSN hST ht
  refine ⟨S,hSN,hST,?_⟩
  have hweight := stationaryCutoffLift_modulus_independent hmod (Icc (l-R) (u+R))
    (fun x => (m:ℝ)*V x) c.ψ
  rw [hweight] at ht
  let K : ℕ → UnitAddCircle → ℝ := fun n => foldCircleDensity (fineResidueKernel
    (passageBranchKernel (Ioo δ (1-δ)) (lawJitter ρ c) (fun p : ℝ × ℝ => w p.2*c.ψ p.1^2)) 1 0 n)
  have ht' : Tendsto (fun n => ∫ z,
      |exactRetainedPacketDensity (Ioo δ (1-δ)) (lawJitter ρ c) (neutralCircleCutoff c)
        χ m H A (S n) n z-K n z| ∂AddCircle.haarAddCircle) atTop (𝓝 0) := ht
  have h2 := quantile_fine_signal_estimate hw.1 hw.2.1 hw.2.2
    (stationaryWeight_nonneg _ _ _) hρ hi hp hρm hC hb hF c hδ hδ' hg hideal (half_pos hη)
  filter_upwards [ht'.eventually (eventually_lt_nhds (half_pos hη)),h2,eventually_gt_atTop (0:ℕ)]
    with n hn hn2 hnpos
  have hDi := exactRetainedPacketDensity_integrable (m := m) hJs isOpen_Ioo hJinj hJd
    (continuous_neutralCircleCutoff c) hχc hHc hAcont hnpos (hSN n hnpos)
  have hqc := (lawDensity_smooth c hρ hi).continuous
  have hqcomp := lawDensity_compact c hρ hi hp hρm hδ hδ'
  have hK : K n = foldCircleDensity (fun s => w s*foldCircleDensity (scaledDensity (lawDensity ρ c) s)
      (((n:ℝ)*s:ℝ):UnitAddCircle)) := by
    dsimp only [K]
    congr 1
    exact funext (lawJitter_fineKernel c hρ hi hp hρm hδ w n)
  have hRcont : Continuous (fun s => w s*foldCircleDensity (scaledDensity (lawDensity ρ c) s)
      (((n:ℝ)*s:ℝ):UnitAddCircle)) := by
    simpa only [add_zero] using continuous_weighted_fast_compact hw.1 hw.2.2 hqc hqcomp n 0
  have hKi : Integrable (K n) AddCircle.haarAddCircle := by
    rw [hK]
    exact integrable_foldCircleDensity hRcont.measurable
      (hRcont.integrable_of_hasCompactSupport hw.2.1.mul_right)
  have hGcont : Continuous (fun s : ℝ => w s*g (((n:ℝ)*s:ℝ):UnitAddCircle)) :=
    hw.1.mul (hg.comp ((AddCircle.continuous_mk' 1).comp (continuous_const.mul continuous_id)))
  have hG : (fun z => foldCircleDensity w z*g ((n:ℤ) • z)) =
      foldCircleDensity (fun s => w s*g (((n:ℝ)*s:ℝ):UnitAddCircle)) := by
    funext z
    simpa only [add_zero] using (foldCircleDensity_mul_fast w g n 0 z).symm
  have hGi : Integrable (fun z => foldCircleDensity w z*g ((n:ℤ) • z)) AddCircle.haarAddCircle := by
    rw [hG]
    exact integrable_foldCircleDensity hGcont.measurable
      (hGcont.integrable_of_hasCompactSupport hw.2.1.mul_right)
  have hh := integral_abs_sub_triangle hDi hKi hGi
  exact hh.trans_lt (by change _ < _ at hn2; linarith)

end ThreeTorus

end

end OAI
end

theorem solution : type_of% @OAI.ThreeTorus.exact_quantile_circle_spectral_estimate_oai := @OAI.ThreeTorus.exact_quantile_circle_spectral_estimate_oai
