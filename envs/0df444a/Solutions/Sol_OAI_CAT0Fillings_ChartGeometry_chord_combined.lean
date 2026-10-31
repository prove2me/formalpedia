-- Prove2me | solution 1 for OAI.CAT0Fillings.ChartGeometry.chord_combined
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:02:55.885964+00:00
-- url     : https://prove2.me/submissions/1db8a80e-05c6-40fd-beea-8aa984d4f800

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002
import Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_chord_energy
import Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_closed_chord_product
import Theorems.Thm_OAI_CAT0Fillings_Conformal_chordBubble_bounded_derivatives

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_GroundState
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry

lemma ground_state_pointwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D ξ : E) (w d : ℝ) :
    ‖w • D+d • ξ‖^2 = inner ℝ D (w^2 • D+(2*w*d) • ξ)+d^2*‖ξ‖^2 := by
  rw [norm_add_sq_real,inner_add_right,real_inner_smul_right,real_inner_smul_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,mul_pow,sq_abs,sq_abs]
  ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ground_state (v P Q : q.Sobolev) {w d : X → ℝ} {ξ : ℕ × Euc (k+1) → Euc (k+1)}
    {β : ℝ} (hb : 0 < β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hP : (q.inclusion P : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => q.inclusion v x*w x))
    (hQ : (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
      (fun x => q.inclusion v x*(w x)^2))
    (hDP : (q.closedGradient P : _ → _) =ᵐ[q.atlasMeasure]
      (fun z => w (q.atlasParam z) • q.closedGradient v z+d (q.atlasParam z) • ξ z))
    (hDQ : (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
      (fun z => (w (q.atlasParam z))^2 • q.closedGradient v z+
        (2*w (q.atlasParam z)*d (q.atlasParam z)) • ξ z))
    (heuler : 4*β*inner ℝ (q.closedGradient v) (q.closedGradient Q) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion Q) =
      (k+1:ℝ)*(∫ x, (q.inclusion v x)^(1+4*β)*(q.inclusion Q x) ∂MassMeasure.currentMassMeasure hT)) :
    Integrable (fun z => (d (q.atlasParam z))^2*‖ξ z‖^2) q.atlasMeasure ∧
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P =
        (k+1:ℝ)*(∫ x, (q.inclusion v x)^(2+4*β)*(w x)^2 ∂MassMeasure.currentMassMeasure hT)+
          4*β*(∫ z, (d (q.atlasParam z))^2*‖ξ z‖^2 ∂q.atlasMeasure) := by
  have hg : (fun z => ‖q.closedGradient P z‖^2-inner ℝ (q.closedGradient v z) (q.closedGradient Q z))
      =ᵐ[q.atlasMeasure] (fun z => (d (q.atlasParam z))^2*‖ξ z‖^2) := by
    filter_upwards [hDP,hDQ] with z hp hq
    rw [hp,hq,ground_state_pointwise]
    ring
  have hi : Integrable (fun z => ‖q.closedGradient P z‖^2) q.atlasMeasure := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) (q.closedGradient P) (q.closedGradient P)
  have hj := L2.integrable_inner (𝕜 := ℝ) (q.closedGradient v) (q.closedGradient Q)
  have hf := (hi.sub hj).congr hg
  refine ⟨hf,?_⟩
  have hG : ‖q.closedGradient P‖^2 = inner ℝ (q.closedGradient v) (q.closedGradient Q)+
      (∫ z, (d (q.atlasParam z))^2*‖ξ z‖^2 ∂q.atlasMeasure) := by
    have h := integral_congr_ae hg
    rw [integral_sub hi hj] at h
    have hn := L2.inner_def (𝕜 := ℝ) (q.closedGradient P) (q.closedGradient P)
    simp only [real_inner_self_eq_norm_sq] at hn
    rw [←hn,←L2.inner_def] at h
    linarith
  have hI : ‖q.inclusion P‖^2 = inner ℝ (q.inclusion v) (q.inclusion Q) := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hP,hQ] with x hp hq
    simp only [RCLike.inner_apply,conj_trivial,hp,hq]
    ring
  have hR : (∫ x, (q.inclusion v x)^(1+4*β)*(q.inclusion Q x) ∂MassMeasure.currentMassMeasure hT) =
      ∫ x, (q.inclusion v x)^(2+4*β)*(w x)^2 ∂MassMeasure.currentMassMeasure hT := by
    apply integral_congr_ae
    filter_upwards [hv,hQ] with x hv hq
    rw [hq,←mul_assoc]
    conv_lhs => lhs; rhs; rw [←Real.rpow_one (q.inclusion v x)]
    rw [←Real.rpow_add' hv (by linarith : 1+4*β+1 ≠ 0)]
    congr 2
    ring
  rw [hR] at heuler
  unfold AnalyticMinimizer.energy
  rw [hG,hI]
  nlinarith [heuler]
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_GroundProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry

lemma deriv_square {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    deriv (fun x => (f x)^2) t = 2*f t*deriv f t := by
  have h := ((hf.differentiable (by norm_num) t).hasDerivAt.pow 2).deriv
  norm_num only [show 2-1 = (1:ℕ) by rfl, pow_one, Nat.cast_ofNat] at h
  exact h

lemma deriv_square_bound {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f)
    (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B) :
    ∀ t, |(f t)^2| ≤ 2*B^2 ∧ |deriv (fun x => (f x)^2) t| ≤ 2*B^2 := by
  intro t
  have hder := deriv_square hf t
  constructor
  · rw [abs_pow]
    have h := pow_le_pow_left₀ (abs_nonneg (f t)) (hfB t).1 2
    nlinarith [sq_nonneg B]
  · rw [hder,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ 2*B*B := mul_le_mul (mul_le_mul_of_nonneg_left (hfB t).1 (by norm_num))
        (hfB t).2 (abs_nonneg _) (by positivity)
      _ = _ := by ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chord_ground_state (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β B : ℝ}
    {f : ℝ → ℝ} (hb : 0 < β) (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f)
    (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT)) :
    ∃ P : q.Sobolev,
      (q.inclusion P : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => q.inclusion v x*f (κ*dist o x*(q.inclusion v x)^β)) ∧
      Integrable (fun z => (deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))^2*
        ‖q.chordXi o v κ β z‖^2) q.atlasMeasure ∧
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P =
        (k+1:ℝ)*(∫ x, (q.inclusion v x)^(2+4*β)*(f (κ*dist o x*(q.inclusion v x)^β))^2 ∂MassMeasure.currentMassMeasure hT)+
          4*β*(∫ z, (deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))^2*
            ‖q.chordXi o v κ β z‖^2 ∂q.atlasMeasure) := by
  obtain ⟨P,hP,hDP⟩ := q.closed_chord_product hz o v (κ := κ) hb hB hf hfB hv hm hpow
  obtain ⟨Q,hQ,hDQ⟩ := q.closed_chord_product hz o v (κ := κ) hb (show 0 ≤ 2*B^2 by positivity)
    (hf.pow 2) (deriv_square_bound hB hf hfB) hv hm hpow
  refine ⟨P,hP,?_⟩
  apply q.ground_state v P Q
    (w := fun x => f (κ*dist o x*(q.inclusion v x)^β))
    (d := fun x => deriv f (κ*dist o x*(q.inclusion v x)^β))
    (ξ := q.chordXi o v κ β) hb hv hP hQ hDP ?_ (heuler Q)
  filter_upwards [hDQ] with z hzD
  rw [hzD]
  rw [deriv_square hf]
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_AverageProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.Conformal
lemma avg_pow_bound {τ : ℝ} (hτ : τ ∈ Icc (0:ℝ) 1) (n : ℕ) : |τ^n| ≤ 1 := by
  rw [abs_of_nonneg (pow_nonneg hτ.1 _)]
  exact pow_le_one₀ hτ.1 hτ.2
lemma avg_integrand_bound {d : ℝ → ℝ} {B τ t : ℝ} (hτ : τ ∈ Icc (0:ℝ) 1)
    (hd : ∀ x, |d x| ≤ B) (n : ℕ) : |τ^(n-1)*(d (τ*t))^2| ≤ B^2 := by
  simp only [abs_mul,abs_pow]
  have hp : |τ|^(n-1) ≤ 1 := by simpa only [abs_pow] using avg_pow_bound hτ (n-1)
  calc
    _ ≤ 1*B^2 := mul_le_mul hp (pow_le_pow_left₀ (abs_nonneg _) (hd _) _) (by positivity) zero_le_one
    _ = _ := one_mul _
lemma avg_deriv_bound {d : ℝ → ℝ} {B τ t : ℝ} (hB : 0 ≤ B) (hτ : τ ∈ Icc (0:ℝ) 1)
    (hd : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) (n : ℕ) :
    |2*τ^n*d (τ*t)*deriv d (τ*t)| ≤ 2*B^2 := by
  rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*1*B*B := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (avg_pow_bound hτ _) (by norm_num)) (hd _).1 (abs_nonneg _) (by norm_num)) (hd _).2 (abs_nonneg _) (by positivity)
    _ = _ := by ring
lemma averageProfile_hasDerivAt {n : ℕ} (hn : 0 < n) {d : ℝ → ℝ} {B : ℝ}
    (hd : ContDiff ℝ 1 d) (hB : 0 ≤ B) (hdB : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) (t : ℝ) :
    HasDerivAt (averageProfile n d) (averageProfileDeriv n d t) t := by
  have hdc := hd.continuous_deriv_one
  have hmeas (x : ℝ) : AEStronglyMeasurable (fun τ : ℝ => τ^(n-1)*(d (τ*x))^2) (volume.restrict (Icc (0:ℝ) 1)) :=
    (by fun_prop : Continuous (fun τ : ℝ => τ^(n-1)*(d (τ*x))^2)).aestronglyMeasurable
  have hmeas' (x : ℝ) : AEStronglyMeasurable (fun τ : ℝ => 2*τ^n*d (τ*x)*deriv d (τ*x)) (volume.restrict (Icc (0:ℝ) 1)) :=
    (by fun_prop : Continuous (fun τ : ℝ => 2*τ^n*d (τ*x)*deriv d (τ*x))).aestronglyMeasurable
  have hi : Integrable (fun τ : ℝ => τ^(n-1)*(d (τ*t))^2) (volume.restrict (Icc (0:ℝ) 1)) :=
    (by fun_prop : Continuous (fun τ : ℝ => τ^(n-1)*(d (τ*t))^2)).integrableOn_Icc
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Icc (0:ℝ) 1))
    (F := fun x τ => τ^(n-1)*(d (τ*x))^2) (F' := fun x τ => 2*τ^n*d (τ*x)*deriv d (τ*x))
    (bound := fun _ => 2*B^2) (s := univ) (by simp) (Eventually.of_forall hmeas) hi (hmeas' t) ?_ (integrable_const _) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ x hx
    exact avg_deriv_bound hB hτ hdB n
  · filter_upwards [] with τ x hx
    have hg := ((hd.differentiable (by norm_num) (τ*x)).hasDerivAt.comp x ((hasDerivAt_id x).const_mul τ)).pow 2
    have hh := hg.const_mul (τ^(n-1))
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    simp only [Function.comp_apply,Nat.cast_ofNat,mul_one]
    have hp : τ^(n-1)*τ = τ^n := by rw [←pow_succ,Nat.sub_add_cancel hn]
    calc
      _ = 2*(τ^(n-1)*τ)*d (τ*x)*deriv d (τ*x) := by rw [hp]
      _ = _ := by ring
lemma averageProfile_contDiff {n : ℕ} (hn : 0 < n) {d : ℝ → ℝ} {B : ℝ}
    (hd : ContDiff ℝ 1 d) (hB : 0 ≤ B) (hdB : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) :
    ContDiff ℝ 1 (averageProfile n d) := by
  have hdc := hd.continuous_deriv_one
  rw [contDiff_one_iff_deriv]
  constructor
  · exact fun t => (averageProfile_hasDerivAt hn hd hB hdB t).differentiableAt
  · have he : deriv (averageProfile n d) = averageProfileDeriv n d :=
      funext fun t => (averageProfile_hasDerivAt hn hd hB hdB t).deriv
    rw [he]
    apply continuous_of_dominated (bound := fun _ => 2*B^2)
    · intro t
      exact (by fun_prop : Continuous (fun τ : ℝ => 2*τ^n*d (τ*t)*deriv d (τ*t))).aestronglyMeasurable
    · intro t
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact avg_deriv_bound hB hτ hdB n
    · exact integrable_const _
    · filter_upwards [] with τ
      fun_prop
lemma averageProfile_nonneg (n : ℕ) (d : ℝ → ℝ) (t : ℝ) : 0 ≤ averageProfile n d t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  exact mul_nonneg (pow_nonneg hτ.1 _) (sq_nonneg _)
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Bubble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.Conformal
lemma averageProfile_bound {n : ℕ} {d : ℝ → ℝ} {B : ℝ}
    (hdB : ∀ x, |d x| ≤ B) (t : ℝ) : |averageProfile n d t| ≤ B^2 := by
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (0:ℝ) 1))
    (f := fun τ => τ^(n-1)*(d (τ*t))^2) (C := B^2) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact avg_integrand_bound hτ hdB n)
  simpa [averageProfile,Measure.real,Real.norm_eq_abs] using h
lemma averageProfile_deriv_bound {n : ℕ} (hn : 0 < n) {d : ℝ → ℝ} {B : ℝ}
    (hd : ContDiff ℝ 1 d) (hB : 0 ≤ B) (hdB : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) (t : ℝ) :
    |deriv (averageProfile n d) t| ≤ 2*B^2 := by
  rw [(averageProfile_hasDerivAt hn hd hB hdB t).deriv]
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (0:ℝ) 1))
    (f := fun τ => 2*τ^n*d (τ*t)*deriv d (τ*t)) (C := 2*B^2) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact avg_deriv_bound hB hτ hdB n)
  simpa [averageProfileDeriv,Measure.real,Real.norm_eq_abs] using h
lemma averageProfile_identity {n : ℕ} (hn : 0 < n) {d : ℝ → ℝ} {B : ℝ}
    (hd : ContDiff ℝ 1 d) (hB : 0 ≤ B) (hdB : ∀ x, |d x| ≤ B ∧ |deriv d x| ≤ B) (t : ℝ) :
    (n:ℝ)*averageProfile n d t+t*deriv (averageProfile n d) t = (d t)^2 := by
  have hdc := hd.continuous_deriv_one
  have hder (τ : ℝ) : HasDerivAt (fun τ => τ^n*(d (τ*t))^2)
      ((n:ℝ)*τ^(n-1)*(d (τ*t))^2+t*(2*τ^n*d (τ*t)*deriv d (τ*t))) τ := by
    have h := ((hasDerivAt_id τ).pow n).mul
      (((hd.differentiable (by norm_num) (τ*t)).hasDerivAt.comp τ ((hasDerivAt_id τ).mul_const t)).pow 2)
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    simp only [Function.comp_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one,one_mul]
    ring
  have hint : IntervalIntegrable (fun τ : ℝ => (n:ℝ)*τ^(n-1)*(d (τ*t))^2+
      t*(2*τ^n*d (τ*t)*deriv d (τ*t))) volume 0 1 := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hder τ) hint
  simp only [one_pow,zero_pow hn.ne',one_mul,zero_mul,sub_zero] at hFTC
  rw [(averageProfile_hasDerivAt hn hd hB hdB t).deriv]
  unfold averageProfile averageProfileDeriv
  rw [←integral_const_mul,←integral_const_mul,←integral_add]
  · rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
    convert hFTC using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext τ
    ring
  · exact ((by fun_prop : Continuous (fun τ : ℝ => (n:ℝ)*(τ^(n-1)*(d (τ*t))^2)))).integrableOn_Icc
  · exact ((by fun_prop : Continuous (fun τ : ℝ => t*(2*τ^n*d (τ*t)*deriv d (τ*t))))).integrableOn_Icc
end CAT0Fillings.Conformal
end

section
open Set Filter MeasureTheory

namespace CAT0Fillings.Conformal
lemma chordBubble_contDiff {a : ℝ} (ha : 0 ≤ a) (q : ℝ) (m : ℕ∞) :
    ContDiff ℝ m (chordBubble q a) := by
  exact (by fun_prop : ContDiff ℝ m (fun t : ℝ => 1+a*t^2)).rpow_const_of_ne
    (fun t => ne_of_gt (by positivity))
lemma chordBubbleD_contDiff {a : ℝ} (ha : 0 ≤ a) (q : ℝ) (m : ℕ∞) :
    ContDiff ℝ m (chordBubbleD q a) := by
  have h := (by fun_prop : ContDiff ℝ m (fun t : ℝ => 1+a*t^2)).rpow_const_of_ne
    (p := -q-1) (fun t => ne_of_gt (by positivity))
  exact (by fun_prop : ContDiff ℝ m (fun t : ℝ => -2*q*a*t)).mul h
lemma chordBubble_hasDerivAt {a : ℝ} (ha : 0 ≤ a) (q t : ℝ) :
    HasDerivAt (chordBubble q a) (chordBubbleD q a t) t := by
  have hb := (((hasDerivAt_id t).pow 2).const_mul a).const_add 1
  simp only [Pi.pow_apply,id_eq] at hb
  have hh := hb.rpow_const (p := -q) (Or.inl (ne_of_gt (by positivity)))
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [chordBubbleD,Nat.cast_ofNat,mul_one]
  ring
end CAT0Fillings.Conformal
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_Combined
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open CAT0Fillings.Conformal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chord_combined_oai (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β a : ℝ}
    (hb : 0 < β) (ha : 0 < a) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0) (_hg : LipschitzWith K g),
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g) :
    let w := chordBubble (1/(2*β)) a
    let f := averageProfile (k+1) (chordBubbleD (1/(2*β)) a)
    ∃ P : q.Sobolev,
      (q.inclusion P : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => q.inclusion v x*w (κ*dist o x*(q.inclusion v x)^β)) ∧
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P ≤
        (k+1:ℝ)*(∫ x, (q.inclusion v x)^(2+4*β)*(w (κ*dist o x*(q.inclusion v x)^β))^2 ∂MassMeasure.currentMassMeasure hT)+
        β*(k+1:ℝ)*(∫ x, (κ*dist o x*(q.inclusion v x)^β)^2*
          f (κ*dist o x*(q.inclusion v x)^β)*(q.inclusion v x)^(2+4*β) ∂MassMeasure.currentMassMeasure hT) := by
  dsimp only
  let c := 1/(2*β)
  let w := chordBubble c a
  let d := chordBubbleD c a
  let f := averageProfile (k+1) d
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨B,hB,hbounds⟩ := chordBubble_bounded_derivatives ha hc
  have hw : ContDiff ℝ 1 w := chordBubble_contDiff ha.le c 1
  have hd : ContDiff ℝ 1 d := chordBubbleD_contDiff ha.le c 1
  have hdB : ∀ t, |d t| ≤ B ∧ |deriv d t| ≤ B := by
    intro t
    refine ⟨?_,(hbounds t).2.2⟩
    simpa only [(chordBubble_hasDerivAt ha.le c t).deriv] using (hbounds t).2.1
  obtain ⟨P,hP,hInt,hE⟩ := q.chord_ground_state hz o v (κ := κ) hb hB hw
    (fun t => ⟨(hbounds t).1,(hbounds t).2.1⟩) hv hm hpow heuler
  have hf : ContDiff ℝ 1 f := averageProfile_contDiff (Nat.succ_pos _) hd hB hdB
  have hfB : ∀ t, |f t| ≤ B^2+2*B^2 ∧ |deriv f t| ≤ B^2+2*B^2 := by
    intro t
    exact ⟨(averageProfile_bound (fun t => (hdB t).1) t).trans (by nlinarith [sq_nonneg B]),
      (averageProfile_deriv_bound (Nat.succ_pos _) hd hB hdB t).trans (by nlinarith [sq_nonneg B])⟩
  have hf0 : ∀ t, 0 ≤ f t := fun t => averageProfile_nonneg (k+1) d t
  have hce := (q.chord_energy hz o v (κ := κ) hb hn (show 0 ≤ B^2+2*B^2 by positivity)
    hf hf0 hfB hv hm hpow heuler hr).2
  have hident (t : ℝ) : (k+1:ℝ)*f t+t*deriv f t = (deriv w t)^2 := by
    have hi := averageProfile_identity (Nat.succ_pos k) hd hB hdB t
    have hwder : deriv w t = d t := (chordBubble_hasDerivAt ha.le c t).deriv
    rw [hwder]
    simpa only [Nat.cast_succ] using hi
  have hleft : (∫ z, ((k+1:ℝ)*f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)+
      (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β)*
        deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))*‖q.chordXi o v κ β z‖^2 ∂q.atlasMeasure) =
    (∫ z, (deriv w (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))^2*
      ‖q.chordXi o v κ β z‖^2 ∂q.atlasMeasure) := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact congrArg (fun r : ℝ => r*‖q.chordXi o v κ β z‖^2) (hident _)
  change _ ≤ _ at hce
  rw [hleft] at hce
  refine ⟨P,hP,?_⟩
  apply hE.le.trans
  apply add_le_add le_rfl
  calc
    _ ≤ 4*β*((k+1:ℝ)/4*_) := mul_le_mul_of_nonneg_left hce (by positivity)
    _ = _ := by ring
end CAT0Fillings.ChartGeometry
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.ChartGeometry.chord_combined_oai.{u_1} := @OAI.CAT0Fillings.ChartGeometry.chord_combined_oai.{u_1}
