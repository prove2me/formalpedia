-- Prove2me | solution 1 for OAI.ElasticityPlanar.exists_algebra_variable_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:56:04.480564+00:00
-- url     : https://prove2.me/submissions/7f3acd1c-e361-499d-94f8-d9fb202f6142

import Mathlib
import Definitions.Def_OAIQ6El005

section
-- module Solutions.OAIQ6_Elast.Compat
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
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
-- module Solutions.OAIQ6_Elast.Elasticity_Compact
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Topology
namespace ElasticityCompact
variable {A P F : Type*} [TopologicalSpace A] [CompactSpace A]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasFDerivAt_compact (f : P → C(A,F)) (q : P → C(A,P →L[ℝ] F))
    (hq : Continuous q)
    (hd : ∀ p a, HasFDerivAt (fun p => f p a) (q p a) p) (p : P) :
    HasFDerivAt f (flipLinear (q p)) p := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r,hr,he⟩ := (Metric.continuousAt_iff (f := q) (a := p)).mp hq.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds p hr] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro a
  have hb (z : P) (hz : z∈Metric.ball p r) : ‖q z a-q p a‖ ≤ ε := by
    have hh := le_of_lt (he hz)
    simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist (f := q z) (g := q p) a).trans hh
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hd z a).hasFDerivWithinAt) hb (convex_ball p r)
    (Metric.mem_ball_self hr) hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [CompactSpace A] [NormedSpace ℝ P] [NormedSpace ℝ F] [NormedSpace ℝ E] in
lemma curryCompact_continuous (f : P × E → F) (hf : Continuous f) (j : A → E) (hj : Continuous j) :
    Continuous (curryCompact f hf j hj) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hf.comp (continuous_fst.prodMk (hj.comp continuous_snd))

lemma curryCompact_hasFDerivAt (f : P × E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : A → E) (hj : Continuous j) (p : P) :
    HasFDerivAt (curryCompact f hf.continuous j hj)
      (flipLinear ⟨fun a => (fderiv ℝ f (p,j a)).comp (ContinuousLinearMap.inl ℝ P E),
        ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp (continuous_const.prodMk hj)).clm_comp continuous_const⟩) p := by
  let q : P → C(A,P →L[ℝ] F) := fun p =>
    ⟨fun a => (fderiv ℝ f (p,j a)).comp (ContinuousLinearMap.inl ℝ P E),
      ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp (continuous_const.prodMk hj)).clm_comp continuous_const⟩
  apply hasFDerivAt_compact _ q ?_ ?_ p
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp
      (continuous_fst.prodMk (hj.comp continuous_snd))).clm_comp continuous_const
  · intro p a
    exact (hf.differentiable (by simp) (p,j a)).hasFDerivAt.comp p
      ((hasFDerivAt_id p).prodMk (hasFDerivAt_const (j a) p))

/-- Smooth currying over a compact set. This supplies the Banach-space parameter
regularity needed for the actual coefficient multipliers and linear ODE. -/
theorem curryCompact_contDiff [FiniteDimensional ℝ P]
    (f : P × E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : A → E) (hj : Continuous j) :
    ContDiff ℝ (⊤ : ℕ∞) (curryCompact f hf.continuous j hj) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing f with
  | zero =>
    simp only [Nat.cast_zero,contDiff_zero]
    exact curryCompact_continuous f hf.continuous j hj
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv_apply]
    refine ⟨fun p => (curryCompact_hasFDerivAt f hf j hj p).differentiableAt,by simp,fun v => ?_⟩
    let f' : P × E → F := fun q => fderiv ℝ f q (v,0)
    have hf' : ContDiff ℝ (⊤ : ℕ∞) f' := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    have he : (fun p => fderiv ℝ (curryCompact f hf.continuous j hj) p v)=
        curryCompact f' hf'.continuous j hj := by
      funext p
      ext a
      rw [(curryCompact_hasFDerivAt f hf j hj p).fderiv]
      rfl
    rw [he]
    exact ih f' hf'
end ElasticityCompact

end
end
section
noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal
namespace ElasticityCompact
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {S : Set E} [CompactSpace S]
omit [NormedSpace ℝ E] in
lemma toLinfCompact_ae (hS : MeasurableSet S) (μ : Measure E) (f : C(S,ℂ)) :
    toLinfCompact hS μ f =ᵐ[μ] zeroExtend f := MemLp.coeFn_toLp (zeroExtend_memLp hS μ f)
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- A joint smooth family with a fixed compact spatial support is genuinely
smooth with values in L-infinity, not merely pointwise smooth. -/
theorem exists_smooth_linf_family (hS : MeasurableSet S) (μ : Measure E)
    (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) :
    ∃ b : P → Lp ℂ ∞ μ, ContDiff ℝ (⊤ : ℕ∞) b ∧ ∀ p, b p =ᵐ[μ] fun x => a (p,x) := by
  let f := curryCompact a ha.continuous (fun x : S => (x:E)) continuous_subtype_val
  have hf := curryCompact_contDiff a ha (fun x : S => (x:E)) continuous_subtype_val
  refine ⟨fun p => toLinfCompact hS μ (f p),?_,fun p => ?_⟩
  · have hL : ContDiff ℝ (⊤ : ℕ∞) (toLinfCompact hS μ) :=
      (toLinfCompact hS μ).restrictScalars ℝ |>.contDiff
    exact hL.comp hf
  · apply (toLinfCompact_ae hS μ (f p)).trans
    apply Eventually.of_forall
    intro x
    by_cases hx : x∈S
    · exact zeroExtend_mem (f p) ⟨x,hx⟩
    · rw [zeroExtend_notMem _ hx]
      change 0=a (p,x)
      exact (hs p x hx).symm
end ElasticityCompact

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
namespace ElasticityRegularity

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma fourierMultiplier_add {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    fourierMultiplierCLM F (g+h) u=fourierMultiplierCLM F g u+fourierMultiplierCLM F h u := by
  simp only [fourierMultiplierCLM_apply,smulLeftCLM_add hg hh,add_apply,fourierInv_add]

omit [CompleteSpace F] in
lemma besselPotential_two (u : 𝓢'(E,F)) :
    besselPotential E F 2 u=u+fourierMultiplierCLM F (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) u := by
  have he : (fun x : E => (((1+‖x‖^2)^(2/2 : ℝ) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ))+(fun x : E => ((‖x‖^2 : ℝ) : ℂ)) := by
    funext x
    norm_num
  rw [besselPotential,he,fourierMultiplier_add (by fun_prop) (by fun_prop)]
  simp

lemma sobolev_real_smul {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (c : ℝ) :
    MemSobolev s 2 (c • u) := by
  convert hu.smul (c : ℂ) using 1
  all_goals try with_reducible_and_instances rfl

/-- Whole-space elliptic gain for the actual distributional Laplacian. -/
theorem laplacian_gain {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) : MemSobolev (s+2) 2 u := by
  have hp : (-(2*Real.pi)^2 : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hm := sobolev_real_smul hΔ (-(2*Real.pi)^2)⁻¹
  rw [laplacian_eq_fourierMultiplierCLM,smul_smul,inv_mul_cancel₀ hp,one_smul] at hm
  have h := hu.add hm
  rw [← besselPotential_two,memSobolev_besselPotential_iff] at h
  simpa only [add_comm] using h

/-- One derivative of gain from information on all coordinate first derivatives. -/
theorem coordinate_derivative_gain {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hd : ∀ i, MemSobolev s 2 (∂_{b i} u)) :
    MemSobolev (s+1) 2 u := by
  have hall : ∀ S : Finset ι, MemSobolev (s-1) 2 (∑ i ∈ S, ∂_{b i} (∂_{b i} u)) := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi hS =>
      rw [Finset.sum_insert hi]
      exact ((hd i).lineDerivOp).add hS
  have hsum := hall Finset.univ
  rw [← laplacian_eq_sum b] at hsum
  have h := laplacian_gain (hu.mono (by linarith : s-1 ≤ s)) hsum
  have he : s-1+2=s+1 := by ring
  rwa [he] at h

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma compact_derivative {g : E → ℂ} (hg : HasCompactSupport g) (m : E) :
    HasCompactSupport (fun x => fderiv ℝ g x m) :=
  (hg.fderiv ℝ).comp_left (g := fun T : E →L[ℝ] ℂ => T m) (by simp)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma smooth_derivative {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ g x m) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

lemma sobolev_zero_product {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hb : MemLp g ∞ (volume : Measure E)) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (smulLeftCLM F g u) := by
  obtain ⟨v,rfl⟩ := memSobolev_zero_iff.mp hu
  apply memSobolev_zero_iff.mpr
  exact ⟨hb.toLp g • v, (Lp.toTemperedDistribution_smul_eq hg hb v).symm⟩

/-- Smooth compact coefficients preserve every nonnegative integral Sobolev order.
This is proved for the actual tempered distribution product, not an assumed
bounded multiplier on an unspecified Sobolev completion. -/
theorem sobolev_nat_product {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (n : ℕ) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    {u : 𝓢'(E,F)} (hu : MemSobolev n 2 u) : MemSobolev n 2 (smulLeftCLM F g u) := by
  induction n generalizing u g with
  | zero =>
    rw [Nat.cast_zero] at hu ⊢
    exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one] at hu ⊢
    apply coordinate_derivative_gain b (ih hg hc (hu.mono (by norm_num)))
    intro i
    have hd : MemSobolev (n : ℝ) 2 (∂_{b i} u) := by
      simpa only [add_sub_cancel_right] using hu.lineDerivOp (m := b i)
    rw [distribution_leibniz (hc.hasTemperateGrowth hg) (b i)
      ((compact_derivative hc (b i)).hasTemperateGrowth (smooth_derivative hg (b i)))]
    exact (ih (smooth_derivative hg (b i)) (compact_derivative hc (b i))
      (hu.mono (by norm_num))).add (ih hg hc hd)

end ElasticityRegularity

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity


section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma decay_memLp {s : ℝ} (hs : Module.finrank ℝ E < 2*s) :
    MemLp (fun x : E => (1+‖x‖^2)^(-s/2)) 2 := by
  have growth : (fun x : E => (1+‖x‖^2)^(-s/2)).HasTemperateGrowth := by fun_prop
  refine ⟨growth.1.continuous.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num)]
  suffices h : ∫⁻ x : E, ENNReal.ofReal ‖(1+‖x‖^2)^(-s)‖ < ⊤ from by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h
    rw [← Real.rpow_mul_natCast (by positivity)]
    simp
  apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weighted_decay_bound (x : E) (n k : ℕ) :
    ‖x‖^n*(1+‖x‖^2)^(-(n+k : ℝ)) ≤ (1+‖x‖^2)^(-(k : ℝ)) := by
  have hpos : 0 < 1+‖x‖^2 := by positivity
  have hbase : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
  calc
    _ ≤ (1+‖x‖^2)^n*(1+‖x‖^2)^(-(n+k : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hbase n) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_add hpos]
      congr 1
      ring

lemma all_orders_fourier_moments {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolev n 2 u) :
    ∃ v : Lp F 1 (volume : Measure E), 𝓕 u = (v : 𝓢'(E,F)) ∧
      ∀ n : ℕ, Integrable (fun x => ‖x‖^n*‖v x‖) := by
  let k : ℕ := Module.finrank ℝ E+1
  have hk : (Module.finrank ℝ E : ℝ) < 2*k := by dsimp [k]; push_cast; linarith
  obtain ⟨v,hv⟩ := (hu k).fourier_memL1 hk
  refine ⟨v,hv,fun n => ?_⟩
  obtain ⟨w,hw⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp (hu (2*(n+k)))
  have hdec (m : ℕ) (hm : k ≤ m) : MemLp (fun x : E => (1+‖x‖^2)^(-(m : ℝ))) 2 := by
    have hh : (Module.finrank ℝ E : ℝ) < 2*(2*m) := by
      have : (k : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    convert decay_memLp hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    congr 1
    ring
  have hg : MemLp (fun x : E => Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ)))) 2 :=
    (hdec (n+k) (Nat.le_add_left _ _)).ofReal
  let q : Lp F 1 (volume : Measure E) := hg.toLp _ • w
  have hq : (q : 𝓢'(E,F)) = 𝓕 u := by
    rw [Lp.toTemperedDistribution_smul_eq (by fun_prop),← hw,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert (smulLeftCLM_const (1 : ℂ) (𝓕 u)) using 1
    · congr 2
      ext x
      change Complex.ofReal ((1+‖x‖^2)^((↑(2*(n+k)) : ℝ)/2)) *
        Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ))) = 1
      rw [← Complex.ofReal_mul,← Complex.ofReal_one,Complex.ofReal_inj]
      rw [← Real.rpow_add (by positivity : 0 < (1+‖x‖^2 : ℝ))]
      convert Real.rpow_zero (1+‖x‖^2) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      push_cast
      ring
    · simp
  have heq : q=v := by
    apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F))
    change (q : 𝓢'(E,F)) = (v : 𝓢'(E,F))
    rw [hq,hv]
  have hqa : ∀ᵐ x, v x = Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ))) • w x := by
    rw [← heq]
    filter_upwards [Lp.coeFn_lpSMul (r := 1) (hg.toLp _) w, hg.coeFn_toLp] with x hx hy
    change q x = _ at hx
    rw [hx]
    change (hg.toLp _ : E → ℂ) x • w x = _
    rw [hy]
  have hi : Integrable (fun x : E => (1+‖x‖^2)^(-(k : ℝ))*‖w x‖) :=
    (hdec k le_rfl).integrable_mul (Lp.memLp w).norm
  apply hi.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v).norm)
  filter_upwards [hqa] with x hx
  change ‖‖x‖^n*‖v x‖‖ ≤ _
  rw [hx,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),← mul_assoc]
  simpa only [Nat.cast_add] using
    mul_le_mul_of_nonneg_right (weighted_decay_bound x n k) (norm_nonneg (w x))

end

section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma l1_inverse_fourier_distribution (v : Lp F 1 (volume : Measure E)) :
    (((Real.Lp.fourierTransformInv v).memLp_top.toLp _ : Lp F ∞ (volume : Measure E)) : 𝓢'(E,F)) =
      𝓕⁻ (v : 𝓢'(E,F)) := by
  ext φ
  rw [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x : E, φ x • 𝓕⁻ (v : E → F) x := by
      apply integral_congr_ae
      filter_upwards [(Real.Lp.fourierTransformInv v).memLp_top.coeFn_toLp] with x hx
      rw [hx,Real.Lp.fourierTransformInv_apply]
    _ = ∫ x : E, (𝓕⁻ φ) x • v x := by
      have hf : (-innerₗ E).flip = -innerₗ E := by
        ext x y
        exact congrArg Neg.neg (real_inner_comm x y)
      have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := -innerₗ E) (μ := (volume : Measure E)) (ν := volume) Real.continuous_fourierChar
        (show Continuous (fun p : E × E => -inner ℝ p.1 p.2) by fun_prop) φ.integrable (L1.integrable_coeFn v)
      rw [hf] at h
      simp only [SchwartzMap.fourierInv_coe]
      convert h.symm using 1
      all_goals try with_reducible_and_instances rfl
    _ = _ := rfl
  rfl

/-- A tempered distribution lying in all integral Sobolev spaces has an actual
bounded smooth representative. All moments of a single L1 Fourier representative
are proved first, so the smooth representatives do not depend on the order. -/
theorem all_orders_smooth_representative {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolev n 2 u) :
    ∃ g : BoundedContinuousFunction E F, ContDiff ℝ (⊤ : ℕ∞) (g : E → F) ∧
      u = ((g.memLp_top.toLp _ : Lp F ∞ (volume : Measure E)) : 𝓢'(E,F)) := by
  obtain ⟨v,hv,hm⟩ := all_orders_fourier_moments hu
  refine ⟨Real.Lp.fourierTransformInv v,?_,?_⟩
  · have hs := Real.contDiff_fourier (N := (⊤ : ℕ∞)) (fun n _ => hm n)
    convert hs.comp contDiff_neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact (Real.Lp.fourierTransformInv_apply v x).trans (Real.fourierInv_eq_fourier_neg _ _)
  · rw [l1_inverse_fourier_distribution,← hv,fourierInv_fourier_eq]

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_support_subset (g : E → ℂ) (m : E) :
    tsupport (fun x => fderiv ℝ g x m) ⊆ tsupport g :=
  (tsupport_comp_subset (g := fun T : E →L[ℝ] ℂ => T m) (by simp) (fderiv ℝ g)).trans
    (tsupport_fderiv_subset ℝ)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma laplacian_product {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (u : 𝓢'(E,F)) :
    Δ (smulLeftCLM F g u) = smulLeftCLM F g (Δ u)+
      ∑ d, (smulLeftCLM F (fun x => fderiv ℝ (fun y => fderiv ℝ g y (b d)) x (b d)) u+
        (2 : ℂ) • smulLeftCLM F (fun x => fderiv ℝ g x (b d)) (∂_{b d} u)) := by
  classical
  rw [laplacian_eq_sum b,laplacian_eq_sum b,map_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have hgd := smooth_derivative hg (b d)
  have hcd := compact_derivative hc (b d)
  rw [distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd),LineDeriv.lineDerivOp_add,
    distribution_leibniz (hcd.hasTemperateGrowth hgd) _
      ((compact_derivative hcd (b d)).hasTemperateGrowth (smooth_derivative hgd (b d))),
    distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd)]
  module

end ElasticityRegularity

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Solvability
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The Hahn--Banach / Riesz step used by the physical solvability argument.
This proves the functional-analytic implication, rather than postulating
existence of a right inverse. The physical test estimate is proved separately. -/
namespace ElasticityDualSolvability

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A lower norm estimate on an (unbounded) test operator gives a weak solution
for every Hilbert-space forcing, with precisely the same constant. No density
or completeness of the test space, or closedness of the range, is assumed. -/
theorem exists_weak_solution (D : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ v : D, ‖(v : H)‖ ≤ C * ‖A v‖) (f : H) :
    ∃ z : H, ‖z‖ ≤ C * ‖f‖ ∧ ∀ v : D, inner ℂ z (A v) = inner ℂ f (v : H) := by
  have hinj : Function.Injective A := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply Subtype.val_injective
    apply norm_eq_zero.mp
    have ht := hA (v-w)
    rw [map_sub, hvw, sub_self, norm_zero, mul_zero] at ht
    exact le_antisymm ht (norm_nonneg _)
  let T := (LinearEquiv.ofInjective A hinj).symm
  let l : A.range →ₗ[ℂ] ℂ :=
    ((innerSL ℂ f).toLinearMap.comp D.subtype).comp T.toLinearMap
  have hT (y : A.range) : A (T y) = (y : H) := by
    exact congrArg Subtype.val ((LinearEquiv.ofInjective A hinj).apply_symm_apply y)
  have hl : ∀ y : A.range, ‖l y‖ ≤ (C*‖f‖)*‖y‖ := by
    intro y
    change ‖inner ℂ f ((T y : D) : H)‖ ≤ _
    calc
      _ ≤ ‖f‖ * ‖((T y : D) : H)‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (C*‖A (T y)‖) := mul_le_mul_of_nonneg_left (hA (T y)) (norm_nonneg _)
      _ = _ := by rw [hT]; change ‖f‖ * (C * ‖y‖) = _; ring
  let L : A.range →L[ℂ] ℂ := l.mkContinuous (C*‖f‖) hl
  obtain ⟨G, hG, hnorm⟩ := exists_extension_norm_eq A.range L
  let z : H := (InnerProductSpace.toDual ℂ H).symm G
  refine ⟨z, ?_, fun v => ?_⟩
  · calc
      ‖z‖ = ‖G‖ := (InnerProductSpace.toDual ℂ H).symm.norm_map _
      _ = ‖L‖ := hnorm
      _ ≤ C*‖f‖ := l.mkContinuous_norm_le (mul_nonneg hC (norm_nonneg _)) hl
  · change inner ℂ ((InnerProductSpace.toDual ℂ H).symm G) (A v) = _
    rw [InnerProductSpace.toDual_symm_apply]
    change G ((LinearEquiv.ofInjective A hinj v : A.range) : H) = _
    rw [hG]
    change inner ℂ f ((T (LinearEquiv.ofInjective A hinj v) : D) : H) = _
    rw [LinearEquiv.symm_apply_apply]

end ElasticityDualSolvability

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_LocalRegularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
namespace ElasticityRegularity


section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace LocalEqual
variable {Ω : Set E} {u v w u' v' : 𝓢'(E,ℂ)}
lemma symm (h : LocalEqual Ω u v) : LocalEqual Ω v u := fun φ hc hs => (h φ hc hs).symm
lemma trans (h : LocalEqual Ω u v) (h' : LocalEqual Ω v w) : LocalEqual Ω u w :=
  fun φ hc hs => (h φ hc hs).trans (h' φ hc hs)
lemma add (h : LocalEqual Ω u v) (h' : LocalEqual Ω u' v') : LocalEqual Ω (u+u') (v+v') := by
  intro φ hc hs
  simp only [add_apply,h φ hc hs,h' φ hc hs]
lemma sub (h : LocalEqual Ω u v) (h' : LocalEqual Ω u' v') : LocalEqual Ω (u-u') (v-v') := by
  intro φ hc hs
  simp only [sub_apply,h φ hc hs,h' φ hc hs]
lemma smul (h : LocalEqual Ω u v) (c : ℂ) : LocalEqual Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
lemma sum {ι : Type*} (S : Finset ι) {u v : ι → 𝓢'(E,ℂ)}
    (h : ∀ i ∈ S, LocalEqual Ω (u i) (v i)) : LocalEqual Ω (∑ i ∈ S, u i) (∑ i ∈ S, v i) := by
  intro φ hc hs
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun i hi => h i hi φ hc hs)
lemma derivative (h : LocalEqual Ω u v) (a : E) : LocalEqual Ω (∂_{a} u) (∂_{a} v) := by
  intro φ hc hs
  change u (- ∂_{a} φ) = v (- ∂_{a} φ)
  apply h
  · change HasCompactSupport (fun x => -((∂_{a} φ : 𝓢(E,ℂ)) x))
    exact (hc.fderiv_apply (𝕜 := ℝ) a).neg
  · change tsupport (-((∂_{a} φ : 𝓢(E,ℂ)) : E → ℂ)) ⊆ Ω
    rw [tsupport_neg]
    exact (derivative_support_subset (φ : E → ℂ) a).trans hs
lemma cutoff (h : LocalEqual Ω u v) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    smulLeftCLM ℂ g u = smulLeftCLM ℂ g v := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ g φ) = v (SchwartzMap.smulLeftCLM ℂ g φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_right : HasCompactSupport (g * (φ : E → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_left (f := g) (g := (φ : E → ℂ))).trans hs
end LocalEqual
end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_dist_injective : Function.Injective (fun u : 𝓢(E,ℂ) => (u : 𝓢'(E,ℂ))) := by
  intro u v h
  apply SchwartzMap.injective_toLp 2 volume
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  change ((u.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ)) =
    ((v.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ))
  simpa only [Lp.toTemperedDistribution_toLp_eq] using h

lemma distribution_schwartz_product {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢(E,ℂ)) :
    smulLeftCLM ℂ g (u : 𝓢'(E,ℂ)) = (SchwartzMap.smulLeftCLM ℂ g u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply,SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma LocalEqual.cutoff_one {Ω : Set E} (u : 𝓢'(E,ℂ)) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (h1 : Set.EqOn g 1 Ω) :
    LocalEqual Ω (smulLeftCLM ℂ g u) u := by
  intro φ _ hs
  rw [smulLeftCLM_apply_apply]
  congr 1
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg,smul_eq_mul]
  by_cases hx : φ x=0
  · simp [hx]
  · rw [h1 (hs (subset_tsupport _ hx))]
    simp

lemma LocalEqual.schwartz_eqOn {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : 𝓢(E,ℂ)} (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    Set.EqOn (u : E → ℂ) (v : E → ℂ) Ω := by
  intro x hx
  obtain ⟨g,hs,hc,hg,_,h1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hΩ.mem_nhds hx)
  let f : E → ℂ := fun y => (g y : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  have hfs : tsupport f ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro y hy
    change g y ≠ 0
    intro hy0
    apply hy
    change (g y : ℂ)=0
    rw [hy0,Complex.ofReal_zero]
  have he := h.cutoff hfg hfc hfs
  rw [distribution_schwartz_product (hfc.hasTemperateGrowth hfg),
    distribution_schwartz_product (hfc.hasTemperateGrowth hfg)] at he
  have he' := congrArg (fun w : 𝓢(E,ℂ) => w x) (schwartz_dist_injective he)
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hfc.hasTemperateGrowth hfg),smul_eq_mul] at he'
  have hx1 : f x=1 := by simp only [f,h1,Complex.ofReal_one]
  simpa only [hx1,one_mul] using he'

lemma smooth_Linfty_product {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (v : BoundedContinuousFunction E ℂ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (v : E → ℂ)) :
    let f : 𝓢(E,ℂ) := (hc.mul_right : HasCompactSupport (g*(v : E → ℂ))).toSchwartzMap (hg.mul hv)
    smulLeftCLM ℂ g (((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))) : 𝓢'(E,ℂ)) = (f : 𝓢'(E,ℂ)) := by
  intro f
  ext φ
  simp only [smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply,SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [v.memLp_top.coeFn_toLp] with x hx
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hc.hasTemperateGrowth hg),hx,smul_eq_mul]
  change g x*φ x*v x = φ x*(g x*v x)
  ring

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma LocalEqual.lp_ae {Ω : Set E} (hΩ : IsOpen Ω)
    (u v : Lp ℂ 2 (volume : Measure E))
    (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → u x=v x := by
  have hu : LocallyIntegrable (u : E → ℂ) (volume : Measure E) := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hv : LocallyIntegrable (v : E → ℂ) (volume : Measure E) := (Lp.memLp v).locallyIntegrable (by norm_num)
  have he : ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → (u x-v x)=0 := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hu.sub hv).locallyIntegrableOn Ω) ?_
  · filter_upwards [he] with x hx
    intro hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  intro g hg hc hs
  let f : E → ℂ := fun x => (g x : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  let φ : 𝓢(E,ℂ) := hfc.toSchwartzMap hfg
  have hfs : tsupport (φ : E → ℂ) ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro x hx hzero
    apply hx
    change (g x : ℂ)=0
    rw [hzero,Complex.ofReal_zero]
  have hh := h φ hfc hfs
  simp only [Lp.toTemperedDistribution_apply] at hh
  have hiu := hu.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  have hiv := hv.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  simp only [smul_sub]
  rw [integral_sub hiu hiv,sub_eq_zero]
  simp only [show (φ : E → ℂ)=f from rfl,f,Complex.real_smul,smul_eq_mul] at hh ⊢
  convert hh using 1
  all_goals try with_reducible_and_instances rfl

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions _root_.OAI.ElasticityPlanar.graphComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityRegularity
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- A joint smooth compactly spatially supported coefficient yields a genuinely
operator-norm-smooth family of actual L2 multipliers. -/
theorem exists_smooth_lp_multiplier {S : Set E} (hS : IsCompact S)
    (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) :
    ∃ M : P → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ContDiff ℝ (⊤ : ℕ∞) M ∧ ∀ p f,
        (M p f : 𝓢'(E,ℂ))=smulLeftCLM ℂ (fun x => a (p,x)) (f : 𝓢'(E,ℂ)) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨b,hb,hbe⟩ := ElasticityCompact.exists_smooth_linf_family hS.measurableSet
    (volume : Measure E) a ha hs
  let B := (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure E) ∞ 2 2
  refine ⟨fun p => B (b p),(B.restrictScalars ℝ).contDiff.comp hb,fun p f => ?_⟩
  have ha' : ContDiff ℝ (⊤ : ℕ∞) (fun x => a (p,x)) :=
    ha.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun x => a (p,x)) := by
    apply hS.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hS.isClosed
    intro x hx
    contrapose! hx
    simpa only [Function.mem_support,not_not] using hs p x hx
  have hm := compact_bounded_multiplier ha' hc
  have hprod : B (b p) f=(hm.toLp (fun x => a (p,x))) • f := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (b p) f,
      Lp.coeFn_lpSMul (r := 2) (hm.toLp _) f,hm.coeFn_toLp,hbe p] with x h₁ h₂ h₃ h₄
    change ((ContinuousLinearMap.mul ℂ ℂ).holder 2 (b p) f) x=_
    rw [h₁,h₂]
    simp only [Pi.smul_apply',h₃,h₄]
    rfl
  rw [hprod,Lp.toTemperedDistribution_smul_eq (hc.hasTemperateGrowth ha') hm]
end ElasticityRegularity
namespace ElasticityPlanar
open MeasureTheory Complex

lemma d_Z (v : ℂ) (f : Test) : d v (Z f) = v • f + Z (d v f) := by
  apply Subtype.ext
  funext z
  change fderiv ℝ (fun z => z * f z) z v = v * f z + z * ((d v f : ℂ → ℂ) z)
  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    ((hasFDerivAt_id z).mul ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  simpa [d_apply, add_comm, mul_comm, Pi.mul_def] using h

lemma deriv_conj (f : Test) (z v : ℂ) :
    fderiv ℝ (fun z => star (f z)) z v = star (fderiv ℝ (f : ℂ → ℂ) z v) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z
    ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) h

lemma d_Zbar (v : ℂ) (f : Test) : d v (Zbar f) = (star v) • f + Zbar (d v f) := by
  apply Subtype.ext
  funext z
  change fderiv ℝ (fun z => star z * f z) z v = star v * f z + star z * ((d v f : ℂ → ℂ) z)
  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    ((Complex.conjCLE.hasFDerivAt (x := z)).mul
      ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  simpa [d_apply, Complex.star_def, add_comm, mul_comm, Pi.mul_def] using h

lemma d_d (v w : ℂ) (f : Test) (z : ℂ) :
    (d v (d w f) : ℂ → ℂ) z = fderiv ℝ (fderiv ℝ (f : ℂ → ℂ)) z v w := by
  have hd : Differentiable ℝ (fderiv ℝ (f : ℂ → ℂ)) :=
    ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : ℂ → ℂ) y w) z v = _
  rw [fderiv_clm_apply (hd z) (differentiableAt_const w)]
  simp

lemma d_comm (v w : ℂ) (f : Test) : d v (d w f) = d w (d v f) := by
  apply Subtype.ext
  funext z
  rw [d_d, d_d]
  exact (smooth f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

lemma integrable_pair (f g : Test) : Integrable (fun z : ℂ => star (f z)*g z) := by
  exact ((Complex.conjCLE.continuous.comp (smooth f).continuous).mul (smooth g).continuous).integrable_of_hasCompactSupport (compact g).mul_left

lemma pair_add_right (f g h : Test) : pair f (g+h) = pair f g + pair f h := by
  simpa only [pair, Submodule.coe_add, Pi.add_apply, mul_add] using
    integral_add (integrable_pair f g) (integrable_pair f h)

lemma pair_add_left (f g h : Test) : pair (f+g) h = pair f h + pair g h := by
  simpa only [pair, Submodule.coe_add, Pi.add_apply, star_add, add_mul] using
    integral_add (integrable_pair f h) (integrable_pair g h)

lemma pair_sub_right (f g h : Test) : pair f (g-h) = pair f g - pair f h := by
  simpa only [pair, Submodule.coe_sub, Pi.sub_apply, mul_sub] using
    integral_sub (integrable_pair f g) (integrable_pair f h)

lemma pair_sub_left (f g h : Test) : pair (f-g) h = pair f h - pair g h := by
  simpa only [pair, Submodule.coe_sub, Pi.sub_apply, star_sub, sub_mul] using
    integral_sub (integrable_pair f h) (integrable_pair g h)

lemma pair_smul_right (f g : Test) (a : ℂ) : pair f (a • g) = a * pair f g := by
  simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (star (f _)) a, mul_assoc]
  exact integral_const_mul a _

lemma pair_smul_left (f g : Test) (a : ℂ) : pair (a • f) g = star a * pair f g := by
  simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul, mul_comm (star (f _)), mul_assoc]
  exact integral_const_mul (star a) _

/-- Coordinate derivatives are skew adjoint on the actual test space. -/
lemma pair_d (f g : Test) (v : ℂ) : pair f (d v g) = -pair (d v f) g := by
  have h1 : Integrable (fun z : ℂ => fderiv ℝ (fun z => star (f z)) z v * g z) := by
    simpa only [deriv_conj, d_apply] using integrable_pair (d v f) g
  have h2 : Integrable (fun z : ℂ => star (f z)*fderiv ℝ (g : ℂ → ℂ) z v) :=
    integrable_pair f (d v g)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 (integrable_pair f g)
    (fun z _ => Complex.conjCLE.differentiableAt.comp z ((smooth f).differentiable (by simp) z))
    (fun z _ => (smooth g).differentiable (by simp) z)
    |>.trans (by simp only [pair, deriv_conj, d_apply])

lemma pair_Z (f g : Test) : pair f (Z g) = pair (Zbar f) g := by
  apply integral_congr_ae
  filter_upwards [] with z
  simp [mul_comm, mul_left_comm, mul_assoc]

lemma pair_Zbar (f g : Test) : pair f (Zbar g) = pair (Z f) g := by
  apply integral_congr_ae
  filter_upwards [] with z
  simp [mul_comm, mul_left_comm]

lemma pair_B (f g : Test) (t : ℝ) : pair f (B t g) = pair (C t f) g := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, pair_add_right, pair_sub_right, pair_smul_right,
    pair_add_left, pair_sub_left, pair_smul_left, pair_d, pair_Z,
    ← neg_one_smul ℂ (d 1 f), pair_smul_left, map_neg, map_one,
    Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma pair_C (f g : Test) (t : ℝ) : pair f (C t g) = pair (B t f) g := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, pair_add_right, pair_sub_right, pair_smul_right,
    pair_add_left, pair_sub_left, pair_smul_left, pair_d, pair_Zbar,
    ← neg_one_smul ℂ (d 1 g), pair_smul_right, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma Z_Zbar (f : Test) : Z (Zbar f) = Zbar (Z f) := by
  apply Subtype.ext
  funext z
  change z * (star z * f z) = star z * (z * f z)
  ring

/-- Positive commutator of the two Gaussian-conjugated planar operators. -/
lemma commutator (t : ℝ) (f : Test) :
    C t (B t f) - B t (C t f) = (4 * (t : ℂ)) • f := by
  simp only [B, C, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, map_add, map_sub, map_smul, map_neg, d_Z, d_Zbar,
    star_one, Complex.star_def, Complex.conj_I]
  rw [d_comm I 1 f, Z_Zbar f]
  trans (2 * (t : ℂ) - 2 * (t : ℂ) * I ^ 2) • f
  · module
  · congr 1
    rw [Complex.I_sq]
    ring

lemma energy_identity (t : ℝ) (f : Test) :
    pair (B t f) (B t f) - pair (C t f) (C t f) =
      (4 * (t : ℂ)) * pair f f := by
  calc
    _ = pair f (C t (B t f) - B t (C t f)) := by
      rw [pair_sub_right, pair_C f (B t f) t, pair_B f (C t f) t]
    _ = _ := by rw [commutator, pair_smul_right]

lemma mass_integral (f : Test) : mass f = ∫ z : ℂ, Complex.normSq (f z) := by
  have h := integral_re (integrable_pair f f)
  simpa only [mass, pair, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h.symm

lemma integrable_normSq (f : Test) : Integrable (fun z : ℂ => Complex.normSq (f z)) := by
  have h := (integrable_pair f f).re
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h

lemma mass_nonneg (f : Test) : 0 ≤ mass f := by
  rw [mass_integral]
  exact integral_nonneg fun _ => Complex.normSq_nonneg _

/-- An actual weighted support estimate, independent of any frame existence. -/
theorem gaussian_coercivity (t : ℝ) (f : Test) :
    4 * t * mass f ≤ mass (B t f) := by
  have h := congrArg Complex.re (energy_identity t f)
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero, zero_mul, add_zero] at h
  change mass (B t f) - mass (C t f) = 4 * t * mass f at h
  linarith [mass_nonneg (C t f)]

lemma fderiv_gaussian (t : ℝ) (z v : ℂ) :
    fderiv ℝ (gaussian t) z v =
      gaussian t z * ((t : ℂ) / 2) * (v * star z + z * star v) := by
  have hd := (((hasFDerivAt_id z).mul (Complex.conjCLE.hasFDerivAt (x := z))).const_mul
    ((t : ℂ) / 2)).cexp
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hd.fderiv
  change fderiv ℝ (gaussian t) z v = _ at he
  rw [he]
  simp only [smul_apply, add_apply,
    smul_eq_mul, Complex.conjCLE_apply]
  change gaussian t z * ((t : ℂ) / 2 * (z * star v + star z * v)) = _
  ring

lemma d_W (t : ℝ) (v : ℂ) (f : Test) (z : ℂ) :
    (d v (W t f) : ℂ → ℂ) z = gaussian t z *
      (((t : ℂ) / 2) * (v * star z + z * star v) * f z + (d v f : ℂ → ℂ) z) := by
  have hd := ((smooth_gaussian t).differentiable (by simp) z).hasFDerivAt.mul
    ((smooth f).differentiable (by simp) z).hasFDerivAt
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hd.fderiv
  change fderiv ℝ (fun z => gaussian t z * f z) z v = _
  simp only [Pi.mul_def] at he
  rw [he]
  simp only [add_apply, smul_apply,
    smul_eq_mul, fderiv_gaussian, d_apply]
  ring

/-- Exact Gaussian conjugation of twice the planar Cauchy--Riemann operator. -/
lemma gaussian_conjugation (t : ℝ) (f : Test) :
    B t (W t f) = W t (d 1 f + I • d I f) := by
  apply Subtype.ext
  funext z
  change (d 1 (W t f) : ℂ → ℂ) z + I * (d I (W t f) : ℂ → ℂ) z -
      (t : ℂ) * (z * (gaussian t z * f z)) =
    gaussian t z * ((d 1 f : ℂ → ℂ) z + I * (d I f : ℂ → ℂ) z)
  rw [d_W, d_W]
  simp only [star_one, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

open scoped BigOperators

lemma normSq_sum_mul {n : Type*} [Fintype n] (a u : n → ℂ) :
    Complex.normSq (∑ j, a j * u j) ≤
      (∑ j, Complex.normSq (a j)) * ∑ j, Complex.normSq (u j) := by
  simp only [Complex.normSq_eq_norm_sq]
  have h := norm_sum_le Finset.univ (fun j => a j * u j)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖u j‖))

lemma mass_bound {n : Type*} [Fintype n] (f : Test) (u : n → Test) (K : ℝ)
    (h : ∀ z : ℂ, Complex.normSq (f z) ≤ K * ∑ j, Complex.normSq (u j z)) :
    mass f ≤ K * ∑ j, mass (u j) := by
  simp only [mass_integral]
  have hi : Integrable (fun z : ℂ => ∑ j, Complex.normSq (u j z)) :=
    integrable_finsetSum _ (fun j _ => integrable_normSq (u j))
  calc
    _ ≤ ∫ z : ℂ, K * ∑ j, Complex.normSq (u j z) :=
      integral_mono (integrable_normSq f) (hi.const_mul K) h
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => integrable_normSq (u j))]

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped BigOperators

lemma normSq_add_le (z w : ℂ) :
    normSq (z+w) ≤ 2*normSq z+2*normSq w := by
  simp only [normSq_eq_norm_sq]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le z w) 2
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

lemma mass_mul_bound (f g : Test) (K : ℝ)
    (hb : ∀ z, normSq (f z) ≤ K*normSq (g z)) : mass f ≤ K*mass g := by
  simpa using (mass_bound (n := Unit) f (fun _ => g) K (by simpa using hb))

/-- Quantitative Gaussian absorption for a system with no smallness of coefficients. -/
theorem weighted_inhomogeneous_bound {n : Type*} [Fintype n]
    (a : n → n → ℂ → ℂ) (u v : n → Test) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ z, (∃ j, u j z ≠ 0) → ∀ i, (∑ j, normSq (a i j z)) ≤ K)
    (heq : ∀ i z, (d 1 (u i)+I • d I (u i) : Test) z =
      v i z+∑ j, a i j z*u j z) :
    let t := (Fintype.card n : ℝ)*K+1
    (∑ i, mass (W t (u i))) ≤ ∑ i, mass (W t (v i)) := by
  classical
  dsimp only
  let t : ℝ := (Fintype.card n : ℝ)*K+1
  let w : n → Test := fun i => W t (u i)
  let f : n → Test := fun i => W t (v i)
  have hi (i : n) : mass (B t (w i)) ≤
      2*mass (f i)+2*K*∑ j, mass (w j) := by
    have hp (z : ℂ) : normSq ((B t (w i) : Test) z) ≤
        2*normSq (f i z)+2*K*∑ j, normSq (w j z) := by
      have he : (B t (w i) : Test) z=f i z+∑ j, a i j z*w j z := by
        dsimp [w,f]
        rw [gaussian_conjugation,W_apply,heq,mul_add,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      apply (normSq_add_le _ _).trans
      have hm : normSq (∑ j, a i j z*w j z) ≤ K*∑ j, normSq (w j z) := by
        by_cases hu : ∃ j, u j z ≠ 0
        · exact (normSq_sum_mul (fun j => a i j z) (fun j => w j z)).trans
            (mul_le_mul_of_nonneg_right (hb z hu i)
              (Finset.sum_nonneg fun j _ => normSq_nonneg _))
        · have hw : ∀ j, w j z=0 := by
            intro j
            have hj : u j z=0 := by simpa using not_exists.mp hu j
            simp [w,hj]
          simp [hw]
      linarith
    rw [mass_integral,mass_integral]
    simp only [mass_integral]
    calc
      _ ≤ ∫ z : ℂ, (2*normSq (f i z)+2*K*∑ j, normSq (w j z)) :=
        integral_mono (integrable_normSq _) (((integrable_normSq _).const_mul 2).add
          ((integrable_finsetSum _ (fun j _ => integrable_normSq (w j))).const_mul _)) hp
      _ = _ := by
        rw [integral_add ((integrable_normSq _).const_mul 2)
          ((integrable_finsetSum _ (fun j _ => integrable_normSq (w j))).const_mul _),
          integral_const_mul,integral_const_mul,
          integral_finsetSum _ (fun j _ => integrable_normSq (w j))]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (gaussian_coercivity t (w i)).trans (hi i))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul] at hs
  have hn : 0 ≤ (Fintype.card n : ℝ)*K := mul_nonneg (Nat.cast_nonneg _) hK
  have hw : 0 ≤ ∑ i, mass (w i) := Finset.sum_nonneg fun i _ => mass_nonneg _
  change (∑ i, mass (w i)) ≤ ∑ i, mass (f i)
  dsimp [t] at hs
  nlinarith [mul_nonneg hn hw]


lemma gaussian_inv (t : ℝ) (z : ℂ) : gaussian (-t) z*gaussian t z=1 := by
  rw [gaussian,gaussian,← Complex.exp_add]
  have h : (((-t : ℝ) : ℂ)/2)*(z*star z)+((t : ℂ)/2)*(z*star z)=0 := by
    push_cast
    ring
  rw [h,Complex.exp_zero]

lemma supported_weight_bound {S : Set ℂ} (hS : IsCompact S) (t : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ f : Test, tsupport (f : ℂ → ℂ) ⊆ S →
      mass (W t f) ≤ C*mass f := by
  have hc : Continuous (fun z => normSq (gaussian t z)) :=
    continuous_normSq.comp (smooth_gaussian t).continuous
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max K 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro f hf
  apply mass_mul_bound
  intro z
  rw [W_apply,normSq_mul]
  by_cases hz : f z=0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (normSq_nonneg _)
    exact (le_abs_self (normSq (gaussian t z))).trans
      ((hK z (hf (subset_tsupport _ hz))).trans (le_max_left _ _))

lemma supported_weight_equivalence {S : Set ℂ} (hS : IsCompact S) (t : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ f : Test, tsupport (f : ℂ → ℂ) ⊆ S →
      mass f ≤ C*mass (W t f) ∧ mass (W t f) ≤ C*mass f := by
  obtain ⟨C₁,hC₁,h₁⟩ := supported_weight_bound hS t
  obtain ⟨C₂,hC₂,h₂⟩ := supported_weight_bound hS (-t)
  refine ⟨max C₁ C₂,lt_of_lt_of_le hC₁ (le_max_left _ _),?_⟩
  intro f hf
  have hw : tsupport (W t f : ℂ → ℂ) ⊆ S :=
    (tsupport_mul_subset_right (f := gaussian t) (g := (f : ℂ → ℂ))).trans hf
  have he : W (-t) (W t f)=f := by
    apply Subtype.ext
    funext z
    change gaussian (-t) z*(gaussian t z*f z)=f z
    rw [← mul_assoc,gaussian_inv,one_mul]
  constructor
  · have hh := h₂ (W t f) hw
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (mass_nonneg _))
  · exact (h₁ f hf).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (mass_nonneg _))

lemma matrix_bound_on_compact {n : Type*} [Fintype n] {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, Continuous (a i j)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ S, ∀ i, (∑ j, normSq (a i j z)) ≤ K := by
  classical
  let F : ℂ → ℝ := fun z => ∑ i, ∑ j, normSq (a i j z)
  have hF : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨K,hK⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max K 0,le_max_right _ _,?_⟩
  intro z hz i
  calc
    _ ≤ F z := Finset.single_le_sum (fun k _ => Finset.sum_nonneg
      (fun j _ => normSq_nonneg _)) (Finset.mem_univ i)
    _ ≤ ‖F z‖ := le_abs_self _
    _ ≤ K := hK z hz
    _ ≤ max K 0 := le_max_left _ _

/-- A true unweighted supported L2 estimate, uniform over all test columns on a
fixed compact set, for an arbitrary continuous matrix coefficient. -/
theorem supported_inhomogeneous_L2 {n : Type*} [Fintype n]
    {S : Set ℂ} (hS : IsCompact S) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, Continuous (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∀ u v : n → Test,
      (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      (∀ i, tsupport (v i : ℂ → ℂ) ⊆ S) →
      (∀ i z, (d 1 (u i)+I • d I (u i) : Test) z=v i z+∑ j, a i j z*u j z) →
      (∑ i, mass (u i)) ≤ C*∑ i, mass (v i) := by
  classical
  obtain ⟨K,hK,hb⟩ := matrix_bound_on_compact hS a ha
  let t : ℝ := (Fintype.card n : ℝ)*K+1
  obtain ⟨C,hC,hW⟩ := supported_weight_equivalence hS t
  refine ⟨C*C,mul_pos hC hC,?_⟩
  intro u v hu hv heq
  have hbound : ∀ z, (∃ j, u j z ≠ 0) → ∀ i, (∑ j, normSq (a i j z)) ≤ K := by
    intro z hz
    obtain ⟨j,hj⟩ := hz
    exact hb z (hu j (subset_tsupport _ hj))
  have hw := weighted_inhomogeneous_bound a u v K hK hbound heq
  change (∑ i, mass (W t (u i))) ≤ ∑ i, mass (W t (v i)) at hw
  calc
    _ ≤ ∑ i, C*mass (W t (u i)) := Finset.sum_le_sum fun i _ => (hW _ (hu i)).1
    _ = C*∑ i, mass (W t (u i)) := (Finset.mul_sum ..).symm
    _ ≤ C*∑ i, mass (W t (v i)) := mul_le_mul_of_nonneg_left hw hC.le
    _ ≤ C*(C*∑ i, mass (v i)) := mul_le_mul_of_nonneg_left (by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (hW _ (hv i)).2) hC.le
    _ = _ := by ring

end ElasticityPlanar
namespace ElasticityDualSolvability
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma weak_unique_in_range (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) {f z w : H}
    (hz : z ∈ A.range.topologicalClosure) (hw : w ∈ A.range.topologicalClosure)
    (hez : ∀ v : D, inner ℂ z (A v)=inner ℂ f (v : H))
    (hew : ∀ v : D, inner ℂ w (A v)=inner ℂ f (v : H)) : z=w := by
  have horth : z-w ∈ A.rangeᗮ := by
    intro y hy
    obtain ⟨v,rfl⟩ := hy
    rw [inner_eq_zero_symm,inner_sub_left,hez,hew,sub_self]
  have hcl : z-w ∈ A.range.topologicalClosureᗮ := by simpa using horth
  have hself := hcl (z-w) (A.range.topologicalClosure.sub_mem hz hw)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)

/-- Hilbert projection makes the actual Hahn--Banach solver canonical and linear.
It will be used for smooth parameter dependence of the planar right inverse. -/
theorem exists_linear_weak_solver (D : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ v : D, ‖(v : H)‖ ≤ C*‖A v‖) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ C ∧ ∀ f v, inner ℂ (T f) (A v)=inner ℂ f (v : H) := by
  let V := A.range.topologicalClosure
  have : CompleteSpace V := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hex (f : H) : ∃ z : H, z ∈ V ∧ ‖z‖ ≤ C*‖f‖ ∧
      ∀ v : D, inner ℂ z (A v)=inner ℂ f (v : H) := by
    obtain ⟨z,hz,heq⟩ := exists_weak_solution D A C hC hA f
    refine ⟨V.orthogonalProjectionOnto z,(V.orthogonalProjectionOnto z).property,
      (V.norm_orthogonalProjectionOnto_apply_le z).trans hz,?_⟩
    intro v
    let av : V := ⟨A v,Submodule.le_topologicalClosure _ (LinearMap.mem_range_self A v)⟩
    have h := V.inner_orthogonalProjectionOnto_eq_of_mem_right av z
    change inner ℂ _ (A v) = inner ℂ z (A v) at h
    exact h.trans (heq v)
  choose t ht hnorm heq using hex
  let L : H →ₗ[ℂ] H :=
    { toFun := t
      map_add' := by
        intro f g
        apply weak_unique_in_range D A (ht (f+g)) (V.add_mem (ht f) (ht g)) (heq (f+g))
        intro v
        simp only [inner_add_left,heq]
      map_smul' := by
        intro c f
        apply weak_unique_in_range D A (ht (c • f)) (V.smul_mem c (ht f)) (heq (c • f))
        intro v
        simp only [inner_smul_left,heq] }
  refine ⟨L.mkContinuous C hnorm,L.mkContinuous_norm_le hC hnorm,heq⟩
end ElasticityDualSolvability
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped SchwartzMap ENNReal BigOperators

lemma toSchwartz_injective : Function.Injective toSchwartz := by
  intro u v h
  apply Subtype.ext
  exact congrArg (fun f : 𝓢(ℂ,ℂ) => (f : ℂ → ℂ)) h

lemma L2_injective : Function.Injective L2 := (SchwartzMap.injective_toLp 2 volume).comp toSchwartz_injective
lemma inner_L2 (f g : Test) : inner ℂ (L2 f) (L2 g)=pair f g := by
  simpa only [L2,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,SchwartzMap.toLpCLM_apply,
    RCLike.inner_apply',RCLike.star_def,toSchwartz_apply,pair] using
    SchwartzMap.inner_toL2_toL2_eq (toSchwartz f) (toSchwartz g) volume
lemma norm_L2_sq (f : Test) : ‖L2 f‖^2=mass f := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),inner_L2]
  rfl

lemma cj_neg (f : Test) : cj (-f)= -cj f := by ext z; exact star_neg _
lemma mass_cj (f : Test) : mass (cj f)=mass f := by
  rw [mass_integral,mass_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [cj_apply,Complex.star_def,normSq_conj]
lemma support_cj (S : Set ℂ) (f : Test) (h : tsupport (f : ℂ → ℂ) ⊆ S) :
    tsupport (cj f : ℂ → ℂ) ⊆ S := by
  apply Set.Subset.trans (closure_mono ?_) h
  intro z hz hh
  exact hz (by change star (f z)=0; rw [hh,star_zero])

variable {n : Type*}
lemma embed_injective : Function.Injective (embed (n := n)) := by
  intro u v h
  funext i
  exact L2_injective (congrArg (fun w : Hilbert n => w i) h)
variable [Fintype n]
lemma norm_embed_sq (u : n → Test) : ‖embed u‖^2=∑ i, mass (u i) := by
  rw [PiLp.norm_eq_of_L2,Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl (fun i _ => norm_L2_sq (u i))
lemma norm_embed_cj (u : n → Test) : ‖embed (fun i => cj (u i))‖=‖embed u‖ := by
  have h : ‖embed (fun i => cj (u i))‖^2=‖embed u‖^2 := by
    simp only [norm_embed_sq,mass_cj]
  nlinarith [norm_nonneg (embed (fun i => cj (u i))),norm_nonneg (embed u)]

lemma transport_supported {S : Set ℂ} (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) (u : n → Test)
    (hu : ∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) :
    ∀ i, tsupport (transport a ha u i : ℂ → ℂ) ⊆ S := by
  intro i
  apply (tsupport_add _ _).trans
  apply Set.union_subset
  · apply (tsupport_add _ _).trans
    apply Set.union_subset
    · exact (tsupport_fderiv_apply_subset ℝ _).trans (hu i)
    · exact (tsupport_smul_subset_right (fun _ : ℂ => (I : ℂ)) (d I (u i) : ℂ → ℂ)).trans ((tsupport_fderiv_apply_subset ℝ I).trans (hu i))
  · have hsum (s : Finset n) : tsupport ((∑ j ∈ s, mulSmooth (a i j) (ha i j) (u j) : Test) : ℂ → ℂ) ⊆ S := by
      classical
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty,Submodule.coe_zero,tsupport_zero,Set.empty_subset]
      | @insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact (tsupport_add _ _).trans (Set.union_subset ((tsupport_mul_subset_right).trans (hu j)) ih)
    exact hsum Finset.univ

/-- A true L2 lower bound for the actual transport operator. -/
theorem supported_transport_estimate {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∀ u : n → Test, (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      ‖embed u‖ ≤ C*‖embed (transport a ha u)‖ := by
  obtain ⟨C,hC,hest⟩ := supported_inhomogeneous_L2 hS (fun i j z => -(a i j z)) (fun i j => (ha i j).continuous.neg)
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun u hu => ?_⟩
  have heq : ∀ i z, (d 1 (u i)+I • d I (u i) : Test) z =
      transport a ha u i z+∑ j, -(a i j z)*u j z := by
    intro i z
    change _ = (d 1 (u i)+I • d I (u i) : Test) z+(∑ j, mulSmooth (a i j) (ha i j) (u j) : Test) z+_
    simp only [Submodule.coe_sum,Finset.sum_apply,mulSmooth,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_neg_distrib,neg_mul]
    ring
  have h := hest u (transport a ha u) hu (transport_supported a ha u hu) heq
  rw [← norm_embed_sq,← norm_embed_sq] at h
  have hs := Real.sq_sqrt hC.le
  have hp : 0 ≤ Real.sqrt C*‖embed (transport a ha u)‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (embed u)]
end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory Complex Set
open scoped SchwartzMap ENNReal BigOperators
variable {n : Type*} [Fintype n]

lemma norm_adjTransport (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (u : n → Test) : ‖embed (adjTransport a ha u)‖=
      ‖embed (transport (fun i j z => -a j i z) (fun i j => (ha j i).neg) (fun i => cj (u i)))‖ := by
  change ‖embed (-(fun i => cj (transport (fun i j z => -a j i z) (fun i j => (ha j i).neg) (fun i => cj (u i)) i)))‖=_
  rw [map_neg,norm_neg,norm_embed_cj]

/-- Actual supported matrix transport has a bounded linear L2 weak right inverse.
The estimate comes from the proved Gaussian positive commutator, not a smallness
assumption or a globally given frame. -/
theorem exists_planar_weak_inverse {S : Set ℂ} (hS : IsCompact S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j)) :
    ∃ C : ℝ, 0<C ∧ ∃ T : Hilbert n →L[ℂ] Hilbert n, ‖T‖ ≤ C ∧
      ∀ f : Hilbert n, ∀ u : n → Test, (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
        inner ℂ (T f) (embed (adjTransport a ha u))=inner ℂ f (embed u) := by
  obtain ⟨C,hC,hest⟩ := supported_transport_estimate hS (fun i j z => -a j i z) (fun i j => (ha j i).neg)
  have hbound (u : n → Test) (hu : ∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) :
      ‖embed u‖ ≤ C*‖embed (adjTransport a ha u)‖ := by
    rw [norm_adjTransport,← norm_embed_cj u]
    exact hest _ (fun i => support_cj S (u i) (hu i))
  let V := supported (n := n) S
  let e : V →ₗ[ℂ] Hilbert n := embed.comp V.subtype
  have hinj : Function.Injective e := by
    intro u v h
    exact Subtype.val_injective (embed_injective h)
  let E := LinearEquiv.ofInjective e hinj
  let A : e.range →ₗ[ℂ] Hilbert n :=
    (embed.comp (adjTransport a ha)).comp (V.subtype.comp E.symm.toLinearMap)
  have he (u : e.range) : e (E.symm u)=(u : Hilbert n) := congrArg Subtype.val (E.apply_symm_apply u)
  have hA (u : e.range) : ‖(u : Hilbert n)‖ ≤ C*‖A u‖ := by
    rw [← he u]
    exact hbound _ (E.symm u).property
  obtain ⟨T,hT,heq⟩ := ElasticityDualSolvability.exists_linear_weak_solver e.range A C hC.le hA
  refine ⟨C,hC,T,hT,fun f u hu => ?_⟩
  let u' : V := ⟨u,hu⟩
  have h := heq f (E u')
  change inner ℂ (T f) (embed (adjTransport a ha ((E.symm (E u') : V) : n → Test)))=inner ℂ f (e u') at h
  rw [E.symm_apply_apply] at h
  exact h
end ElasticityPlanar
namespace ElasticityPlanarDistribution
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap LineDeriv Laplacian ENNReal BigOperators
open ElasticityRegularity

lemma schwartz_derivative_commute (v w : ℂ) (f : Test) : ∂_{v} (∂_{w} f)=∂_{w} (∂_{v} f) := by
  ext x
  have hdd (v w : ℂ) : (∂_{v} (∂_{w} f) : Test) x =
      fderiv ℝ (fderiv ℝ (f : ℂ → ℂ)) x v w := by
    change fderiv ℝ (fun y => fderiv ℝ (f : ℂ → ℂ) y w) x v = _
    rw [fderiv_clm_apply (((f.smooth ⊤).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) x)
      (differentiableAt_const w)]
    simp
  rw [hdd,hdd]
  exact (f.smooth ⊤).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _
lemma derivative_commute (v w : ℂ) (u : Dist) : ∂_{v} (∂_{w} u)=∂_{w} (∂_{v} u) := by
  ext φ
  change u (- ∂_{w} (- ∂_{v} φ))=u (- ∂_{v} (- ∂_{w} φ))
  simp only [LineDeriv.lineDerivOp_neg,neg_neg]
  rw [schwartz_derivative_commute]
lemma dhol_dbar (u : Dist) : dhol (dbar u)=Δ u := by
  rw [laplacian_eq_sum Complex.orthonormalBasisOneI]
  simp only [Complex.coe_orthonormalBasisOneI,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [dhol,dbar,LineDeriv.lineDerivOp_add,LineDeriv.lineDerivOp_smul,
    smul_add,smul_smul,Complex.I_mul_I,neg_one_smul]
  rw [derivative_commute (1 : ℂ) I]
  module
lemma LocalEqual.dhol {Ω : Set ℂ} {u v : Dist} (h : ElasticityRegularity.LocalEqual Ω u v) :
    ElasticityRegularity.LocalEqual Ω (dhol u) (dhol v) :=
  (h.derivative 1).sub ((h.derivative I).smul I)
end ElasticityPlanarDistribution
namespace ElasticityPlanar
open MeasureTheory Complex TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators LineDeriv
variable {n : Type*} [Fintype n]

lemma toSchwartz_d (v : ℂ) (φ : Test) : toSchwartz (d v φ)=∂_{v} (toSchwartz φ) := by
  ext z
  rfl
lemma Lp_test (w : Lp ℂ 2 (volume : Measure ℂ)) (φ : Test) :
    (w : 𝓢'(ℂ,ℂ)) (toSchwartz φ) = inner ℂ (L2 (cj φ)) w := by
  rw [Lp.toTemperedDistribution_apply,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(toSchwartz (cj φ)).coeFn_toLp 2 volume] with z hz
  change φ z • w z = inner ℂ ((L2 (cj φ)) z) (w z)
  change (L2 (cj φ) : ℂ → ℂ) z=cj φ z at hz
  rw [hz]
  simp only [cj_apply,RCLike.inner_apply',starRingEnd_apply,star_star,smul_eq_mul,mul_comm]

lemma vector_transpose (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (w : n → 𝓢'(ℂ,ℂ)) (φ : n → Test) :
    (∑ i, (ElasticityPlanarDistribution.dbar (w i)+∑ j, smulLeftCLM ℂ (a i j) (w j)) (toSchwartz (φ i))) =
      ∑ i, w i (toSchwartz (- transport (fun i j z => -a j i z) (fun i j => (ha j i).1.neg) φ i)) := by
  simp only [ElasticityPlanarDistribution.dbar,add_apply,sum_apply,smul_apply,
    smulLeftCLM_apply_apply,TemperedDistribution.lineDerivOp_apply_apply]
  simp only [transport,LinearMap.coe_mk,AddHom.coe_mk,map_neg,map_add,map_smul,map_sum,
    toSchwartz_d, smul_eq_mul]
  have hm (i j : n) : toSchwartz (mulSmooth (fun z => -a j i z) (ha j i).1.neg (φ j)) =
      -SchwartzMap.smulLeftCLM ℂ (a j i) (toSchwartz (φ j)) := by
    ext z
    simp only [toSchwartz_apply,neg_apply,SchwartzMap.smulLeftCLM_apply_apply (ha j i),smul_eq_mul]
    change (-a j i z)*φ j z= -(a j i z*φ j z)
    ring
  simp only [hm,map_neg,Finset.sum_neg_distrib,neg_add_rev,neg_neg,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [mul_neg,Finset.sum_neg_distrib]
  ring

lemma weak_to_vector_distribution (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth) (S : Set ℂ) (w f : Hilbert n)
    (heq : ∀ u : n → Test, (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      inner ℂ w (embed (adjTransport a (fun i j => (ha i j).1) u))=inner ℂ f (embed u))
    (φ : n → Test) (hφ : ∀ i, tsupport (φ i : ℂ → ℂ) ⊆ S) :
    (∑ i, (ElasticityPlanarDistribution.dbar (w i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (w j : 𝓢'(ℂ,ℂ))) (toSchwartz (φ i))) =
      ∑ i, (f i : 𝓢'(ℂ,ℂ)) (toSchwartz (φ i)) := by
  rw [vector_transpose a ha]
  simp only [Lp_test]
  have h := congrArg star (heq (fun i => cj (φ i)) (fun i => support_cj S _ (hφ i)))
  have hs (u v : Hilbert n) : star (inner ℂ u v)=inner ℂ v u := inner_conj_symm (𝕜 := ℂ) v u
  rw [hs,hs] at h
  simp only [PiLp.inner_apply,embed_apply] at h
  have he (i : n) : adjTransport a (fun i j => (ha i j).1) (fun i => cj (φ i)) i =
      cj (-transport (fun i j z => -a j i z) (fun i j => (ha j i).1.neg) φ i) := by
    simp only [adjTransport,LinearMap.coe_mk,AddHom.coe_mk,cj_cj,cj_neg]
  simpa only [he] using h

lemma weak_to_local_equation (Ω S : Set ℂ) (hΩ : Ω ⊆ S)
    (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth) (w f : Hilbert n)
    (heq : ∀ u : n → Test, (∀ i, tsupport (u i : ℂ → ℂ) ⊆ S) →
      inner ℂ w (embed (adjTransport a (fun i j => (ha i j).1) u))=inner ℂ f (embed u)) :
    ∀ i, ElasticityRegularity.LocalEqual Ω (ElasticityPlanarDistribution.dbar (w i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (w j : 𝓢'(ℂ,ℂ))) (f i : 𝓢'(ℂ,ℂ)) := by
  classical
  intro i φ hc hs
  let φ' : Test := ⟨φ,⟨φ.smooth ⊤,hc⟩⟩
  let ψ : n → Test := fun j => if j=i then φ' else 0
  have hψ : ∀ j, tsupport (ψ j : ℂ → ℂ) ⊆ S := by
    intro j
    by_cases hji : j=i
    · simpa only [ψ,ite_eq_left hji] using hs.trans hΩ
    · simpa only [ψ,ite_eq_right hji,Submodule.coe_zero,tsupport_zero] using Set.empty_subset S
  have h := weak_to_vector_distribution a ha S w f heq ψ hψ
  simpa only [ψ,apply_ite,ite_true,map_zero,Finset.sum_ite_eq',Finset.mem_univ,
    show toSchwartz φ'=φ from by ext z; rfl] using h
end ElasticityPlanar
section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
namespace ElasticityRegularity

/-- The closed graph argument supplies norms for genuine distribution operators,
not additional quantitative regularity assumptions. -/
theorem exists_continuous_lift
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
    (J : Y →L[ℂ] Z) (hJ : Function.Injective J) (T : X →L[ℂ] Z)
    (hT : ∀ x, ∃ y, J y=T x) :
    ∃ L : X →L[ℂ] Y, ∀ x, J (L x)=T x := by
  choose l hl using hT
  let L : X →ₗ[ℂ] Y := {
    toFun := l
    map_add' := fun x y => hJ (by rw [map_add,hl,hl,hl,map_add])
    map_smul' := fun c x => hJ (by rw [map_smul,hl,hl,map_smul]; rfl) }
  have hc : IsClosed (L.graph : Set (X × Y)) := by
    have he : (L.graph : Set (X × Y))={p | T p.1=J p.2} := by
      ext p
      change p.2=L p.1 ↔ T p.1=J p.2
      constructor
      · intro h
        rw [h]
        exact (hl p.1).symm
      · intro h
        apply hJ
        exact h.symm.trans (hl p.1).symm
    rw [he]
    exact isClosed_eq (T.continuous.comp continuous_fst) (J.continuous.comp continuous_snd)
  exact ⟨⟨L,L.continuous_of_isClosed_graph hc⟩,hl⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lp_distribution_injective : Function.Injective
    (fun u : Lp ℂ 2 (volume : Measure E) => (u : 𝓢'(E,ℂ))) := by
  intro u v huv
  apply Lp.ext
  have h : LocalEqual Set.univ (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ)) :=
    fun _ _ _ => congrArg (fun T : 𝓢'(E,ℂ) => T _) huv
  filter_upwards [h.lp_ae isOpen_univ u v] with x hx
  exact hx (Set.mem_univ x)

lemma sobolevInjection_injective (s : ℝ) :
    Function.Injective (sobolevInjection (E := E) s) := by
  intro u v huv
  have h := congrArg (besselPotential E ℂ s) huv
  have hh : (u : 𝓢'(E,ℂ))=(v : 𝓢'(E,ℂ)) := by
    simpa only [sobolevInjection,ContinuousLinearMap.comp_apply,
      besselPotential_besselPotential_apply,neg_add_cancel,besselPotential_zero,
      ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply] using h
  exact lp_distribution_injective hh

lemma sobolevInjection_mem (s : ℝ) (f : Lp ℂ 2 (volume : Measure E)) :
    MemSobolev s 2 (sobolevInjection s f) := by
  refine ⟨f,?_⟩
  simp only [sobolevInjection,ContinuousLinearMap.comp_apply,
    besselPotential_besselPotential_apply,neg_add_cancel,besselPotential_zero,
    ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply]

lemma memSobolev_iff_range (s : ℝ) (u : 𝓢'(E,ℂ)) :
    MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure E), sobolevInjection s f=u := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨f,?_⟩
    change besselPotential E ℂ (-s) (f : 𝓢'(E,ℂ))=u
    exact (besselPotential_neg_apply_eq_iff s (f : 𝓢'(E,ℂ)) u).mpr hf
  · rintro ⟨f,rfl⟩
    exact sobolevInjection_mem s f

/-- A qualitative everywhere-defined Sobolev mapping theorem for a continuous
actual distribution operator automatically gives its bounded Sobolev realization.
This is useful for smooth multipliers and coordinate derivatives on cutoffs. -/
theorem exists_sobolev_realization (s t : ℝ) (P : 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ))
    (hP : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (P u)) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection t (L f)=P (sobolevInjection s f) := by
  exact exists_continuous_lift (sobolevInjection t) (sobolevInjection_injective t)
    (P.comp (sobolevInjection s)) (fun f =>
      (memSobolev_iff_range t _).mp (hP _ (sobolevInjection_mem s f)))

theorem exists_bounded_sobolev_derivative (s : ℝ) (m : E) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (s-1) (L f)=∂_{m} (sobolevInjection s f) := by
  exact exists_sobolev_realization s (s-1) (LineDeriv.lineDerivOpCLM ℂ 𝓢'(E,ℂ) m)
    (fun _ h => h.lineDerivOp)

theorem exists_bounded_sobolev_inclusion {s t : ℝ} (hst : t ≤ s) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection t (L f)=sobolevInjection s f := by
  exact exists_sobolev_realization s t (ContinuousLinearMap.id ℂ _)
    (fun _ h => h.mono hst)

end ElasticityRegularity

end
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_bounded_nat_multiplier (n : ℕ) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (n : ℝ) (L f)=smulLeftCLM ℂ g (sobolevInjection (n : ℝ) f) := by
  exact exists_sobolev_realization _ _ (smulLeftCLM ℂ g)
    (fun _ h => sobolev_nat_product (stdOrthonormalBasis ℝ E) n hg hc h)
end ElasticityRegularity
namespace ElasticityDualSolvability
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Smooth dependence of the local Neumann inverse, established with the stock
Banach-algebra inversion theorem. -/
theorem smooth_local_weak_inverse {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (T : H →L[ℂ] H) (B : P → H →L[ℂ] H) {p : P}
    (hB : ContDiffAt ℝ (⊤ : ℕ∞) B p) (hBT : ‖B p*T‖<1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => T*Ring.inverse (1+B q*T)) p := by
  have hu : IsUnit (1+B p*T) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one
      (by simpa only [norm_neg] using hBT : ‖-(B p*T)‖<1)
  obtain ⟨u,hu⟩ := hu
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) Ring.inverse (1+B p*T) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (1 : H →L[ℂ] H)+B q*T) p :=
    contDiffAt_const.add (hB.mul contDiffAt_const)
  have hc := hi.comp p hg
  exact contDiffAt_const.mul hc
end ElasticityDualSolvability

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Parameters
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions _root_.OAI.ElasticityPlanar.graphComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]

lemma lp_dist_add (f g : PL2) : ((f+g : PL2) : 𝓢'(ℂ,ℂ))=(f : 𝓢'(ℂ,ℂ))+(g : 𝓢'(ℂ,ℂ)) :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2).map_add f g
lemma lp_dist_sum (f : n → PL2) : ((∑ j, f j : PL2) : 𝓢'(ℂ,ℂ))=∑ j, (f j : 𝓢'(ℂ,ℂ)) :=
  map_sum (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2) f _

 theorem exists_planar_distribution_inverse {S Ω : Set ℂ} (hS : IsCompact S)
    (hΩ : Ω ⊆ S) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth) :
    ∃ T : Hilbert n →L[ℂ] Hilbert n, ∀ f : Hilbert n, ∀ i,
      LocalEqual Ω (ElasticityPlanarDistribution.dbar (T f i : 𝓢'(ℂ,ℂ))+
        ∑ j, smulLeftCLM ℂ (a i j) (T f j : 𝓢'(ℂ,ℂ))) (f i : 𝓢'(ℂ,ℂ)) := by
  obtain ⟨C,hC,T,hT,heq⟩ := exists_planar_weak_inverse hS a (fun i j => (ha i j).1)
  exact ⟨T,fun f => weak_to_local_equation Ω S hΩ a ha (T f) f (heq f)⟩

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators LineDeriv Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]

omit [Fintype n] in
lemma entryInjection_apply (i : n) (f : Hilbert n) : entryInjection i f=(f i : 𝓢'(ℂ,ℂ)) := rfl

lemma planarOperator_apply (a : n → n → ℂ → ℂ) (i : n) (f : Hilbert n) :
    planarOperator a i f=ElasticityPlanarDistribution.dbar (f i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (f j : 𝓢'(ℂ,ℂ)) := by
  simp only [planarOperator,ContinuousLinearMap.comp_apply,add_apply,smul_apply,sum_apply,
    entryInjection_apply,LineDeriv.lineDerivOpCLM_apply,ElasticityPlanarDistribution.dbar]

end ElasticityPlanar
section
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators Manifold
namespace ElasticityRegularity
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
lemma complex_clm_apply_smooth {f : P → E →L[ℂ] F} {g : P → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => f p (g p)) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).contDiff.comp hf).clm_apply hg
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
lemma complex_clm_comp_smooth {f : P → F →L[ℂ] G} {g : P → E →L[ℂ] F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => (f p).comp (g p)) := by
  let C := ContinuousLinearMap.compL ℂ E F G
  exact complex_clm_apply_smooth ((C.restrictScalars ℝ).contDiff.comp hf) hg
end ElasticityRegularity
namespace ElasticityPlanar
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
theorem exists_smooth_matrix_multiplier {K : Set ℂ} (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0) :
    ∃ M : P → Hilbert n →L[ℂ] Hilbert n,
      ContDiff ℝ (⊤ : ℕ∞) M ∧ ∀ p (f : Hilbert n) i,
        (M p f i : 𝓢'(ℂ,ℂ))=∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (f j : 𝓢'(ℂ,ℂ)) := by
  choose L hL hLe using fun i j => exists_smooth_lp_multiplier hK (a i j) (ha i j) (hs i j)
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)
  let M' : P → (n → PL2) →L[ℂ] (n → PL2) := fun p =>
    ContinuousLinearMap.pi (fun i => ∑ j, (L i j p).comp (ContinuousLinearMap.proj j))
  have hM' : ContDiff ℝ (⊤ : ℕ∞) M' := by
    apply (ContinuousLinearMap.piEquivL ℂ (n → PL2) (fun _ : n => PL2)).toContinuousLinearMap.restrictScalars ℝ |>.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    exact ContDiff.sum (fun j _ => complex_clm_comp_smooth (hL i j) contDiff_const)
  refine ⟨fun p => e.symm.toContinuousLinearMap.comp ((M' p).comp e.toContinuousLinearMap),
    complex_clm_comp_smooth contDiff_const (complex_clm_comp_smooth hM' contDiff_const),fun p f i => ?_⟩
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,e,
    PiLp.continuousLinearEquiv_apply,PiLp.continuousLinearEquiv_symm_apply,WithLp.ofLp_toLp,
    M',ContinuousLinearMap.pi_apply,sum_apply,ContinuousLinearMap.proj_apply]
  rw [lp_dist_sum]
  exact Finset.sum_congr rfl (fun j _ => hLe i j p (f j))

/-- Local inversion for an arbitrary joint smooth compact coefficient family,
not merely scalar multiples of one coefficient. -/
theorem local_variable_inverse {S Ω K : Set ℂ} (hS : IsCompact S) (hΩ : Ω ⊆ S)
    (hK : IsCompact K) (a : n → n → P × ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0) (p₀ : P) :
    ∃ (U : Set P) (T : P → Hilbert n →L[ℂ] Hilbert n),
      IsOpen U ∧ p₀∈U ∧ ContDiffOn ℝ (⊤ : ℕ∞) T U ∧
      ∀ p∈U, ∀ (f : Hilbert n) i,
        LocalEqual Ω (planarOperator (fun i j z => a i j (p,z)) i (T p f)) (f i : 𝓢'(ℂ,ℂ)) := by
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth := by
    have hc : HasCompactSupport (fun z => a i j (p,z)) := by
      apply hK.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ hK.isClosed
      intro z hz
      contrapose! hz
      simpa only [Function.mem_support,not_not] using hs i j p z hz
    exact hc.hasTemperateGrowth ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  obtain ⟨M,hM,hMe⟩ := exists_smooth_matrix_multiplier hK a ha hs
  obtain ⟨T₀,hT₀⟩ := exists_planar_distribution_inverse hS hΩ
    (fun i j z => a i j (p₀,z)) (hat p₀)
  let B : P → Hilbert n →L[ℂ] Hilbert n := fun p => M p-M p₀
  let T : P → Hilbert n →L[ℂ] Hilbert n := fun p => T₀*Ring.inverse (1+B p*T₀)
  let U : Set P := {p | ‖B p*T₀‖<1}
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hM.sub contDiff_const
  have hopen : IsOpen U := isOpen_lt (hB.continuous.mul continuous_const).norm continuous_const
  have hmem : p₀∈U := by simp only [U,B,mem_ofPred_eq,sub_self,zero_mul,norm_zero,zero_lt_one]
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) T U := fun p hp =>
    (ElasticityDualSolvability.smooth_local_weak_inverse T₀ B hB.contDiffAt hp).contDiffWithinAt
  refine ⟨U,T,hopen,hmem,hsmooth,fun p hp f i => ?_⟩
  change ‖B p*T₀‖<1 at hp
  have hu : IsUnit (1+B p*T₀) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one
      (by simpa only [norm_neg] using hp : ‖-(B p*T₀)‖<1)
  let q := Ring.inverse (1+B p*T₀) f
  have htot : q+B p (T₀ q)=f := by
    have h := congrArg (fun L : Hilbert n →L[ℂ] Hilbert n => L f)
      (Ring.mul_inverse_cancel (1+B p*T₀) hu)
    simpa only [mul_apply_eq_comp,add_apply,one_apply_eq_self] using h
  have hprod : ((B p (T₀ q)) i : 𝓢'(ℂ,ℂ))=
      (∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (T₀ q j : 𝓢'(ℂ,ℂ)))-
      (∑ j, smulLeftCLM ℂ (fun z => a i j (p₀,z)) (T₀ q j : 𝓢'(ℂ,ℂ))) := by
    change (((M p (T₀ q)-M p₀ (T₀ q) : Hilbert n)) i : 𝓢'(ℂ,ℂ))=_
    rw [PiLp.sub_apply]
    change (Lp.toTemperedDistributionCLM ℂ volume 2) (_-_) = _
    rw [map_sub]
    exact congrArg₂ (·-·) (hMe p (T₀ q) i) (hMe p₀ (T₀ q) i)
  intro φ hφ hφs
  have he := hT₀ q i φ hφ hφs
  have ht := congrArg (fun v : Hilbert n => (v i : 𝓢'(ℂ,ℂ)) φ) htot
  rw [PiLp.add_apply,lp_dist_add,hprod] at ht
  simp only [planarOperator_apply]
  change (ElasticityPlanarDistribution.dbar (T₀ q i : 𝓢'(ℂ,ℂ))+
    ∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (T₀ q j : 𝓢'(ℂ,ℂ))) φ=_
  simp only [add_apply,sub_apply] at he ht ⊢
  linear_combination he+ht
end ElasticityPlanar

end
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- A global smooth weak right inverse for actual smooth compactly supported
matrix coefficients over any finite-dimensional real parameter space. -/
theorem global_variable_inverse {S Ω K : Set ℂ} (hS : IsCompact S) (hΩ : Ω ⊆ S)
    (hK : IsCompact K) (a : n → n → P × ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0) :
    ∃ T : P → Hilbert n →L[ℂ] Hilbert n,
      ContDiff ℝ (⊤ : ℕ∞) T ∧ ∀ p, ∀ f : Hilbert n, ∀ i,
      LocalEqual Ω (planarOperator (fun i j z => a i j (p,z)) i (T p f)) (f i : 𝓢'(ℂ,ℂ)) := by
  let Q : P → Set (Hilbert n →L[ℂ] Hilbert n) := fun p => {T | ∀ f i,
    LocalEqual Ω (planarOperator (fun i j z => a i j (p,z)) i (T f)) (f i : 𝓢'(ℂ,ℂ))}
  have hconv : ∀ p, Convex ℝ (Q p) := by
    intro p T₁ hT₁ T₂ hT₂ b c _ _ hbc f i φ hφ hφs
    have h₁ := hT₁ f i φ hφ hφs
    have h₂ := hT₂ f i φ hφ hφs
    change (planarOperator (fun i j z => a i j (p,z)) i
      ((b : ℂ) • (T₁ f)+(c : ℂ) • (T₂ f))) φ=_
    simp only [map_add,map_smul,add_apply,smul_apply,h₁,h₂,smul_eq_mul]
    have hh : (b : ℂ)+(c : ℂ)=1 := by exact_mod_cast hbc
    rw [← add_mul,hh,one_mul]
  have hlocal : ∀ p : P, ∃ U ∈ nhds p, ∃ T : P → Hilbert n →L[ℂ] Hilbert n,
      ContMDiffOn 𝓘(ℝ,P) 𝓘(ℝ,Hilbert n →L[ℂ] Hilbert n) (⊤ : ℕ∞) T U ∧
      ∀ t ∈ U, T t∈Q t := by
    intro p
    obtain ⟨U,T,hU,hp,hT,heq⟩ := local_variable_inverse hS hΩ hK a ha hs p
    exact ⟨U,hU.mem_nhds hp,T,hT.contMDiffOn,heq⟩
  obtain ⟨T,hT⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ,P) hconv hlocal
  exact ⟨T,T.contMDiff.contDiff,hT⟩
end ElasticityPlanar
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


/-- A bounded realization of the actual Laplacian graph gain, extended by
orthogonal projection only off its graph. On the graph it is the unique actual
Sobolev representative. This is used for strong parameter regularity. -/
theorem bounded_laplacian_graph_gain (s : ℝ) :
    ∃ L : (Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E)) →L[ℂ]
        Lp ℂ 2 (volume : Measure E),
      ∀ f g, Δ (sobolevInjection s f)=sobolevInjection (s-1) g →
        sobolevInjection (s+1) (L (f,g))=sobolevInjection s f := by
  let H := Lp ℂ 2 (volume : Measure E)
  let X := WithLp 2 (H × H)
  let e : X ≃L[ℂ] H × H := WithLp.prodContinuousLinearEquiv 2 ℂ H H
  let D : 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ) := LineDeriv.laplacianCLM ℂ E _
  let T : X →L[ℂ] 𝓢'(E,ℂ) := (sobolevInjection s).comp
    ((ContinuousLinearMap.fst ℂ H H).comp e.toContinuousLinearMap)
  let A : X →L[ℂ] 𝓢'(E,ℂ) := D.comp T-
    (sobolevInjection (s-1)).comp ((ContinuousLinearMap.snd ℂ H H).comp e.toContinuousLinearMap)
  let G : Submodule ℂ X := A.ker
  have hclosed : IsClosed (G : Set X) := A.isClosed_ker
  let : CompleteSpace G := hclosed.completeSpace_coe
  have he (p : G) : Δ (sobolevInjection s (e p.1).1)=sobolevInjection (s-1) (e p.1).2 := by
    have hp := p.2
    change A p.1=0 at hp
    apply sub_eq_zero.mp
    simpa only [A,D,T,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',laplacianCLM_apply,
      ContinuousLinearEquiv.coe_coe] using hp
  obtain ⟨L,hL⟩ := exists_continuous_lift (sobolevInjection (E := E) (s+1))
    (sobolevInjection_injective (s+1)) (T.comp G.subtypeL) (fun p => by
      apply (memSobolev_iff_range (s+1) _).mp
      change MemSobolev (s+1) 2 (sobolevInjection s (e p.1).1)
      have hΔ : MemSobolev (s-1) 2 (Δ (sobolevInjection s (e p.1).1)) := by
        rw [he]
        exact sobolevInjection_mem _ _
      have h := laplacian_gain ((sobolevInjection_mem s (e p.1).1).mono (by linarith : s-1 ≤ s)) hΔ
      rw [show s-1+2=s+1 by ring] at h
      exact h)
  refine ⟨(L.comp G.orthogonalProjectionOnto).comp e.symm.toContinuousLinearMap,fun f g hfg => ?_⟩
  have hG : e.symm (f,g) ∈ G := by
    change A (e.symm (f,g))=0
    simpa only [A,D,T,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',laplacianCLM_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using
      (sub_eq_zero.mpr hfg)
  let p : G := ⟨e.symm (f,g),hG⟩
  have hp : G.orthogonalProjectionOnto (e.symm (f,g))=p :=
    G.orthogonalProjectionOnto_mem_subspace_eq_self p
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,hp,hL]
  change sobolevInjection s (e p.1).1=sobolevInjection s f
  simp only [p,ContinuousLinearEquiv.apply_symm_apply]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem smooth_laplacian_gain (s : ℝ)
    (f g : P → Lp ℂ 2 (volume : Measure E))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (heq : ∀ p, Δ (sobolevInjection s (f p))=sobolevInjection (s-1) (g p)) :
    ∃ q : P → Lp ℂ 2 (volume : Measure E), ContDiff ℝ (⊤ : ℕ∞) q ∧
      ∀ p, sobolevInjection (s+1) (q p)=sobolevInjection s (f p) := by
  obtain ⟨L,hL⟩ := bounded_laplacian_graph_gain (E := E) s
  exact ⟨fun p => L (f p,g p),(L.restrictScalars ℝ).contDiff.comp (hf.prodMk hg),
    fun p => hL (f p) (g p) (heq p)⟩
end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

namespace SmoothSobolev
variable {s t : ℝ} {u v : P → 𝓢'(E,ℂ)}
lemma add (hu : SmoothSobolev s u) (hv : SmoothSobolev s v) :
    SmoothSobolev s (fun p => u p+v p) := by
  obtain ⟨f,hf,he⟩ := hu
  obtain ⟨g,hg,hg'⟩ := hv
  exact ⟨fun p => f p+g p,hf.add hg,fun p => by rw [map_add,he,hg']⟩
lemma sub (hu : SmoothSobolev s u) (hv : SmoothSobolev s v) :
    SmoothSobolev s (fun p => u p-v p) := by
  obtain ⟨f,hf,he⟩ := hu
  obtain ⟨g,hg,hg'⟩ := hv
  exact ⟨fun p => f p-g p,hf.sub hg,fun p => by rw [map_sub,he,hg']⟩
lemma smul (hu : SmoothSobolev s u) (c : P → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    SmoothSobolev s (fun p => c p • u p) := by
  obtain ⟨f,hf,he⟩ := hu
  exact ⟨fun p => c p • f p,hc.smul hf,fun p => by rw [map_smul,he]⟩
lemma zero : SmoothSobolev s (fun _ : P => (0 : 𝓢'(E,ℂ))) :=
  ⟨fun _ => 0,contDiff_const,fun _ => map_zero _⟩
lemma sum {ι : Type*} (S : Finset ι) (u : ι → P → 𝓢'(E,ℂ))
    (hu : ∀ i ∈ S, SmoothSobolev s (u i)) :
    SmoothSobolev s (fun p => ∑ i ∈ S, u i p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (zero (s := s) (P := P) (E := E))
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hu i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))
lemma mono (hu : SmoothSobolev s u) (hst : t ≤ s) : SmoothSobolev t u := by
  obtain ⟨L,hL⟩ := exists_bounded_sobolev_inclusion (E := E) hst
  obtain ⟨f,hf,he⟩ := hu
  exact ⟨fun p => L (f p),(L.restrictScalars ℝ).contDiff.comp hf,fun p => (hL _).trans (he p)⟩
lemma derivative (hu : SmoothSobolev s u) (a : E) :
    SmoothSobolev (s-1) (fun p => ∂_{a} (u p)) := by
  obtain ⟨L,hL⟩ := exists_bounded_sobolev_derivative (E := E) s a
  obtain ⟨f,hf,he⟩ := hu
  exact ⟨fun p => L (f p),(L.restrictScalars ℝ).contDiff.comp hf,fun p => by rw [hL,he]⟩
lemma laplacian_gain (hu : SmoothSobolev s u)
    (hΔ : SmoothSobolev (s-1) (fun p => Δ (u p))) : SmoothSobolev (s+1) u := by
  obtain ⟨f,hf,he⟩ := hu
  obtain ⟨g,hg,hg'⟩ := hΔ
  obtain ⟨q,hq,hq'⟩ := smooth_laplacian_gain s f g hf hg (fun p => by rw [he,hg'])
  exact ⟨q,hq,fun p => (hq' p).trans (he p)⟩
end SmoothSobolev

namespace SmoothLocalSobolev
variable {Ω : Set E} {s t : ℝ} {u v : P → 𝓢'(E,ℂ)}
lemma add (hu : SmoothLocalSobolev Ω s u) (hv : SmoothLocalSobolev Ω s v) :
    SmoothLocalSobolev Ω s (fun p => u p+v p) := by
  intro g hg hc hs
  simpa only [map_add] using (hu g hg hc hs).add (hv g hg hc hs)
lemma sub (hu : SmoothLocalSobolev Ω s u) (hv : SmoothLocalSobolev Ω s v) :
    SmoothLocalSobolev Ω s (fun p => u p-v p) := by
  intro g hg hc hs
  simpa only [map_sub] using (hu g hg hc hs).sub (hv g hg hc hs)
lemma smul (hu : SmoothLocalSobolev Ω s u) (c : P → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    SmoothLocalSobolev Ω s (fun p => c p • u p) := by
  intro g hg hcg hs
  simpa only [map_smul] using (hu g hg hcg hs).smul c hc
lemma sum {ι : Type*} (S : Finset ι) (u : ι → P → 𝓢'(E,ℂ))
    (hu : ∀ i ∈ S, SmoothLocalSobolev Ω s (u i)) :
    SmoothLocalSobolev Ω s (fun p => ∑ i ∈ S, u i p) := by
  intro g hg hc hs
  simpa only [map_sum] using SmoothSobolev.sum S
    (fun i p => smulLeftCLM ℂ g (u i p)) (fun i hi => hu i hi g hg hc hs)
lemma product_derivative (hu : SmoothLocalSobolev Ω s u) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (a : E) :
    SmoothSobolev (s-1) (fun p => smulLeftCLM ℂ g (∂_{a} (u p))) := by
  have hd := smooth_derivative hg a
  have hdc := compact_derivative hc a
  have hds := (derivative_support_subset g a).trans hs
  have h := ((hu g hg hc hs).derivative a).sub
    ((hu _ hd hdc hds).mono (by linarith : s-1 ≤ s))
  simpa only [distribution_leibniz (hc.hasTemperateGrowth hg) a (hdc.hasTemperateGrowth hd),
    add_sub_cancel_left] using h
lemma derivative (hu : SmoothLocalSobolev Ω s u) (a : E) :
    SmoothLocalSobolev Ω (s-1) (fun p => ∂_{a} (u p)) :=
  fun _ hg hc hs => hu.product_derivative hg hc hs a
lemma congr (hu : SmoothLocalSobolev Ω s u) (he : ∀ p, LocalEqual Ω (v p) (u p)) :
    SmoothLocalSobolev Ω s v := by
  intro g hg hc hs
  have h : (fun p => smulLeftCLM ℂ g (v p))=(fun p => smulLeftCLM ℂ g (u p)) :=
    funext (fun p => (he p).cutoff hg hc hs)
  rw [h]
  exact hu g hg hc hs

/-- Strong smooth parameter regularity is gained for the actual distribution
family; the proof uses fixed bounded Laplacian graph operators. -/
lemma laplacian_gain (hu : SmoothLocalSobolev Ω s u)
    (hΔ : SmoothLocalSobolev Ω (s-1) (fun p => Δ (u p))) :
    SmoothLocalSobolev Ω (s+1) u := by
  let b := stdOrthonormalBasis ℝ E
  intro g hg hc hs
  have hbase := hu g hg hc hs
  apply SmoothSobolev.laplacian_gain hbase
  simp only [laplacian_product b hg hc]
  apply (hΔ g hg hc hs).add
  apply SmoothSobolev.sum Finset.univ
  intro i _
  have hgd := smooth_derivative hg (b i)
  have hcd := compact_derivative hc (b i)
  have hsd := (derivative_support_subset g (b i)).trans hs
  exact ((hu _ (smooth_derivative hgd (b i)) (compact_derivative hcd (b i))
    ((derivative_support_subset _ (b i)).trans hsd)).mono (by linarith)).add
    ((hu.product_derivative hgd hcd hsd (b i)).smul (fun _ => 2) contDiff_const)
end SmoothLocalSobolev
end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
lemma smooth_spatial_derivative {a : P × E → ℂ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => fderiv ℝ (fun x => a (q.1,x)) q.2 v) := by
  have he : (fun q : P × E => fderiv ℝ (fun x => a (q.1,x)) q.2 v)=
      (fun q : P × E => fderiv ℝ a q (0,v)) := by
    funext q
    have hg : HasFDerivAt (fun x : E => (q.1,x)) (ContinuousLinearMap.inr ℝ P E) q.2 :=
      (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
    have hh := (ha.differentiable (by simp) (q.1,q.2)).hasFDerivAt.comp q.2 hg
    change fderiv ℝ (a ∘ Prod.mk q.1) q.2 v=_
    rw [hh.fderiv]
    rfl
  rw [he]
  exact (ha.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma spatial_derivative_outside {S : Set E} (hS : IsClosed S) (a : P × E → ℂ)
    (hs : ∀ p x, x∉S → a (p,x)=0) (v : E) :
    ∀ p x, x∉S → fderiv ℝ (fun y => a (p,y)) x v=0 := by
  intro p x hx
  apply image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ (fun z => a (p,z)) y v)
  intro hh
  have ht : tsupport (fun y => a (p,y)) ⊆ S :=
    closure_minimal (fun y hy => by contrapose! hy; simpa only [Function.mem_support,not_not] using hs p y hy) hS
  exact hx (ht (derivative_support_subset (fun y => a (p,y)) v hh))

omit [FiniteDimensional ℝ P] in
lemma SmoothSobolev.coordinate_gain {s : ℝ} {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev s u)
    (hd : ∀ v : E, SmoothSobolev s (fun p => ∂_{v} (u p))) :
    SmoothSobolev (s+1) u := by
  apply hu.laplacian_gain
  let b := stdOrthonormalBasis ℝ E
  have h := SmoothSobolev.sum Finset.univ (fun i p => ∂_{b i} (∂_{b i} (u p)))
    (fun i _ => (hd (b i)).derivative (b i))
  simpa only [laplacian_eq_sum b] using h

lemma SmoothSobolev.variable_zero {S : Set E} (hS : IsCompact S)
    (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev 0 u) :
    SmoothSobolev 0 (fun p => smulLeftCLM ℂ (fun x => a (p,x)) (u p)) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨b,hb,hbe⟩ := ElasticityCompact.exists_smooth_linf_family hS.measurableSet
    (volume : Measure E) a ha hs
  obtain ⟨v,hv,he⟩ := hu
  simp only [sobolevInjection,neg_zero,besselPotential_zero,ContinuousLinearMap.id_comp,
    Lp.toTemperedDistributionCLM_apply] at he
  let B := (ContinuousLinearMap.mul ℝ ℂ).holderL (volume : Measure E) ∞ 2 2
  refine ⟨fun p => B (b p) (v p),(B.contDiff.comp hb).clm_apply hv,fun p => ?_⟩
  simp only [sobolevInjection,neg_zero,besselPotential_zero,ContinuousLinearMap.id_comp,
    Lp.toTemperedDistributionCLM_apply]
  have ha' : ContDiff ℝ (⊤ : ℕ∞) (fun x => a (p,x)) :=
    ha.comp (contDiff_const.prodMk contDiff_id)
  have hc := compact_slice hS a hs p
  have hm := compact_bounded_multiplier ha' hc
  have hprod : B (b p) (v p)=(hm.toLp (fun x => a (p,x))) • v p := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℝ ℂ).coeFn_holder (r := 2) (b p) (v p),
      Lp.coeFn_lpSMul (r := 2) (hm.toLp _) (v p),hm.coeFn_toLp,hbe p] with x h₁ h₂ h₃ h₄
    change ((ContinuousLinearMap.mul ℝ ℂ).holder 2 (b p) (v p)) x=_
    rw [h₁,h₂]
    simp only [Pi.smul_apply',h₃,h₄]
    rfl
  rw [hprod,Lp.toTemperedDistribution_smul_eq (hc.hasTemperateGrowth ha') hm,he]

/-- Joint smooth coefficient multiplication in the strong Hilbert Sobolev
parameter topology, for each actual nonnegative integral order. -/
theorem SmoothSobolev.variable_nat {S : Set E} (hS : IsCompact S)
    (N : ℕ) (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev N u) :
    SmoothSobolev N (fun p => smulLeftCLM ℂ (fun x => a (p,x)) (u p)) := by
  induction N generalizing a u with
  | zero =>
    rw [Nat.cast_zero] at hu ⊢
    exact SmoothSobolev.variable_zero hS a ha hs hu
  | succ N ih =>
    rw [Nat.cast_add,Nat.cast_one] at hu ⊢
    have hu' := hu.mono (by norm_num : (N : ℝ) ≤ N+1)
    apply (ih a ha hs hu').coordinate_gain
    intro v
    have hd : SmoothSobolev (N : ℝ) (fun p => ∂_{v} (u p)) := by
      simpa only [add_sub_cancel_right] using hu.derivative v
    have hsum := (ih _ (smooth_spatial_derivative ha v)
      (spatial_derivative_outside hS.isClosed a hs v) hu').add (ih a ha hs hd)
    convert hsum using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    have ha' : ContDiff ℝ (⊤ : ℕ∞) (fun x => a (p,x)) :=
      ha.comp (contDiff_const.prodMk contDiff_id)
    have hc := compact_slice hS a hs p
    exact distribution_leibniz (hc.hasTemperateGrowth ha') v
      ((compact_derivative hc v).hasTemperateGrowth (smooth_derivative ha' v)) (u p)
end ElasticityRegularity
namespace ElasticityPlanarDistribution
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open ElasticityRegularity
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {n : Type*} [Fintype n]
lemma SmoothLocalSobolev.dhol {Ω : Set ℂ} {s : ℝ} {u : P → Dist}
    (h : ElasticityRegularity.SmoothLocalSobolev Ω s u) :
    ElasticityRegularity.SmoothLocalSobolev Ω (s-1) (fun p => dhol (u p)) :=
  (h.derivative 1).sub ((h.derivative I).smul (fun _ => I) contDiff_const)

end ElasticityPlanarDistribution
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The continuous Sobolev embedding is a genuinely bounded operator, obtained
from the actual Fourier representative and the closed graph theorem. -/
theorem exists_bounded_continuous_embedding {s : ℝ} (hs : Module.finrank ℝ E < 2*s) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] BoundedContinuousFunction E ℂ,
      ∀ f, sobolevInjection s f=
        (((L f).memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E,ℂ)) := by
  let J := Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 1
  have hJ : Function.Injective J :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  obtain ⟨T,hT⟩ := exists_continuous_lift J hJ
    ((fourierCLM ℂ 𝓢'(E,ℂ)).comp (sobolevInjection s)) (fun f => by
      obtain ⟨v,hv⟩ := (sobolevInjection_mem s f).fourier_memL1 hs
      exact ⟨v,hv.symm⟩)
  let R : Lp ℂ 1 (volume : Measure E) →L[ℂ] BoundedContinuousFunction E ℂ :=
    (BoundedContinuousFunction.compContinuousCLM ℂ ℂ (-ContinuousMap.id E)).comp
      (Real.Lp.fourierTransformCLM E ℂ)
  refine ⟨R.comp T,fun f => ?_⟩
  change sobolevInjection s f=
    (((Real.Lp.fourierTransformInv (T f)).memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E,ℂ))
  rw [l1_inverse_fourier_distribution]
  have h := hT f
  change (T f : 𝓢'(E,ℂ))=𝓕 (sobolevInjection s f) at h
  rw [h,fourierInv_fourier_eq]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma SmoothSobolev.continuous_representative {s : ℝ} {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev s u) (hs : Module.finrank ℝ E < 2*s) :
    ∃ g : P → BoundedContinuousFunction E ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∀ p, u p=(((g p).memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E,ℂ)) := by
  obtain ⟨f,hf,he⟩ := hu
  obtain ⟨L,hL⟩ := exists_bounded_continuous_embedding hs
  exact ⟨fun p => L (f p),(L.restrictScalars ℝ).contDiff.comp hf,fun p => (he p).symm.trans (hL _)⟩

end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma bcfToDist_apply (g : BoundedContinuousFunction E ℂ) :
    bcfToDist g=(((g.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))) : 𝓢'(E,ℂ)) := rfl
lemma bcfToDist_injective : Function.Injective (bcfToDist (E := E)) := by
  intro f g h
  have hh : (f.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))=g.memLp_top.toLp _ :=
    LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)) h
  have ha : (f : E → ℂ)=ᵐ[volume] (g : E → ℂ) :=
    f.memLp_top.coeFn_toLp.symm.trans (hh ▸ g.memLp_top.coeFn_toLp)
  exact DFunLike.coe_injective ((f.continuous.ae_eq_iff_eq volume g.continuous).mp ha)
lemma bcf_smooth_of_all_orders (g : BoundedContinuousFunction E ℂ)
    (hg : ∀ n : ℕ, MemSobolev n 2 (bcfToDist g)) :
    ContDiff ℝ (⊤ : ℕ∞) (g : E → ℂ) := by
  obtain ⟨h,hh,he⟩ := all_orders_smooth_representative hg
  have : g=h := bcfToDist_injective he
  rwa [this]

/-- Distributional and classical derivatives agree for the actual bounded smooth
representatives. A compact smooth multiplier makes every term Schwartz. -/
lemma bcf_derivative (g h : BoundedContinuousFunction E ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) (g : E → ℂ))
    (hh : ContDiff ℝ (⊤ : ℕ∞) (h : E → ℂ)) (a x : E)
    (he : ∂_{a} (bcfToDist g)=bcfToDist h) :
    fderiv ℝ (g : E → ℂ) x a=h x := by
  obtain ⟨q,_,hc,hq,_,h1⟩ := exists_contDiff_tsupport_subset (x := x) (n := (⊤ : ℕ∞))
    (s := Set.univ) Filter.univ_mem
  let c : E → ℂ := fun y => (q y : ℂ)
  have hcg : ContDiff ℝ (⊤ : ℕ∞) c := Complex.ofRealCLM.contDiff.comp hq
  have hcc : HasCompactSupport c := hc.comp_left Complex.ofReal_zero
  have hdg := smooth_derivative hcg a
  have hdc := compact_derivative hcc a
  let cg : 𝓢(E,ℂ) := (hcc.mul_right : HasCompactSupport (c*(g : E → ℂ))).toSchwartzMap (hcg.mul hg)
  let ch : 𝓢(E,ℂ) := (hcc.mul_right : HasCompactSupport (c*(h : E → ℂ))).toSchwartzMap (hcg.mul hh)
  let cdg : 𝓢(E,ℂ) := (hdc.mul_right : HasCompactSupport ((fun y => fderiv ℝ c y a)*(g : E → ℂ))).toSchwartzMap (hdg.mul hg)
  have hd := distribution_leibniz (hcc.hasTemperateGrowth hcg) a
    (hdc.hasTemperateGrowth hdg) (bcfToDist g)
  rw [he,bcfToDist_apply,bcfToDist_apply,smooth_Linfty_product hcg hcc g hg,
    smooth_Linfty_product hcg hcc h hh,smooth_Linfty_product hdg hdc g hg] at hd
  have hdist : ((∂_{a} cg : 𝓢(E,ℂ)) : 𝓢'(E,ℂ))=((cdg+ch : 𝓢(E,ℂ)) : 𝓢'(E,ℂ)) := by
    simpa only [← lineDerivOp_toTemperedDistributionCLM_eq,map_add] using hd
  have hv := congrArg (fun f : 𝓢(E,ℂ) => f x) (schwartz_dist_injective hdist)
  change fderiv ℝ (c*(g : E → ℂ)) x a=fderiv ℝ c x a*g x+c x*h x at hv
  rw [fderiv_mul (hcg.differentiable (by simp) x) (hg.differentiable (by simp) x)] at hv
  have hx : c x=1 := by simp only [c,h1,Complex.ofReal_one]
  simp only [add_apply,smul_apply,smul_eq_mul,hx,one_mul] at hv
  linear_combination hv
end ElasticityRegularity
namespace ElasticityRegularity

section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma bcf_family_spatial_smooth (g : P → BoundedContinuousFunction E ℂ)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (p : P) :
    ContDiff ℝ (⊤ : ℕ∞) (g p : E → ℂ) := by
  apply bcf_smooth_of_all_orders
  intro n
  obtain ⟨f,_,he⟩ := hu n
  dsimp only at he
  rw [← he p]
  exact sobolevInjection_mem _ _

lemma bcf_parameter_derivative (g : P → BoundedContinuousFunction E ℂ)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (a : P) :
    ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (fderiv ℝ g p a)) := by
  intro n
  let t : ℕ := n+Module.finrank ℝ E+1
  have ht : Module.finrank ℝ E < 2*(t : ℝ) := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
  obtain ⟨f,hf,he⟩ := hu t
  obtain ⟨T,hT⟩ := exists_bounded_continuous_embedding ht
  have hge : g=fun p => T (f p) := by
    funext p
    apply bcfToDist_injective
    exact (he p).symm.trans (hT _)
  have hd (p : P) : fderiv ℝ g p a=T (fderiv ℝ f p a) := by
    have h := (T.restrictScalars ℝ).hasFDerivAt.comp p (hf.differentiable (by simp) p).hasFDerivAt
    change HasFDerivAt (fun p => T (f p)) _ p at h
    rw [← hge] at h
    exact congrArg (fun L : P →L[ℝ] BoundedContinuousFunction E ℂ => L a) h.fderiv
  have h : SmoothSobolev (t : ℝ) (fun p => bcfToDist (fderiv ℝ g p a)) := by
    refine ⟨fun p => fderiv ℝ f p a,?_,fun p => ?_⟩
    · exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
    · dsimp only
      rw [hd]
      exact hT _
  exact h.mono (by dsimp [t]; norm_cast; omega)

/-- Actual spatial derivatives have smoothly parameter-dependent bounded
representatives in every Sobolev order. -/
lemma bcf_spatial_derivative (g : P → BoundedContinuousFunction E ℂ)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (a : E) :
    ∃ h : P → BoundedContinuousFunction E ℂ,
      ContDiff ℝ (⊤ : ℕ∞) h ∧
      (∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (h p))) ∧
      ∀ p x, fderiv ℝ (g p : E → ℂ) x a=h p x := by
  have hd (n : ℕ) : SmoothSobolev n (fun p => ∂_{a} (bcfToDist (g p))) := by
    have h := (hu (n+1)).derivative a
    convert h using 1; push_cast; ring
  let t : ℕ := Module.finrank ℝ E+1
  obtain ⟨h,hh,he⟩ := (hd t).continuous_representative (by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)])
  change ∀ p, ∂_{a} (bcfToDist (g p))=bcfToDist (h p) at he
  have hs (n : ℕ) : SmoothSobolev n (fun p => bcfToDist (h p)) := by
    simpa only [he] using hd n
  refine ⟨h,hh,hs,fun p x => ?_⟩
  exact bcf_derivative (g p) (h p) (bcf_family_spatial_smooth g hu p)
    (bcf_family_spatial_smooth h hs p) a x (he p)
end
open MeasureTheory TemperedDistribution Filter Topology
open scoped SchwartzMap ENNReal LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma bcf_joint_hasFDerivAt (g : P → BoundedContinuousFunction E ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) (q : P × E) :
    HasFDerivAt (fun q : P × E => g q.1 q.2)
      (((BoundedContinuousFunction.evalCLM ℝ q.2).comp (fderiv ℝ g q.1)).coprod
        (fderiv ℝ (g q.1 : E → ℂ) q.2)) q := by
  let A : P → E → P →L[ℝ] ℂ := fun p x =>
    (BoundedContinuousFunction.evalCLM ℝ x).comp (fderiv ℝ g p)
  let B : P → E → E →L[ℝ] ℂ := fun p x => fderiv ℝ (g p : E → ℂ) x
  have hA : Continuous (fun q : P × E => A q.1 q.2) := by
    apply continuous_clm_apply.mpr
    intro a
    have ht : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ g p a) :=
      (hg.fderiv_right (by simp)).clm_apply contDiff_const
    exact (ht.continuous.comp continuous_fst).eval continuous_snd
  have hB : Continuous (fun q : P × E => B q.1 q.2) := by
    apply continuous_clm_apply.mpr
    intro a
    obtain ⟨h,hh,_,he⟩ := bcf_spatial_derivative g hu a
    change Continuous (fun q : P × E => fderiv ℝ (g q.1 : E → ℂ) q.2 a)
    simp only [he]
    exact (hh.continuous.comp continuous_fst).eval continuous_snd
  apply (hasStrictFDerivAt_uncurry_coprod (f := fun p x => g p x)
    (f₁ := A) (f₂ := B) ?_ ?_ hA.continuousAt hB.continuousAt).hasFDerivAt
  · apply Filter.Eventually.of_forall
    intro v
    exact (BoundedContinuousFunction.evalCLM ℝ v.2).hasFDerivAt.comp v.1
      (hg.differentiable (by simp) v.1).hasFDerivAt
  · apply Filter.Eventually.of_forall
    intro v
    exact ((bcf_family_spatial_smooth g hu v.1).differentiable (by simp) v.2).hasFDerivAt

/-- Strong smoothness in every Sobolev order yields actual joint smoothness,
including mixed parameter and spatial derivatives. -/
theorem bcf_joint_smooth (g : P → BoundedContinuousFunction E ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ∀ n : ℕ, SmoothSobolev n (fun p => bcfToDist (g p))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => g q.1 q.2) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing g with
  | zero =>
    simp only [Nat.cast_zero,contDiff_zero]
    exact (hg.continuous.comp continuous_fst).eval continuous_snd
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv_apply]
    refine ⟨fun q => (bcf_joint_hasFDerivAt g hg hu q).differentiableAt,by simp,fun a => ?_⟩
    have hp : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ g p a.1) :=
      (hg.fderiv_right (by simp)).clm_apply contDiff_const
    have hpu := bcf_parameter_derivative g hu a.1
    obtain ⟨h,hh,hs,he⟩ := bcf_spatial_derivative g hu a.2
    have hp' := ih (fun p => fderiv ℝ g p a.1) hp hpu
    have hs' := ih h hh hs
    have hf (q : P × E) :
        fderiv ℝ (fun q : P × E => g q.1 q.2) q a=
          (fderiv ℝ g q.1 a.1) q.2+h q.1 q.2 := by
      rw [(bcf_joint_hasFDerivAt g hg hu q).fderiv]
      change (fderiv ℝ g q.1 a.1) q.2+fderiv ℝ (g q.1 : E → ℂ) q.2 a.2=_
      rw [he]
    simp only [hf]
    exact hp'.add hs'

theorem SmoothSobolev.joint_smooth_representative {u : P → 𝓢'(E,ℂ)}
    (hu : ∀ n : ℕ, SmoothSobolev n u) :
    ∃ g : P → BoundedContinuousFunction E ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => g q.1 q.2) ∧
      ∀ p, u p=bcfToDist (g p) := by
  let t : ℕ := Module.finrank ℝ E+1
  obtain ⟨g,hg,he⟩ := (hu t).continuous_representative
    (by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)])
  change ∀ p, u p=bcfToDist (g p) at he
  have hs (n : ℕ) : SmoothSobolev n (fun p => bcfToDist (g p)) := by
    rw [← show u=(fun p => bcfToDist (g p)) from funext he]
    exact hu n
  exact ⟨g,hg,bcf_joint_smooth g hg hs,he⟩
end ElasticityRegularity
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Joint smoothness on an arbitrary smaller fixed open set. The representative
is an actual Schwartz function in space for every parameter. -/
theorem SmoothLocalSobolev.joint_schwartz_representative {Ω Ω' : Set E}
    (u : P → 𝓢'(E,ℂ)) (hu : ∀ N : ℕ, SmoothLocalSobolev Ω N u)
    {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ f : P → 𝓢(E,ℂ), ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => f q.1 q.2) ∧
      ∀ p, LocalEqual Ω' (u p) (f p : 𝓢'(E,ℂ)) := by
  obtain ⟨v,_,hv,he⟩ := SmoothSobolev.joint_smooth_representative
    (fun N => hu N g hg hc hs)
  have hvs (p : P) : ContDiff ℝ (⊤ : ℕ∞) (v p : E → ℂ) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  let f : P → 𝓢(E,ℂ) := fun p =>
    (hc.mul_right : HasCompactSupport (g*(v p : E → ℂ))).toSchwartzMap (hg.mul (hvs p))
  refine ⟨f,?_,fun p => ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun q : P × E => g q.2*v q.1 q.2)
    exact (hg.comp contDiff_snd).mul hv
  · have he' := smooth_Linfty_product hg hc (v p) (hvs p)
    have hl := (LocalEqual.cutoff_one (u p) (hc.hasTemperateGrowth hg) h1).symm
    have hl' := (LocalEqual.cutoff_one (smulLeftCLM ℂ g (u p)) (hc.hasTemperateGrowth hg) h1).symm
    have h := hl.trans hl'
    rw [he p] at h
    exact h.trans (by intro φ _ _; exact congrArg (fun T : 𝓢'(E,ℂ) => T φ) he')
end ElasticityRegularity
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap ENNReal LineDeriv BigOperators
variable {n : Type*} [Fintype n]
open ElasticityRegularity

lemma dbar_schwartz (v : 𝓢(ℂ,ℂ)) :
    ElasticityPlanarDistribution.dbar (v : 𝓢'(ℂ,ℂ))=(schwartzDbar v : 𝓢'(ℂ,ℂ)) := by
  simp only [ElasticityPlanarDistribution.dbar,schwartzDbar,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]
  rw [map_add,map_smul]
lemma LocalEqual.dbar {Ω : Set ℂ} {u v : 𝓢'(ℂ,ℂ)} (h : LocalEqual Ω u v) :
    LocalEqual Ω (ElasticityPlanarDistribution.dbar u) (ElasticityPlanarDistribution.dbar v) :=
  (h.derivative 1).add ((h.derivative I).smul I)

lemma LocalEqual.coeff {Ω : Set ℂ} {u v : 𝓢'(ℂ,ℂ)} (h : LocalEqual Ω u v)
    {a : ℂ → ℂ} (ha : a.HasTemperateGrowth) :
    LocalEqual Ω (smulLeftCLM ℂ a u) (smulLeftCLM ℂ a v) := by
  intro φ hc hs
  change u (SchwartzMap.smulLeftCLM ℂ a φ)=v (SchwartzMap.smulLeftCLM ℂ a φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply ha,Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_left : HasCompactSupport (a*(φ : ℂ → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply ha,Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_right (f := a) (g := (φ : ℂ → ℂ))).trans hs

end ElasticityPlanar
section
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal BigOperators
namespace ElasticityRegularity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma SmoothSobolev.local_nat {N : ℕ} {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothSobolev N u) (Ω : Set E) : SmoothLocalSobolev Ω N u := by
  intro g hg hc _
  obtain ⟨u,hu,he⟩ := hu
  obtain ⟨L,hL⟩ := exists_bounded_nat_multiplier N hg hc
  exact ⟨fun p => L (u p),(L.restrictScalars ℝ).contDiff.comp hu,fun p => by rw [hL,he]⟩
lemma smoothSobolev_schwartz_const (N : ℕ) (f : 𝓢(E,ℂ)) :
    SmoothSobolev N (fun _ : P => (f : 𝓢'(E,ℂ))) := by
  obtain ⟨v,hv⟩ := (memSobolev_iff_range (N:ℝ) (f : 𝓢'(E,ℂ))).mp f.memSobolev
  exact ⟨fun _ => v,contDiff_const,fun _ => hv⟩
end ElasticityRegularity

end
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_schwartz_one_on_compact {K : Set E} (hK : IsCompact K) :
    ∃ g : 𝓢(E,ℂ), Set.EqOn g 1 K := by
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : E) := ⟨R,R+1,hR,by simp⟩
  have hc : HasCompactSupport (fun x : E => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => (b x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hc.toSchwartzMap hg,fun x hx => ?_⟩
  change (b x : ℂ)=1
  rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hKR x hx)]
  rfl
/-- The actual Schwartz representatives of joint smooth uniform-compact-support
families vary smoothly in every nonnegative Hilbert Sobolev norm. -/
theorem compact_smooth_sobolev {K : Set E} (hK : IsCompact K)
    (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉K → a (p,x)=0) :
    ∃ f : P → 𝓢(E,ℂ), (∀ p x, f p x=a (p,x)) ∧
      ∀ N : ℕ, SmoothSobolev N (fun p => (f p : 𝓢'(E,ℂ))) := by
  obtain ⟨g,hg⟩ := exists_schwartz_one_on_compact hK
  have hat (p : P) : (fun x => a (p,x)).HasTemperateGrowth :=
    (compact_slice hK a hs p).hasTemperateGrowth (ha.comp (contDiff_const.prodMk contDiff_id))
  let f : P → 𝓢(E,ℂ) := fun p => SchwartzMap.smulLeftCLM ℂ (fun x => a (p,x)) g
  refine ⟨f,fun p x => ?_,fun N => ?_⟩
  · change SchwartzMap.smulLeftCLM ℂ (fun x => a (p,x)) g x=_
    rw [SchwartzMap.smulLeftCLM_apply_apply (hat p),smul_eq_mul]
    by_cases hx : x∈K
    · rw [hg hx,Pi.one_apply,mul_one]
    · rw [hs p x hx,zero_mul]
  · have H := (smoothSobolev_schwartz_const (P := P) N g).variable_nat hK N a ha hs
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact (distribution_schwartz_product (hat p) g).symm
end ElasticityRegularity
section
open MeasureTheory TemperedDistribution Set Complex
open scoped SchwartzMap LineDeriv Laplacian BigOperators
namespace ElasticityRegularity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
lemma SmoothLocalSobolev.variable_nat {Ω S : Set E} (hS : IsCompact S)
    (N : ℕ) (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) {u : P → 𝓢'(E,ℂ)}
    (hu : SmoothLocalSobolev Ω N u) :
    SmoothLocalSobolev Ω N (fun p => smulLeftCLM ℂ (fun x => a (p,x)) (u p)) := by
  intro g hg hc hgs
  have H := (hu g hg hc hgs).variable_nat hS N a ha hs
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  have hat : (fun x => a (p,x)).HasTemperateGrowth :=
    (compact_slice hS a hs p).hasTemperateGrowth (ha.comp (contDiff_const.prodMk contDiff_id))
  rw [smulLeftCLM_smulLeftCLM_apply (hc.hasTemperateGrowth hg) hat,
    smulLeftCLM_smulLeftCLM_apply hat (hc.hasTemperateGrowth hg),mul_comm g]
end ElasticityRegularity
namespace ElasticityPlanarDistribution
open ElasticityRegularity
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable {n : Type*} [Fintype n]
/-- The full variable-coefficient planar weak equation has strong smooth
parameter regularity at every spatial order. -/
theorem smooth_variable_all_orders {Ω S : Set ℂ} (hS : IsCompact S)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉S → a i j (p,z)=0)
    (u f : P → n → Dist)
    (heq : ∀ p i, LocalEqual Ω (dbar (u p i))
      (f p i+∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j)))
    (hu : ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω 0 (fun p => u p i))
    (hf : ∀ N : ℕ, ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω N (fun p => f p i)) :
    ∀ N : ℕ, ∀ i, ElasticityRegularity.SmoothLocalSobolev Ω N (fun p => u p i) := by
  intro N
  induction N with
  | zero => simpa only [Nat.cast_zero] using hu
  | succ N ih =>
    rw [Nat.cast_add,Nat.cast_one]
    intro i
    apply (ih i).laplacian_gain
    have H := SmoothLocalSobolev.dhol ((hf N i).add
      (ElasticityRegularity.SmoothLocalSobolev.sum Finset.univ
        (fun j p => smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j))
        (fun j _ => (ih j).variable_nat hS N (a i j) (ha i j) (hs i j))))
    apply H.congr
    intro p
    simpa only [dhol_dbar] using LocalEqual.dhol (heq p i)
end ElasticityPlanarDistribution

end
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- Actual smooth classical solutions for arbitrary joint smooth compactly
supported planar coefficient and source families. -/
theorem exists_classical_variable {S Ω Ω' K : Set ℂ} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hac : ∀ i j p z, z∉K → a i j (p,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfc : ∀ i p z, z∉K → f i (p,z)=0)
    {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : P → n → 𝓢(ℂ,ℂ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
      ∀ p i, Set.EqOn (fun z => schwartzDbar (v p i) z+∑ j, a i j (p,z)*v p j z)
        (fun z => f i (p,z)) Ω' := by
  choose F hFe hF using fun i => compact_smooth_sobolev hK (f i) (hf i) (hfc i)
  have hF₀ (i : n) : ∃ w : P → PL2, ContDiff ℝ (⊤ : ℕ∞) w ∧
      ∀ p, (w p : 𝓢'(ℂ,ℂ))=(F i p : 𝓢'(ℂ,ℂ)) := by
    obtain ⟨w,hw,he⟩ := hF i 0
    simp only [Nat.cast_zero,sobolevInjection,neg_zero,besselPotential_zero,
      ContinuousLinearMap.id_comp,Lp.toTemperedDistributionCLM_apply] at he
    exact ⟨w,hw,he⟩
  choose W hW hWe using hF₀
  let rhs : P → Hilbert n := fun p => WithLp.toLp 2 (fun i => W i p)
  have hrhs : ContDiff ℝ (⊤ : ℕ∞) rhs :=
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      (contDiff_pi.mpr hW)
  obtain ⟨T,hT,heq⟩ := global_variable_inverse hS hΩS hK a ha hac
  let w : P → Hilbert n := fun p => T p (rhs p)
  let u : P → n → 𝓢'(ℂ,ℂ) := fun p i => (w p i : 𝓢'(ℂ,ℂ))
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := complex_clm_apply_smooth hT hrhs
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hac i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  have he (p : P) (i : n) : LocalEqual Ω
      (ElasticityPlanarDistribution.dbar (u p i)+
        ∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j)) (F i p : 𝓢'(ℂ,ℂ)) := by
    simpa only [planarOperator_apply,rhs,WithLp.ofLp_toLp,hWe] using heq p (rhs p) i
  have he' (p : P) (i : n) : LocalEqual Ω (ElasticityPlanarDistribution.dbar (u p i))
      ((F i p : 𝓢'(ℂ,ℂ))+∑ j, smulLeftCLM ℂ (fun z => -(a i j (p,z))) (u p j)) := by
    intro φ hφ hφs
    have h := he p i φ hφ hφs
    have hn (j : n) : smulLeftCLM ℂ (fun z => -(a i j (p,z))) (u p j)=
        -smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j) := by
      change smulLeftCLM ℂ (-(fun z => a i j (p,z))) (u p j)=_
      rw [smulLeftCLM_neg (hat p i j),neg_apply]
    simp only [hn,Finset.sum_neg_distrib,add_apply,neg_apply] at h ⊢
    linear_combination h
  have hu (i : n) : SmoothLocalSobolev Ω 0 (fun p => u p i) := by
    have hz : SmoothSobolev 0 (fun p => u p i) := by
      let L : Hilbert n →L[ℂ] PL2 := (ContinuousLinearMap.proj i).comp
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)).toContinuousLinearMap
      refine ⟨fun p => L (w p),(L.restrictScalars ℝ).contDiff.comp hw,fun p => ?_⟩
      simp only [sobolevInjection,neg_zero,besselPotential_zero,ContinuousLinearMap.id_comp,
        Lp.toTemperedDistributionCLM_apply]
      rfl
    simpa only [Nat.cast_zero] using (SmoothSobolev.local_nat (N := 0) (by simpa only [Nat.cast_zero] using hz) Ω)
  have hall := ElasticityPlanarDistribution.smooth_variable_all_orders hK
    (fun i j q => -(a i j q)) (fun i j => (ha i j).neg)
    (fun i j p z hz => by rw [hac i j p z hz,neg_zero])
    u (fun p i => (F i p : 𝓢'(ℂ,ℂ))) he' hu
    (fun N i => (hF i N).local_nat Ω)
  have hv (i : n) : ∃ v : P → 𝓢(ℂ,ℂ),
      ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 q.2) ∧
      ∀ p, LocalEqual Ω' (u p i) (v p : 𝓢'(ℂ,ℂ)) :=
    SmoothLocalSobolev.joint_schwartz_representative (fun p => u p i)
      (fun N => hall N i) hg hc hs h1
  choose v hv hv' using hv
  refine ⟨fun p i => v i p,hv,fun p i => ?_⟩
  let q : 𝓢(ℂ,ℂ) := schwartzDbar (v i p)+
    ∑ j, SchwartzMap.smulLeftCLM ℂ (fun z => a i j (p,z)) (v j p)
  have hq : (q : 𝓢'(ℂ,ℂ))=ElasticityPlanarDistribution.dbar (v i p : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (v j p : 𝓢'(ℂ,ℂ)) := by
    simp only [q,map_add,map_sum,← dbar_schwartz]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => (distribution_schwartz_product (hat p i j) (v j p)).symm)
  have hqq : LocalEqual Ω' (q : 𝓢'(ℂ,ℂ)) (F i p : 𝓢'(ℂ,ℂ)) := by
    rw [hq]
    have hh := (LocalEqual.dbar (hv' i p)).add (LocalEqual.sum Finset.univ
      (fun j _ => LocalEqual.coeff (hv' j p) (hat p i j)))
    exact fun φ hφ hφs => (hh φ hφ hφs).symm.trans (he p i φ hφ (hφs.trans hsub))
  intro z hz
  have hp := hqq.schwartz_eqOn hΩ' hz
  simpa only [q,add_apply,sum_apply,SchwartzMap.smulLeftCLM_apply_apply (hat p i _),smul_eq_mul,hFe] using hp
end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Homotopy
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Complex Module
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityPlanar
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
  [FiniteDimensional ℂ R]
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [CompleteSpace R] [DecidableEq n] in
lemma coord_linear_apply (q : Basis n ℂ R) (L : R →ₗ[ℂ] R) (x : R) (i : n) :
    coord q i (L x)=∑ j, coord q i (L (q j))*coord q j x := by
  have h : L x=∑ j, (q.equivFun x j) • L (q j) := by
    calc
      L x=L (∑ j, q.equivFun x j • q j) := congrArg L (q.sum_equivFun x).symm
      _=∑ j, q.equivFun x j • L (q j) := by simp only [map_sum,map_smul]
  rw [h,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,smul_eq_mul,mul_comm]
  rfl

omit [CompleteSpace R] [DecidableEq n] in
lemma coord_dbar (q : Basis n ℂ R) (f : ℂ → R) (hf : Differentiable ℝ f) (z : ℂ) (i : n) :
    coord q i (classicalDbar f z)=
      fderiv ℝ (fun z => coord q i (f z)) z 1+I*fderiv ℝ (fun z => coord q i (f z)) z I := by
  have h := ((coord q i).restrictScalars ℝ).hasFDerivAt.comp z (hf z).hasFDerivAt
  change HasFDerivAt (fun z => coord q i (f z)) _ z at h
  rw [h.fderiv]
  simp only [classicalDbar,map_add,map_smul,ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  rfl

end ElasticityPlanar

end
end
section
noncomputable section
open Set Complex Module
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityPlanar
open ElasticityRegularity
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
  [FiniteDimensional ℂ R]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
omit [CompleteSpace R] [DecidableEq n] in
/-- The commutator homotopy equation in a genuine finite-dimensional complex
Banach algebra, with actual joint smooth representatives. -/
theorem exists_algebra_variable_homotopy_oai {S Ω Ω' K : Set ℂ} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (hK : IsCompact K) (q : Basis n ℂ R) (A : P × ℂ → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAc : ∀ p z, z∉K → A (p,z)=0) {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ B : (ℝ × P) × ℂ → R, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ s p z, z∈Ω' → classicalDbar (fun z => B ((s,p),z)) z=
        A (p,z)+s • (A (p,z)*B ((s,p),z)-B ((s,p),z)*A (p,z)) := by
  let A' : (ℝ × P) × ℂ → R := fun q => A (q.1.2,q.2)
  have hA' : ContDiff ℝ (⊤ : ℕ∞) A' :=
    hA.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  let a : n → n → (ℝ × P) × ℂ → ℂ := fun i j w =>
    (w.1.1 : ℂ)*coord q i (q j*A' w-A' w*q j)
  have ha (i j : n) : ContDiff ℝ (⊤ : ℕ∞) (a i j) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_fst)).mul
      (((coord q i).restrictScalars ℝ).contDiff.comp
        ((contDiff_const.mul hA').sub (hA'.mul contDiff_const)))
  have hac (i j : n) (w : ℝ × P) (z : ℂ) (hz : z∉K) : a i j (w,z)=0 := by
    simp only [a,A',hAc w.2 z hz,mul_zero,zero_mul,sub_self,map_zero]
  let f : n → (ℝ × P) × ℂ → ℂ := fun i w => coord q i (A' w)
  have hf (i : n) : ContDiff ℝ (⊤ : ℕ∞) (f i) :=
    ((coord q i).restrictScalars ℝ).contDiff.comp hA'
  have hfc (i : n) (w : ℝ × P) (z : ℂ) (hz : z∉K) : f i (w,z)=0 := by
    simp only [f,A',hAc w.2 z hz,map_zero]
  obtain ⟨v,hv,he⟩ := exists_classical_variable hS hΩS hΩ' hsub hK a ha hac f hf hfc hg hc hs h1
  let B : (ℝ × P) × ℂ → R := fun p => (coords q).symm (fun i => v p.1 i p.2)
  have hL : ContDiff ℝ (⊤ : ℕ∞) (coords q).symm := by
    let L : (n → ℂ) →L[ℝ] R := (coords q).symm.toContinuousLinearMap.restrictScalars ℝ
    exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := n → ℂ) (F := R) L
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hL.comp (contDiff_pi.mpr hv)
  have hev (w : ℝ × P) (i : n) : (fun z => coord q i (B (w,z)))=fun z => v w i z := by
    funext z
    change (coords q) ((coords q).symm (fun i => v w i z)) i=v w i z
    rw [ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨B,hB,fun s p z hz => ?_⟩
  apply (coords q).injective
  ext i
  change coord q i (classicalDbar (fun z => B ((s,p),z)) z)=
    coord q i (A (p,z)+s • (A (p,z)*B ((s,p),z)-B ((s,p),z)*A (p,z)))
  have hBs : Differentiable ℝ (fun z => B ((s,p),z)) :=
    (hB.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hD := coord_dbar q (fun z => B ((s,p),z)) hBs z i
  rw [hev] at hD
  have he' := he (s,p) i hz
  change schwartzDbar (v (s,p) i) z+∑ j, (s:ℂ)*coord q i (q j*A (p,z)-A (p,z)*q j)*v (s,p) j z=coord q i (A (p,z)) at he'
  simp only [schwartzDbar,add_apply,smul_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,smul_eq_mul] at he'
  rw [← hD] at he'
  have hcomm : coord q i (B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z))=∑ j, coord q i (q j*A (p,z)-A (p,z)*q j)*v (s,p) j z := by
    let L : R →ₗ[ℂ] R := ((ContinuousLinearMap.mul ℂ R).flip (A (p,z))-
      ContinuousLinearMap.mul ℂ R (A (p,z))).toLinearMap
    have hh := coord_linear_apply q L (B ((s,p),z)) i
    change coord q i (B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z))=
      ∑ j, coord q i (q j*A (p,z)-A (p,z)*q j)*coord q j (B ((s,p),z)) at hh
    simpa only [congrFun (hev (s,p) _) z] using hh
  have hs' : coord q i (A (p,z)+s • (A (p,z)*B ((s,p),z)-B ((s,p),z)*A (p,z)))=
      coord q i (A (p,z))-(s:ℂ)*(∑ j, coord q i (q j*A (p,z)-A (p,z)*q j)*v (s,p) j z) := by
    rw [map_add]
    have hneg : A (p,z)*B ((s,p),z)-B ((s,p),z)*A (p,z)=-(B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z)) := by abel
    rw [hneg]
    have hl := ((coord q i).restrictScalars ℝ).map_smul s (-(B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z)))
    change coord q i (s • (-(B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z))))=s • coord q i (-(B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z))) at hl
    rw [hl,map_neg,hcomm]
    simp [Complex.real_smul,sub_eq_add_neg]
  rw [hs']
  change _+∑ j, (s:ℂ)*coord q i (q j*A (p,z)-A (p,z)*q j)*v (s,p) j z=coord q i (A (p,z)) at he'
  rw [Finset.mul_sum]
  simp_rw [mul_assoc] at he' ⊢
  linear_combination he'
end ElasticityPlanar

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElasticityPlanar.exists_algebra_variable_homotopy_oai.{u_1, u_2, u_3} := @OAI.ElasticityPlanar.exists_algebra_variable_homotopy_oai.{u_1, u_2, u_3}
