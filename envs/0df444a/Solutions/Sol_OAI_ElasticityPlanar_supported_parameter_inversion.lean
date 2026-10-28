-- Prove2me | solution 1 for OAI.ElasticityPlanar.supported_parameter_inversion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:24:16.674588+00:00
-- url     : https://prove2.me/submissions/bd5f78ba-fe08-4130-b367-d757cce7f025

import Mathlib
import Definitions.Def_OAIQ6El005
import Theorems.Thm_OAI_ElasticityPlanar_global_supported_of_dense
import Theorems.Thm_OAI_ElasticityPlanar_supported_smooth_test_family

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
lemma sub (h : LocalEqual Ω u v) (h' : LocalEqual Ω u' v') : LocalEqual Ω (u-u') (v-v') := by
  intro φ hc hs
  simp only [sub_apply,h φ hc hs,h' φ hc hs]
lemma smul (h : LocalEqual Ω u v) (c : ℂ) : LocalEqual Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
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
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

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
lemma toSchwartz_mul (a : ℂ → ℂ) (ha : a.HasTemperateGrowth) (φ : Test) :
    toSchwartz (mulSmooth a ha.1 φ)=SchwartzMap.smulLeftCLM ℂ a (toSchwartz φ) := by
  ext z
  simp only [toSchwartz_apply,SchwartzMap.smulLeftCLM_apply_apply ha,smul_eq_mul]
  rfl
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

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Supported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/- The exact extension proofs are reused from their canonical original module. -/

namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

open ElasticityRegularity
variable {n : Type*} [Fintype n]
lemma L2_distribution (u : Test) : (L2 u : 𝓢'(ℂ,ℂ))=(toSchwartz u : 𝓢'(ℂ,ℂ)) :=
  Lp.toTemperedDistribution_toLp_eq (toSchwartz u)
lemma planarOperator_test (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u : n → Test) (i : n) :
    planarOperator a i (embed u)=entryInjection i (embed (transport a (fun i j => (ha i j).1) u)) := by
  simp only [planarOperator_apply,entryInjection_apply,embed_apply,L2_distribution,dbar_schwartz]
  have ht : toSchwartz (transport a (fun i j => (ha i j).1) u i)=
      schwartzDbar (toSchwartz (u i))+∑ j, SchwartzMap.smulLeftCLM ℂ (a i j) (toSchwartz (u j)) := by
    simp only [transport,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_smul,map_sum,
      toSchwartz_d,schwartzDbar]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => toSchwartz_mul (a i j) (ha i j) (u j))
  rw [ht,map_add,map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => distribution_schwartz_product (ha i j) (toSchwartz (u j)))

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal BigOperators Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
lemma compact_smooth_source {K : Set ℂ} (hK : IsCompact K)
    (f : n → P × ℂ → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hs : ∀ i p z, z∉K → f i (p,z)=0) :
    ∃ (F : P → n → 𝓢(ℂ,ℂ)) (w : P → Hilbert n),
      (∀ p i z, F p i z=f i (p,z)) ∧
      (∀ N : ℕ, ∀ i, SmoothSobolev N (fun p => (F p i : 𝓢'(ℂ,ℂ)))) ∧
      ContDiff ℝ (⊤ : ℕ∞) w ∧ ∀ p i, entryInjection i (w p)=(F p i : 𝓢'(ℂ,ℂ)) := by
  choose F hFe hF using fun i => compact_smooth_sobolev hK (f i) (hf i) (hs i)
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
  exact ⟨fun p i => F i p,rhs,(fun p i z => hFe i p z),(fun N i => hF i N),hrhs,
    fun p i => hWe i p⟩

end ElasticityPlanar
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
lemma smooth_operator_all_orders {K : Set ℂ} (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
    (w : P → Hilbert n) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (F : P → n → 𝓢(ℂ,ℂ))
    (hF : ∀ N : ℕ, ∀ i, SmoothSobolev N (fun p => (F p i : 𝓢'(ℂ,ℂ))))
    (he : ∀ p i, planarOperator (fun i j z => a i j (p,z)) i (w p)=(F p i : 𝓢'(ℂ,ℂ))) :
    ∀ N : ℕ, ∀ i, SmoothLocalSobolev univ N (fun p => entryInjection i (w p)) := by
  let u : P → n → 𝓢'(ℂ,ℂ) := fun p i => entryInjection i (w p)
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  have he' (p : P) (i : n) : LocalEqual univ (ElasticityPlanarDistribution.dbar (u p i))
      ((F p i : 𝓢'(ℂ,ℂ))+∑ j, smulLeftCLM ℂ (fun z => -(a i j (p,z))) (u p j)) := by
    intro φ _ _
    have h := congrArg (fun v : 𝓢'(ℂ,ℂ) => v φ) (he p i)
    rw [planarOperator_apply] at h
    have hn (j : n) : smulLeftCLM ℂ (fun z => -(a i j (p,z))) (u p j)=
        -smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j) := by
      change smulLeftCLM ℂ (-(fun z => a i j (p,z))) (u p j)=_
      rw [smulLeftCLM_neg (hat p i j),neg_apply]
    simp only [hn,Finset.sum_neg_distrib,add_apply,neg_apply] at h ⊢
    change ElasticityPlanarDistribution.dbar (u p i) φ+
      (∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (u p j)) φ=(F p i : 𝓢'(ℂ,ℂ)) φ at h
    linear_combination h
  have hu (i : n) : SmoothLocalSobolev univ 0 (fun p => u p i) := by
    have hz : SmoothSobolev 0 (fun p => u p i) := by
      let L : Hilbert n →L[ℂ] PL2 := (ContinuousLinearMap.proj i).comp
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)).toContinuousLinearMap
      refine ⟨fun p => L (w p),(L.restrictScalars ℝ).contDiff.comp hw,fun p => ?_⟩
      simp only [sobolevInjection,neg_zero,besselPotential_zero,ContinuousLinearMap.id_comp,
        Lp.toTemperedDistributionCLM_apply]
      rfl
    simpa only [Nat.cast_zero] using (SmoothSobolev.local_nat (N := 0) (by simpa only [Nat.cast_zero] using hz) univ)
  exact ElasticityPlanarDistribution.smooth_variable_all_orders hK
    (fun i j q => -(a i j q)) (fun i j => (ha i j).neg)
    (fun i j p z hz => by rw [hs i j p z hz,neg_zero])
    u (fun p i => (F p i : 𝓢'(ℂ,ℂ))) he' hu (fun N i => (hF N i).local_nat univ)

/-- The dense-parameter assertion uses genuine weak solutions, not an assumed
smooth selection. Compact support and the elliptic estimate construct the
unique jointly smooth selection. -/
theorem supported_parameter_inversion_oai {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i p z, z∉K → f i (p,z)=0)
    {D : Set P} (hD : Dense D)
    (hex : ∀ p∈D, ∃ w : Hilbert n, ∀ i,
      planarOperator (fun i j z => a i j (p,z)) i w=
        (toSchwartz ⟨fun z => f i (p,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
          compact_slice hK (f i) (hfs i) p⟩⟩ : 𝓢'(ℂ,ℂ)) ∧
      LocalEqual Sᶜ (entryInjection i w) 0) :
    ∃ v : P → n → Test,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
      (∀ p i, tsupport (v p i : ℂ → ℂ)⊆S) ∧
      ∀ p i z, schwartzDbar (toSchwartz (v p i)) z+
        ∑ j, a i j (p,z)*v p j z=f i (p,z) := by
  obtain ⟨F,w,hFe,hF,hw,hwe⟩ := compact_smooth_source hK f hf hfs
  have hFt (p : P) (i : n) : F p i=toSchwartz
      ⟨fun z => f i (p,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
          compact_slice hK (f i) (hfs i) p⟩⟩ := by
    ext z
    exact hFe p i z
  have hex' : ∀ p∈D, ∃ u : Hilbert n, ∀ i,
      planarOperator (fun i j z => a i j (p,z)) i u=entryInjection i (w p) ∧
        LocalEqual Sᶜ (entryInjection i u) 0 := by
    intro p hp
    obtain ⟨u,hu⟩ := hex p hp
    exact ⟨u,fun i => ⟨by rw [hwe,hFt]; exact (hu i).1,(hu i).2⟩⟩
  obtain ⟨u,hu,he⟩ := global_supported_of_dense hS hK a ha hs F w hw hwe hD hex'
  have he' (p : P) (i : n) : planarOperator (fun i j z => a i j (p,z)) i (u p)=(F p i : 𝓢'(ℂ,ℂ)) :=
    (he p i).1.trans (hwe p i)
  have hall := smooth_operator_all_orders hK a ha hs u hu F hF he'
  choose v hv hve using fun i => supported_smooth_test_family hS (fun p => u p i)
    (fun N => hall N i) (fun p => (he p i).2)
  have hvu (p : P) : embed (fun i => v i p)=u p := PiLp.ext (fun i => (hve i p).1)
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  refine ⟨fun p i => v i p,hv,(fun p i => (hve i p).2),fun p i z => ?_⟩
  let q : Test := transport (fun i j z => a i j (p,z)) (fun i j => (hat p i j).1) (fun i => v i p) i
  have hq : (toSchwartz q : 𝓢'(ℂ,ℂ))=(F p i : 𝓢'(ℂ,ℂ)) := by
    rw [← L2_distribution]
    change entryInjection i (embed (transport (fun i j z => a i j (p,z))
      (fun i j => (hat p i j).1) (fun i => v i p)))=_
    rw [← planarOperator_test _ (hat p),hvu,he']
  have hp := (show LocalEqual univ (toSchwartz q : 𝓢'(ℂ,ℂ)) (F p i : 𝓢'(ℂ,ℂ)) from
    fun φ _ _ => congrArg (fun t : 𝓢'(ℂ,ℂ) => t φ) hq).schwartz_eqOn isOpen_univ (mem_univ z)
  have hqv : toSchwartz q=schwartzDbar (toSchwartz (v i p))+
      ∑ j, SchwartzMap.smulLeftCLM ℂ (fun z => a i j (p,z)) (toSchwartz (v j p)) := by
    simp only [q,transport,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_smul,map_sum,
      toSchwartz_d,schwartzDbar]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => toSchwartz_mul _ (hat p i j) (v j p))
  rw [hqv] at hp
  simpa only [add_apply,sum_apply,SchwartzMap.smulLeftCLM_apply_apply (hat p i _),
    smul_eq_mul,toSchwartz_apply,hFe] using hp

end ElasticityPlanar

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElasticityPlanar.supported_parameter_inversion_oai.{u_1, u_2} := @OAI.ElasticityPlanar.supported_parameter_inversion_oai.{u_1, u_2}
