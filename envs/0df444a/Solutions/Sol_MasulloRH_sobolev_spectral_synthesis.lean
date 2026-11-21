-- Prove2me | solution 1 for MasulloRH.sobolev_spectral_synthesis
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:12:43.394897+00:00
-- url     : https://prove2.me/submissions/dc57fc55-6256-4b29-aad2-0b8cb613c720

import Mathlib
import Theorems.Thm_MasulloGRH_sobolev_oscillatory_jet_memLp_iff
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic
import Theorems.Thm_MasulloRH_compact_window_theta_annihilator

namespace SobolevSynthesisProof
section
open MeasureTheory Set Filter Bornology
open scoped Polynomial FourierTransform SchwartzMap
namespace MasulloRH.JetAdmissibility
noncomputable section

def weight (p x : ℝ) : ℂ := ((1+x^2)^(-p/2) : ℝ)
def phase (ν x : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * (ν*x)) * Complex.I)
def mode (p ν : ℝ) (P : ℂ[X]) (x : ℝ) : ℂ := weight p x * (P.eval (x:ℂ) * phase ν x)

theorem norm_phase (ν x : ℝ) : ‖phase ν x‖ = 1 := by simp [phase, Complex.norm_exp]

@[fun_prop] theorem continuous_weight (p : ℝ) : Continuous (weight p) := by
  apply Complex.continuous_ofReal.comp
  exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))

theorem weight_ne (p x : ℝ) : weight p x ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne'

@[fun_prop] theorem continuous_phase (ν : ℝ) : Continuous (phase ν) := by unfold phase; fun_prop
@[fun_prop] theorem continuous_mode (p ν : ℝ) (P : ℂ[X]) : Continuous (mode p ν P) := by
  exact (continuous_weight p).mul ((P.continuous.comp Complex.continuous_ofReal).mul (continuous_phase ν))

theorem monomial_memLp_iff (p ν : ℝ) (hp : 1/2<p) (r : ℕ) :
    MemLp (mode p ν (Polynomial.X^r)) 2 volume ↔ (r:ℝ)+1/2<p := by
  have h := MasulloGRH.sobolev_oscillatory_jet_memLp_iff r (-2*Real.pi*ν) (2*p) (by linarith)
  rw [memLp_map_measure_iff (by fun_prop) Real.continuous_exp.aemeasurable] at h
  have he : -(2*p)/4 = -p/2 := by ring
  have hμ : (fun t : ℝ => ((1+(Real.log t)^2)^(-(2*p)/4) : ℝ) •
      (Complex.exp (↑((-2*Real.pi*ν)*Real.log t) * Complex.I) * (Real.log t:ℂ)^r)) ∘ Real.exp =
      mode p ν (Polynomial.X^r) := by
    funext x
    simp only [Function.comp_apply, Real.log_exp, he, mode, weight, phase, Polynomial.eval_pow,
      Polynomial.eval_X, Complex.real_smul, mul_assoc]
    ring
  rw [hμ] at h
  exact h.trans (by constructor <;> intro hh <;> linarith)

private theorem polynomial_growth {P Q : ℂ[X]} (hdeg : Q.degree ≤ P.degree) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : ℂ, ‖Q.eval z‖ ≤ C * (1+‖P.eval z‖) := by
  obtain ⟨c,hc,h⟩ := (Polynomial.isBigO_cobounded_of_degree_le hdeg).exists_pos
  have he := h.bound
  rw [Metric.cobounded_eq_cocompact] at he
  obtain ⟨K,hK,hKC⟩ := mem_cocompact.mp he
  obtain ⟨b,hb⟩ := hK.exists_bound_of_continuousOn Q.continuous.continuousOn
  let C := max b c
  have hC : 0 ≤ C := hc.le.trans (le_max_right _ _)
  refine ⟨C,hC,fun z => ?_⟩
  by_cases hz : z ∈ K
  · exact (hb z hz).trans ((le_max_left _ _).trans (le_mul_of_one_le_right hC (by linarith [norm_nonneg (P.eval z)])))
  · exact (hKC hz).trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (by linarith) hC))

theorem polynomial_mode_memLp_iff (p ν : ℝ) (hp : 1/2<p) (P : ℂ[X]) :
    MemLp (mode p ν P) 2 volume ↔ ∀ r : ℕ, P.coeff r ≠ 0 → (r:ℝ)+1/2 < p := by
  constructor
  · intro h r hr
    have h0 : P ≠ 0 := by intro hP; simp [hP] at hr
    have hdeg : (Polynomial.X^r : ℂ[X]).degree ≤ P.degree := by
      rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree h0]
      exact_mod_cast Polynomial.le_natDegree_of_ne_zero hr
    obtain ⟨C,hC,hbound⟩ := polynomial_growth hdeg
    have hw := (monomial_memLp_iff p ν hp 0).mpr (by simpa using hp)
    apply (monomial_memLp_iff p ν hp r).mp
    apply (hw.norm.add h.norm).of_le_mul (c:=C) (continuous_mode p ν _).aestronglyMeasurable
    apply ae_of_all
    intro x
    have hx := hbound (x:ℂ)
    simp only [mode, norm_mul, norm_phase, mul_one, Polynomial.eval_pow, Polynomial.eval_X, pow_zero,
      Polynomial.eval_one, norm_one, Pi.add_apply] at hx ⊢
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ ‖weight p x‖ * (C * (1+‖P.eval (x:ℂ)‖)) := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = _ := by ring
  · intro hr
    have hs := memLp_finsetSum P.support (fun r h => ((monomial_memLp_iff p ν hp r).mpr
      (hr _ (Polynomial.mem_support_iff.mp h))).const_mul (P.coeff r))
    refine hs.ae_eq (ae_of_all _ fun x => ?_)
    simp only [mode, Polynomial.eval_eq_sum (p:=P), Polynomial.sum_def, Polynomial.eval_pow, Polynomial.eval_X,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
end
end MasulloRH.JetAdmissibility
end

section
open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform Polynomial ContDiff
namespace MasulloRH.JetAdmissibility
noncomputable section

private theorem kernel_moment_eq_jet (b : 𝓢(ℝ,ℂ)) (r : ℕ) (ξ : ℝ) :
    iteratedDeriv r b ξ = ((-2:ℂ) * Real.pi * Complex.I)^r *
      ∫ t : ℝ, (t:ℂ)^r * Complex.exp ((↑(-2 * Real.pi * (ξ*t)) : ℂ) * Complex.I) *
        (𝓕⁻ (b : ℝ → ℂ)) t := by
  let f : 𝓢(ℝ,ℂ) := 𝓕⁻ b
  have hi (a : ℕ) : Integrable (fun t : ℝ => t^a • f t) := by
    apply (f.integrable_pow_mul volume a).mono' (by fun_prop)
    exact Eventually.of_forall fun t => by simp
  have h := congrFun (Real.iteratedDeriv_fourier (f:=(f:ℝ→ℂ)) (N:=(r:ℕ∞))
    (fun a _ => hi a) (le_rfl : (r:ℕ∞) ≤ r)) ξ
  have he : 𝓕 (f:ℝ→ℂ) = (b:ℝ→ℂ) := by
    rw [← SchwartzMap.fourier_coe]
    simp [f]
  rw [he, Real.fourier_eq'] at h
  rw [← integral_const_mul]
  change iteratedDeriv r b ξ = ∫ t : ℝ, _ * (_ * _ * ((𝓕⁻ (b:ℝ→ℂ)) t))
  apply h.trans
  apply integral_congr_ae
  refine Eventually.of_forall fun t => ?_
  simp only [Real.inner_apply, smul_eq_mul, ← SchwartzMap.fourierInv_coe]
  dsimp [f]
  rw [mul_pow]
  rw [mul_comm t ξ]
  ring

abbrev JetL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Conversion from derivatives of the frequency test to physical-space monomials. -/
def momentFactor : ℂ := (-2:ℂ)*Real.pi*Complex.I

theorem momentFactor_ne : momentFactor ≠ 0 := by
  unfold momentFactor
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

def physicalPolynomial (s : Finset ℕ) (c : ℕ → ℂ) : ℂ[X] :=
  ∑ r ∈ s, Polynomial.monomial r (c r * momentFactor^r)

theorem physicalPolynomial_coeff (s : Finset ℕ) (c : ℕ → ℂ) (r : ℕ) :
    (physicalPolynomial s c).coeff r = if r ∈ s then c r * momentFactor^r else 0 := by
  classical
  simp [physicalPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, eq_comm]

theorem finite_jet_pairing (s : Finset ℕ) (c : ℕ→ℂ) (ν : ℝ) (f : 𝓢(ℝ,ℂ)) :
    ∫ x : ℝ, (physicalPolynomial s c).eval (x:ℂ) * phase ν x * (𝓕⁻ (f : ℝ→ℂ)) x =
      ∑ r ∈ s, c r * iteratedDeriv r f ν := by
  classical
  let K : 𝓢(ℝ,ℂ) := 𝓕⁻ f
  have hi (r : ℕ) : Integrable fun x : ℝ => ((x:ℂ)^r * phase ν x) * (𝓕⁻ (f:ℝ→ℂ)) x := by
    rw [← SchwartzMap.fourierInv_coe]
    apply (K.integrable_pow_mul volume r).mono' (by fun_prop)
    exact ae_of_all _ fun x => by simp [K, norm_phase]
  have hf (x : ℝ) : (physicalPolynomial s c).eval (x:ℂ) * phase ν x * (𝓕⁻ (f : ℝ→ℂ)) x =
      ∑ r ∈ s, (c r * momentFactor^r) * (((x:ℂ)^r * phase ν x) * (𝓕⁻ (f : ℝ→ℂ)) x) := by
    simp only [physicalPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hf]
  rw [integral_finsetSum _ (fun r _ => (hi r).const_mul (c r * momentFactor^r))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_const_mul, kernel_moment_eq_jet]
  simp only [momentFactor, phase, mul_assoc]


theorem integral_of_mode (p ν : ℝ) (r : ℕ) (u : JetL2)
    (hu : (u : ℝ→ℂ) =ᵐ[volume] mode p ν (Polynomial.X^r)) (f : 𝓢(ℝ,ℂ)) :
    ∫ x : ℝ, (u x / weight p x) * (𝓕⁻ (f:ℝ→ℂ)) x =
      iteratedDeriv r f ν / momentFactor^r := by
  apply (eq_div_iff (pow_ne_zero _ momentFactor_ne)).mpr
  rw [kernel_moment_eq_jet, mul_comm _ (momentFactor^r)]
  apply congrArg (momentFactor^r * ·)
  apply integral_congr_ae
  filter_upwards [hu] with x hx
  rw [hx, mode, Polynomial.eval_pow, Polynomial.eval_X]
  field_simp [weight_ne p x]
  unfold phase
  ring_nf

/-- Equality as Fourier distributions determines the weighted function almost everywhere. -/
theorem ae_eq_mode_of_finite_jets (p ν : ℝ) (u : JetL2) (s : Finset ℕ) (c : ℕ→ℂ)
    (hD : ∀ f : 𝓢(ℝ,ℂ), ∫ x : ℝ, (u x / weight p x) * (𝓕⁻ (f:ℝ→ℂ)) x =
      ∑ r ∈ s, c r * iteratedDeriv r f ν) :
    (u : ℝ→ℂ) =ᵐ[volume] mode p ν (physicalPolynomial s c) := by
  have hleft : LocallyIntegrable (fun x : ℝ => u x / weight p x) volume := by
    simp only [div_eq_mul_inv]
    exact LocallyIntegrable.mul_continuous ((continuous_weight p).inv₀ (weight_ne p))
      ((Lp.memLp u).locallyIntegrable (by norm_num))
  have hright : LocallyIntegrable (fun x : ℝ => (physicalPolynomial s c).eval (x:ℂ) * phase ν x) volume :=
    (((physicalPolynomial s c).continuous.comp Complex.continuous_ofReal).mul (continuous_phase ν)).locallyIntegrable
  have heq := ae_eq_of_integral_contDiff_smul_eq hleft hright (by
    intro g hg hgc
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    let G := hg₁.toSchwartzMap hg₂
    let f := (𝓕 G : 𝓢(ℝ,ℂ))
    have hf : 𝓕⁻ (f : ℝ→ℂ) = fun x => (g x : ℂ) := by
      rw [← SchwartzMap.fourierInv_coe]
      change (↑(𝓕⁻ (𝓕 G) : 𝓢(ℝ,ℂ)) : ℝ → ℂ) = _
      simp [G]
      rfl
    have h := (hD f).trans (finite_jet_pairing s c ν f).symm
    rw [hf] at h
    simpa only [Complex.real_smul, mul_comm, mul_assoc, mul_left_comm] using h)
  filter_upwards [heq] with x hx
  exact (div_eq_iff (weight_ne p x)).mp hx |>.trans (by unfold mode; ring)

theorem jet_coefficients_admissible (p ν : ℝ) (hp : 1/2<p) (u : JetL2) (s : Finset ℕ) (c : ℕ→ℂ)
    (hD : ∀ f : 𝓢(ℝ,ℂ), ∫ x : ℝ, (u x / weight p x) * (𝓕⁻ (f:ℝ→ℂ)) x =
      ∑ r ∈ s, c r * iteratedDeriv r f ν) :
    ∀ r ∈ s, c r ≠ 0 → (r:ℝ)+1/2<p := by
  have h := (Lp.memLp u).ae_eq (ae_eq_mode_of_finite_jets p ν u s c hD)
  obtain hall := (polynomial_mode_memLp_iff p ν hp _).mp h
  intro r hr hc
  exact hall r (by simpa [physicalPolynomial_coeff, hr, momentFactor_ne] using hc)
end
end MasulloRH.JetAdmissibility
end

section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Polynomial
namespace MasulloRH.JetAdmissibility
noncomputable section

/-- A one-point distribution of finite order represented by a weighted L² vector
belongs to the algebraic span of the allowed modes at that frequency. -/
theorem mem_span_of_finite_jets (p ν : ℝ) (hp : 1/2<p) (u : JetL2) (s : Finset ℕ) (c : ℕ→ℂ)
    (hD : ∀ f : 𝓢(ℝ,ℂ), ∫ x : ℝ, (u x / weight p x) * (𝓕⁻ (f:ℝ→ℂ)) x =
      ∑ r ∈ s, c r * iteratedDeriv r f ν) :
    u ∈ Submodule.span ℂ {v : JetL2 | ∃ r ∈ s, (r:ℝ)+1/2<p ∧
      (v : ℝ→ℂ) =ᵐ[volume] mode p ν (Polynomial.X^r)} := by
  classical
  let P := physicalPolynomial s c
  have hu : (u : ℝ→ℂ) =ᵐ[volume] mode p ν P := ae_eq_mode_of_finite_jets p ν u s c hD
  have ha := (polynomial_mode_memLp_iff p ν hp _).mp ((Lp.memLp u).ae_eq hu)
  have hr (r : P.support) := ha r (Polynomial.mem_support_iff.mp r.property)
  have hf (r : P.support) := (monomial_memLp_iff p ν hp r).mpr (hr r)
  let v (r : P.support) : JetL2 := (hf r).toLp _
  have hmem (r : P.support) : (r:ℕ) ∈ s := by
    by_contra h
    exact Polynomial.mem_support_iff.mp r.property (by simp [P,physicalPolynomial_coeff,h])
  have hz : ∑ r : P.support, P.coeff r • v r = u := by
    apply Lp.ext
    have he (r : P.support) : (P.coeff r • v r : JetL2) =ᵐ[volume]
        (fun x : ℝ => P.coeff r * mode p ν (Polynomial.X^r.val) x) := by
      filter_upwards [Lp.coeFn_smul (P.coeff r) (v r), (hf r).coeFn_toLp] with x hs hv
      exact hs.trans (congrArg (P.coeff r * ·) hv)
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun r : P.support => P.coeff r • v r),
      ae_all_iff.mpr he, hu] with x hs hh hx
    rw [hs,hx]
    simp_rw [hh]
    rw [Finset.sum_coe_sort P.support (fun r => P.coeff r * mode p ν (Polynomial.X^r) x)]
    simp only [mode, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_eq_sum (p:=P),
      Polynomial.sum_def, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [← hz]
  apply Submodule.sum_mem
  intro r _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r.val,hmem r,hr r,(hf r).coeFn_toLp⟩)
end
end MasulloRH.JetAdmissibility
end

section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap FourierTransform Topology BigOperators
set_option autoImplicit false
namespace MasulloSynthesis
noncomputable section

abbrev H := Lp ℂ 2 (volume : Measure ℝ)

def weight (a : ℝ) (x : ℝ) : ℂ := ((1+x^2)^a : ℝ)

theorem weight_temperate (a : ℝ) : (weight a).HasTemperateGrowth := by
  have h := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ a
  have h' := Complex.ofRealCLM.hasTemperateGrowth.comp h
  change (fun x : ℝ => (((1+x^2)^a : ℝ):ℂ)).HasTemperateGrowth
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Real.norm_eq_abs, sq_abs] using h'

theorem weight_mul (a b x : ℝ) : weight a x * weight b x = weight (a+b) x := by
  unfold weight
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]

def logDistribution (p : ℝ) : H →L[ℂ] 𝓢'(ℝ,ℂ) :=
  (fourierInvCLM ℂ 𝓢'(ℝ,ℂ)).comp
    ((TemperedDistribution.smulLeftCLM ℂ (weight (p/2))).comp (Lp.toTemperedDistributionCLM ℂ volume 2))

theorem logDistribution_apply (p : ℝ) (u : H) (f : 𝓢(ℝ,ℂ)) :
    logDistribution p u f = ∫ x : ℝ, (weight (p/2) x * (𝓕⁻ f) x) * u x := by
  change 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ _ (Lp.toTemperedDistribution u)) f = _
  rw [TemperedDistribution.fourierInv_apply,TemperedDistribution.smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply]
  simp only [SchwartzMap.smulLeftCLM_apply_apply (weight_temperate _), smul_eq_mul]

theorem logDistribution_injective (p : ℝ) : Function.Injective (logDistribution p) := by
  intro u v h
  change 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ _ (Lp.toTemperedDistribution u)) =
    𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ _ (Lp.toTemperedDistribution v)) at h
  have h' := congrArg (fun t : 𝓢'(ℝ,ℂ) => TemperedDistribution.smulLeftCLM ℂ (weight (-p/2)) (𝓕 t)) h
  simp only [fourier_fourierInv_eq, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (weight_temperate _) (weight_temperate _)] at h'
  have hw : weight (p/2) * weight (-p/2) = fun _ => 1 := by
    funext x
    change weight (p/2) x * weight (-p/2) x = 1
    rw [weight_mul, show p/2 + -p/2 = 0 by ring]
    simp [weight] 
  rw [hw] at h'
  simp only [TemperedDistribution.smulLeftCLM_const,one_smul] at h'
  exact LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot h'

theorem logDistribution_mode (p ν : ℝ) (v : H)
    (hv : (v : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => weight (-p/2) x *
        Complex.exp (↑(-2*Real.pi*x*ν) * Complex.I)) (f : 𝓢(ℝ,ℂ)) :
    logDistribution p v f = f ν := by
  rw [logDistribution_apply]
  have h := congrArg (fun g : 𝓢(ℝ,ℂ) => g ν) (fourier_fourierInv_eq (F := 𝓢(ℝ,ℂ)) f)
  change (𝓕 (𝓕⁻ f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ)) ν = f ν at h
  rw [← h]
  change _ = 𝓕 (⇑(𝓕⁻ f : 𝓢(ℝ,ℂ))) ν
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx,smul_eq_mul]
  have hw : weight (p/2) x * weight (-p/2) x = 1 := by
    rw [weight_mul, show p/2 + -p/2 = 0 by ring]
    simp [weight]
  linear_combination (norm := ring_nf) ((𝓕⁻ f) x * Complex.exp (↑(-2*Real.pi*x*ν) * Complex.I)) * hw

theorem logDistribution_intertwines {ι : Type*} (p : ℝ) (v : ι → H) (ν : ι → ℝ)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (heval : ∀ i (f : 𝓢(ℝ,ℂ)), logDistribution p (v i) f = f (ν i))
    (A : H →L[ℂ] H) (b : 𝓢(ℝ,ℂ))
    (hA : ∀ i, A (v i) = b (ν i) • v i) (u : H) :
    logDistribution p (A u) = TemperedDistribution.smulLeftCLM ℂ b (logDistribution p u) := by
  let L := (logDistribution p).comp A
  let R := (TemperedDistribution.smulLeftCLM ℂ b).comp (logDistribution p)
  have he : L = R := ContinuousLinearMap.ext_on hd (by
    rintro _ ⟨i,rfl⟩
    ext f
    simp only [L,R,ContinuousLinearMap.comp_apply,hA,map_smul,TemperedDistribution.smulLeftCLM_apply_apply]
    change b (ν i) * (logDistribution p (v i) f) = _
    rw [heval,heval,SchwartzMap.smulLeftCLM_apply_apply b.hasTemperateGrowth]
    rfl)
  exact DFunLike.congr_fun he u
end
end MasulloSynthesis
end

section
open MeasureTheory Filter
open scoped Polynomial SchwartzMap FourierTransform
namespace MasulloSynthesis
noncomputable section
open MasulloRH.JetAdmissibility

theorem logDistribution_eq_unweighted_integral (p : ℝ) (u : H) (f : 𝓢(ℝ,ℂ)) :
    logDistribution p u f = ∫ x : ℝ, (u x / MasulloRH.JetAdmissibility.weight p x) * (𝓕⁻ (f:ℝ→ℂ)) x := by
  rw [logDistribution_apply, ← SchwartzMap.fourierInv_coe]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hw : weight (p/2) x * MasulloRH.JetAdmissibility.weight p x = 1 := by
    change weight (p/2) x * weight (-p/2) x = 1
    rw [weight_mul, show p/2 + -p/2 = 0 by ring]
    simp [weight]
  field_simp [MasulloRH.JetAdmissibility.weight_ne p x]
  linear_combination ((𝓕⁻ f) x * u x) * hw

theorem logDistribution_jet (p ν : ℝ) (r : ℕ) (u : H)
    (hu : (u : ℝ→ℂ) =ᵐ[volume] fun x : ℝ => weight (-p/2) x *
      ((x:ℂ)^r * Complex.exp (↑(-2*Real.pi*x*ν) * Complex.I))) (f : 𝓢(ℝ,ℂ)) :
    logDistribution p u f = iteratedDeriv r f ν / ((-2:ℂ)*Real.pi*Complex.I)^r := by
  rw [logDistribution_eq_unweighted_integral]
  apply integral_of_mode
  refine hu.trans (ae_of_all _ fun x => ?_)
  simp only [mode, phase, MasulloRH.JetAdmissibility.weight, weight, Polynomial.eval_pow, Polynomial.eval_X,
    mul_assoc, mul_comm ν]

theorem logDistribution_finite_jets (p ν : ℝ) (hp : 1/2<p) (u : H)
    (s : Finset ℕ) (c : ℕ→ℂ)
    (hD : ∀ f : 𝓢(ℝ,ℂ), logDistribution p u f = ∑ r ∈ s, c r * iteratedDeriv r f ν) :
    (∀ r ∈ s, c r ≠ 0 → (r:ℝ)+1/2<p) ∧
    u ∈ Submodule.span ℂ {v : H | ∃ r ∈ s, (r:ℝ)+1/2<p ∧
      (v : ℝ→ℂ) =ᵐ[volume] fun x : ℝ => weight (-p/2) x *
        ((x:ℂ)^r * Complex.exp (↑(-2*Real.pi*x*ν) * Complex.I))} := by
  simp only [logDistribution_eq_unweighted_integral] at hD
  refine ⟨MasulloRH.JetAdmissibility.jet_coefficients_admissible p ν hp u s c hD, ?_⟩
  have hs := MasulloRH.JetAdmissibility.mem_span_of_finite_jets p ν hp u s c hD
  apply Submodule.span_mono _ hs
  rintro v ⟨r,hr,ha,hv⟩
  refine ⟨r,hr,ha,hv.trans (ae_of_all _ fun x => ?_)⟩
  simp only [mode, phase, MasulloRH.JetAdmissibility.weight, weight, Polynomial.eval_pow, Polynomial.eval_X,
    mul_assoc, mul_comm ν]

theorem logDistribution_range_jets (p ν : ℝ) (hp : 1/2<p) (u : H)
    (m : ℕ) (c : Fin m → ℂ)
    (hD : ∀ f : 𝓢(ℝ,ℂ), logDistribution p u f = ∑ r : Fin m, c r * iteratedDeriv r.val f ν) :
    (∀ r : Fin m, c r ≠ 0 → (r.val:ℝ)+1/2<p) ∧
    u ∈ Submodule.span ℂ {v : H | ∃ r : ℕ, r < m ∧ (r:ℝ)+1/2<p ∧
      (v : ℝ→ℂ) =ᵐ[volume] fun x : ℝ => weight (-p/2) x *
        ((x:ℂ)^r * Complex.exp (↑(-2*Real.pi*x*ν) * Complex.I))} := by
  let C n := if h : n < m then c ⟨n,h⟩ else 0
  have h (f : 𝓢(ℝ,ℂ)) : logDistribution p u f = ∑ r ∈ Finset.range m, C r * iteratedDeriv r f ν := by
    rw [hD, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun r _ => by simp [C,r.isLt]
  obtain ⟨ha,hv⟩ := logDistribution_finite_jets p ν hp u (Finset.range m) C h
  refine ⟨fun r hc => ha r.val (Finset.mem_range.mpr r.isLt) (by simpa [C,r.isLt] using hc), ?_⟩
  simpa only [Finset.mem_range] using hv
end
end MasulloSynthesis
end

section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology ContDiff
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace LocalizedFourier

private noncomputable def rawWindow (x : ℝ) : ℂ :=
  ((Real.smoothTransition (x+1) - Real.smoothTransition x : ℝ) : ℂ)

private lemma rawWindow_zero (x : ℝ) (hx : 1 ≤ |x|) : rawWindow x = 0 := by
  rcases le_abs.mp hx with h | h
  · simp [rawWindow, Real.smoothTransition.one_of_one_le h,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x+1)]
  · simp [rawWindow, Real.smoothTransition.zero_of_nonpos (by linarith : x ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : x+1 ≤ 0)]

private lemma rawWindow_smooth : ContDiff ℝ ∞ rawWindow := by
  have H : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (x+1) - Real.smoothTransition x) :=
    (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub Real.smoothTransition.contDiff
  exact Complex.ofRealCLM.contDiff.comp H

private lemma rawWindow_compact : HasCompactSupport rawWindow := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(-1:ℝ)) (b:=1))
  intro x hx
  by_contra h
  apply hx
  apply rawWindow_zero
  by_contra! h'
  exact h ⟨(abs_lt.mp h').1.le, (abs_lt.mp h').2.le⟩

/-- A smooth integer-translate partition window, supported in the unit interval on each side of zero. -/
noncomputable def integerWindow : 𝓢(ℝ,ℂ) := rawWindow_compact.toSchwartzMap rawWindow_smooth

theorem integerWindow_zero (x : ℝ) (hx : 1 ≤ |x|) : integerWindow x = 0 := rawWindow_zero x hx

end LocalizedFourier
namespace MasulloRH
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem integratedOperator_exists
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (W : ℝ → ℝ) (A : ℝ)
    (hcont : ∀ u, Continuous (fun y => U y u))
    (hK : AEStronglyMeasurable K) (hKW : Integrable (fun y => ‖K y‖ * W y))
    (hW : ∀ y, 0 ≤ W y) (hA : 0 ≤ A) (hU : ∀ y, ‖U y‖ ≤ A * W y) :
    ∃ T : H →L[ℂ] H, (∀ u, T u = ∫ y : ℝ, K y • U y u) ∧
      ‖T‖ ≤ A * ∫ y : ℝ, ‖K y‖ * W y := by
  have hdom (u : H) (y : ℝ) :
      ‖K y • U y u‖ ≤ (‖K y‖ * W y) * (A * ‖u‖) := by
    rw [norm_smul]
    calc
      _ ≤ ‖K y‖ * ((A * W y) * ‖u‖) := by
        gcongr
        exact ((U y).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hU y) (norm_nonneg _))
      _ = _ := by ring
  have hi (u : H) : Integrable (fun y => K y • U y u) := by
    apply (hKW.mul_const (A * ‖u‖)).mono' (hK.smul (hcont u).aestronglyMeasurable)
    exact Eventually.of_forall (hdom u)
  let L : H →ₗ[ℂ] H := {
    toFun := fun u => ∫ y : ℝ, K y • U y u
    map_add' := by
      intro u v
      simp only [map_add, smul_add, integral_add (hi u) (hi v)]
    map_smul' := by
      intro c u
      simp only [map_smul, RingHom.id_apply]
      simp_rw [smul_comm (K _) c, integral_smul] }
  have hb (u : H) : ‖L u‖ ≤ (A * ∫ y : ℝ, ‖K y‖ * W y) * ‖u‖ := by
    calc
      _ ≤ ∫ y : ℝ, (‖K y‖ * W y) * (A * ‖u‖) := by
        exact norm_integral_le_of_norm_le (hKW.mul_const _) (Eventually.of_forall (hdom u))
      _ = _ := by rw [integral_mul_const]; ring
  have hC : 0 ≤ A * ∫ y : ℝ, ‖K y‖ * W y := mul_nonneg hA
    (integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (hW y)))
  exact ⟨L.mkContinuous _ hb, fun _ => rfl, L.mkContinuous_norm_le hC hb⟩

theorem integratedOperator_eigen
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ u, T u = ∫ y : ℝ, K y • U y u)
    (character : ℝ → ℂ) (v : H) (hv : ∀ y, U y v = character y • v) :
    T v = (∫ y : ℝ, K y * character y) • v := by
  rw [hT]
  simp_rw [hv, smul_smul]
  exact integral_smul_const _ _

theorem integratedOperator_fourier
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ u, T u = ∫ y : ℝ, K y • U y u)
    (ξ : ℝ) (v : H)
    (hv : ∀ y : ℝ, U y v = Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • v) :
    T v = (𝓕 K ξ) • v := by
  rw [integratedOperator_eigen U K T hT _ v hv, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => mul_comm _ _

theorem integratedOperator_inverseFourier
    (U : ℝ → H →L[ℂ] H) (m : ℝ → ℂ) (T : H →L[ℂ] H)
    (hm : Integrable m) (hmF : Integrable (𝓕 m))
    (hT : ∀ u, T u = ∫ y : ℝ, (𝓕⁻ m) y • U y u)
    (ξ : ℝ) (hmξ : ContinuousAt m ξ) (v : H)
    (hv : ∀ y : ℝ, U y v = Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • v) :
    T v = m ξ • v := by
  rw [integratedOperator_fourier U (𝓕⁻ m) T hT ξ v hv, hm.fourier_fourierInv_eq hmF hmξ]

end MasulloRH
private lemma schwartz_weighted_integral (g : 𝓢(ℝ,ℂ)) (k : ℕ) :
    Integrable (fun x : ℝ => (1+|x|)^k * ‖g x‖) := by
  have h := (g.integrable.norm.add (g.integrable_pow_mul volume k)).const_mul ((2:ℝ)^(k-1))
  apply h.mono' (by fun_prop)
  refine Eventually.of_forall fun x => ?_
  change ‖(1+|x|)^k * ‖g x‖‖ ≤ 2^(k-1) * (‖g x‖ + ‖x‖ ^ k * ‖g x‖)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, ← one_add_mul, ← mul_assoc]
  gcongr
  simpa using add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg x) k


theorem MasulloSynthesis.window_exhaustion {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (U : ℝ → H →L[ℂ] H) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h0 : U 0 = ContinuousLinearMap.id ℂ H)
    (horbit : ∀ u, Continuous (fun y => U y u))
    (hU : ∀ y, ‖U y‖ ≤ B * (1+|y|)^k) :
    ∃ (θ : 𝓢(ℝ,ℂ)) (b : ℕ → 𝓢(ℝ,ℂ)) (A : ℕ → H →L[ℂ] H) (C : ℝ),
      HasCompactSupport (θ:ℝ→ℂ) ∧ θ 0 = 1 ∧ 0 ≤ C ∧
      (∀ n, HasCompactSupport (b n:ℝ→ℂ)) ∧
      (∀ (n : ℕ) (ξ : ℝ), b n ξ = θ (ξ/((n:ℝ)+1))) ∧
      (∀ n, ‖A n‖ ≤ C) ∧
      (∀ n u, A n u = ∫ y : ℝ, (𝓕⁻ (θ:ℝ→ℂ)) y • U (y/((n:ℝ)+1)) u) ∧
      (∀ n (ξ : ℝ) v, (∀ y : ℝ, U y v = Complex.exp (↑(-2*Real.pi*y*ξ) * Complex.I) • v) →
        A n v = b n ξ • v) ∧ ∀ u, Tendsto (fun n => A n u) atTop (𝓝 u) := by
  classical
  let θ := LocalizedFourier.integerWindow
  have hθ0 : θ 0 = 1 := by
    change ((Real.smoothTransition (0+1) - Real.smoothTransition 0 : ℝ) : ℂ) = 1
    simp
  let h (n : ℕ) := (n:ℝ)+1
  have hpos (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hle (n : ℕ) : 1 ≤ h n := by dsimp [h]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  let g (n : ℕ) (ξ : ℝ) := θ (ξ/h n)
  have hgc (n : ℕ) : HasCompactSupport (g n) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:= -(h n)) (b:= h n))
    intro x hx
    by_contra hi
    apply hx
    apply LocalizedFourier.integerWindow_zero
    rw [abs_div, abs_of_pos (hpos n),le_div_iff₀ (hpos n),one_mul]
    by_contra! h'
    exact hi ⟨(abs_lt.mp h').1.le,(abs_lt.mp h').2.le⟩
  have hgs (n : ℕ) : ContDiff ℝ ∞ (g n) := (θ.smooth ⊤).comp (contDiff_id.div_const _)
  let b (n : ℕ) := (hgc n).toSchwartzMap (hgs n)
  let V (n : ℕ) (y : ℝ) := U (y/h n)
  have hVc (n : ℕ) (u : H) : Continuous (fun y => V n y u) := (horbit u).comp (continuous_id.div_const _)
  have hV (n : ℕ) (y : ℝ) : ‖V n y‖ ≤ B * (1+|y|)^k := by
    apply (hU _).trans
    rw [abs_div,abs_of_pos (hpos n)]
    gcongr
    exact div_le_self (abs_nonneg y) (hle n)
  let K : 𝓢(ℝ,ℂ) := 𝓕⁻ θ
  have hK (y : ℝ) : (𝓕⁻ (θ:ℝ→ℂ)) y = K y := (congrFun (SchwartzMap.fourierInv_coe θ) y).symm
  let W := fun y : ℝ => (1+|y|)^k
  have hW (y : ℝ) : 0 ≤ W y := by dsimp [W]; positivity
  have hKW : Integrable (fun y : ℝ => ‖K y‖ * W y) := by
    simpa only [W, mul_comm (‖_‖)] using schwartz_weighted_integral K k
  choose A hA hbound using fun n => MasulloRH.integratedOperator_exists (V n) K W B (hVc n)
    K.continuous.aestronglyMeasurable hKW hW hB (hV n)
  have hres (n : ℕ) (u : H) : A n u = ∫ y : ℝ, (𝓕⁻ (θ:ℝ→ℂ)) y • U (y/((n:ℝ)+1)) u := by
    simpa only [hK] using hA n u
  have hθc : HasCompactSupport (θ:ℝ→ℂ) := LocalizedFourier.rawWindow_compact
  refine ⟨θ,b,A,_,hθc,hθ0,mul_nonneg hB (integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (hW y))),
    hgc,fun _ _ => rfl,hbound,hres,?_,?_⟩
  · intro n ξ v hv
    apply MasulloRH.integratedOperator_inverseFourier (V n) θ (A n) θ.integrable
      (by simpa only [← SchwartzMap.fourier_coe] using (𝓕 θ : 𝓢(ℝ,ℂ)).integrable) (hres n)
      (ξ/h n) θ.continuous.continuousAt
    intro y
    rw [show V n y v = U (y/h n) v from rfl, hv]
    rw [show -2*Real.pi*(y/h n)*ξ = -2*Real.pi*y*(ξ/h n) by ring]
  · intro u
    have hI : (∫ y : ℝ, K y) = 1 := by
      have he : (𝓕 K : 𝓢(ℝ,ℂ)) = θ := by simp [K]
      have he0 := congrArg (fun z : 𝓢(ℝ,ℂ) => z 0) he
      simpa [SchwartzMap.fourier_coe, Real.fourier_eq', hθ0] using he0
    have hlim (y : ℝ) : Tendsto (fun n => y/h n) atTop (𝓝 0) := by
      have hd : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact tendsto_const_nhds.div_atTop hd
    have hconv (y : ℝ) : Tendsto (fun n : ℕ => K y • V n y u) atTop (𝓝 (K y • u)) := by
      have hh := ((horbit u).tendsto 0).comp (hlim y)
      simpa only [V, Function.comp_apply, h0, ContinuousLinearMap.id_apply] using tendsto_const_nhds.smul hh
    have hdom (n : ℕ) (y : ℝ) : ‖K y • V n y u‖ ≤ (‖K y‖ * W y) * (B*‖u‖) := by
      rw [norm_smul]
      have h1 := ((V n y).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hV n y) (norm_nonneg _))
      calc
        _ ≤ ‖K y‖ * ((B * W y) * ‖u‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = _ := by ring
    have hD := tendsto_integral_of_dominated_convergence (μ:=volume)
      (F:=fun n y => K y • V n y u) (f:=fun y => K y • u) (fun y => (‖K y‖*W y)*(B*‖u‖))
      (fun n => (K.continuous.smul (hVc n u)).aestronglyMeasurable)
      (hKW.mul_const _) (fun n => Eventually.of_forall (hdom n)) (Eventually.of_forall hconv)
    simp only [integral_smul_const, hI, one_smul, ← hA] at hD
    exact hD

open scoped InnerProductSpace FourierTransform SchwartzMap
open Filter MeasureTheory FourierTransform
private lemma fourier_uniqueness_L1 {f : ℝ → ℂ} (hf : Integrable f)
    (hz : ∀ ξ : ℝ, 𝓕 f ξ = 0) : ∀ᵐ x, f x = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hgc
  let h : ℝ → ℂ := fun x => (g x : ℂ)
  have hhc : HasCompactSupport h := hgc.comp_left (g:=fun z : ℝ => (z:ℂ)) (by simp)
  have hhs : ContDiff ℝ ∞ h := Complex.ofRealCLM.contDiff.comp hg
  let b := hhc.toSchwartzMap hhs
  let t : 𝓢(ℝ,ℂ) := 𝓕⁻ b
  have hswap : (∫ ξ : ℝ, 𝓕 (t:ℝ→ℂ) ξ • f ξ) = ∫ x : ℝ, t x • 𝓕 f x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L:=innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner t.integrable hf
  have he : 𝓕 (t:ℝ→ℂ) = (b:ℝ→ℂ) := by rw [← SchwartzMap.fourier_coe]; simp [t]
  simp only [he,hz,smul_zero,integral_zero] at hswap
  change (∫ x : ℝ, (g x:ℂ) * f x) = 0 at hswap
  simpa only [Complex.real_smul] using hswap

/-- A family of all real characters multiplied by a fixed a.e. nonzero L² weight is total.
The L² hypothesis on the weight follows from the representative of the zero mode. -/
theorem MasulloSynthesis.all_modes_total (w : ℝ → ℂ) (hw : ∀ᵐ x, w x ≠ 0) (v : ℝ → Lp ℂ 2 (volume : Measure ℝ))
    (hv : ∀ ξ : ℝ, (v ξ : ℝ → ℂ) =ᵐ[volume]
      (fun x : ℝ => w x * Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I))) :
    (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro z hz
  have horth (ξ : ℝ) : inner ℂ z (v ξ) = 0 :=
    (Submodule.span ℂ (Set.range v)).inner_left_of_mem_orthogonal (Submodule.subset_span ⟨ξ,rfl⟩) hz
  let f : ℝ → ℂ := fun x => inner ℂ (z x) (v 0 x)
  have hi : Integrable f := L2.integrable_inner z (v 0)
  have hv0 : (v 0 : ℝ→ℂ) =ᵐ[volume] w := by simpa using hv 0
  have hF (ξ : ℝ) : 𝓕 f ξ = 0 := by
    rw [← horth ξ, L2.inner_def, Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards [hv ξ,hv0] with x hx hx0
    simp only [f, hx, hx0, RCLike.inner_apply, smul_eq_mul, conj_trivial]
    rw [show -2*Real.pi*(ξ*x) = -2*Real.pi*x*ξ by ring]
    ring
  have hzero := fourier_uniqueness_L1 hi hF
  apply Lp.ext
  filter_upwards [hzero,hv0,hw,Lp.coeFn_zero (E:=ℂ) (p:=2) (μ:=(volume : Measure ℝ))] with x hx hx0 hxw hz0
  rw [hz0]
  change z x = 0
  change inner ℂ (z x) (v 0 x) = 0 at hx
  rw [RCLike.inner_apply, hx0] at hx
  simpa using (mul_eq_zero.mp hx).resolve_left hxw

open _root_.SobolevSynthesisProof.MasulloRH
namespace MasulloSynthesis
private lemma schwartz_weighted_integral (g : 𝓢(ℝ,ℂ)) (k : ℕ) :
    Integrable (fun x : ℝ => (1+|x|)^k * ‖g x‖) := by
  have h := (g.integrable.norm.add (g.integrable_pow_mul volume k)).const_mul ((2:ℝ)^(k-1))
  apply h.mono' (by fun_prop)
  refine Eventually.of_forall fun x => ?_
  change ‖(1+|x|)^k * ‖g x‖‖ ≤ 2^(k-1) * (‖g x‖ + ‖x‖ ^ k * ‖g x‖)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, ← one_add_mul, ← mul_assoc]
  gcongr
  simpa using add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg x) k


lemma makeFrequencyOperator {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (horbit : ∀ u, Continuous (fun y => U y u))
    (hU : ∀ y, ‖U y‖ ≤ B * (1+|y|)^k) (m : 𝓢(ℝ,ℂ)) :
    ∃ T : H →L[ℂ] H, (∀ u, T u = ∫ y : ℝ, (𝓕⁻ (⇑m)) y • U y u) ∧
      ‖T‖ ≤ B * (∫ y : ℝ, (1+|y|)^k * ‖(𝓕⁻ (⇑m)) y‖) ∧
      ∀ (ξ : ℝ) (v : H), (∀ y : ℝ, U y v = Complex.exp (↑(-2*Real.pi*y*ξ) * Complex.I) • v) →
        T v = m ξ • v := by
  let g : 𝓢(ℝ,ℂ) := 𝓕⁻ m
  have hcoe : (⇑g : ℝ → ℂ) = 𝓕⁻ (⇑m) := SchwartzMap.fourierInv_coe m
  have hK : AEStronglyMeasurable (𝓕⁻ (⇑m)) := hcoe ▸ g.continuous.aestronglyMeasurable
  have hw : Integrable (fun x : ℝ => ‖(𝓕⁻ (⇑m)) x‖ * (1+|x|)^k) := by
    simpa only [mul_comm (‖_‖), ← hcoe] using schwartz_weighted_integral g k
  obtain ⟨T,hT,hb⟩ := integratedOperator_exists U (𝓕⁻ (⇑m)) (fun y : ℝ => (1+|y|)^k) B
    horbit hK hw (fun y => by positivity) hB hU
  refine ⟨T, hT, ?_, ?_⟩
  · simpa only [mul_comm (‖_‖)] using hb
  · intro ξ v hv
    apply integratedOperator_inverseFourier U m T m.integrable _ hT ξ m.continuous.continuousAt v hv
    simpa only [← SchwartzMap.fourier_coe] using (𝓕 m : 𝓢(ℝ,ℂ)).integrable


end MasulloSynthesis
end

section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace MasulloRH
noncomputable section

abbrev LogL2 := Lp ℂ 2 (volume : Measure ℝ)

def logWeight (p x : ℝ) : ℝ := (1 + |x|) ^ (-p)

lemma logWeight_pos (p x : ℝ) : 0 < logWeight p x := Real.rpow_pos_of_pos (by positivity) _

lemma continuous_logWeight (p : ℝ) : Continuous (logWeight p) := by
  apply Continuous.rpow_const (continuous_const.add continuous_abs)
  exact fun x => Or.inl (show (1 + |x| : ℝ) ≠ 0 by positivity)

lemma logWeight_ratio_le {p : ℝ} (hp : 0 ≤ p) (x y : ℝ) :
    logWeight p x / logWeight p (x+y) ≤ (1 + |y|)^p := by
  have hx : 0 < 1 + |x| := by positivity
  have hxy : 0 < 1 + |x+y| := by positivity
  have hab : 1 + |x+y| ≤ (1 + |x|) * (1 + |y|) := by
    nlinarith [abs_add_le x y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]
  rw [logWeight, logWeight, Real.rpow_neg hx.le, Real.rpow_neg hxy.le, inv_div_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hx p)).2
  rw [mul_comm, ← Real.mul_rpow hx.le (show 0 ≤ 1 + |y| by positivity)]
  exact Real.rpow_le_rpow hxy.le hab hp

private def ratio (p y x : ℝ) : ℂ := (logWeight p x / logWeight p (x+y) : ℝ)

private lemma ratio_norm (p y x : ℝ) : ‖ratio p y x‖ = logWeight p x / logWeight p (x+y) := by
  exact Complex.norm_of_nonneg (div_nonneg (logWeight_pos _ _).le (logWeight_pos _ _).le)

private lemma ratio_mem (p : ℝ) (hp : 0 ≤ p) (y : ℝ) : MemLp (ratio p y) ⊤ volume := by
  apply memLp_top_of_bound _ ((1+|y|)^p) (ae_of_all _ fun x => (ratio_norm p y x).le.trans (logWeight_ratio_le hp x y))
  apply Continuous.aestronglyMeasurable
  exact Complex.continuous_ofReal.comp <| (continuous_logWeight p).div
    ((continuous_logWeight p).comp (continuous_id.add_const y)) (fun x => (logWeight_pos _ _).ne')

private def shift (y : ℝ) : LogL2 →ₗᵢ[ℂ] LogL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x+y) (measurePreserving_add_right volume y)

def weightedTranslation (p : ℝ) (hp : 0 ≤ p) (y : ℝ) : LogL2 →L[ℂ] LogL2 :=
  (((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2) ((ratio_mem p hp y).toLp (ratio p y))).comp
    (shift y).toContinuousLinearMap

lemma weightedTranslation_apply_ae (p : ℝ) (hp : 0 ≤ p) (y : ℝ) (f : LogL2) :
    (weightedTranslation p hp y f : ℝ → ℂ) =ᵐ[volume] fun x =>
      ((logWeight p x / logWeight p (x+y) : ℝ) : ℂ) * f (x+y) := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((ratio_mem p hp y).toLp (ratio p y)) (shift y f)
  have hs := Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)
  refine h.trans ?_
  filter_upwards [(ratio_mem p hp y).coeFn_toLp, hs] with x hx hsx
  change ((ratio_mem p hp y).toLp (ratio p y)) x * (shift y f) x = _
  change (shift y f) x = f (x+y) at hsx
  rw [hx, hsx]; rfl

lemma norm_weightedTranslation_le (p : ℝ) (hp : 0 ≤ p) (y : ℝ) :
    ‖weightedTranslation p hp y‖ ≤ (1+|y|)^p := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [← (shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedTranslation_apply_ae p hp y f,
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hs
  change (shift y f) x = f (x+y) at hs
  rw [hx, hs, norm_mul]
  exact mul_le_mul_of_nonneg_right ((ratio_norm p y x).le.trans (logWeight_ratio_le hp x y)) (norm_nonneg _)

lemma weightedTranslation_zero (p : ℝ) (hp : 0 ≤ p) : weightedTranslation p hp 0 = .id ℂ LogL2 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [weightedTranslation_apply_ae p hp 0 f] with x h
  change (weightedTranslation p hp 0 f) x = f x
  simpa only [add_zero, div_self (logWeight_pos p x).ne', Complex.ofReal_one, one_mul] using h

lemma weightedTranslation_add (p : ℝ) (hp : 0 ≤ p) (y z : ℝ) :
    weightedTranslation p hp (y+z) = (weightedTranslation p hp y).comp (weightedTranslation p hp z) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hz := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp
    (weightedTranslation_apply_ae p hp z f)
  filter_upwards [weightedTranslation_apply_ae p hp (y+z) f,
    weightedTranslation_apply_ae p hp y ((weightedTranslation p hp z) f), hz] with x hall hy hz
  change (weightedTranslation p hp z f) (x+y) = _ at hz
  change (weightedTranslation p hp (y+z) f) x = (weightedTranslation p hp y ((weightedTranslation p hp z) f)) x
  rw [hall, hy, hz]
  simp only [Function.comp_apply, ← add_assoc, ← mul_assoc, ← Complex.ofReal_mul]
  field_simp [ne_of_gt (logWeight_pos p (x+y)), ne_of_gt (logWeight_pos p (x+y+z))]

def angularCharacter (ξ x : ℝ) : ℂ := Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)

lemma angularCharacter_add (ξ x y : ℝ) :
    angularCharacter ξ (x+y) = angularCharacter ξ x * angularCharacter ξ y := by
  simp [angularCharacter, mul_add, add_mul, Complex.exp_add]

lemma norm_angularCharacter (ξ x : ℝ) : ‖angularCharacter ξ x‖ = 1 := by
  simp [angularCharacter, Complex.norm_exp]

lemma weightedExponential_memLp (p ξ : ℝ) (hp : 1/2 < p) :
    MemLp (fun x : ℝ => (logWeight p x : ℂ) * angularCharacter ξ x) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm _).2
  · have hdeg : (Module.finrank ℝ ℝ : ℝ) < 2*p := by simp; linarith
    have hint := integrable_one_add_norm (E := ℝ) (μ := volume) hdeg
    apply hint.congr
    apply Filter.Eventually.of_forall
    intro x
    change (1 + ‖x‖)^(-(2*p)) = ‖(logWeight p x : ℂ) * angularCharacter ξ x‖^2
    rw [norm_mul, norm_angularCharacter, mul_one, Complex.norm_of_nonneg (logWeight_pos _ _).le,
      logWeight, ← Real.rpow_mul_natCast (by positivity)]
    simp [Real.norm_eq_abs, mul_comm]
  · apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp (continuous_logWeight p)).mul
      (show Continuous (angularCharacter ξ) by unfold angularCharacter; fun_prop)

def weightedExponential (p ξ : ℝ) (hp : 1/2 < p) : LogL2 := (weightedExponential_memLp p ξ hp).toLp _

lemma weightedTranslation_exponential (p ξ : ℝ) (hp : 1/2 < p) (y : ℝ) :
    weightedTranslation p (by linarith) y (weightedExponential p ξ hp) =
      angularCharacter ξ y • weightedExponential p ξ hp := by
  have he := (weightedExponential_memLp p ξ hp).coeFn_toLp
  have hesh := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp he
  apply Lp.ext
  filter_upwards [weightedTranslation_apply_ae p (by linarith) y (weightedExponential p ξ hp), he,
    hesh, Lp.coeFn_smul (angularCharacter ξ y) (weightedExponential p ξ hp)] with x hU hx hxy hsm
  change weightedExponential p ξ hp x = (logWeight p x : ℂ) * angularCharacter ξ x at hx
  change weightedExponential p ξ hp (x+y) = (logWeight p (x+y) : ℂ) * angularCharacter ξ (x+y) at hxy
  rw [hU, hsm, Pi.smul_apply, smul_eq_mul, hx, hxy, angularCharacter_add, Complex.ofReal_div]
  field_simp [ne_of_gt (logWeight_pos p (x+y))]

private lemma ratio_sub_one_bound {p : ℝ} (hp : 0 ≤ p) (x y : ℝ) :
    |logWeight p x / logWeight p (x+y) - 1| ≤ (1+|y|)^p - 1 := by
  let a := logWeight p x / logWeight p (x+y)
  let D := (1+|y|)^p
  have hD : 1 ≤ D := Real.one_le_rpow (by linarith [abs_nonneg y]) hp
  have ha : a ≤ D := logWeight_ratio_le hp x y
  have hinv := logWeight_ratio_le hp (x+y) (-y)
  simp only [add_neg_cancel_right, abs_neg] at hinv
  have hDa : 1 ≤ D*a := by
    change 1 ≤ D * (logWeight p x / logWeight p (x+y))
    rw [← mul_div_assoc, le_div_iff₀ (logWeight_pos p (x+y)), one_mul]
    exact (div_le_iff₀ (logWeight_pos p x)).mp hinv
  change |a-1| ≤ D-1
  apply abs_le.mpr
  refine ⟨?_, by linarith⟩
  by_cases h : a ≤ 1
  · have h' := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hD)
    nlinarith
  · linarith

private lemma shift_continuous (f : LogL2) : Continuous (fun y : ℝ => shift y f) := by
  let g : C(ℝ × ℝ, ℝ) := ⟨fun z => z.2 + z.1, continuous_snd.add continuous_fst⟩
  exact continuous_const.compMeasurePreservingLp (g := g.curry) g.curry.continuous
    (fun y => measurePreserving_add_right volume y) (by norm_num)

private lemma diff_shift_bound (p : ℝ) (hp : 0 ≤ p) (y : ℝ) (f : LogL2) :
    ‖weightedTranslation p hp y f - shift y f‖ ≤ ((1+|y|)^p-1) * ‖f‖ := by
  rw [← (shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedTranslation_apply_ae p hp y f,
    Lp.coeFn_sub (weightedTranslation p hp y f) (shift y f),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hsub hs
  change (shift y f) x = f (x+y) at hs
  rw [hsub, Pi.sub_apply, hx, hs, ← sub_one_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact ratio_sub_one_bound hp x y

lemma continuous_weightedTranslation_orbit (p : ℝ) (hp : 0 ≤ p) (f : LogL2) :
    Continuous (fun y : ℝ => weightedTranslation p hp y f) := by
  have hlim : Tendsto (fun y : ℝ => weightedTranslation p hp y f) (𝓝 0) (𝓝 f) := by
    have hg : Continuous (fun y : ℝ => ((1+|y|)^p-1) * ‖f‖) := by
      apply Continuous.mul_const
      apply Continuous.sub _ continuous_const
      apply Continuous.rpow_const (continuous_const.add continuous_abs)
      exact fun x => Or.inl (show (1 + |x| : ℝ) ≠ 0 by positivity)
    have hbound : Tendsto (fun y : ℝ => ((1+|y|)^p-1) * ‖f‖) (𝓝 0) (𝓝 0) := by
      simpa using hg.tendsto 0
    have hdiff : Tendsto (fun y : ℝ => weightedTranslation p hp y f - shift y f) (𝓝 0) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => norm_nonneg _) (fun y => diff_shift_bound p hp y f) hbound
    have hs0 : shift 0 f = f := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume (0:ℝ))] with x hx
      change (shift 0 f) x = f (x+0) at hx
      simpa only [add_zero] using hx
    have hs := (shift_continuous f).tendsto 0
    rw [hs0] at hs
    simpa only [sub_add_cancel, zero_add] using hdiff.add hs
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd : Tendsto (fun z : ℝ => z-y) (𝓝 y) (𝓝 0) := by simpa using (show Continuous (fun z : ℝ => z-y) from continuous_id.sub continuous_const).tendsto y
  have h := (weightedTranslation p hp y).continuous.continuousAt.tendsto.comp (hlim.comp hd)
  refine h.congr fun z => ?_
  change (weightedTranslation p hp y) ((weightedTranslation p hp (z-y)) f) = _
  rw [← ContinuousLinearMap.comp_apply, ← weightedTranslation_add]
  simp

end
end MasulloRH
end

section
open MeasureTheory Filter Set
open scoped Topology
namespace MasulloRH
noncomputable section

def paperWeight (p x : ℝ) := (1+x^2)^(-p/2)
theorem paperWeight_pos (p x : ℝ) : 0 < paperWeight p x := Real.rpow_pos_of_pos (by positivity) _
private theorem paperWeight_cont (p : ℝ) : Continuous (paperWeight p) := by
  unfold paperWeight
  exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))

private theorem weightRatio_upper {p : ℝ} (hp : 0 < p) (x : ℝ) :
    paperWeight p x / logWeight p x ≤ 2^(p/2) := by
  apply (div_le_iff₀ (logWeight_pos _ _)).mpr
  simpa only [paperWeight, logWeight, Real.norm_eq_abs, sq_abs] using rpow_neg_one_add_norm_sq_le x hp

private theorem weightRatio_lower {p : ℝ} (hp : 0 < p) (x : ℝ) :
    logWeight p x / paperWeight p x ≤ 1 := by
  rw [div_le_one (paperWeight_pos _ _), paperWeight, Real.rpow_div_two_eq_sqrt _ (by positivity)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hp.le)
  simpa only [Real.norm_eq_abs, sq_abs] using sqrt_one_add_norm_sq_le x

private def weightChange (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (C : ℝ) (hC : ∀ x, f x / g x ≤ C) : LogL2 →L[ℂ] LogL2 :=
  let v := fun x : ℝ => ((f x / g x : ℝ) : ℂ)
  let hv : MemLp v ⊤ volume := memLp_top_of_bound
      (Complex.continuous_ofReal.comp (hf.div hg (fun x => (hgp x).ne'))).aestronglyMeasurable C
      (ae_of_all _ (fun x => by
        change ‖((f x / g x : ℝ) : ℂ)‖ ≤ C
        rw [Complex.norm_of_nonneg (div_nonneg (hfp x).le (hgp x).le)]
        exact hC x))
  ((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2) (hv.toLp v)

private theorem weightChange_ae (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (C : ℝ) (hC : ∀ x, f x / g x ≤ C) (u : LogL2) :
    (weightChange f g hf hg hfp hgp C hC u : ℝ → ℂ) =ᵐ[volume] fun x => ((f x / g x : ℝ) : ℂ) * u x := by
  let v := fun x : ℝ => ((f x / g x : ℝ) : ℂ)
  have hv : MemLp v ⊤ volume := memLp_top_of_bound
      (Complex.continuous_ofReal.comp (hf.div hg (fun x => (hgp x).ne'))).aestronglyMeasurable C
      (ae_of_all _ (fun x => by
        change ‖((f x / g x : ℝ) : ℂ)‖ ≤ C
        rw [Complex.norm_of_nonneg (div_nonneg (hfp x).le (hgp x).le)]
        exact hC x))
  have hw := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hv.toLp v) u
  refine hw.trans ?_
  filter_upwards [hv.coeFn_toLp] with x hx
  change hv.toLp v x * u x = v x * u x
  rw [hx]

def paperForward (p : ℝ) (hp : 1/2 < p) := weightChange (paperWeight p) (logWeight p)
  (paperWeight_cont p) (continuous_logWeight p) (paperWeight_pos p) (logWeight_pos p) _ (weightRatio_upper (by linarith))
def paperBackward (p : ℝ) (hp : 1/2 < p) := weightChange (logWeight p) (paperWeight p)
  (continuous_logWeight p) (paperWeight_cont p) (logWeight_pos p) (paperWeight_pos p) _ (weightRatio_lower (by linarith))

theorem paperForward_ae (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    (paperForward p hp u : ℝ → ℂ) =ᵐ[volume] fun x => ((paperWeight p x / logWeight p x : ℝ) : ℂ) * u x :=
  weightChange_ae _ _ _ _ _ _ _ _ _
theorem paperBackward_ae (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    (paperBackward p hp u : ℝ → ℂ) =ᵐ[volume] fun x => ((logWeight p x / paperWeight p x : ℝ) : ℂ) * u x :=
  weightChange_ae _ _ _ _ _ _ _ _ _

theorem paper_backward_forward (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    paperBackward p hp (paperForward p hp u) = u := by
  apply Lp.ext
  filter_upwards [paperBackward_ae p hp (paperForward p hp u), paperForward_ae p hp u] with x hx hy
  rw [hx,hy,Complex.ofReal_div,Complex.ofReal_div]
  field_simp [(logWeight_pos p x).ne', (paperWeight_pos p x).ne']

def paperShift (p : ℝ) (hp : 1/2 < p) (y : ℝ) : LogL2 →L[ℂ] LogL2 :=
  (paperForward p hp).comp ((weightedTranslation p (by linarith) y).comp (paperBackward p hp))

theorem paperShift_ae (p : ℝ) (hp : 1/2 < p) (y : ℝ) (u : LogL2) :
    (paperShift p hp y u : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      ((paperWeight p x / paperWeight p (x+y) : ℝ) : ℂ) * u (x+y) := by
  have hs := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp (paperBackward_ae p hp u)
  filter_upwards [paperForward_ae p hp (weightedTranslation p (by linarith) y (paperBackward p hp u)),
    weightedTranslation_apply_ae p (by linarith) y (paperBackward p hp u), hs] with x hx ht hb
  change paperForward p hp (weightedTranslation p (by linarith) y (paperBackward p hp u)) x = _
  change paperBackward p hp u (x+y) = _ at hb
  rw [hx,ht,hb]
  change _ * (_ * ((((logWeight p (x+y) / paperWeight p (x+y)) : ℝ) : ℂ) * u (x+y))) = _
  simp only [Complex.ofReal_div]
  field_simp [(logWeight_pos p x).ne',(logWeight_pos p (x+y)).ne',(paperWeight_pos p (x+y)).ne']

theorem paperShift_continuous (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    Continuous (fun y => paperShift p hp y u) :=
  (paperForward p hp).continuous.comp (continuous_weightedTranslation_orbit p (by linarith) (paperBackward p hp u))

theorem paperShift_bound (p : ℝ) (hp : 1/2 < p) (y : ℝ) :
    ‖paperShift p hp y‖ ≤ (‖paperForward p hp‖ * ‖paperBackward p hp‖) * (1+|y|)^⌈p⌉₊ := by
  have hw : ‖weightedTranslation p (by linarith) y‖ ≤ (1+|y|)^⌈p⌉₊ := by
    apply (norm_weightedTranslation_le p (by linarith) y).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (Nat.le_ceil p)
  calc
    _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖paperForward p hp‖ * (‖weightedTranslation p (by linarith) y‖ * ‖paperBackward p hp‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc, mul_comm ‖paperBackward p hp‖]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (norm_nonneg _)) (norm_nonneg _)

end
end MasulloRH
end

section
open MeasureTheory Filter _root_.SobolevSynthesisProof.MasulloRH
open scoped SchwartzMap FourierTransform Topology
noncomputable section
namespace MasulloSynthesis

def ambientMode (p : ℝ) (hp : 1/2 < p) (ξ : ℝ) : H :=
  paperForward p hp (weightedExponential p (-2*Real.pi*ξ) hp)

theorem ambientMode_ae (p : ℝ) (hp : 1/2 < p) (ξ : ℝ) :
    (ambientMode p hp ξ : ℝ → ℂ) =ᵐ[volume] fun x =>
      weight (-p/2) x * Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I) := by
  filter_upwards [paperForward_ae p hp (weightedExponential p (-2*Real.pi*ξ) hp),
    (weightedExponential_memLp p (-2*Real.pi*ξ) hp).coeFn_toLp] with x hx hu
  change paperForward p hp (weightedExponential p (-2*Real.pi*ξ) hp) x = _
  rw [hx]
  change weightedExponential p (-2*Real.pi*ξ) hp x = _ at hu
  rw [hu,Complex.ofReal_div]
  change _ * ((logWeight p x : ℂ) * angularCharacter _ _) =
    (paperWeight p x : ℂ) * Complex.exp _
  have he : angularCharacter (-2*Real.pi*ξ) x = Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I) := by
    unfold angularCharacter
    push_cast
    congr 1; ring
  rw [he]
  field_simp [(logWeight_pos p x).ne']

theorem ambientMode_dense (p : ℝ) (hp : 1/2 < p) :
    Dense (Submodule.span ℂ (Set.range (ambientMode p hp)) : Set H) := by
  have hd := all_modes_total (weight (-p/2)) (ae_of_all volume fun x =>
    (Complex.ofReal_ne_zero.mpr (paperWeight_pos p x).ne')) (ambientMode p hp) (ambientMode_ae p hp)
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,hd]
  rfl

theorem ambientMode_shift (p : ℝ) (hp : 1/2 < p) (ξ y : ℝ) :
    paperShift p hp y (ambientMode p hp ξ) =
      Complex.exp (↑(-2*Real.pi*y*ξ)*Complex.I) • ambientMode p hp ξ := by
  simp only [ambientMode,paperShift,ContinuousLinearMap.comp_apply,paper_backward_forward,
    weightedTranslation_exponential,map_smul]
  congr 1
  unfold angularCharacter
  push_cast
  congr 1; ring

theorem ambient_localizes_integral (p : ℝ) (hp : 1/2 < p) (b : 𝓢(ℝ,ℂ)) :
    ∃ A : H →L[ℂ] H, (∀ u, A u = ∫ y : ℝ, (𝓕⁻ (b:ℝ→ℂ)) y • paperShift p hp y u) ∧
    ∀ u, logDistribution p (A u) =
      TemperedDistribution.smulLeftCLM ℂ b (logDistribution p u) := by
  obtain ⟨A,hA,_,hmode⟩ := makeFrequencyOperator (paperShift p hp) ⌈p⌉₊
    (‖paperForward p hp‖ * ‖paperBackward p hp‖) (by positivity) (paperShift_continuous p hp)
    (paperShift_bound p hp) b
  refine ⟨A,hA,logDistribution_intertwines p (ambientMode p hp) id (ambientMode_dense p hp)
    (fun ξ => logDistribution_mode p ξ _ (ambientMode_ae p hp ξ)) A b ?_⟩
  exact fun ξ => hmode ξ _ (ambientMode_shift p hp ξ)

theorem ambient_localizes (p : ℝ) (hp : 1/2 < p) (b : 𝓢(ℝ,ℂ)) :
    ∃ A : H →L[ℂ] H, ∀ u, logDistribution p (A u) =
      TemperedDistribution.smulLeftCLM ℂ b (logDistribution p u) := by
  obtain ⟨A,_,h⟩ := ambient_localizes_integral p hp b
  exact ⟨A,h⟩

theorem ambient_exhaustion (p : ℝ) (hp : 1/2 < p) :
    ∃ (b : ℕ→𝓢(ℝ,ℂ)) (A : ℕ→H→L[ℂ]H), (∀ n, HasCompactSupport (b n:ℝ→ℂ)) ∧
      (∀ n u, logDistribution p (A n u) =
        TemperedDistribution.smulLeftCLM ℂ (b n) (logDistribution p u)) ∧
      ∀ u, Tendsto (fun n => A n u) atTop (𝓝 u) := by
  have h0 : paperShift p hp 0 = ContinuousLinearMap.id ℂ H := by
    ext1 u
    apply Lp.ext
    filter_upwards [paperShift_ae p hp 0 u] with x hx
    simpa [(paperWeight_pos p x).ne'] using hx
  obtain ⟨_,b,A,_,_,_,_,hc,_,_,_,he,ht⟩ := window_exhaustion (paperShift p hp) ⌈p⌉₊
    (‖paperForward p hp‖ * ‖paperBackward p hp‖) (by positivity) h0 (paperShift_continuous p hp)
    (paperShift_bound p hp)
  refine ⟨b,A,hc,fun n => logDistribution_intertwines p (ambientMode p hp) id (ambientMode_dense p hp)
    (fun ξ => logDistribution_mode p ξ _ (ambientMode_ae p hp ξ)) (A n) (b n) ?_,ht⟩
  exact fun ξ => he n ξ _ (ambientMode_shift p hp ξ)

end MasulloSynthesis
end
end

section
open scoped SchwartzMap Topology ContDiff
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 800000

private lemma isolate_one_frequency (S : Finset ℝ) (a : S) :
    ∃ b : 𝓢(ℝ,ℂ), HasCompactSupport (b:ℝ→ℂ) ∧
      ((b:ℝ→ℂ) =ᶠ[𝓝 a.val] fun _ => 1) ∧
      ∀ t : S, t ≠ a → (b:ℝ→ℂ) =ᶠ[𝓝 t.val] fun _ => 0 := by
  classical
  have hnh : ((↑(S.erase a.val) : Set ℝ)ᶜ) ∈ 𝓝 a.val :=
    (S.erase a.val).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨r,hr,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnh
  let φ : ContDiffBump a.val := ⟨r/2,r,half_pos hr,half_lt_self hr⟩
  let g (t : ℝ) : ℂ := (φ t : ℂ)
  have hc : HasCompactSupport g := φ.hasCompactSupport.comp_left (g:=fun t : ℝ => (t:ℂ)) (by simp)
  have hs : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp φ.contDiff
  let b := hc.toSchwartzMap hs
  refine ⟨b,hc,?_,fun t ht => ?_⟩
  · filter_upwards [φ.eventuallyEq_one] with z hz
    change (φ z : ℂ) = 1
    rw [show φ z = 1 from hz]
    rfl
  · have hz : t.val ∉ tsupport (φ:ℝ→ℝ) := by
      rw [φ.tsupport_eq]
      intro h
      exact hsub h (Finset.mem_erase.mpr ⟨fun he => ht (Subtype.ext he),t.prop⟩)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with z h
    change (φ z : ℂ) = 0
    rw [show φ z = 0 from h]
    rfl

/-- Finite sums of distinct point-supported jet distributions decompose into
vectors already in the original space if that space admits compact spectral cutoffs. -/
private theorem finite_window_isolation {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (D : H →L[ℂ] 𝓢'(ℝ,ℂ)) (hD : Function.Injective D)
    (hcut : ∀ b : 𝓢(ℝ,ℂ), HasCompactSupport (b:ℝ→ℂ) →
      ∃ A : H →L[ℂ] H, ∀ w, D (A w) = TemperedDistribution.smulLeftCLM ℂ (b:ℝ→ℂ) (D w))
    (S : Finset ℝ) (d : S → ℕ) (c : (a : S) → Fin (d a) → ℂ) (u : H)
    (hu : ∀ f : 𝓢(ℝ,ℂ), D u f = ∑ a : S, ∑ k : Fin (d a), c a k * iteratedDeriv k.val f a.val)
    (V : Submodule ℂ H)
    (hone : ∀ (a : S) (w : H) (z : Fin (d a) → ℂ),
      (∀ f : 𝓢(ℝ,ℂ), D w f = ∑ k : Fin (d a), z k * iteratedDeriv k.val f a.val) → w ∈ V) :
    u ∈ V := by
  classical
  choose b hb honeNear hzeroNear using isolate_one_frequency S
  choose A hA using fun a : S => hcut (b a) (hb a)
  have hjet (a : S) (f : 𝓢(ℝ,ℂ)) :
      D (A a u) f = ∑ k : Fin (d a), c a k * iteratedDeriv k.val f a.val := by
    let g := SchwartzMap.smulLeftCLM ℂ (b a:ℝ→ℂ) f
    have hg (x : ℝ) : g x = b a x * f x :=
      SchwartzMap.smulLeftCLM_apply_apply (b a).hasTemperateGrowth f x
    have h1 : (g:ℝ→ℂ) =ᶠ[𝓝 a.val] (f:ℝ→ℂ) := by
      filter_upwards [honeNear a] with x hx
      simp only [hg,hx,one_mul]
    have h0 (t : S) (ht : t ≠ a) : (g:ℝ→ℂ) =ᶠ[𝓝 t.val] (fun _ => (0:ℂ)) := by
      filter_upwards [hzeroNear a t ht] with x hx
      simp only [hg,hx,zero_mul]
    rw [hA,TemperedDistribution.smulLeftCLM_apply_apply]
    change D u g = _
    rw [hu]
    rw [Finset.sum_eq_single a]
    · simp only [h1.iteratedDeriv_eq]
    · intro t _ ht
      apply Finset.sum_eq_zero
      intro k _
      simp only [(h0 t ht).iteratedDeriv_eq,iteratedDeriv_fun_const_zero,mul_zero]
    · simp
  have hsum : u = ∑ a : S, A a u := by
    apply hD
    rw [map_sum]
    ext1 f
    rw [hu]
    let eval : 𝓢'(ℝ,ℂ) →ₗ[ℂ] ℂ := {
      toFun := fun z => z f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    change _ = eval (∑ a : S, D (A a u))
    rw [map_sum]
    exact Finset.sum_congr rfl (fun a _ => (hjet a f).symm)
  rw [hsum]
  exact V.sum_mem (fun a _ => hone a _ (c a) (hjet a))

private lemma small_jets_zero_of_product {G q : ℝ → ℂ} (hG : ∀ a, AnalyticAt ℝ G a)
    (hfinite : ∀ a, analyticOrderAt G a ≠ ⊤) (hq : ContDiff ℝ ∞ q)
    (a : ℝ) (n : ℕ) (hn : n < analyticOrderNatAt G a) :
    iteratedDeriv n (fun x : ℝ => G x * q x) a = 0 := by
  have hh : (analyticOrderNatAt G a : ℕ∞) ≤ analyticOrderAt G a :=
    (Nat.cast_analyticOrderNatAt (hfinite a)).le
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG a)).mp hh
  rw [iteratedDeriv_fun_mul (hG a).contDiffAt (hq.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := (Finset.mem_range_succ_iff.mp hk).trans_lt hn
  simp [hz k hk']

open MasulloSynthesis MeasureTheory
open scoped FourierTransform
private theorem synthesis_of_ambient (p : ℝ) (hp : 1/2<p) (G : ℝ→ℂ)
    (hG : ∀ x, AnalyticAt ℝ G x) (hfin : ∀ x, analyticOrderAt G x ≠ ⊤)
    (u : Lp ℂ 2 (volume : Measure ℝ))
    (hloc : ∀ b : 𝓢(ℝ,ℂ), ∃ A : H →L[ℂ] H, ∀ v,
      logDistribution p (A v) = TemperedDistribution.smulLeftCLM ℂ b (logDistribution p v))
    (hexh : ∃ (b : ℕ → 𝓢(ℝ,ℂ)) (A : ℕ → H →L[ℂ] H), (∀ n, HasCompactSupport (b n:ℝ→ℂ)) ∧
      (∀ n v, logDistribution p (A n v) = TemperedDistribution.smulLeftCLM ℂ (b n) (logDistribution p v)) ∧
      ∀ v, Tendsto (fun n => A n v) atTop (𝓝 v)) :
    (∀ q : 𝓢(ℝ,ℂ), HasCompactSupport (q:ℝ→ℂ) →
      ∫ x : ℝ, (↑((1+x^2)^(p/2) : ℝ) * (𝓕⁻ (fun t : ℝ => G t * q t)) x : ℂ) * u x = 0) ↔
    u ∈ (Submodule.span ℂ {v : Lp ℂ 2 (volume : Measure ℝ) | ∃ (ν : ℝ) (r : ℕ),
      G ν = 0 ∧ r < analyticOrderNatAt G ν ∧ (r:ℝ)+1/2<p ∧
      (v : ℝ→ℂ) =ᵐ[volume] (fun x : ℝ => (↑((1+x^2)^(-p/2) : ℝ) : ℂ) *
        ((x:ℂ)^r * Complex.exp (↑(-2*Real.pi*x*ν)*Complex.I)))}).topologicalClosure := by
  classical
  let Z : Set H := {v | ∃ (ν : ℝ) (r : ℕ), G ν = 0 ∧ r < analyticOrderNatAt G ν ∧
    (r:ℝ)+1/2<p ∧ (v : ℝ→ℂ) =ᵐ[volume] (fun x : ℝ => weight (-p/2) x *
        ((x:ℂ)^r * Complex.exp (↑(-2*Real.pi*x*ν)*Complex.I)))}
  let V := (Submodule.span ℂ Z).topologicalClosure
  change _ ↔ u ∈ V
  constructor
  · intro hann
    have hprincipal : ∀ q t : 𝓢(ℝ,ℂ), HasCompactSupport (q:ℝ→ℂ) →
        (∀ x, t x = G x * q x) → logDistribution p u t = 0 := by
      intro q t hc ht
      rw [logDistribution_apply]
      simp_rw [SchwartzMap.fourierInv_coe,funext ht]
      exact hann q hc
    obtain ⟨b,A,hb,hA,hlim⟩ := hexh
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (hlim u)
    refine Eventually.of_forall fun n => ?_
    obtain ⟨S,hS,c,hc⟩ := MasulloRH.compact_window_theta_annihilator hG hfin _ hprincipal (b n) (hb n)
    have hDn (f : 𝓢(ℝ,ℂ)) : logDistribution p (A n u) f =
        ∑ a : S, ∑ k : Fin (analyticOrderNatAt G a.val), c a k * iteratedDeriv k.val f a.val := by
      rw [hA,TemperedDistribution.smulLeftCLM_apply_apply]
      exact hc f
    apply finite_window_isolation (logDistribution p) (logDistribution_injective p)
      (fun b _ => hloc b) S (fun a => analyticOrderNatAt G a.val) c (A n u) hDn V
    intro a w z hw
    have hspan := (logDistribution_range_jets p a.val hp w _ z hw).2
    have hsub : {v : H | ∃ r : ℕ, r < analyticOrderNatAt G a.val ∧ (r:ℝ)+1/2<p ∧
      (v : ℝ→ℂ) =ᵐ[volume] fun x : ℝ => weight (-p/2) x *
        ((x:ℂ)^r * Complex.exp (↑(-2*Real.pi*x*a.val) * Complex.I))} ⊆ Z := by
      rintro v ⟨r,hr,hp',hv⟩
      exact ⟨a.val,r,((hS _).mp a.prop).2,hr,hp',hv⟩
    exact (Submodule.span ℂ Z).le_topologicalClosure (Submodule.span_mono hsub hspan)
  · intro hu q hq
    let g := fun x : ℝ => G x * q x
    have hg : ContDiff ℝ ∞ g :=
      (contDiff_iff_contDiffAt.mpr (fun x => (hG x).contDiffAt)).mul (q.smooth ⊤)
    have hg' : HasCompactSupport g := hq.mul_left
    let t := hg'.toSchwartzMap hg
    let L := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ t).comp (logDistribution p)
    have hsub : Submodule.span ℂ Z ≤ LinearMap.ker L.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro v ⟨ν,r,hν,hr,hpr,hv⟩
      change logDistribution p v t = 0
      rw [logDistribution_jet p ν r v hv]
      have hd : iteratedDeriv r t ν = 0 :=
        small_jets_zero_of_product hG hfin (q.smooth ⊤) ν r hr
      simp only [hd,zero_div]
    have hLu : logDistribution p u t = 0 :=
      (Submodule.span ℂ Z).topologicalClosure_minimal hsub L.isClosed_ker hu
    simpa only [logDistribution_apply, weight, SchwartzMap.fourierInv_coe, show ⇑t = g from rfl, g] using hLu

end
end SobolevSynthesisProof
open MeasureTheory Filter SobolevSynthesisProof SobolevSynthesisProof.MasulloSynthesis
open scoped FourierTransform SchwartzMap
theorem solution (p : ℝ) (hp : 1/2<p) (G : ℝ→ℂ)
    (hG : ∀ x, AnalyticAt ℝ G x) (hfin : ∀ x, analyticOrderAt G x ≠ ⊤)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∀ q : 𝓢(ℝ,ℂ), HasCompactSupport (q:ℝ→ℂ) →
      ∫ x : ℝ, (↑((1+x^2)^(p/2) : ℝ) * (𝓕⁻ (fun t : ℝ => G t * q t)) x : ℂ) * u x = 0) ↔
    u ∈ (Submodule.span ℂ {v : Lp ℂ 2 (volume : Measure ℝ) | ∃ (ν : ℝ) (r : ℕ),
      G ν = 0 ∧ r < analyticOrderNatAt G ν ∧ (r:ℝ)+1/2<p ∧
      (v : ℝ→ℂ) =ᵐ[volume] (fun x : ℝ => (↑((1+x^2)^(-p/2) : ℝ) : ℂ) *
        ((x:ℂ)^r * Complex.exp (↑(-2*Real.pi*x*ν)*Complex.I)))}).topologicalClosure := by
  exact synthesis_of_ambient p hp G hG hfin u (ambient_localizes p hp) (ambient_exhaustion p hp)
