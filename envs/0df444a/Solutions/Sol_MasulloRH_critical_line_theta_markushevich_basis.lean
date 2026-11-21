-- Prove2me | solution 1 for MasulloRH.critical_line_theta_markushevich_basis
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:45:40.6829+00:00
-- url     : https://prove2.me/submissions/8be4b672-f5c6-4503-9a41-d7dbd779f516

import Mathlib
import Theorems.Thm_MasulloGRH_sobolev_oscillatory_jet_memLp_iff
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_sobolev_spectral_synthesis
import Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace

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


end
end MasulloRH.JetAdmissibility
end
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

end
end MasulloSynthesis

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

end
end MasulloSynthesis

open Set Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology

namespace MasulloRH

abbrev CriticalLineZero := {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1 / 2}

theorem criticalLineOrder_pos (ρ : CriticalLineZero) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    linarith [ρ.prop.2, Complex.one_re]
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfinite := analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  have hnonzero := (analyticOn_riemannZeta _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1
  exact Nat.pos_of_ne_zero (fun h => (ENat.toNat_eq_zero.mp h).elim hnonzero hfinite)

theorem criticalLineZero_scaled_multiplicity_summable :
    Summable (fun ρ : CriticalLineZero => (analyticOrderNatAt riemannZeta ρ.val : ℝ) /
        (1 + (-ρ.val.im / (2 * Real.pi)) ^ 2)) := by
  let e (ρ : CriticalLineZero) : ZetaZerosInTraceStrip 1 :=
    ⟨ρ.val, ρ.prop.1, by rw [ρ.prop.2]; norm_num, by rw [ρ.prop.2]; norm_num,
      by rw [ρ.prop.2]; norm_num⟩
  have he : Function.Injective e := fun _ _ h => Subtype.ext (congrArg (fun s : ZetaZerosInTraceStrip 1 => s.val) h)
  have hs := ((weighted_zero_summability 1 one_pos).comp_injective he).mul_left ((2 * Real.pi)^2)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro ρ
  let y := ρ.val.im
  let c := 2 * Real.pi
  have hc : 1 ≤ c := by dsimp [c]; linarith [Real.pi_gt_three]
  have hc0 : 0 < c := by linarith
  have hsc : 1 + y^2 ≤ c^2 * (1 + (-y/c)^2) := calc
    _ ≤ c^2 + y^2 := by nlinarith [sq_nonneg (c-1)]
    _ = _ := by field_simp
  have hrecip : 1 / (1 + (-y / c)^2) ≤ c^2 / (1+y^2) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa only [one_mul] using hsc)
  let m : ℝ := analyticOrderNatAt riemannZeta ρ.val
  have hm : 0 ≤ m := Nat.cast_nonneg _
  change m / (1 + (-y / c)^2) ≤ c^2 * (m / (1+y^2))
  calc
    _ = m * (1 / (1 + (-y / c)^2)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hrecip hm).trans_eq (by ring)

theorem criticalLineZero_scaled_weight_summable :
    Summable (fun ρ : CriticalLineZero => 1 / (1 + (-ρ.val.im / (2 * Real.pi)) ^ 2)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ criticalLineZero_scaled_multiplicity_summable
  intro ρ
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast criticalLineOrder_pos ρ

end MasulloRH
open Set Filter MeasureTheory
open scoped SchwartzMap Topology ContDiff Classical
namespace MasulloMB
noncomputable section

/-- Isolate one frequency of a locally finite injective family; every other frequency has
a whole neighborhood outside the support of the selected smooth bump. -/
private theorem isolated_bump {ι : Type*} (ν : ι → ℝ) (hν : Function.Injective ν)
    (hF : ∀ s : Set ℝ, IsCompact s → (ν ⁻¹' s).Finite) (i : ι) :
    ∃ b : 𝓢(ℝ,ℝ), HasCompactSupport (b:ℝ→ℝ) ∧
      (b:ℝ→ℝ) =ᶠ[𝓝 (ν i)] (fun _ => 1) ∧
      ∀ j : ι, j ≠ i → (b:ℝ→ℝ) =ᶠ[𝓝 (ν j)] (fun _ => 0) := by
  classical
  let F := (hF (Metric.closedBall (ν i) 1) (isCompact_closedBall ..)).toFinset
  let S := ((F.erase i).image ν : Finset ℝ)
  have hnot : ν i ∉ S := by
    intro h
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp h
    exact (Finset.mem_erase.mp hk).1 (hν he)
  have hnh : ((↑S:Set ℝ)ᶜ ∩ Metric.closedBall (ν i) 1) ∈ 𝓝 (ν i) :=
    inter_mem (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hnot) (Metric.closedBall_mem_nhds _ zero_lt_one)
  obtain ⟨r,hr,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnh
  let b : ContDiffBump (ν i) := ⟨r/2,r,half_pos hr,half_lt_self hr⟩
  refine ⟨b.hasCompactSupport.toSchwartzMap b.contDiff,b.hasCompactSupport,b.eventuallyEq_one,fun j hj => ?_⟩
  apply notMem_tsupport_iff_eventuallyEq.mp
  change ν j ∉ tsupport (b:ℝ→ℝ)
  rw [b.tsupport_eq]
  intro hx
  obtain ⟨hs,h1⟩ := hsub hx
  have hjF : j ∈ F := (Set.Finite.mem_toFinset _).mpr h1
  exact hs (Finset.mem_image.mpr ⟨j,Finset.mem_erase.mpr ⟨hj,hjF⟩,rfl⟩)

/-- A compact smooth function with a single prescribed derivative on a locally finite frequency
set. Every other order at that site, as well as every jet at the other sites, vanishes. -/
theorem exists_delta_test {ι : Type*} (ν : ι → ℝ) (hν : Function.Injective ν)
    (hF : ∀ s : Set ℝ, IsCompact s → (ν ⁻¹' s).Finite) (i : ι) (r : ℕ) (c : ℂ) :
    ∃ f : 𝓢(ℝ,ℂ), HasCompactSupport (f:ℝ→ℂ) ∧
      ∀ (j : ι) (k : ℕ), iteratedDeriv k f (ν j) = if j=i ∧ k=r then c else 0 := by
  classical
  obtain ⟨b,hbc,h1,h0⟩ := isolated_bump ν hν hF i
  let q (x : ℝ) := (x-ν i)^r
  let w : ℂ := c/(r.factorial:ℂ)
  let f (x : ℝ) := (b x*q x) • w
  have hc : HasCompactSupport f :=
    (hbc.mul_right (f':=q)).smul_right (f':=fun _ => w)
  have hs : ContDiff ℝ ∞ f := ((b.smooth ⊤).mul (by dsimp [q]; fun_prop)).smul contDiff_const
  refine ⟨hc.toSchwartzMap hs,hc,fun j k => ?_⟩
  by_cases hj : j=i
  · subst j
    have he : f =ᶠ[𝓝 (ν i)] (fun x => q x • w) := by
      filter_upwards [h1] with x hx
      simp [f, show b x=1 from hx]
    change iteratedDeriv k f (ν i) = _
    rw [he.iteratedDeriv_eq k,iteratedDeriv_smul_const (by dsimp [q]; fun_prop)]
    change iteratedDeriv k (fun x : ℝ => (x-ν i)^r) (ν i) • w = _
    simp only [iteratedDeriv_comp_sub_const (f:=fun x : ℝ => x^r),sub_self,iteratedDeriv_fun_pow_zero]
    by_cases hk : k=r
    · simp [hk,w,Complex.real_smul]
      have hne : (r.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
      field_simp [hne]
    · simp [hk]
  · have he : f =ᶠ[𝓝 (ν j)] (fun _ => 0) := by
      filter_upwards [h0 j hj] with x hx
      simp [f,show b x=0 from hx]
    change iteratedDeriv k f (ν j) = _
    rw [he.iteratedDeriv_eq k]
    simp [hj]

end
end MasulloMB
open Set Filter MeasureTheory
open scoped SchwartzMap Topology Classical
namespace MasulloMB
noncomputable section

/-- A discrete complete collection of Fourier jet vectors admits localized continuous
biorthogonal functionals that separate all vectors. -/
theorem jet_coordinates {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ν : ι → ℝ) (hν : Function.Injective ν) (d : ι → ℕ)
    (hF : ∀ s : Set ℝ, IsCompact s → (ν ⁻¹' s).Finite)
    (v : (Σ i, Fin (d i)) → E) (hspan : Dense (Submodule.span ℂ (range v) : Set E))
    (L : 𝓢(ℝ,ℂ) → E →L[ℂ] ℂ) (w : ℂ) (hw : w ≠ 0)
    (hEval : ∀ f i, L f (v i) = iteratedDeriv i.2.val f (ν i.1)/w^i.2.val)
    (hsep : ∀ u : E, (∀ f : 𝓢(ℝ,ℂ), HasCompactSupport (f:ℝ→ℂ) → L f u = 0) → u=0) :
    ∃ ℓ : (Σ i, Fin (d i)) → E →L[ℂ] ℂ,
      (∀ i, ℓ i (v i) = 1) ∧ (∀ i j, i ≠ j → ℓ i (v j)=0) ∧
      (∀ u : E, (∀ i, ℓ i u=0) → u=0) := by
  classical
  choose f _ hf using fun i : Σ i, Fin (d i) =>
    exists_delta_test ν hν hF i.1 i.2.val (w^i.2.val)
  let ℓ (i : Σ i, Fin (d i)) := L (f i)
  have hℓ (i j : Σ i, Fin (d i)) : ℓ i (v j) = if i=j then 1 else 0 := by
    rw [show ℓ i = L (f i) from rfl,hEval,hf]
    by_cases h : i=j
    · subst j; simp [hw]
    · have hn : ¬(j.1=i.1 ∧ j.2.val=i.2.val) := by
        rintro ⟨h1,h2⟩
        cases i with | mk a t =>
          cases j with | mk b s =>
            dsimp at h1 h2
            subst b
            exact h (by rw [Fin.ext h2])
      simp [h,hn]
  refine ⟨ℓ,fun i => by simpa using hℓ i i,fun i j hij => by simpa [hij] using hℓ i j,fun u hu => hsep u (fun g hg => ?_)⟩
  let F := (hF (tsupport (g:ℝ→ℂ)) hg).toFinset
  let S : Finset (Σ i, Fin (d i)) := F.sigma fun _ => Finset.univ
  have he : L g = ∑ i ∈ S, (L g (v i)) • ℓ i := by
    apply ContinuousLinearMap.ext_on hspan
    rintro _ ⟨j,rfl⟩
    simp only [sum_apply, smul_apply, hℓ,smul_eq_mul,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq']
    by_cases hs : j ∈ S
    · simp [hs]
    · have hnot : ν j.1 ∉ tsupport (g:ℝ→ℂ) := by
        intro h
        exact hs (Finset.mem_sigma.mpr ⟨(Set.Finite.mem_toFinset _).mpr h,Finset.mem_univ j.2⟩)
      rw [if_neg hs,hEval, (notMem_tsupport_iff_eventuallyEq.mp hnot).iteratedDeriv_eq j.2.val]
      simp
  rw [he]
  simp [hu]

end
end MasulloMB
open Set Filter MeasureTheory MasulloRH MasulloSynthesis
open scoped Topology FourierTransform SchwartzMap Classical Polynomial
namespace MasulloMB
noncomputable section
abbrev Z := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
def freq (z : Z) : ℝ := -z.val.im/(2*Real.pi)
def dim (p : ℝ) (z : Z) := min (analyticOrderNatAt riemannZeta z.val) ⌈p-1/2⌉₊
abbrev J (p : ℝ) := Σ z : Z, Fin (dim p z)
def formula (p : ℝ) (i : J p) (x : ℝ) : ℂ :=
  ((1+x^2)^(-p/2) : ℝ) * ((x:ℂ)^i.2.val * Complex.exp (↑(i.1.val.im*x)*Complex.I))

theorem freq_injective : Function.Injective freq := by
  intro a b h
  have hIm : a.val.im = b.val.im := by
    dsimp [freq] at h
    field_simp [Real.pi_ne_zero] at h
    linarith
  exact Subtype.ext (Complex.ext (a.property.2.trans b.property.2.symm) hIm)

theorem freq_finite (s : Set ℝ) (hs : IsCompact s) : (freq ⁻¹' s).Finite := by
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_ball (0:ℝ)).mp hs.isBounded
  obtain ⟨B,hB⟩ := exists_gt (max R 0)
  have hb : 0 < B := lt_of_le_of_lt (le_max_right _ _) hB
  have he : ∀ᶠ z : Z in cofinite, 1/(1+(freq z)^2)<1/(1+B^2) :=
    criticalLineZero_scaled_weight_summable.tendsto_cofinite_zero.eventually_lt_const (by positivity)
  apply (Filter.mem_cofinite.mp he).subset
  intro z hz
  have hz' := hR hz
  have hn : |freq z| < B := by
    have hl : |freq z| < R := by simpa [Real.dist_eq] using hz'
    exact hl.trans (lt_of_le_of_lt (le_max_left _ _) hB)
  change ¬(1/(1+(freq z)^2) < 1/(1+B^2))
  apply not_lt_of_ge
  apply one_div_le_one_div_of_le (by positivity)
  have hs := (sq_lt_sq₀ (abs_nonneg (freq z)) hb.le).mpr hn
  nlinarith [sq_abs (freq z)]

private lemma phaseEq (ρ : Z) (x : ℝ) : -2*Real.pi*x*freq ρ = ρ.val.im*x := by
  dsimp [freq]
  field_simp [Real.pi_ne_zero]

theorem formula_phase (p : ℝ) (i : J p) (x : ℝ) :
    formula p i x = MasulloSynthesis.weight (-p/2) x *
      ((x:ℂ)^i.2.val * Complex.exp (↑(-2*Real.pi*x*freq i.1)*Complex.I)) := by
  rw [phaseEq]; rfl

theorem vectorExists (p : ℝ) (hp : 1/2<p) :
    ∃ v : J p → rationalThetaAnnihilator p, (∀ i : J p,
      ((v i).val : ℝ → ℂ) =ᵐ[volume] formula p i) ∧
      Dense (Submodule.span ℂ (range v) : Set (rationalThetaAnnihilator p)) := by
  have hmem (i : J p) : MemLp (formula p i) 2 volume := by
    have had : (i.2.val:ℝ) + 1/2 < p := by
      have h := Nat.lt_ceil.mp (i.2.isLt.trans_le (min_le_right _ _))
      linarith
    have h := (MasulloRH.JetAdmissibility.monomial_memLp_iff p (freq i.1) hp i.2.val).2 had
    refine h.ae_eq (ae_of_all _ fun x => ?_)
    simp only [MasulloRH.JetAdmissibility.mode,MasulloRH.JetAdmissibility.weight,MasulloRH.JetAdmissibility.phase,
      Polynomial.eval_pow,Polynomial.eval_X,formula]
    rw [show -2*Real.pi*(freq i.1*x) = i.1.val.im*x by rw [← phaseEq i.1 x]; ring]
  let v0 (i : J p) := (hmem i).toLp (formula p i)
  have h0 (i : J p) : (v0 i : ℝ→ℂ) =ᵐ[volume] formula p i := (hmem i).coeFn_toLp
  have hE : rationalThetaAnnihilator p = (Submodule.span ℂ (range v0)).topologicalClosure := by
    rw [(rational_theta_annihilator_jet_trace p hp).1]
    congr 2
    ext u
    constructor
    · rintro ⟨ρ,r,hr,hp',hu⟩
      let i : J p := ⟨ρ,⟨r,lt_min hr (Nat.lt_ceil.mpr (by linarith))⟩⟩
      exact ⟨i,Lp.ext ((h0 i).trans hu.symm)⟩
    · rintro ⟨i,rfl⟩
      refine ⟨i.1,i.2.val,i.2.isLt.trans_le (min_le_left _ _),?_,h0 i⟩
      have h := Nat.lt_ceil.mp (i.2.isLt.trans_le (min_le_right _ _))
      linarith
  let v (i : J p) : rationalThetaAnnihilator p := ⟨v0 i,by
    rw [hE]; exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i,rfl⟩)⟩
  refine ⟨v,h0,?_⟩
  rw [Subtype.dense_iff]
  have he : ((rationalThetaAnnihilator p).subtype '' (Submodule.span ℂ (range v) : Set _)) =
      (Submodule.span ℂ (range v0) : Set H) := by
    rw [← Submodule.map_coe,Submodule.map_span,← Set.range_comp]; rfl
  change (rationalThetaAnnihilator p : Set H) ⊆ closure ((rationalThetaAnnihilator p).subtype '' _)
  rw [he,← Submodule.topologicalClosure_coe,← hE]

def functional (p : ℝ) (f : 𝓢(ℝ,ℂ)) : rationalThetaAnnihilator p →L[ℂ] ℂ :=
  (((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ f).comp (logDistribution p))).comp
    (rationalThetaAnnihilator p).subtypeL

theorem compact_sep (p : ℝ) (hp : 1/2<p) (u : rationalThetaAnnihilator p)
    (h : ∀ f : 𝓢(ℝ,ℂ), HasCompactSupport (f:ℝ→ℂ) → functional p f u = 0) : u=0 := by
  let G : ℝ → ℂ := fun _ => 1
  have hG (x : ℝ) : AnalyticAt ℝ G x := analyticAt_const
  have hfin (x : ℝ) : analyticOrderAt G x ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (.inr (by simp [G] : G x ≠ 0))]; simp
  have hD := (sobolev_spectral_synthesis p hp G hG hfin u.val).mp (by
    intro q hq
    have hh := h q hq
    change logDistribution p u.val q = 0 at hh
    rw [logDistribution_apply] at hh
    simpa only [G,one_mul,← SchwartzMap.fourierInv_coe,MasulloSynthesis.weight] using hh)
  apply Subtype.ext
  simpa [G] using hD

end
end MasulloMB

open Set Filter MeasureTheory MasulloRH MasulloSynthesis MasulloMB
open scoped Topology SchwartzMap FourierTransform Classical

/-- The critical-line zeta jets form a countable Markushevich basis of the annihilator of
all rational real-place theta tests at the fixed polynomial Sobolev weight. -/
theorem solution (p : ℝ) (hp : 1/2<p) :
    let Z := {ρ : ℂ // riemannZeta ρ=0 ∧ ρ.re=1/2}
    let I := Σ ρ : Z, Fin (min (analyticOrderNatAt riemannZeta ρ.val) ⌈p-1/2⌉₊)
    Countable I ∧ ∃ (v : I → rationalThetaAnnihilator p) (ℓ : I → rationalThetaAnnihilator p →L[ℂ] ℂ),
      (∀ i : I, ((v i).val : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
        ((1+x^2)^(-p/2) : ℝ) * ((x:ℂ)^i.2.val * Complex.exp (↑(i.1.val.im*x)*Complex.I))) ∧
      (∀ i : I, ℓ i (v i) = 1) ∧ (∀ i j : I, i ≠ j → ℓ i (v j)=0) ∧
      Dense (Submodule.span ℂ (Set.range v) : Set (rationalThetaAnnihilator p)) ∧
      (∀ u : rationalThetaAnnihilator p, (∀ i : I, ℓ i u=0) → u=0) := by
  classical
  have hcount : Countable Z := by
    apply Set.countable_univ_iff.mp
    have hs := criticalLineZero_scaled_weight_summable.countable_support
    have hu : Function.support (fun ρ : Z => 1/(1+(-ρ.val.im/(2*Real.pi))^2)) = univ := by
      ext ρ
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      positivity
    rwa [hu] at hs
  refine ⟨inferInstanceAs (Countable (J p)),?_⟩
  obtain ⟨v,hv,hd⟩ := vectorExists p hp
  let w : ℂ := (-2:ℂ)*Real.pi*Complex.I
  have hw : w ≠ 0 := by dsimp [w]; exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hL (f : 𝓢(ℝ,ℂ)) (i : J p) : functional p f (v i) =
      iteratedDeriv i.2.val f (freq i.1)/w^i.2.val :=
    logDistribution_jet p (freq i.1) i.2.val (v i).val
      ((hv i).trans (Eventually.of_forall (formula_phase p i))) f
  obtain ⟨ℓ,hdiag,hoff,hsep⟩ := jet_coordinates freq freq_injective (dim p) freq_finite
    v hd (functional p) w hw hL (compact_sep p hp)
  exact ⟨v,ℓ,hv,hdiag,hoff,hd,hsep⟩
