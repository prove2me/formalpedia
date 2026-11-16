-- Prove2me | solution 1 for Matrix.hasDerivAt_trace_rpow_at_one
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-16T02:01:42.25384+00:00
-- url     : https://prove2.me/submissions/65a3f0d8-abbc-47dd-81f7-d506124a40e2

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TracePowerDerivativeSupport.RecoveryTracePowerSlope

def dPower (α x : ℝ) : ℝ := (max 0 x)^α*Real.log (max 0 x)

lemma dPower_eq (α x : ℝ) (hα : 0 < α) :
    dPower α x=α⁻¹*((max 0 x)^α*Real.log ((max 0 x)^α)) := by
  by_cases hx : max 0 x=0
  · simp [dPower,hx,Real.zero_rpow hα.ne']
  · have hp : 0 < max 0 x := lt_of_le_of_ne (le_max_left _ _) (Ne.symm hx)
    rw [Real.log_rpow hp]
    unfold dPower
    field_simp

lemma continuousOn_dPower : ContinuousOn (fun p : ℝ×ℝ => dPower p.1 p.2) {p | 0 < p.1} := by
  have hp : ContinuousOn (fun p : ℝ×ℝ => (max 0 p.2)^p.1) {p | 0 < p.1} :=
    (continuous_const.max continuous_snd).continuousOn.rpow continuous_fst.continuousOn (fun p hp => Or.inr hp)
  have hi : ContinuousOn (fun p : ℝ×ℝ => p.1⁻¹) {p | 0 < p.1} :=
    continuous_fst.continuousOn.inv₀ (fun p hp => ne_of_gt hp)
  apply (hi.mul (Real.continuous_mul_log.comp_continuousOn hp)).congr
  intro p hp
  exact dPower_eq p.1 p.2 hp

def clamp (t : ℝ) : ℝ := max 0 (min 1 t)
lemma clamp_mem (t : ℝ) : clamp t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_left _ _)
lemma clamp_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp t=t := by
  simp [clamp,min_eq_right ht.2,max_eq_right ht.1]
lemma exponent_pos (α t : ℝ) (hα : 0 < α) : 0 < 1+clamp t*(α-1) := by
  have ht := clamp_mem t
  by_cases ha : 1 ≤ α
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ha)]
  · have ha' : 0 < 1-α := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) ha'.le]

def slopeIntegral (α x : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, dPower (1+clamp t*(α-1)) x

lemma continuous_slopeIntegral :
    Continuous (fun p : {α : ℝ // 0 < α}×ℝ => slopeIntegral p.1 p.2) := by
  let f : ({α : ℝ // 0 < α}×ℝ) → ℝ → ℝ :=
    fun p t => dPower (1+clamp t*((p.1 : ℝ)-1)) p.2
  letI : LocallyCompactSpace {α : ℝ // 0 < α} := isOpen_Ioi.locallyCompactSpace
  have hf : Continuous f.uncurry := by
    change Continuous ((fun q : ℝ×ℝ => dPower q.1 q.2) ∘
      (fun p : ({α : ℝ // 0 < α}×ℝ)×ℝ => (1+clamp p.2*((p.1.1 : ℝ)-1),p.1.2)))
    apply continuousOn_dPower.comp_continuous
    · change Continuous (fun p : ({α : ℝ // 0 < α}×ℝ)×ℝ =>
        (1+clamp p.2*((p.1.1 : ℝ)-1),p.1.2))
      unfold clamp
      fun_prop
    · intro p
      exact exponent_pos _ _ p.1.1.property
  have hh := continuous_parametric_integral_of_continuous (μ := volume) hf (s := Icc (0 : ℝ) 1) isCompact_Icc
  have he (p : {α : ℝ // 0 < α}×ℝ) : slopeIntegral p.1 p.2=∫t in Icc (0 : ℝ) 1, f p t := by
    unfold slopeIntegral
    rw [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]
  simpa only [← he] using hh

lemma slopeIntegral_one (x : ℝ) : slopeIntegral 1 x=max 0 x*Real.log (max 0 x) := by
  simp [slopeIntegral,dPower]

lemma hasDerivAt_power (α x : ℝ) (hα : 0 < α) :
    HasDerivAt (fun s : ℝ => (max 0 x)^s) (dPower α x) α := by
  by_cases hx : max 0 x=0
  · have hd : dPower α x=0 := by simp [dPower,hx]
    rw [hd]
    apply (hasDerivAt_const α (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hα] with s hs
    simp [hx,Real.zero_rpow hs.ne']
  · have hp : 0 < max 0 x := lt_of_le_of_ne (le_max_left _ _) (Ne.symm hx)
    simpa only [dPower,mul_one,one_mul,mul_comm,id_eq] using (hasDerivAt_id α).const_rpow hp

lemma slopeIntegral_mul (α x : ℝ) (hα : 0 < α) :
    (α-1)*slopeIntegral α x=(max 0 x)^α-max 0 x := by
  have hc : ContinuousOn (fun t : ℝ => dPower (1+t*(α-1)) x) (Icc (0 : ℝ) 1) := by
    change ContinuousOn ((fun p : ℝ×ℝ => dPower p.1 p.2) ∘
      (fun t : ℝ => (1+t*(α-1),x))) (Icc (0 : ℝ) 1)
    apply continuousOn_dPower.comp (by fun_prop)
    intro t ht
    have hh := exponent_pos α t hα
    rwa [clamp_of_mem ht] at hh
  have hh := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (f := fun s : ℝ => (max 0 x)^s) (f' := fun s => dPower s x) (z₀ := (1 : ℝ)) (z₁ := α-1) hc (fun t ht =>
      hasDerivAt_power _ x (by
        have hh := exponent_pos α t hα
        rwa [clamp_of_mem ht,← smul_eq_mul] at hh))
  have he : slopeIntegral α x=∫ t in (0 : ℝ)..1, dPower (1+t*(α-1)) x := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    dsimp only
    rw [clamp_of_mem ht]
  rw [he]
  simpa only [smul_eq_mul,show (1 : ℝ)+(α-1)=α by ring,Real.rpow_one] using hh

end TracePowerDerivativeSupport.RecoveryTracePowerSlope

end

noncomputable section
open Matrix Set Filter MeasureTheory TracePowerDerivativeSupport.RecoveryTracePowerSlope
open scoped MatrixOrder ComplexOrder Topology UniformConvergence Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TracePowerDerivativeSupport.RecoveryTracePowerCFC
abbrev Pos := {α : ℝ // 0 < α}
def one : Pos := ⟨1,zero_lt_one⟩
variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

lemma continuous_slope_fixed (α : Pos) : Continuous (slopeIntegral α) := by
  exact continuous_slopeIntegral.comp (continuous_const.prodMk continuous_id)

lemma uniform_slope (M : ℝ) : Continuous (fun α : Pos => UniformOnFun.ofFun {Icc (0 : ℝ) M} (slopeIntegral α)) := by
  let F : Pos → C(Icc (0 : ℝ) M,ℝ) := fun α => ⟨_,(continuous_slope_fixed α).comp continuous_subtype_val⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_slopeIntegral.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact (ContinuousOn.continuous_domRestrict_iff_continuous_uniformOnFun
    (fun α : Pos => (continuous_slope_fixed α).continuousOn)).mp hF

lemma spectrum_subset (A : Matrix n n ℂ) (hA : A.PosSemidef) {M : ℝ} (hM : ‖A‖ ≤ M) :
    spectrum ℝ A ⊆ Icc 0 M := by
  intro x hx
  exact ⟨spectrum_nonneg_of_nonneg hA.nonneg hx,
    (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hM)⟩

lemma continuousAt_cfc_slope (H : Pos → Matrix n n ℂ)
    (hH : ContinuousAt H one) (hPSD : ∀ α, (H α).PosSemidef) :
    ContinuousAt (fun α : Pos => cfc (slopeIntegral α) (H α)) one := by
  let A := H one
  let M := ‖A‖+1
  have hM : ‖A‖ < M := by dsimp [M]; linarith
  have hnorm : ∀ᶠ α in 𝓝 one, ‖H α‖ < M := hH.norm.eventually (gt_mem_nhds hM)
  let F : Pos → ℝ →ᵤ[{Icc (0 : ℝ) M}] ℝ := fun α => UniformOnFun.ofFun {Icc (0 : ℝ) M} (slopeIntegral α)
  let pair : Pos → (ℝ →ᵤ[{Icc (0 : ℝ) M}] ℝ)×Matrix n n ℂ := fun α => (F α,H α)
  have ht : Tendsto pair (𝓝 one) (𝓝 (F one,A)) :=
    (uniform_slope M).continuousAt.tendsto.prodMk_nhds hH
  have hmem : ∀ᶠ α in 𝓝 one,
      pair α ∈ {f : ℝ →ᵤ[{Icc (0 : ℝ) M}] ℝ | ContinuousOn (UniformOnFun.toFun {Icc (0 : ℝ) M} f) (Icc (0 : ℝ) M)} ×ˢ
        {B : Matrix n n ℂ | IsSelfAdjoint B ∧ spectrum ℝ B ⊆ Icc (0 : ℝ) M} := by
    filter_upwards [hnorm] with α hα
    exact ⟨(continuous_slope_fixed α).continuousOn,(hPSD α).isHermitian,spectrum_subset _ (hPSD α) hα.le⟩
  have hbase : (F one,A) ∈
      {f : ℝ →ᵤ[{Icc (0 : ℝ) M}] ℝ | ContinuousOn (UniformOnFun.toFun {Icc (0 : ℝ) M} f) (Icc (0 : ℝ) M)} ×ˢ
        {B : Matrix n n ℂ | IsSelfAdjoint B ∧ spectrum ℝ B ⊆ Icc (0 : ℝ) M} :=
    ⟨(continuous_slope_fixed one).continuousOn,(hPSD one).isHermitian,spectrum_subset _ (hPSD one) hM.le⟩
  have hc := (continuousOn_cfc_setProd (A := Matrix n n ℂ) (𝕜 := ℝ) (s := Icc (0 : ℝ) M) isCompact_Icc).continuousWithinAt hbase
  exact hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht,hmem⟩)

end TracePowerDerivativeSupport.RecoveryTracePowerCFC

end

noncomputable section
open Matrix Set Filter MeasureTheory TracePowerDerivativeSupport.RecoveryTracePowerSlope TracePowerDerivativeSupport.RecoveryTracePowerCFC
open scoped MatrixOrder ComplexOrder Topology UniformConvergence Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TracePowerDerivativeSupport.RecoveryTracePowerDeriv
variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

lemma cfc_power_identity (A : Matrix n n ℂ) (hA : A.PosSemidef) (α : ℝ) (hα : 0 < α) :
    cfc (fun x : ℝ => x^α) A=A+(α-1) • cfc (slopeIntegral α) A := by
  have hSA : IsSelfAdjoint A := hA.isHermitian
  have hc : Continuous (slopeIntegral α) := continuous_slope_fixed ⟨α,hα⟩
  have hp : Continuous (fun x : ℝ => x^α) := Real.continuous_rpow_const hα.le
  have hh : cfc (fun x : ℝ => (α-1)*slopeIntegral α x) A=cfc (fun x : ℝ => x^α-x) A := by
    apply cfc_congr
    intro x hx
    simpa only [max_eq_right (spectrum_nonneg_of_nonneg hA.nonneg hx)] using slopeIntegral_mul α x hα
  rw [cfc_const_mul _ _ _ hc.continuousOn,cfc_sub (fun x : ℝ => x^α) (fun x : ℝ => x) A hp.continuousOn continuous_id.continuousOn,cfc_id' ℝ A] at hh
  rw [hh]
  abel

lemma trace_power_identity (A : Matrix n n ℂ) (hA : A.PosSemidef) (α : ℝ) (hα : 0 < α) :
    (cfc (fun x : ℝ => x^α) A).trace.re=A.trace.re+(α-1)*(cfc (slopeIntegral α) A).trace.re := by
  rw [cfc_power_identity A hA α hα,trace_add,trace_smul,Complex.add_re,Complex.smul_re,smul_eq_mul]

lemma continuousAt_slope_real (H : ℝ → Matrix n n ℂ) (hH : ContinuousAt H 1)
    (hPSD : ∀ α, (H α).PosSemidef) :
    ContinuousAt (fun α : ℝ => cfc (slopeIntegral α) (H α)) 1 := by
  have hval : ContinuousAt (fun α : Pos => (α : ℝ)) one := continuous_subtype_val.continuousAt
  have hH' : ContinuousAt (fun α : Pos => H α) one := hH.comp_of_eq hval rfl
  have hh := continuousAt_cfc_slope (fun α : Pos => H α) hH' (fun α => hPSD α)
  have hc : ContinuousWithinAt (fun α : ℝ => cfc (slopeIntegral α) (H α)) (Ioi 0) 1 :=
    (continuousWithinAt_iff_continuousAt_domRestrict _ zero_lt_one).mpr hh
  exact hc.continuousAt (Ioi_mem_nhds zero_lt_one)

lemma trace_slope_one (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (cfc (slopeIntegral 1) A).trace.re=(cfc (fun x : ℝ => x*Real.log x) A).trace.re := by
  congr 2
  apply cfc_congr
  intro x hx
  rw [slopeIntegral_one,max_eq_right (spectrum_nonneg_of_nonneg hA.nonneg hx)]

lemma hasDerivAt_trace_power (H : ℝ → Matrix n n ℂ) (hH : ContinuousAt H 1)
    (hPSD : ∀ α, (H α).PosSemidef) (d : ℝ)
    (hD : HasDerivAt (fun α => (H α).trace.re) d 1) :
    HasDerivAt (fun α => (cfc (fun x : ℝ => x^α) (H α)).trace.re)
      (d+(cfc (fun x : ℝ => x*Real.log x) (H 1)).trace.re) 1 := by
  let S : ℝ → ℝ := fun α => (cfc (slopeIntegral α) (H α)).trace.re
  have hS : ContinuousAt S 1 := by
    have ht : Continuous (fun A : Matrix n n ℂ => A.trace.re) := by fun_prop
    exact ht.continuousAt.comp (continuousAt_slope_real H hH hPSD)
  have hlim := hD.tendsto_slope.add (hS.tendsto.mono_left nhdsWithin_le_nhds)
  have hbase : S 1=(cfc (fun x : ℝ => x*Real.log x) (H 1)).trace.re := trace_slope_one _ (hPSD 1)
  rw [hbase] at hlim
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply hlim.congr'
  have hpos : ∀ᶠ α : ℝ in 𝓝[≠] 1, 0 < α :=
    (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,self_mem_nhdsWithin] with α hα hne
  simp only [slope_def_field]
  rw [trace_power_identity _ (hPSD α) α hα,trace_power_identity _ (hPSD 1) 1 zero_lt_one]
  dsimp [S]
  have hne' : α-1 ≠ 0 := sub_ne_zero.mpr hne
  field_simp [hne']
  <;> ring

end TracePowerDerivativeSupport.RecoveryTracePowerDeriv

end

open Matrix
open scoped MatrixOrder ComplexOrder Topology Matrix.Norms.L2Operator

set_option autoImplicit false


theorem solution {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : ℝ → Matrix n n ℂ) (hH : ContinuousAt H 1)
    (hPSD : ∀ α, (H α).PosSemidef) (d : ℝ)
    (hD : HasDerivAt (fun α => (H α).trace.re) d 1) :
    HasDerivAt (fun α => (cfc (fun x : ℝ => x^α) (H α)).trace.re)
      (d+(cfc (fun x : ℝ => x*Real.log x) (H 1)).trace.re) 1 := by
  exact TracePowerDerivativeSupport.RecoveryTracePowerDeriv.hasDerivAt_trace_power H hH hPSD d hD