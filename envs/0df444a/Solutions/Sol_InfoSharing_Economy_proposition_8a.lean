-- Prove2me | solution 1 for InfoSharing.Economy.proposition_8a
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T14:33:35.558007+00:00
-- url     : https://prove2.me/submissions/df08166d-f3e9-45de-b3e5-f03fd4b5dc1c

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSequentialSPE
import Definitions.Def_InfoSharing_Economy_NoContractOptN
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InfoSharing_Shared_PayoffTable
import Definitions.Def_InfoSharing_Shared_ClosedForms
import Definitions.Def_InfoSharing_Shared_IsPricingEq
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
import Definitions.Def_InfoSharing_Economy_IsConcurrentOutcome
set_option maxHeartbeats 3000000
open MeasureTheory Filter
open InfoSharing.Shared
namespace InfoEconBase
noncomputable section
theorem cond_mul_integral {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z W : Ω→ℝ) (hZ : Measurable Z) (hW : MemLp W 2 μ)
    (f : ℝ→ℝ) (hmf : Measurable f) (hif : MemLp (fun ω=> f (Z ω)) 2 μ)
    (β : ℝ) (hc : μ[W | MeasurableSpace.comap Z inferInstance] =ᵐ[μ] fun ω=> β*Z ω) :
    (∫ ω,f (Z ω)*W ω ∂μ)=β*(∫ ω,f (Z ω)*Z ω ∂μ) := by
  let m := MeasurableSpace.comap Z inferInstance
  have hm : m ≤ mΩ := hZ.comap_le
  have hfm : StronglyMeasurable[m] (fun ω=> f (Z ω)) :=
    (hmf.comp (comap_measurable Z)).stronglyMeasurable
  have hp := condExp_mul_of_stronglyMeasurable_left hfm (hif.integrable_mul hW)
    (hW.integrable (by norm_num))
  calc
    _ = ∫ ω,(μ[(fun ω=> f (Z ω))*W | m]) ω ∂μ := by
      convert! (integral_condExp (μ:=μ) (f:=(fun ω=> f (Z ω))*W) hm).symm using 1
    _ = ∫ ω,f (Z ω)*(β*Z ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hp,hc] with ω hp hc
      change (μ[W | m]) ω=β*Z ω at hc
      simpa only [Pi.mul_apply,hc] using hp
    _ = β*(∫ ω,f (Z ω)*Z ω ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      ring

theorem signal_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (σ β : ℝ) (h : IsSignalModel μ θ Y σ β) :
    (∫ ω,Y ω ∂μ)=0 ∧ (∫ ω,θ ω*Y ω ∂μ)=σ^2 ∧
    β*(∫ ω,Y ω^2 ∂μ)=σ^2 ∧ 0< β := by
  obtain ⟨hprob,hmθ,hmY,hiθ,hiY,hmean,hvar,hσ,hcY,hcθ⟩ := h
  haveI := hprob
  have hY : (∫ ω,Y ω ∂μ)=0 := by
    calc
      _ = ∫ ω,(μ[Y | MeasurableSpace.comap θ inferInstance]) ω ∂μ := (integral_condExp hmθ.comap_le).symm
      _ = ∫ ω,θ ω ∂μ := integral_congr_ae hcY
      _ = 0 := hmean
  have hcross : (∫ ω,θ ω*Y ω ∂μ)=σ^2 := by
    have hh := cond_mul_integral μ θ Y hmθ hiY id measurable_id hiθ 1 (by simpa using hcY)
    simpa only [id_eq,one_mul,← sq,hvar] using hh
  have hbeta : β*(∫ ω,Y ω^2 ∂μ)=σ^2 := by
    have hh := cond_mul_integral μ Y θ hmY hiθ id measurable_id hiY β hcθ
    have hcomm : (∫ ω,Y ω*θ ω ∂μ)=(∫ ω,θ ω*Y ω ∂μ) := by congr 1;funext ω;ring
    simpa only [id_eq,← sq,hcomm,hcross] using hh.symm
  have hβ : 0< β := by
    have hnn : 0≤∫ ω,Y ω^2 ∂μ := integral_nonneg (fun ω=> sq_nonneg _)
    have hσ2 : 0< σ^2 := sq_pos_of_pos hσ
    nlinarith
  exact ⟨hY,hcross,hbeta,hβ⟩

theorem residual_orthogonal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (σ β : ℝ) (h : IsSignalModel μ θ Y σ β)
    (f : ℝ→ℝ) (hmf : Measurable f) (hif : MemLp (fun ω=> f (Y ω)) 2 μ) :
    (∫ ω,f (Y ω)*(θ ω-β*Y ω) ∂μ)=0 := by
  obtain ⟨hprob,hmθ,hmY,hiθ,hiY,hmean,hvar,hσ,hcY,hcθ⟩ := h
  haveI := hprob
  have hh := cond_mul_integral μ Y θ hmY hiθ f hmf hif β hcθ
  have hθ : Integrable (fun ω=> f (Y ω)*θ ω) μ := hif.integrable_mul hiθ
  have hY : Integrable (fun ω=> f (Y ω)*Y ω) μ := hif.integrable_mul hiY
  calc
    _ = ∫ ω,f (Y ω)*θ ω-β*(f (Y ω)*Y ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = 0 := by rw [integral_sub hθ (hY.const_mul β),integral_const_mul,hh];ring

theorem retailer_gap (a φ m : ℝ) (w p : Fin 2→ℝ) :
    retailerInterim a φ w m (fun i=>(a+m+w i)/2)-retailerInterim a φ w m p =
      (p 0-(a+m+w 0)/2)^2+(p 1-(a+m+w 1)/2)^2+
        φ*((p 0-(a+m+w 0)/2)-(p 1-(a+m+w 1)/2))^2 := by
  simp only [retailerInterim,Fin.sum_univ_two,other]
  norm_num
  ring

theorem retailer_br (a φ β : ℝ) (hφ : 0< φ)
    (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) :
    IsRetailerBR a φ β ρ ↔ ∀ w y i,ρ w y i=(a+β*y+w i)/2 := by
  constructor
  · intro h w y i
    have hh := h w y (fun i=>(a+β*y+w i)/2)
    have hg := retailer_gap a φ (β*y) w (ρ w y)
    have hsq := mul_nonneg hφ.le (sq_nonneg ((ρ w y 0-(a+β*y+w 0)/2)-(ρ w y 1-(a+β*y+w 1)/2)))
    have h0 := sq_nonneg (ρ w y 0-(a+β*y+w 0)/2)
    have h1 := sq_nonneg (ρ w y 1-(a+β*y+w 1)/2)
    fin_cases i
    · change ρ w y 0=(a+β*y+w 0)/2
      nlinarith
    · change ρ w y 1=(a+β*y+w 1)/2
      nlinarith
  · intro h w y p
    have hρ : ρ w y=(fun i=>(a+β*y+w i)/2) := funext (h w y)
    rw [hρ]
    have hg := retailer_gap a φ (β*y) w p
    have hsq := mul_nonneg hφ.le (sq_nonneg ((p 0-(a+β*y+w 0)/2)-(p 1-(a+β*y+w 1)/2)))
    nlinarith [sq_nonneg (p 0-(a+β*y+w 0)/2),sq_nonneg (p 1-(a+β*y+w 1)/2)]


def priceGradient (a b c φ β : ℝ) (f : Fin 2→ℝ→ℝ) (i : Fin 2) (y : ℝ) : ℝ :=
  (1+c*(1+φ))*((a+β*y-(1+φ)*f i y+φ*f (other i) y)/2)-(1+φ)/2*(f i y-b)

theorem other_ne (i : Fin 2) : other i≠i := by fin_cases i <;> decide

theorem demand_lp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (θ Y : Ω→ℝ) (hiθ : MemLp θ 2 μ) (hiY : MemLp Y 2 μ)
    (a φ β : ℝ) (hφ : 0< φ) (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) (hr : IsRetailerBR a φ β ρ)
    (f : Fin 2→ℝ→ℝ) (hif : ∀ i,MemLp (fun ω=> f i (Y ω)) 2 μ) (i : Fin 2) :
    MemLp (demand a φ θ Y ρ f i) 2 μ := by
  have hρ := (retailer_br a φ β hφ ρ).mp hr
  have hp (j : Fin 2) : MemLp (fun ω=>(a+β*Y ω+f j (Y ω))/2) 2 μ := by
    convert! (((memLp_const a).add (hiY.const_mul β)).add (hif j)).mul_const (1/2:ℝ) using 1
    funext ω
    simp only [Pi.add_apply]
    ring
  convert! (((memLp_const a).add hiθ).sub ((hp i).const_mul (1+φ))).add
    ((hp (other i)).const_mul φ) using 1
  funext ω
  simp only [demand,hρ,Pi.add_apply,Pi.sub_apply]

theorem manufacturer_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (θ Y : Ω→ℝ) (hiθ : MemLp θ 2 μ) (hiY : MemLp Y 2 μ)
    (a b c φ β : ℝ) (hφ : 0< φ) (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) (hr : IsRetailerBR a φ β ρ)
    (f : Fin 2→ℝ→ℝ) (hif : ∀ i,MemLp (fun ω=> f i (Y ω)) 2 μ) (i : Fin 2) :
    Integrable (fun ω=>(f i (Y ω)-b)*demand a φ θ Y ρ f i ω-c*(demand a φ θ Y ρ f i ω)^2) μ := by
  have hd := demand_lp μ θ Y hiθ hiY a φ β hφ ρ hr f hif i
  exact ((hif i).sub (memLp_const b) |>.integrable_mul hd).sub (hd.integrable_sq.const_mul c)

theorem gradient_lp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω→ℝ) (hiY : MemLp Y 2 μ)
    (a b c φ β : ℝ) (f : Fin 2→ℝ→ℝ) (hif : ∀ i,MemLp (fun ω=> f i (Y ω)) 2 μ) (i : Fin 2) :
    MemLp (fun ω=> priceGradient a b c φ β f i (Y ω)) 2 μ := by
  have hnum : MemLp (fun ω=> a+β*Y ω-(1+φ)*f i (Y ω)+φ*f (other i) (Y ω)) 2 μ :=
    (((memLp_const a).add (hiY.const_mul β)).sub ((hif i).const_mul (1+φ))).add
      ((hif (other i)).const_mul φ)
  convert! ((hnum.mul_const (1/2:ℝ)).const_mul (1+c*(1+φ))).sub
    (((hif i).sub (memLp_const b)).const_mul ((1+φ)/2)) using 1
  funext ω
  simp only [priceGradient,Pi.sub_apply]
  ring

theorem manufacturer_gain {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hφ : 0< φ) (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) (hr : IsRetailerBR a φ β ρ)
    (f : Fin 2→ℝ→ℝ) (hmf : ∀ i,Measurable (f i))
    (hif : ∀ i,MemLp (fun ω=> f i (Y ω)) 2 μ) (i : Fin 2)
    (g : ℝ→ℝ) (hmg : Measurable g) (hig : MemLp (fun ω=> g (Y ω)) 2 μ) :
    manufacturerProfit μ θ Y a b c φ ρ (Function.update f i g) i-
      manufacturerProfit μ θ Y a b c φ ρ f i =
    (∫ ω,(g (Y ω)-f i (Y ω))*priceGradient a b c φ β f i (Y ω) ∂μ)-
      ((1+φ)*(2+c*(1+φ))/4)*(∫ ω,(g (Y ω)-f i (Y ω))^2 ∂μ) := by
  classical
  have hmodel' := hmodel
  obtain ⟨hprob,hmθ,hmY,hiθ,hiY,hmean,hvar,hσ,hcY,hcθ⟩ := hmodel
  haveI := hprob
  have hρ := (retailer_br a φ β hφ ρ).mp hr
  have hifu (j : Fin 2) : MemLp (fun ω=> Function.update f i g j (Y ω)) 2 μ := by
    by_cases h : j=i
    · subst j;simpa using hig
    · simpa [Function.update_of_ne h] using hif j
  have hiF := manufacturer_integrable μ θ Y hiθ hiY a b c φ β hφ ρ hr f hif i
  have hiG := manufacturer_integrable μ θ Y hiθ hiY a b c φ β hφ ρ hr (Function.update f i g) hifu i
  have hd : MemLp (fun ω=> g (Y ω)-f i (Y ω)) 2 μ := hig.sub (hif i)
  have hgrad := gradient_lp μ Y hiY a b c φ β f hif i
  have hprod : Integrable (fun ω=>(g (Y ω)-f i (Y ω))*priceGradient a b c φ β f i (Y ω)) μ :=
    hd.integrable_mul hgrad
  have hsq := hd.integrable_sq
  have hrprod : Integrable (fun ω=>(g (Y ω)-f i (Y ω))*(θ ω-β*Y ω)) μ :=
    hd.integrable_mul (hiθ.sub (hiY.const_mul β))
  have horth := residual_orthogonal μ θ Y σ β hmodel' (fun y=> g y-f i y) (hmg.sub (hmf i)) hd
  let κ := (1+φ)*(2+c*(1+φ))/4
  calc
    _ = ∫ ω,((Function.update f i g i (Y ω)-b)*demand a φ θ Y ρ (Function.update f i g) i ω-
          c*(demand a φ θ Y ρ (Function.update f i g) i ω)^2)-
        ((f i (Y ω)-b)*demand a φ θ Y ρ f i ω-c*(demand a φ θ Y ρ f i ω)^2) ∂μ := by
      rw [integral_sub hiG hiF]
      rfl
    _ = ∫ ω,((g (Y ω)-f i (Y ω))*priceGradient a b c φ β f i (Y ω)-
        κ*(g (Y ω)-f i (Y ω))^2)+(1+c*(1+φ))*((g (Y ω)-f i (Y ω))*(θ ω-β*Y ω)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [demand,hρ,Function.update_self,Function.update_of_ne (other_ne i),priceGradient]
      dsimp [κ]
      ring
    _ = _ := by
      have hint : Integrable (fun ω=>(g (Y ω)-f i (Y ω))*priceGradient a b c φ β f i (Y ω)-κ*(g (Y ω)-f i (Y ω))^2) μ :=
        hprod.sub (hsq.const_mul κ)
      rw [integral_add hint (hrprod.const_mul (1+c*(1+φ))),
        integral_sub hprod (hsq.const_mul κ),integral_const_mul,integral_const_mul,horth]
      simp only [mul_zero,add_zero]
      rfl

def candidatePrices (a b c φ β : ℝ) (X : Fin 2→Status) : Fin 2→ℝ→ℝ :=
  fun i y=> wbar a b c φ+alphaW c φ β X i*y

theorem status_ne : Status.informed≠Status.uninformed := by decide
theorem status_ne' : Status.uninformed≠Status.informed := by decide
theorem numInformed_vec (s t : Status) :
    numInformed ![s,t]=(if s=Status.informed then 1 else 0)+(if t=Status.informed then 1 else 0) := by
  cases s <;> cases t <;> decide

theorem alphaW_uninformed (c φ β : ℝ) (X : Fin 2→Status) (i : Fin 2)
    (h : X i=Status.uninformed) : alphaW c φ β X i=0 := by
  have hX : X=![X 0,X 1] := by funext j;fin_cases j <;> rfl
  rw [hX] at h ⊢
  cases h0 : X 0 <;> cases h1 : X 1 <;> fin_cases i <;>
    simp [alphaW,numInformed_vec,status_ne,status_ne',h0,h1] at h ⊢

theorem candidate_informed (a b c φ β : ℝ) (hc : 0<2+(1+φ)*c) (hφ : 0< φ)
    (X : Fin 2→Status) (i : Fin 2) (hi : X i=Status.informed) (y : ℝ) :
    priceGradient a b c φ β (candidatePrices a b c φ β X) i y=0 := by
  have h1 : 0<1+φ := by linarith
  have h2 : 0<2+(1+φ)*c := hc
  have h3 : 0<2+φ+(1+φ)*c := by linarith
  have h4 : 2+c+c*φ+φ≠0 := by nlinarith
  have h5 : 2+c+c*φ≠0 := by nlinarith
  have hX : X=![X 0,X 1] := by funext j;fin_cases j <;> rfl
  rw [hX] at hi ⊢
  cases h0 : X 0 <;> cases h1' : X 1 <;> fin_cases i <;>
    simp [priceGradient,candidatePrices,alphaW,numInformed_vec,status_ne,status_ne',other,h0,h1'] at hi ⊢
  all_goals unfold wbar;field_simp [h1.ne',h2.ne',h3.ne',h4,h5] <;> ring_nf <;> field_simp [h4,h5] <;> ring

theorem candidate_gradient_linear (a b c φ β : ℝ) (hc : 0<2+(1+φ)*c) (hφ : 0< φ)
    (X : Fin 2→Status) (i : Fin 2) (y : ℝ) :
    priceGradient a b c φ β (candidatePrices a b c φ β X) i y =
      y*priceGradient a b c φ β (candidatePrices a b c φ β X) i 1 := by
  have h3 : 0<2+φ+(1+φ)*c := by linarith
  have h4 : 2+c+c*φ+φ≠0 := by nlinarith
  have h5 : 2+c+c*φ≠0 := by nlinarith
  unfold priceGradient candidatePrices wbar
  field_simp [h3.ne',h4,h5]
  ring_nf
  field_simp [h4,h5]
  ring

theorem candidate_admissible {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω→ℝ) (hiY : MemLp Y 2 μ)
    (a b c φ β : ℝ) (X : Fin 2→Status) (i : Fin 2) :
    IsAdmissible μ Y (X i) (candidatePrices a b c φ β X i) := by
  refine ⟨by unfold candidatePrices;fun_prop,?_,?_⟩
  · change MemLp (fun ω=> wbar a b c φ+alphaW c φ β X i*Y ω) 2 μ
    exact (memLp_const (wbar a b c φ)).add (hiY.const_mul (alphaW c φ β X i))
  · intro h
    refine ⟨wbar a b c φ,fun y=>?_⟩
    simp only [candidatePrices,alphaW_uninformed c φ β X i h,mul_zero,zero_mul,add_zero]

theorem candidate_stationary {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω→ℝ) (hY : (∫ ω,Y ω ∂μ)=0)
    (a b c φ β : ℝ) (hc : 0<2+(1+φ)*c) (hφ : 0< φ) (X : Fin 2→Status) (i : Fin 2)
    (g : ℝ→ℝ) (hg : IsAdmissible μ Y (X i) g) :
    (∫ ω,(g (Y ω)-candidatePrices a b c φ β X i (Y ω))*
      priceGradient a b c φ β (candidatePrices a b c φ β X) i (Y ω) ∂μ)=0 := by
  by_cases hi : X i=Status.informed
  · simp only [candidate_informed a b c φ β hc hφ X i hi,mul_zero,integral_zero]
  · have hi : X i=Status.uninformed := by cases h : X i <;> simp_all
    obtain ⟨k,hk⟩ := hg.2.2 hi
    have heq : (fun ω=>(g (Y ω)-candidatePrices a b c φ β X i (Y ω))*
        priceGradient a b c φ β (candidatePrices a b c φ β X) i (Y ω)) =
        (fun ω=>((k-wbar a b c φ)*priceGradient a b c φ β (candidatePrices a b c φ β X) i 1)*Y ω) := by
      funext ω
      rw [candidate_gradient_linear a b c φ β hc hφ X i (Y ω),hk]
      simp only [candidatePrices,alphaW_uninformed c φ β X i hi,zero_mul,add_zero]
      ring
    rw [heq,integral_const_mul,hY,mul_zero]

theorem candidate_equilibrium {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hc : 0<2+(1+φ)*c) (hφ : 0< φ) (X : Fin 2→Status) :
    IsPricingEq μ θ Y a b c φ β X (fun w y i=>(a+β*y+w i)/2) (candidatePrices a b c φ β X) := by
  haveI := hmodel.1
  have hiY : MemLp Y 2 μ := hmodel.2.2.2.2.1
  have hY := (signal_moments μ θ Y σ β hmodel).1
  have hr : IsRetailerBR a φ β (fun w y i=>(a+β*y+w i)/2) :=
    (retailer_br a φ β hφ _).mpr (fun _ _ _=> rfl)
  have had (i : Fin 2) := candidate_admissible μ Y hiY a b c φ β X i
  refine ⟨hr,had,?_⟩
  intro i g hg
  have hgain := manufacturer_gain μ θ Y a b c φ σ β hmodel hφ _ hr _
    (fun j=>(had j).1) (fun j=>(had j).2.1) i g hg.1 hg.2.1
  rw [candidate_stationary μ Y hY a b c φ β hc hφ X i g hg] at hgain
  have hk : 0≤(1+φ)*(2+c*(1+φ))/4 := by
    have hh : 0<2+c*(1+φ) := by nlinarith
    positivity
  have hs : 0≤∫ ω,(g (Y ω)-candidatePrices a b c φ β X i (Y ω))^2 ∂μ :=
    integral_nonneg (fun ω=> sq_nonneg _)
  nlinarith

theorem quad_linear_zero (l k : ℝ) (h : ∀ t : ℝ,t*l-t^2*k≤0) : l=0 := by
  have hmax : IsLocalMax (fun t : ℝ=> t*l-t^2*k) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa using h t
  have hd : HasDerivAt (fun t : ℝ=> t*l-t^2*k) l 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const l).sub (((hasDerivAt_id (0:ℝ)).pow 2).mul_const k) using 1 <;> norm_num
  exact hd.deriv.symm.trans hmax.deriv_eq_zero

theorem admissible_variation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω→ℝ) (s : Status) (f g : ℝ→ℝ) (hf : IsAdmissible μ Y s f)
    (hg : IsAdmissible μ Y s g) (t : ℝ) : IsAdmissible μ Y s (fun y=> f y+t*(g y-f y)) := by
  refine ⟨hf.1.add ((hg.1.sub hf.1).const_mul t),hf.2.1.add ((hg.2.1.sub hf.2.1).const_mul t),?_⟩
  intro hs
  obtain ⟨a,ha⟩ := hf.2.2 hs
  obtain ⟨b,hb⟩ := hg.2.2 hs
  exact ⟨a+t*(b-a),fun y=> by dsimp;rw [ha,hb]⟩

theorem equilibrium_first_order {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hφ : 0< φ) (X : Fin 2→Status) (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) (f : Fin 2→ℝ→ℝ)
    (heq : IsPricingEq μ θ Y a b c φ β X ρ f) (i : Fin 2) (g : ℝ→ℝ)
    (hg : IsAdmissible μ Y (X i) g) :
    (∫ ω,(g (Y ω)-f i (Y ω))*priceGradient a b c φ β f i (Y ω) ∂μ)=0 := by
  apply quad_linear_zero _ (((1+φ)*(2+c*(1+φ))/4)*(∫ ω,(g (Y ω)-f i (Y ω))^2 ∂μ))
  intro t
  let gt : ℝ→ℝ := fun y=> f i y+t*(g y-f i y)
  have hgt := admissible_variation μ Y (X i) (f i) g (heq.2.1 i) hg t
  have hm := heq.2.2 i gt hgt
  have hh := manufacturer_gain μ θ Y a b c φ σ β hmodel hφ ρ heq.1 f
    (fun j=>(heq.2.1 j).1) (fun j=>(heq.2.1 j).2.1) i gt hgt.1 hgt.2.1
  have hlin : (∫ ω,(gt (Y ω)-f i (Y ω))*priceGradient a b c φ β f i (Y ω) ∂μ)=
      t*(∫ ω,(g (Y ω)-f i (Y ω))*priceGradient a b c φ β f i (Y ω) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [gt]
    ring
  have hsq : (∫ ω,(gt (Y ω)-f i (Y ω))^2 ∂μ)=t^2*(∫ ω,(g (Y ω)-f i (Y ω))^2 ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [gt]
    ring
  rw [hlin,hsq] at hh
  nlinarith

theorem candidate_retail (a b c φ β : ℝ) (hc : 0<2+(1+φ)*c) (hφ : 0< φ)
    (X : Fin 2→Status) (i : Fin 2) (y : ℝ) :
    (a+β*y+candidatePrices a b c φ β X i y)/2=pbar a b c φ+alphaP c φ β X i*y := by
  have h1 : 0<1+φ := by linarith
  have h2 : 0<2+(1+φ)*c := hc
  have h3 : 0<2+φ+(1+φ)*c := by linarith
  have h4 : 2+c+c*φ+φ≠0 := by nlinarith
  have h5 : 2+c+c*φ≠0 := by nlinarith
  have hX : X=![X 0,X 1] := by funext j;fin_cases j <;> rfl
  rw [hX]
  cases h0 : X 0 <;> cases h1' : X 1 <;> fin_cases i <;>
    simp [candidatePrices,alphaW,alphaP,numInformed_vec,status_ne,status_ne',h0,h1']
  all_goals unfold wbar pbar;field_simp [h1.ne',h2.ne',h3.ne',h4,h5] <;> ring_nf <;> field_simp [h4,h5] <;> ring



theorem equilibrium_gradient_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hφ : 0< φ) (X : Fin 2→Status) (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) (f : Fin 2→ℝ→ℝ)
    (heq : IsPricingEq μ θ Y a b c φ β X ρ f) (i : Fin 2) (hi : X i=Status.informed) :
    (fun ω=> priceGradient a b c φ β f i (Y ω)) =ᵐ[μ] 0 := by
  haveI:=hmodel.1
  have hiY:MemLp Y 2 μ:=hmodel.2.2.2.2.1
  have hmG : Measurable (priceGradient a b c φ β f i) := by
    unfold priceGradient
    have hm₁:Measurable (f i):=(heq.2.1 i).1
    have hm₂:Measurable (f (other i)):=(heq.2.1 (other i)).1
    fun_prop
  have hiG:=gradient_lp μ Y hiY a b c φ β f (fun j=>(heq.2.1 j).2.1) i
  have hg : IsAdmissible μ Y (X i) (fun y=> f i y+priceGradient a b c φ β f i y) := by
    refine ⟨(heq.2.1 i).1.add hmG,(heq.2.1 i).2.1.add hiG,?_⟩
    intro h;exact (status_ne (hi.symm.trans h)).elim
  have hfo:=equilibrium_first_order μ θ Y a b c φ σ β hmodel hφ X ρ f heq i _ hg
  have hs : (∫ ω,(priceGradient a b c φ β f i (Y ω))^2 ∂μ)=0 := by
    simpa only [add_sub_cancel_left,←sq] using hfo
  have hz: (fun ω=>(priceGradient a b c φ β f i (Y ω))^2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω=> sq_nonneg _) hiG.integrable_sq).mp hs
  filter_upwards [hz] with ω hω
  exact sq_eq_zero_iff.mp hω

theorem equilibrium_gradient_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hφ : 0< φ) (X : Fin 2→Status) (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) (f : Fin 2→ℝ→ℝ)
    (heq : IsPricingEq μ θ Y a b c φ β X ρ f) (i : Fin 2) :
    (∫ ω,priceGradient a b c φ β f i (Y ω) ∂μ)=0 := by
  haveI:=hmodel.1
  have hg : IsAdmissible μ Y (X i) (fun y=> f i y+1) := by
    refine ⟨(heq.2.1 i).1.add measurable_const,(heq.2.1 i).2.1.add (memLp_const 1),?_⟩
    intro h
    obtain ⟨k,hk⟩:=(heq.2.1 i).2.2 h
    exact ⟨k+1,fun y=> by dsimp;rw [hk]⟩
  have hfo:=equilibrium_first_order μ θ Y a b c φ σ β hmodel hφ X ρ f heq i _ hg
  simpa only [add_sub_cancel_left,one_mul] using hfo

theorem equilibrium_unique {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hc : 0<2+(1+φ)*c) (hφ : 0< φ)
    (hns : 2+3*φ+(1+φ)*(1+2*φ)*c≠0)
    (X : Fin 2→Status) (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) (f : Fin 2→ℝ→ℝ)
    (heq : IsPricingEq μ θ Y a b c φ β X ρ f) :
    ∀ i,(fun ω=> f i (Y ω)) =ᵐ[μ] (fun ω=> candidatePrices a b c φ β X i (Y ω)) := by
  haveI:=hmodel.1
  let F:=candidatePrices a b c φ β X
  let d : Fin 2→Ω→ℝ:=fun i ω=> f i (Y ω)-F i (Y ω)
  let A:=(1+φ)*(2+c*(1+φ))/2
  let γ:=φ*(1+c*(1+φ))/2
  have hA:0< A:=by
    dsimp [A]
    have hh:0<2+c*(1+φ):=by nlinarith
    positivity
  have hm:0< A-γ:=by dsimp [A,γ];nlinarith
  have hp:A+γ≠0:=by dsimp [A,γ];intro hh;apply hns;nlinarith
  have solve (x y : ℝ) (hx:A*x=γ*y) (hy:A*y=γ*x) : x=0 ∧ y=0 := by
    have hh:(A-γ)*(x+y)=0:=by nlinarith
    have hj:(A+γ)*(x-y)=0:=by nlinarith
    have hs:= (mul_eq_zero.mp hh).resolve_left hm.ne'
    have hd:= (mul_eq_zero.mp hj).resolve_left hp
    constructor <;> linarith
  have hiY:MemLp Y 2 μ:=hmodel.2.2.2.2.1
  have hY: (∫ ω,Y ω ∂μ)=0:=(signal_moments μ θ Y σ β hmodel).1
  have had (i : Fin 2) : IsAdmissible μ Y (X i) (F i):=candidate_admissible μ Y hiY a b c φ β X i
  have hid (i : Fin 2) : MemLp (d i) 2 μ:= (heq.2.1 i).2.1.sub (had i).2.1
  have hidI (i : Fin 2) : Integrable (d i) μ:=(hid i).integrable (by norm_num)
  have hgd (i : Fin 2) (ω : Ω) : priceGradient a b c φ β f i (Y ω)-
      priceGradient a b c φ β F i (Y ω) = -A*d i ω+γ*d (other i) ω := by
    dsimp [priceGradient,d,A,γ];ring
  have hmean (i : Fin 2) : A*(∫ ω,d i ω ∂μ)=γ*(∫ ω,d (other i) ω ∂μ) := by
    have hf:=equilibrium_gradient_mean μ θ Y a b c φ σ β hmodel hφ X ρ f heq i
    have hF:(∫ ω,priceGradient a b c φ β F i (Y ω) ∂μ)=0 := by
      calc
        _ = ∫ ω,Y ω*priceGradient a b c φ β F i 1 ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun ω=> candidate_gradient_linear a b c φ β hc hφ X i (Y ω))
        _ = 0 := by rw [integral_mul_const,hY,zero_mul]
    have hh:(∫ ω,priceGradient a b c φ β f i (Y ω)-priceGradient a b c φ β F i (Y ω) ∂μ)=0 := by
      rw [integral_sub ((gradient_lp μ Y hiY a b c φ β f (fun j=>(heq.2.1 j).2.1) i).integrable (by norm_num))
        ((gradient_lp μ Y hiY a b c φ β F (fun j=>(had j).2.1) i).integrable (by norm_num)),hf,hF,sub_self]
    simp_rw [hgd] at hh
    rw [integral_add ((hidI i).const_mul (-A)) ((hidI (other i)).const_mul γ),integral_const_mul,integral_const_mul] at hh
    linarith
  have h0:=hmean 0
  have h1:=hmean 1
  norm_num [other] at h0 h1
  have hmeans:=solve (∫ ω,d 0 ω ∂μ) (∫ ω,d 1 ω ∂μ) h0 h1
  have hu (i : Fin 2) (hi : X i=Status.uninformed) : ∀ ω,d i ω=0 := by
    obtain ⟨k,hk⟩:=(heq.2.1 i).2.2 hi
    have hd (ω : Ω) : d i ω=k-wbar a b c φ := by
      dsimp [d,F,candidatePrices];rw [hk,alphaW_uninformed c φ β X i hi];ring
    have hh:(∫ ω,d i ω ∂μ)=0:=by fin_cases i;exact hmeans.1;exact hmeans.2
    simp_rw [hd] at hh
    intro ω
    rw [hd]
    simpa using hh
  have hi (i : Fin 2) (hii : X i=Status.informed) :
      (fun ω=> A*d i ω) =ᵐ[μ] (fun ω=> γ*d (other i) ω) := by
    have hg:=equilibrium_gradient_zero μ θ Y a b c φ σ β hmodel hφ X ρ f heq i hii
    filter_upwards [hg] with ω hω
    have hh:=hgd i ω
    rw [show priceGradient a b c φ β F i (Y ω)=0 from candidate_informed a b c φ β hc hφ X i hii (Y ω)] at hh
    change priceGradient a b c φ β f i (Y ω)=0 at hω
    linarith
  have hd (i : Fin 2) : (d i) =ᵐ[μ] 0 := by
    cases hx0 : X 0 <;> cases hx1 : X 1
    · filter_upwards [hi 0 hx0,hi 1 hx1] with ω h₀ h₁
      norm_num [other] at h₀ h₁
      have hz:=solve (d 0 ω) (d 1 ω) h₀ h₁
      fin_cases i;exact hz.1;exact hz.2
    · filter_upwards [hi 0 hx0] with ω h₀
      have h₁:=hu 1 hx1 ω
      norm_num [other] at h₀
      have hz:d 0 ω=0:=by nlinarith
      fin_cases i;exact hz;exact h₁
    · filter_upwards [hi 1 hx1] with ω h₁
      have h₀:=hu 0 hx0 ω
      norm_num [other] at h₁
      have hz:d 1 ω=0:=by nlinarith
      fin_cases i;exact h₀;exact hz
    · exact Eventually.of_forall (fun ω=> by fin_cases i;exact hu 0 hx0 ω;exact hu 1 hx1 ω)
  intro i
  filter_upwards [hd i] with ω hω
  exact sub_eq_zero.mp hω
theorem quadratic_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (A B C D E F : ℝ) :
    (∫ ω,A+B*Y ω+C*θ ω+D*(Y ω)^2+E*(Y ω*θ ω)+F*(θ ω)^2 ∂μ)=
      A+(D/β+E+F)*σ^2 := by
  have hm := signal_moments μ θ Y σ β hmodel
  obtain ⟨hprob,hmθ,hmY,hiθ,hiY,hmean,hvar,hσ,hcY,hcθ⟩ := hmodel
  haveI := hprob
  have hYmean := hm.1
  have hβ := hm.2.2.2
  have hYY : (∫ ω,(Y ω)^2 ∂μ)=σ^2/β :=
    (eq_div_iff hβ.ne').mpr (by simpa only [mul_comm] using hm.2.2.1)
  have hYθ : (∫ ω,Y ω*θ ω ∂μ)=σ^2 := by
    calc
      _ = ∫ ω,θ ω*Y ω ∂μ := by congr 1;funext ω;ring
      _ = σ^2 := hm.2.1
  let f : Fin 6→Ω→ℝ := ![(fun _=> A),(fun ω=> B*Y ω),(fun ω=> C*θ ω),
    (fun ω=> D*(Y ω)^2),(fun ω=> E*(Y ω*θ ω)),(fun ω=> F*(θ ω)^2)]
  have hf (i : Fin 6) : Integrable (f i) μ := by
    fin_cases i
    · exact integrable_const A
    · exact (hiY.integrable (by norm_num)).const_mul B
    · exact (hiθ.integrable (by norm_num)).const_mul C
    · exact hiY.integrable_sq.const_mul D
    · exact (hiY.integrable_mul hiθ).const_mul E
    · exact hiθ.integrable_sq.const_mul F
  calc
    _ = ∫ ω,∑ i,f i ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp [f,Fin.sum_univ_succ]
      ring
    _ = ∑ i,∫ ω,f i ω ∂μ := integral_finset_sum _ (fun i _=> hf i)
    _ = _ := by
      simp [f,Fin.sum_univ_succ,integral_const_mul,hYmean,hmean,hYY,hYθ,hvar]
      ring


def qBase (a b c φ : ℝ) : ℝ := (a-wbar a b c φ)/2
def qSlope (c φ β : ℝ) (X : Fin 2→Status) (i : Fin 2) : ℝ :=
  (-β-(1+φ)*alphaW c φ β X i+φ*alphaW c φ β X (other i))/2

theorem eq_manufacturer_value {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hc : 0<2+(1+φ)*c) (hφ : 0< φ) (hns : 2+3*φ+(1+φ)*(1+2*φ)*c≠0) (X : Fin 2→Status) (ρ) (f)
    (heq : IsPricingEq μ θ Y a b c φ β X ρ f) (i : Fin 2) :
    manufacturerProfit μ θ Y a b c φ ρ f i =
      (wbar a b c φ-b)*qBase a b c φ-c*(qBase a b c φ)^2+
      ((alphaW c φ β X i*qSlope c φ β X i-c*(qSlope c φ β X i)^2)/β+
        alphaW c φ β X i-2*c*qSlope c φ β X i-c)*σ^2 := by
  have hρ := (retailer_br a φ β hφ ρ).mp heq.1
  have hf := equilibrium_unique μ θ Y a b c φ σ β hmodel hc hφ hns X ρ f heq
  let w:=wbar a b c φ
  let d:=qBase a b c φ
  let k:=qSlope c φ β X i
  let α:=alphaW c φ β X i
  calc
    _ = ∫ ω, (w-b)*d-c*d^2+((w-b)*k+α*d-2*c*d*k)*Y ω+
        (w-b-2*c*d)*θ ω+(α*k-c*k^2)*(Y ω)^2+
        (α-2*c*k)*(Y ω*θ ω)+(-c)*(θ ω)^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf i,hf (other i)] with ω hi hj
      simp only [demand,hρ,hi,hj,candidatePrices]
      dsimp [w,d,k,α,qBase,qSlope]
      ring
    _ = _ := by
      rw [quadratic_mean μ θ Y σ β hmodel]
      dsimp [w,d,k,α]
      ring

theorem eq_retailer_value {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hc : 0<2+(1+φ)*c) (hφ : 0< φ) (hns : 2+3*φ+(1+φ)*(1+2*φ)*c≠0) (X : Fin 2→Status) (ρ) (f)
    (heq : IsPricingEq μ θ Y a b c φ β X ρ f) :
    retailerProfit μ θ Y a φ ρ f =
      2*(qBase a b c φ)^2+
      (((β-alphaW c φ β X 0)/2*qSlope c φ β X 0+
        (β-alphaW c φ β X 1)/2*qSlope c φ β X 1)/β+
        (β-alphaW c φ β X 0)/2+(β-alphaW c φ β X 1)/2)*σ^2 := by
  have hρ := (retailer_br a φ β hφ ρ).mp heq.1
  have hf := equilibrium_unique μ θ Y a b c φ σ β hmodel hc hφ hns X ρ f heq
  let d:=qBase a b c φ
  let k₀:=qSlope c φ β X 0
  let k₁:=qSlope c φ β X 1
  let r₀:=(β-alphaW c φ β X 0)/2
  let r₁:=(β-alphaW c φ β X 1)/2
  calc
    _ = ∫ ω, 2*d^2+(d*k₀+r₀*d+d*k₁+r₁*d)*Y ω+
        (2*d)*θ ω+(r₀*k₀+r₁*k₁)*(Y ω)^2+
        (r₀+r₁)*(Y ω*θ ω)+0*(θ ω)^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf 0,hf 1] with ω h₀ h₁
      simp only [Fin.sum_univ_two,demand,hρ]
      norm_num [other] at *
      rw [h₀,h₁]
      dsimp [candidatePrices,d,k₀,k₁,r₀,r₁,qBase,qSlope]
      norm_num [other]
      ring
    _ = _ := by
      rw [quadratic_mean μ θ Y σ β hmodel]
      dsimp [d,k₀,k₁,r₀,r₁]
      ring

theorem num_u : numInformed (fun _=> Status.uninformed)=0 := by decide
theorem num_i : numInformed (fun _=> Status.informed)=2 := by decide
theorem num_only (i : Fin 2) : numInformed (onlyInformed i)=1 := by
  fin_cases i <;> decide

theorem profit_manufacturers {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hc : 0<2+(1+φ)*c) (hns : 2+3*φ+(1+φ)*(1+2*φ)*c≠0) (E : (Fin 2 → Status) → PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    let P := payoffTable μ θ Y a b c φ E
    (∀ i : Fin 2, P.M (fun _ => Status.uninformed) i = piM0 a b c φ σ β) ∧
    (∀ i : Fin 2, P.M (onlyInformed i) (other i) = piMU1 a b c φ σ β) ∧
    (∀ i : Fin 2, P.M (onlyInformed i) i = piMI1 a b c φ σ β) ∧
    (∀ i : Fin 2, P.M (fun _ => Status.informed) i = piM2 a b c φ σ β) := by
  have hβ := (signal_moments μ θ Y σ β hmodel).2.2.2
  have hA : 0<1+φ := by linarith
  have hJ : 0<2+(1+φ)*c := hc
  have hH : 0<2+φ+(1+φ)*c := by linarith
  dsimp only [payoffTable]
  refine ⟨?_,?_,?_,?_⟩ <;> intro i <;>
    rw [eq_manufacturer_value μ θ Y a b c φ σ β hmodel hc hφ hns _ _ _ (hE _)]
  all_goals
    fin_cases i <;>
      simp [qBase,qSlope,wbar,alphaW,num_u,num_i,num_only,onlyInformed,other,
        status_ne,status_ne',piM0,piMU1,piMI1,piM2,piMbar] <;>
      field_simp [hβ.ne',hA.ne',hJ.ne',hH.ne'] <;> ring

theorem profit_retailer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hc : 0<2+(1+φ)*c) (hns : 2+3*φ+(1+φ)*(1+2*φ)*c≠0) (E : (Fin 2 → Status) → PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    let P := payoffTable μ θ Y a b c φ E
    P.R (fun _ => Status.uninformed) = piR0 a b c φ σ β ∧
    (∀ i : Fin 2, P.R (onlyInformed i) = piR1 a b c φ σ β) ∧
    P.R (fun _ => Status.informed) = piR2 a b c φ σ β := by
  have hβ := (signal_moments μ θ Y σ β hmodel).2.2.2
  have hA : 0<1+φ := by linarith
  have hJ : 0<2+(1+φ)*c := hc
  have hH : 0<2+φ+(1+φ)*c := by linarith
  dsimp only [payoffTable]
  refine ⟨?_,?_,?_⟩
  · rw [eq_retailer_value μ θ Y a b c φ σ β hmodel hc hφ hns _ _ _ (hE _)]
    simp [qBase,qSlope,wbar,alphaW,num_u,piR0,piRbar]
    field_simp [hβ.ne',hA.ne',hJ.ne',hH.ne'] <;> ring
  · intro i
    rw [eq_retailer_value μ θ Y a b c φ σ β hmodel hc hφ hns _ _ _ (hE _)]
    fin_cases i <;>
      simp [qBase,qSlope,wbar,alphaW,num_only,onlyInformed,other,
        status_ne,status_ne',piR1,piRbar] <;>
      field_simp [hβ.ne',hA.ne',hJ.ne',hH.ne'] <;> ring
  · rw [eq_retailer_value μ θ Y a b c φ σ β hmodel hc hφ hns _ _ _ (hE _)]
    simp [qBase,qSlope,wbar,alphaW,num_i,piR2,piRbar]
    field_simp [hβ.ne',hA.ne',hJ.ne',hH.ne'] <;> ring


theorem economy_J (φ ce c : ℝ) (hφ : 0< φ) (hc : c= -ce) (hA : ce<2/(1+φ)) :
    0<2+(1+φ)*c := by
  have ha:0<1+φ:=by linarith
  have hh:ce*(1+φ)<2:=(lt_div_iff₀ ha).mp hA
  rw [hc]
  nlinarith
theorem economy_ns (φ ce c : ℝ) (hφ : 0< φ) (hc : c= -ce)
    (hU : ce≠(2+3*φ)/((1+2*φ)*(1+φ))) : 2+3*φ+(1+φ)*(1+2*φ)*c≠0 := by
  intro hh
  apply hU
  have ha:(1+2*φ)*(1+φ)≠0:=by positivity
  apply (eq_div_iff ha).mpr
  rw [hc] at hh
  nlinarith

theorem economy_pricing (φ ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (θ Y : Ω → ℝ) (hφ : 0 < φ) (hc : c = -ce) (hce : 0 < ce)
    (hA : ce < 2 / (1 + φ)) (hM : IsSignalModel μ θ Y σ β) (X : Fin 2 → Status) :
    (∃ (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) (f : Fin 2 → ℝ → ℝ),
      IsPricingEq μ θ Y a b c φ β X ρ f) ∧
    (ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)) → ∀ (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) (f : Fin 2 → ℝ → ℝ),
      IsPricingEq μ θ Y a b c φ β X ρ f → ∀ i : Fin 2,
        (∀ᵐ ω ∂μ, f i (Y ω) = wbar a b c φ + alphaW c φ β X i * Y ω) ∧
        (∀ᵐ ω ∂μ, ρ (fun j => f j (Y ω)) (Y ω) i = pbar a b c φ + alphaP c φ β X i * Y ω)) := by
  have hJ:=economy_J φ ce c hφ hc hA
  refine ⟨⟨(fun w y i=>(a+β*y+w i)/2),candidatePrices a b c φ β X,
    candidate_equilibrium μ θ Y a b c φ σ β hM hJ hφ X⟩,?_⟩
  intro hU ρ f heq i
  have hn:=economy_ns φ ce c hφ hc hU
  have hu:=equilibrium_unique μ θ Y a b c φ σ β hM hJ hφ hn X ρ f heq i
  refine ⟨hu,?_⟩
  have hρ:=(retailer_br a φ β hφ ρ).mp heq.1
  filter_upwards [hu] with ω hω
  rw [hρ,hω,candidate_retail a b c φ β hJ hφ X i (Y ω)]

theorem profile_cases (X : Fin 2→Status) :
    X=(fun _=> Status.uninformed) ∨ X=onlyInformed 0 ∨ X=onlyInformed 1 ∨
      X=(fun _=> Status.informed) := by
  have hv : X=![X 0,X 1] := by funext i;fin_cases i <;> rfl
  rw [hv]
  cases h₀ : X 0 <;> cases h₁ : X 1 <;>
    simp [funext_iff,Fin.forall_fin_two,onlyInformed]

theorem economy_manufacturers (φ ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (θ Y : Ω → ℝ) (E : (Fin 2 → Status) → PricingProfile)
    (hφ : 0 < φ) (hc : c = -ce) (hce : 0 < ce) (hA : ce < 2 / (1 + φ))
    (hU : ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)))
    (hM : IsSignalModel μ θ Y σ β) (hE : IsPricingEqFamily μ θ Y a b c φ β E)
    (X : Fin 2 → Status) (i : Fin 2) :
    (numInformed X = 0 → (payoffTable μ θ Y a b c φ E).M X i = piM0 a b c φ σ β) ∧
    (numInformed X = 1 → X i = Status.uninformed →
      (payoffTable μ θ Y a b c φ E).M X i = piMU1 a b c φ σ β) ∧
    (numInformed X = 1 → X i = Status.informed →
      (payoffTable μ θ Y a b c φ E).M X i = piMI1 a b c φ σ β) ∧
    (numInformed X = 2 → (payoffTable μ θ Y a b c φ E).M X i = piM2 a b c φ σ β) := by
  have hJ:=economy_J φ ce c hφ hc hA
  have hn:=economy_ns φ ce c hφ hc hU
  have hm:=profit_manufacturers μ θ Y a b c φ σ β hM hφ hJ hn E hE
  rcases profile_cases X with rfl|rfl|rfl|rfl
  · simpa [num_u] using hm.1 i
  · simp only [num_only]
    norm_num
    fin_cases i
    · simpa [onlyInformed,status_ne] using hm.2.2.1 0
    · simpa [onlyInformed,status_ne',other] using hm.2.1 0
  · simp only [num_only]
    norm_num
    fin_cases i
    · simpa [onlyInformed,status_ne',other] using hm.2.1 1
    · simpa [onlyInformed,status_ne] using hm.2.2.1 1
  · simpa [num_i] using hm.2.2.2 i

theorem economy_retailer (φ ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (θ Y : Ω → ℝ) (E : (Fin 2 → Status) → PricingProfile)
    (hφ : 0 < φ) (hc : c = -ce) (hce : 0 < ce) (hA : ce < 2 / (1 + φ))
    (hU : ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)))
    (hM : IsSignalModel μ θ Y σ β) (hE : IsPricingEqFamily μ θ Y a b c φ β E)
    (X : Fin 2 → Status) :
    (numInformed X = 0 → (payoffTable μ θ Y a b c φ E).R X = piR0 a b c φ σ β) ∧
    (numInformed X = 1 → (payoffTable μ θ Y a b c φ E).R X = piR1 a b c φ σ β) ∧
    (numInformed X = 2 → (payoffTable μ θ Y a b c φ E).R X = piR2 a b c φ σ β) := by
  have hJ:=economy_J φ ce c hφ hc hA
  have hn:=economy_ns φ ce c hφ hc hU
  have hr:=profit_retailer μ θ Y a b c φ σ β hM hφ hJ hn E hE
  rcases profile_cases X with rfl|rfl|rfl|rfl
  · simpa [num_u] using hr.1
  · simpa [num_only] using hr.2.1 0
  · simpa [num_only] using hr.2.1 1
  · simpa [num_i] using hr.2.2



end
end InfoEconBase

open InfoSharing.Shared
namespace InfoBase
theorem profile_cases (X : Fin 2→Status) :
    X=(fun _=> Status.uninformed) ∨ X=onlyInformed 0 ∨ X=onlyInformed 1 ∨
      X=(fun _=> Status.informed) := by
  have hv : X=![X 0,X 1] := by funext i;fin_cases i <;> rfl
  rw [hv]
  cases h₀ : X 0 <;> cases h₁ : X 1 <;>
    simp [funext_iff,Fin.forall_fin_two,onlyInformed]

theorem forall_status (p : Status→Prop) : (∀ s,p s) ↔ p Status.informed ∧ p Status.uninformed := by
  constructor
  · intro h;exact ⟨h _,h _⟩
  · rintro ⟨hi,hu⟩ s;cases s;exact hi;exact hu
theorem num_u : numInformed (fun _=> Status.uninformed)=0 := by decide
theorem num_i : numInformed (fun _=> Status.informed)=2 := by decide
theorem num_only (i : Fin 2) : numInformed (onlyInformed i)=1 := by
  fin_cases i <;> decide

end InfoBase
namespace InfoSeq
abbrev I := Status.informed
abbrev U := Status.uninformed
@[simp] theorem U_ne_I : Status.uninformed ≠ Status.informed := by decide
@[simp] theorem I_ne_U : Status.informed ≠ Status.uninformed := by decide
def table (m0 mu mi m2 r0 r1 r2 : ℝ) : PayoffTable where
  M X i := if X i=Status.informed then (if X (other i)=Status.informed then m2 else mi)
    else (if X (other i)=Status.informed then mu else m0)
  R X := if numInformed X=0 then r0 else if numInformed X=1 then r1 else r2

end InfoSeq

set_option maxHeartbeats 2000000
open InfoSharing.Shared InfoSharing.Economy InfoSeq
namespace InfoEconGame
noncomputable section
 theorem ne_u (m0 mu mi m2 r0 r1 r2 T:ℝ) :
    IsPureNE (table m0 mu mi m2 r0 r1 r2) T (fun _=> U) ↔ mi-m0 ≤ T := by
  simp [IsPureNE,Fin.forall_fin_two,InfoBase.forall_status,concManufacturerPayoff,table,other,I,U]
  constructor <;> intro h <;> linarith
 theorem ne_i (m0 mu mi m2 r0 r1 r2 T:ℝ) :
    IsPureNE (table m0 mu mi m2 r0 r1 r2) T (fun _=> I) ↔ T ≤ m2-mu := by
  simp [IsPureNE,Fin.forall_fin_two,InfoBase.forall_status,concManufacturerPayoff,table,other,I,U]
  constructor <;> intro h <;> linarith
 theorem ne_only (m0 mu mi m2 r0 r1 r2 T:ℝ) (i:Fin 2) :
    IsPureNE (table m0 mu mi m2 r0 r1 r2) T (onlyInformed i) ↔ m2-mu ≤ T ∧ T ≤ mi-m0 := by
  fin_cases i <;>
    simp [IsPureNE,Fin.forall_fin_two,InfoBase.forall_status,concManufacturerPayoff,table,other,onlyInformed,I,U]
  all_goals constructor <;> intro h <;> constructor <;> linarith
 theorem ret_u (m0 mu mi m2 r0 r1 r2 T:ℝ) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T (fun _=> U)=r0 := by simp [concRetailer,table,I,U,InfoBase.num_u]
 theorem ret_i (m0 mu mi m2 r0 r1 r2 T:ℝ) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T (fun _=> I)=r2+2*T := by simp [concRetailer,table,I,U,InfoBase.num_i];ring
 theorem ret_only (m0 mu mi m2 r0 r1 r2 T:ℝ) (i:Fin 2) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T (onlyInformed i)=r1+T := by simp [concRetailer,table,InfoBase.num_only]
 theorem pareto_only (m0 mu mi m2 r0 r1 r2 T:ℝ) (i:Fin 2)
    (hlo:m2-mu < T) (hhi:T < mi-m0) :
    IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) T (onlyInformed i) := by
  refine ⟨(ne_only _ _ _ _ _ _ _ _ _).mpr ⟨hlo.le,hhi.le⟩,?_⟩
  rintro ⟨X,hX,hw,j,hj⟩
  rcases InfoBase.profile_cases X with rfl|rfl|rfl|rfl
  · have hh:=(ne_u _ _ _ _ _ _ _ _).mp hX;linarith
  · fin_cases i <;> fin_cases j <;>
      simp [concManufacturerPayoff,table,onlyInformed,other,I,U] at hw hj <;>
      first | exact (lt_irrefl _ hj) | (linarith [hw.1,hw.2])
  · fin_cases i <;> fin_cases j <;>
      simp [concManufacturerPayoff,table,onlyInformed,other,I,U] at hw hj <;>
      first | exact (lt_irrefl _ hj) | (linarith [hw.1,hw.2])
  · have hh:=(ne_i _ _ _ _ _ _ _ _).mp hX;linarith
 theorem no_two (m0 mu mi m2 r0 r1 r2:ℝ) (hg0:0 < mi-m0)
    (hgap:m2-mu < mi-m0) (hret:r2+2*(m2-mu) < r1+(mi-m0)) :
    2 ∉ ConcOptN (table m0 mu mi m2 r0 r1 r2) := by
  rintro ⟨T,X,hX,hn⟩
  have hXi:X=(fun _=> I) := by
    rcases InfoBase.profile_cases X with rfl|rfl|rfl|rfl
    · norm_num [InfoBase.num_u] at hn
    · norm_num [InfoBase.num_only] at hn
    · norm_num [InfoBase.num_only] at hn
    · rfl
  subst X
  have ht:=(ne_i _ _ _ _ _ _ _ _).mp hX.2.1
  let eps:=min ((mi-m0)/2) (min ((mi-m0-(m2-mu))/2) ((r1+(mi-m0)-(r2+2*(m2-mu)))/2))
  have heps:0 < eps := by dsimp [eps];positivity
  have he0:eps ≤ (mi-m0)/2:=min_le_left _ _
  have he1:eps ≤ (mi-m0-(m2-mu))/2:=(min_le_right _ _).trans (min_le_left _ _)
  have he2:eps ≤ (r1+(mi-m0)-(r2+2*(m2-mu)))/2:=(min_le_right _ _).trans (min_le_right _ _)
  have hp:=pareto_only m0 mu mi m2 r0 r1 r2 (mi-m0-eps) 0 (by linarith) (by linarith)
  have hh:=hX.2.2.1 (mi-m0-eps) (onlyInformed 0) (by linarith) hp
  rw [ret_only,ret_i] at hh
  linarith
 theorem pareto_equal_bound (m0 mu mi m2 r0 r1 r2:ℝ)
    (heq:m2-mu=mi-m0) (hmi:m2 < mi) (T:ℝ) (X:Fin 2 → Status)
    (hX:IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) T X) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T X ≤ max r0 (r2+2*(mi-m0)) := by
  have hmu:mu < m0 := by linarith
  have hnot (i:Fin 2) (hXi:X=onlyInformed i) : False := by
    subst X
    obtain ⟨hlo,hhi⟩:=(ne_only _ _ _ _ _ _ _ _ i).mp hX.1
    have ht:T=mi-m0 := by linarith
    apply hX.2
    refine ⟨(fun _=> U),(ne_u _ _ _ _ _ _ _ _).mpr (by linarith),?_,?_⟩
    · intro j
      fin_cases i <;> fin_cases j <;> simp [concManufacturerPayoff,table,onlyInformed,other,I,U,ht] <;> linarith
    · refine ⟨other i,?_⟩
      fin_cases i <;> simp [concManufacturerPayoff,table,onlyInformed,other,I,U,ht] <;> linarith
  rcases InfoBase.profile_cases X with hh|hh|hh|hh
  · subst X;rw [ret_u];exact le_max_left _ _
  · exact (hnot 0 hh).elim
  · exact (hnot 1 hh).elim
  · subst X
    have ht:=(ne_i _ _ _ _ _ _ _ _).mp hX.1
    rw [ret_i]
    exact (by linarith : r2+2*T ≤ r2+2*(mi-m0)).trans (le_max_right _ _)
 theorem one_strict (m0 mu mi m2 r0 r1 r2:ℝ) (hmi:m2 < mi)
    (hr0:r0 < r1+(mi-m0)) (heqret:m2-mu=mi-m0 → r2+(mi-m0) < r1)
    (hn:1 ∈ ConcOptN (table m0 mu mi m2 r0 r1 r2)) : m2-mu < mi-m0 := by
  obtain ⟨T,X,hX,hn⟩:=hn
  have hex:∃ i:Fin 2,X=onlyInformed i := by
    rcases InfoBase.profile_cases X with rfl|rfl|rfl|rfl
    · norm_num [InfoBase.num_u] at hn
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · norm_num [InfoBase.num_i] at hn
  obtain ⟨i,rfl⟩:=hex
  obtain ⟨hlo,hhi⟩:=(ne_only _ _ _ _ _ _ _ _ i).mp hX.2.1
  have hle:m2-mu ≤ mi-m0:=hlo.trans hhi
  by_contra hh
  have heq:m2-mu=mi-m0:=le_antisymm hle (le_of_not_gt hh)
  have ht:T=mi-m0:=by linarith
  have hr:r2+(mi-m0) < r1:=heqret heq
  have hmax:max r0 (r2+2*(mi-m0)) < r1+(mi-m0) := max_lt hr0 (by linarith)
  obtain ⟨T',X',hT',hX',hv⟩:=hX.2.2.2 ((r1+(mi-m0)-max r0 (r2+2*(mi-m0)))/2) (by linarith)
  have hbound:=pareto_equal_bound m0 mu mi m2 r0 r1 r2 heq hmi T' X' hX'
  rw [ret_only,ht] at hv
  linarith
end
end InfoEconGame

open MeasureTheory
open scoped ENNReal
namespace InfoCounter
noncomputable section
 def μ : Measure ℝ := (1/2:ℝ≥0∞) • (Measure.dirac 1+Measure.dirac (-1))
 instance : IsProbabilityMeasure μ := by constructor;norm_num [μ,Measure.add_apply];exact ENNReal.inv_two_add_inv_two
 theorem model : InfoSharing.Shared.IsSignalModel μ id id 1 1 := by
  have hb:∀ᵐ x:ℝ ∂μ,‖x‖ ≤ 1 := by
    simp [μ,Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2:ℝ≥0∞) ≠ 0)]
  have hl:MemLp (id:ℝ → ℝ) 2 μ:=MemLp.of_bound (by fun_prop) 1 hb
  have hi:Integrable (id:ℝ → ℝ) μ:=hl.integrable (by norm_num)
  have hmean:(∫ x:ℝ,x ∂μ)=0 := by
    rw [μ,integral_smul_measure,integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp))]
    norm_num
  have hsq:(∫ x:ℝ,x^2 ∂μ)=1 := by
    rw [μ,integral_smul_measure,integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp))]
    norm_num
  refine ⟨inferInstance,measurable_id,measurable_id,hl,hl,hmean,by simpa using hsq,by norm_num,?_,?_⟩
  all_goals simp only [MeasurableSpace.comap_id,one_mul];rw [condExp_of_stronglyMeasurable le_rfl stronglyMeasurable_id hi]
end
end InfoCounter

namespace InfoCounter
noncomputable section
 def m0 (z:ℝ) : ℝ := (2-z)/44
 def mu (z:ℝ) : ℝ := (2-z)*(21*z-10)^2/(5324*z^2)
 def mi (z:ℝ) : ℝ := 1/(44*z)
 def m2 (z:ℝ) : ℝ := 11*z/(4*(z+10)^2)
 def r0 : ℝ := 1/2
 def r1 (z:ℝ) : ℝ := 21/44+1/(44*z^2)
 def r2 (z:ℝ) : ℝ := 121/(2*(z+10)^2)
 def q (z:ℝ) : ℝ := 32*z^3+598*z^2+3790*z-2000
 def p (z:ℝ) : ℝ := 761*z^4+11078*z^3+20159*z^2-113380*z+52100
 theorem gaps (z:ℝ) (hz:0 < z) :
    mi z-m0 z=(z-1)^2/(44*z) ∧
    m2 z-mi z=10*(z-1)*(12*z+10)/(44*z*(z+10)^2) ∧
    r1 z+(mi z-m0 z)-r0=(z-1)*(z^2-2*z-1)/(44*z^2) ∧
    (m2 z-mu z)-(mi z-m0 z)=10*(z-1)^2*q z/(5324*z^2*(z+10)^2) ∧
    r2 z+2*(m2 z-mu z)-(r1 z+(mi z-m0 z))=(z-1)*p z/(5324*z^2*(z+10)^2) := by
  have h10:z+10 ≠ 0:=by positivity
  refine ⟨?_,?_,?_,?_,?_⟩ <;> dsimp only [m0,mu,mi,m2,r0,r1,r2,p,q] <;> field_simp [hz.ne',h10] <;> ring
 theorem poly_pos (z:ℝ) (hz:0 < z) (hzhalf:z ≤ 1/2) : 0 < p z := by
  let w:=1/2-z
  have hw:0 ≤ w:=by dsimp [w];linarith
  have hw1:w ≤ 1/2:=by dsimp [w];linarith
  have hid:p z=761*w^4+w^2*(75835/2-12600*w)+84532*w+30113/16 := by unfold p;dsimp [w];ring
  have hcoef:0 ≤ 75835/2-12600*w:=by linarith
  rw [hid]
  positivity
 theorem scalar_facts (z:ℝ) (hz:0 < z) (hz1:z < 1) :
    0 < mi z-m0 z ∧ m2 z < mi z ∧ r0 < r1 z+(mi z-m0 z) ∧
    (m2 z-mu z ≤ mi z-m0 z → z < 1/2) ∧
    (z ≤ 1/2 → r2 z+2*(m2 z-mu z) < r1 z+(mi z-m0 z)) := by
  obtain ⟨h0,hmi,hr,hgap,hret⟩:=gaps z hz
  have hzneg:z-1 < 0:=by linarith
  have hsq:0 < (z-1)^2:=sq_pos_of_ne_zero hzneg.ne
  have h0pos:0 < mi z-m0 z:=by rw [h0];positivity
  have hmneg:m2 z-mi z < 0:=by rw [hmi];apply div_neg_of_neg_of_pos;exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hzneg) (by positivity);positivity
  have hquad:z^2-2*z-1 < 0:=by nlinarith [mul_pos hz (sub_pos.mpr hz1)]
  have hrpos:0 < r1 z+(mi z-m0 z)-r0:=by rw [hr];exact div_pos (mul_pos_of_neg_of_neg hzneg hquad) (by positivity)
  refine ⟨h0pos,by linarith,by linarith,?_,?_⟩
  · intro hle
    by_contra hhalf
    have hh:1/2 ≤ z:=le_of_not_gt hhalf
    have hq:q (1/2) ≤ q z:=by unfold q;gcongr
    have hqpos:0 < q z:=by norm_num [q] at hq;unfold q;linarith
    have hpos:0 < 10*(z-1)^2*q z/(5324*z^2*(z+10)^2):=by positivity
    linarith
  · intro hh
    have hp:=poly_pos z hz hh
    have hneg:(z-1)*p z/(5324*z^2*(z+10)^2) < 0:=div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hzneg hp) (by positivity)
    linarith
 theorem closed_forms (z:ℝ) (hz:0 < z) :
    InfoSharing.Shared.piM0 0 0 ((z-2)/11) 10 1 1=m0 z ∧
    InfoSharing.Shared.piMU1 0 0 ((z-2)/11) 10 1 1=mu z ∧
    InfoSharing.Shared.piMI1 0 0 ((z-2)/11) 10 1 1=mi z ∧
    InfoSharing.Shared.piM2 0 0 ((z-2)/11) 10 1 1=m2 z ∧
    InfoSharing.Shared.piR0 0 0 ((z-2)/11) 10 1 1=r0 ∧
    InfoSharing.Shared.piR1 0 0 ((z-2)/11) 10 1 1=r1 z ∧
    InfoSharing.Shared.piR2 0 0 ((z-2)/11) 10 1 1=r2 z := by
  have h10:z+10 ≠ 0:=by positivity
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;>
    dsimp only [InfoSharing.Shared.piM0,InfoSharing.Shared.piMU1,InfoSharing.Shared.piMI1,InfoSharing.Shared.piM2,InfoSharing.Shared.piR0,InfoSharing.Shared.piR1,InfoSharing.Shared.piR2,InfoSharing.Shared.piMbar,InfoSharing.Shared.piRbar,m0,mu,mi,m2,r0,r1,r2]
  all_goals ring_nf
  all_goals field_simp [hz.ne',h10] <;> ring
end
end InfoCounter

open InfoSharing.Shared InfoSharing.Economy
namespace InfoCounter
noncomputable section
 def tbl (z:ℝ) : PayoffTable := InfoSeq.table (m0 z) (mu z) (mi z) (m2 z) r0 (r1 z) (r2 z)
 theorem impossible_threshold : ¬ ∃ C:ℝ,1/11 < C ∧ C < 2/11 ∧
    ∀ z:ℝ,0 < z → z < 1 → z ≠ 10/21 →
      ((2-z)/11 < C → 2 ∈ ConcOptN (tbl z)) ∧
      (C ≤ (2-z)/11 → 1 ∈ ConcOptN (tbl z)) := by
  rintro ⟨C,hC0,hC2,hC⟩
  have hbound:C ≤ 69/500 := by
    by_contra hh
    have hmem:2 ∈ ConcOptN (tbl (241/500)):=
      (hC (241/500) (by norm_num) (by norm_num) (by norm_num)).1 (by linarith)
    apply InfoEconGame.no_two (m0 (241/500)) (mu (241/500)) (mi (241/500)) (m2 (241/500)) r0 (r1 (241/500)) (r2 (241/500)) _ _ _ hmem <;>
      norm_num [m0,mu,mi,m2,r0,r1,r2]
  let z:=2-11*C
  have hz:0 < z:=by dsimp [z];linarith
  have hz1:z < 1:=by dsimp [z];linarith
  have hzne:10/21 < z:=by dsimp [z];linarith
  have hmem:1 ∈ ConcOptN (tbl z):=(hC z hz hz1 hzne.ne').2 (by dsimp [z];linarith)
  obtain ⟨hg0,hmi,hr0,hgap,hret⟩:=scalar_facts z hz hz1
  have hstrict:m2 z-mu z < mi z-m0 z := by
    apply InfoEconGame.one_strict (m0 z) (mu z) (mi z) (m2 z) r0 (r1 z) (r2 z) hmi hr0 _ hmem
    intro heq
    have hh:=hret (hgap heq.le).le
    linarith
  have hzhalf:z < 1/2:=hgap hstrict.le
  have hcont:ContinuousAt (fun x:ℝ=>(m2 x-mu x)-(mi x-m0 x)) z := by
    unfold m0 mu mi m2
    fun_prop (disch:=positivity)
  have hev:∀ᶠ x in nhds z,(m2 x-mu x)-(mi x-m0 x) < 0:=
    hcont.eventually (isOpen_Iio.mem_nhds (show (m2 z-mu z)-(mi z-m0 z) < (0:ℝ) by linarith))
  obtain ⟨d,hd,hball⟩:=Metric.eventually_nhds_iff.mp hev
  let e:=min (d/2) ((1/2-z)/2)
  have he:0 < e:=by dsimp [e];positivity
  have hed:e ≤ d/2:=min_le_left _ _
  have hez:e ≤ (1/2-z)/2:=min_le_right _ _
  let z':=z+e
  have hz':0 < z':=by dsimp [z'];linarith
  have hz'half:z' < 1/2:=by dsimp [z'];linarith
  have hg':m2 z'-mu z' < mi z'-m0 z' := by
    have hh:=hball (show dist z' z < d by rw [Real.dist_eq];dsimp [z'];rw [abs_of_nonneg (by linarith)];linarith)
    linarith
  have h2:2 ∈ ConcOptN (tbl z'):=
    (hC z' hz' (by linarith) (by dsimp [z'];linarith)).1 (by dsimp [z',z];linarith)
  have hs':=scalar_facts z' hz' (by linarith)
  exact InfoEconGame.no_two (m0 z') (mu z') (mi z') (m2 z') r0 (r1 z') (r2 z') hs'.1 hg' (hs'.2.2.2.2 hz'half.le) h2
end
end InfoCounter

open MeasureTheory InfoSharing.Shared
namespace InfoEconBase
open InfoSeq
theorem payoff_eq_table {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hφ : 0< φ) (hc : 0 < 2+(1+φ)*c) (hns : 2+3*φ+(1+φ)*(1+2*φ)*c ≠ 0) (E : (Fin 2→Status)→PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    payoffTable μ θ Y a b c φ E=table (piM0 a b c φ σ β) (piMU1 a b c φ σ β)
      (piMI1 a b c φ σ β) (piM2 a b c φ σ β)
      (piR0 a b c φ σ β) (piR1 a b c φ σ β) (piR2 a b c φ σ β) := by
  have hm:=profit_manufacturers μ θ Y a b c φ σ β hmodel hφ hc hns E hE
  have hr:=profit_retailer μ θ Y a b c φ σ β hmodel hφ hc hns E hE
  have hM : (payoffTable μ θ Y a b c φ E).M=(table (piM0 a b c φ σ β)
      (piMU1 a b c φ σ β) (piMI1 a b c φ σ β) (piM2 a b c φ σ β)
      (piR0 a b c φ σ β) (piR1 a b c φ σ β) (piR2 a b c φ σ β)).M := by
    funext X i
    rcases profile_cases X with rfl|rfl|rfl|rfl
    · simpa [table,status_ne'] using hm.1 i
    · fin_cases i
      · simpa [table,onlyInformed,other,status_ne'] using hm.2.2.1 0
      · simpa [table,onlyInformed,other,status_ne'] using hm.2.1 0
    · fin_cases i
      · simpa [table,onlyInformed,other,status_ne'] using hm.2.1 1
      · simpa [table,onlyInformed,other,status_ne'] using hm.2.2.1 1
    · simpa [table] using hm.2.2.2 i
  have hR : (payoffTable μ θ Y a b c φ E).R=(table (piM0 a b c φ σ β)
      (piMU1 a b c φ σ β) (piMI1 a b c φ σ β) (piM2 a b c φ σ β)
      (piR0 a b c φ σ β) (piR1 a b c φ σ β) (piR2 a b c φ σ β)).R := by
    funext X
    rcases profile_cases X with rfl|rfl|rfl|rfl
    · simpa [table,num_u] using hr.1
    · simpa [table,num_only] using hr.2.1 0
    · simpa [table,num_only] using hr.2.1 1
    · simpa [table,num_i] using hr.2.2
  exact congr_arg₂ PayoffTable.mk hM hR

end InfoEconBase
namespace InfoCounter
noncomputable section
 def family (z:ℝ) : (Fin 2 → Status) → PricingProfile :=
    fun X=>⟨fun w y i=>(y+w i)/2,InfoEconBase.candidatePrices 0 0 ((z-2)/11) 10 1 X⟩
 theorem family_eq (z:ℝ) (hz:0 < z) : IsPricingEqFamily μ id id 0 0 ((z-2)/11) 10 1 (family z) := by
  intro X
  simpa [family] using InfoEconBase.candidate_equilibrium μ id id 0 0 ((z-2)/11) 10 1 1 model (by linarith) (by norm_num) X
 theorem family_pay (z:ℝ) (hz:0 < z) (hne:z ≠ 10/21) :
    payoffTable μ id id 0 0 ((z-2)/11) 10 (family z)=
      InfoSeq.table (m0 z) (mu z) (mi z) (m2 z) r0 (r1 z) (r2 z) := by
  rw [InfoEconBase.payoff_eq_table μ id id 0 0 ((z-2)/11) 10 1 1 model (by norm_num) (by linarith)
    (by intro hh;apply hne;linarith) (family z) (family_eq z hz)]
  obtain ⟨h0,hu,hi,h2,hr0,hr1,hr2⟩:=closed_forms z hz
  rw [h0,hu,hi,h2,hr0,hr1,hr2]
end
end InfoCounter
open MeasureTheory InfoSharing.Shared InfoSharing.Economy
theorem solution : ¬ (
    ∀ φ : ℝ, 0 < φ → ∃ cN cS cC : ℝ,
    cN < cS ∧ cS ≤ cC ∧
    1 / (1 + φ) < cN ∧ cC < 2 / (1 + φ) ∧
    ∀ (ce c a b σ β : ℝ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ)
      (E : (Fin 2 → Status) → PricingProfile),
      c = -ce → 0 < ce → ce < 2 / (1 + φ) → ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)) →
      IsSignalModel μ θ Y σ β →
      IsPricingEqFamily μ θ Y a b c φ β E →
      let P := payoffTable μ θ Y a b c φ E
      ((ce < 1 / (1 + φ) → NoContractOptN P = {0}) ∧
         (1 / (1 + φ) ≤ ce → ce < cN → 2 ∈ NoContractOptN P) ∧
         (1 / (1 + φ) < ce → ce < cN → NoContractOptN P = {2}) ∧
         (cN ≤ ce → 1 ∈ NoContractOptN P) ∧
         (cN < ce → NoContractOptN P = {1})) ∧
      ((ce < 1 / (1 + φ) → ConcOptN P = {0}) ∧
         (1 / (1 + φ) ≤ ce → ce < cC → 2 ∈ ConcOptN P) ∧
         (1 / (1 + φ) < ce → ce < cC → ConcOptN P = {2}) ∧
         (cC ≤ ce → 1 ∈ ConcOptN P) ∧
         (cC < ce → ConcOptN P = {1})) ∧
      ∀ k : Fin 2,
        ((ce < 1 / (1 + φ) → SeqOptN P k = {0}) ∧
           (1 / (1 + φ) ≤ ce → ce < cS → 2 ∈ SeqOptN P k) ∧
           (1 / (1 + φ) < ce → ce < cS → SeqOptN P k = {2}) ∧
           (cS ≤ ce → 1 ∈ SeqOptN P k) ∧
           (cS < ce → SeqOptN P k = {1}))) := by
  intro h
  obtain ⟨N,S,C,hNS,hSC,hN0,hC2,hall⟩:=h 10 (by norm_num)
  apply InfoCounter.impossible_threshold
  refine ⟨C,by norm_num at hN0;linarith,by norm_num at hC2 ⊢;exact hC2,?_⟩
  intro z hz hz1 hne
  have hh:=hall ((2-z)/11) ((z-2)/11) 0 0 1 1 InfoCounter.μ id id (InfoCounter.family z)
    (by ring) (by linarith) (by norm_num;linarith) (by norm_num;intro he;apply hne;linarith)
    InfoCounter.model (InfoCounter.family_eq z hz)
  dsimp only at hh
  rw [InfoCounter.family_pay z hz hne] at hh
  exact ⟨fun hlt=> hh.2.1.2.1 (by norm_num;linarith) hlt,fun hle=> hh.2.1.2.2.2.1 hle⟩
