-- Prove2me | solution 1 for InfoSharing.Diseconomy.sequential_vs_concurrent
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:11:36.955812+00:00
-- url     : https://prove2.me/submissions/bb4d3357-e0b7-488f-a3b9-0db282b440e5

import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InfoSharing_Diseconomy_IsConcurrentOutcome
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
import Definitions.Def_InfoSharing_Shared_IsSequentialSPE

set_option maxHeartbeats 3000000
namespace InfoBase
open MeasureTheory Filter
open InfoSharing.Shared
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

theorem candidate_informed (a b c φ β : ℝ) (hc : 0< c) (hφ : 0< φ)
    (X : Fin 2→Status) (i : Fin 2) (hi : X i=Status.informed) (y : ℝ) :
    priceGradient a b c φ β (candidatePrices a b c φ β X) i y=0 := by
  have h1 : 0<1+φ := by linarith
  have h2 : 0<2+(1+φ)*c := by positivity
  have h3 : 0<2+φ+(1+φ)*c := by positivity
  have hX : X=![X 0,X 1] := by funext j;fin_cases j <;> rfl
  rw [hX] at hi ⊢
  cases h0 : X 0 <;> cases h1' : X 1 <;> fin_cases i <;>
    simp [priceGradient,candidatePrices,alphaW,numInformed_vec,status_ne,status_ne',other,h0,h1'] at hi ⊢
  all_goals unfold wbar;field_simp [h1.ne',h2.ne',h3.ne'] <;> ring

theorem candidate_gradient_linear (a b c φ β : ℝ) (hc : 0< c) (hφ : 0< φ)
    (X : Fin 2→Status) (i : Fin 2) (y : ℝ) :
    priceGradient a b c φ β (candidatePrices a b c φ β X) i y =
      y*priceGradient a b c φ β (candidatePrices a b c φ β X) i 1 := by
  have h3 : 0<2+φ+(1+φ)*c := by positivity
  unfold priceGradient candidatePrices wbar
  field_simp [h3.ne']
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
    (a b c φ β : ℝ) (hc : 0< c) (hφ : 0< φ) (X : Fin 2→Status) (i : Fin 2)
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
    (hc : 0< c) (hφ : 0< φ) (X : Fin 2→Status) :
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
  have hk : 0≤(1+φ)*(2+c*(1+φ))/4 := by positivity
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

theorem equilibrium_unique {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hc : 0< c) (hφ : 0< φ) (X : Fin 2→Status) (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) (f : Fin 2→ℝ→ℝ)
    (heq : IsPricingEq μ θ Y a b c φ β X ρ f) :
    ∀ i,(fun ω=> f i (Y ω)) =ᵐ[μ] (fun ω=> candidatePrices a b c φ β X i (Y ω)) := by
  haveI := hmodel.1
  let F := candidatePrices a b c φ β X
  let d : Fin 2→Ω→ℝ := fun i ω=> f i (Y ω)-F i (Y ω)
  let Acoef := (1+φ)*(2+c*(1+φ))/2
  let γ := φ*(1+c*(1+φ))/2
  have hiY : MemLp Y 2 μ := hmodel.2.2.2.2.1
  have hY := (signal_moments μ θ Y σ β hmodel).1
  have had (i : Fin 2) : IsAdmissible μ Y (X i) (F i) := candidate_admissible μ Y hiY a b c φ β X i
  have hif (i : Fin 2) := (heq.2.1 i).2.1
  have hid (i : Fin 2) : MemLp (d i) 2 μ := (hif i).sub (had i).2.1
  have hE (i : Fin 2) : Acoef*(∫ ω,(d i ω)^2 ∂μ)=γ*(∫ ω,d i ω*d (other i) ω ∂μ) := by
    have hfo := equilibrium_first_order μ θ Y a b c φ σ β hmodel hφ X ρ f heq i (F i) (had i)
    have hca := candidate_stationary μ Y hY a b c φ β hc hφ X i (f i) (heq.2.1 i)
    have ha : Integrable (fun ω=>(F i (Y ω)-f i (Y ω))*priceGradient a b c φ β f i (Y ω)) μ :=
      ((had i).2.1.sub (hif i)).integrable_mul (gradient_lp μ Y hiY a b c φ β f hif i)
    have hb : Integrable (fun ω=>(f i (Y ω)-F i (Y ω))*priceGradient a b c φ β F i (Y ω)) μ :=
      (hid i).integrable_mul (gradient_lp μ Y hiY a b c φ β F (fun j=>(had j).2.1) i)
    have hh : (∫ ω,((F i (Y ω)-f i (Y ω))*priceGradient a b c φ β f i (Y ω))+
        ((f i (Y ω)-F i (Y ω))*priceGradient a b c φ β F i (Y ω)) ∂μ)=0 := by
      rw [integral_add ha hb,hfo,zero_add]
      exact hca
    have he : (∫ ω,((F i (Y ω)-f i (Y ω))*priceGradient a b c φ β f i (Y ω))+
        ((f i (Y ω)-F i (Y ω))*priceGradient a b c φ β F i (Y ω)) ∂μ)=
        (∫ ω,Acoef*(d i ω)^2-γ*(d i ω*d (other i) ω) ∂μ) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      dsimp [priceGradient,d,Acoef,γ]
      ring
    have hiprod : Integrable (fun ω=> d i ω*d (other i) ω) μ := (hid i).integrable_mul (hid (other i))
    rw [he,integral_sub ((hid i).integrable_sq.const_mul Acoef)
      (hiprod.const_mul γ),integral_const_mul,integral_const_mul] at hh
    linarith
  let S0 := ∫ ω,(d 0 ω)^2 ∂μ
  let S1 := ∫ ω,(d 1 ω)^2 ∂μ
  let C := ∫ ω,d 0 ω*d 1 ω ∂μ
  have h0 : 0≤ S0 := integral_nonneg (fun ω=> sq_nonneg _)
  have h1 : 0≤ S1 := integral_nonneg (fun ω=> sq_nonneg _)
  have hE0 : Acoef*S0=γ*C := by simpa only [S0,C,other,Fin.reduceSub] using hE 0
  have hE1 : Acoef*S1=γ*C := by
    have hcomm : (∫ ω,d 1 ω*d 0 ω ∂μ)=C := by
      dsimp [C]
      congr 1
      funext ω
      ring
    simpa only [S1,other,Fin.reduceSub,hcomm] using hE 1
  have hcross : 2*C≤ S0+S1 := by
    have hprod : Integrable (fun ω=> d 0 ω*d 1 ω) μ := (hid 0).integrable_mul (hid 1)
    have hh := integral_mono_ae (hprod.const_mul 2) ((hid 0).integrable_sq.add (hid 1).integrable_sq)
      (Eventually.of_forall (fun ω=> show 2*(d 0 ω*d 1 ω)≤(d 0 ω)^2+(d 1 ω)^2 by nlinarith [sq_nonneg (d 0 ω-d 1 ω)]))
    rw [integral_const_mul,integral_add' (hid 0).integrable_sq (hid 1).integrable_sq] at hh
    exact hh
  have hγ : 0≤ γ := by dsimp [γ];positivity
  have hgap : 0< Acoef-γ := by dsimp [Acoef,γ];nlinarith [mul_pos hc (show 0<1+φ by linarith)]
  have hbound := mul_le_mul_of_nonneg_left hcross hγ
  have hzsum : S0+S1≤0 := by nlinarith
  have hz (i : Fin 2) : (∫ ω,(d i ω)^2 ∂μ)=0 := by
    fin_cases i
    · change S0=0
      linarith
    · change S1=0
      linarith
  intro i
  have hsq : (fun ω=>(d i ω)^2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω=> sq_nonneg _) (hid i).integrable_sq).mp (hz i)
  filter_upwards [hsq] with ω hω
  have hd : d i ω=0 := sq_eq_zero_iff.mp hω
  exact sub_eq_zero.mp hd

theorem candidate_retail (a b c φ β : ℝ) (hc : 0< c) (hφ : 0< φ)
    (X : Fin 2→Status) (i : Fin 2) (y : ℝ) :
    (a+β*y+candidatePrices a b c φ β X i y)/2=pbar a b c φ+alphaP c φ β X i*y := by
  have h1 : 0<1+φ := by linarith
  have h2 : 0<2+(1+φ)*c := by positivity
  have h3 : 0<2+φ+(1+φ)*c := by positivity
  have hX : X=![X 0,X 1] := by funext j;fin_cases j <;> rfl
  rw [hX]
  cases h0 : X 0 <;> cases h1' : X 1 <;> fin_cases i <;>
    simp [candidatePrices,alphaW,alphaP,numInformed_vec,status_ne,status_ne',h0,h1']
  all_goals unfold wbar pbar;field_simp [h1.ne',h2.ne',h3.ne'] <;> ring

theorem pricing_equilibrium {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) (X : Fin 2 → Status) :
    (∃ (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) (f : Fin 2 → ℝ → ℝ),
        IsPricingEq μ θ Y a b c φ β X ρ f) ∧
    ∀ (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) (f : Fin 2 → ℝ → ℝ),
      IsPricingEq μ θ Y a b c φ β X ρ f →
        (∀ (w : Fin 2 → ℝ) (y : ℝ) (i : Fin 2), ρ w y i = (a + β * y + w i) / 2) ∧
        ∀ i : Fin 2,
          (fun ω => f i (Y ω)) =ᵐ[μ] (fun ω => wbar a b c φ + alphaW c φ β X i * Y ω) ∧
          (fun ω => ρ (fun j => f j (Y ω)) (Y ω) i) =ᵐ[μ]
            (fun ω => pbar a b c φ + alphaP c φ β X i * Y ω) := by
  refine ⟨⟨(fun w y i=>(a+β*y+w i)/2),candidatePrices a b c φ β X,
    candidate_equilibrium μ θ Y a b c φ σ β hmodel hc hφ X⟩,?_⟩
  intro ρ f heq
  have hρ := (retailer_br a φ β hφ ρ).mp heq.1
  have hu := equilibrium_unique μ θ Y a b c φ σ β hmodel hc hφ X ρ f heq
  refine ⟨hρ,?_⟩
  intro i
  refine ⟨hu i,?_⟩
  filter_upwards [hu i] with ω hω
  rw [hρ,hω,candidate_retail a b c φ β hc hφ X i (Y ω)]



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
    (hc : 0< c) (hφ : 0< φ) (X : Fin 2→Status) (ρ) (f)
    (heq : IsPricingEq μ θ Y a b c φ β X ρ f) (i : Fin 2) :
    manufacturerProfit μ θ Y a b c φ ρ f i =
      (wbar a b c φ-b)*qBase a b c φ-c*(qBase a b c φ)^2+
      ((alphaW c φ β X i*qSlope c φ β X i-c*(qSlope c φ β X i)^2)/β+
        alphaW c φ β X i-2*c*qSlope c φ β X i-c)*σ^2 := by
  have hρ := (retailer_br a φ β hφ ρ).mp heq.1
  have hf := equilibrium_unique μ θ Y a b c φ σ β hmodel hc hφ X ρ f heq
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
    (hc : 0< c) (hφ : 0< φ) (X : Fin 2→Status) (ρ) (f)
    (heq : IsPricingEq μ θ Y a b c φ β X ρ f) :
    retailerProfit μ θ Y a φ ρ f =
      2*(qBase a b c φ)^2+
      (((β-alphaW c φ β X 0)/2*qSlope c φ β X 0+
        (β-alphaW c φ β X 1)/2*qSlope c φ β X 1)/β+
        (β-alphaW c φ β X 0)/2+(β-alphaW c φ β X 1)/2)*σ^2 := by
  have hρ := (retailer_br a φ β hφ ρ).mp heq.1
  have hf := equilibrium_unique μ θ Y a b c φ σ β hmodel hc hφ X ρ f heq
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
    (hb : 0 < b) (hc : 0 < c) (E : (Fin 2 → Status) → PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    let P := payoffTable μ θ Y a b c φ E
    (∀ i : Fin 2, P.M (fun _ => Status.uninformed) i = piM0 a b c φ σ β) ∧
    (∀ i : Fin 2, P.M (onlyInformed i) (other i) = piMU1 a b c φ σ β) ∧
    (∀ i : Fin 2, P.M (onlyInformed i) i = piMI1 a b c φ σ β) ∧
    (∀ i : Fin 2, P.M (fun _ => Status.informed) i = piM2 a b c φ σ β) := by
  have hβ := (signal_moments μ θ Y σ β hmodel).2.2.2
  have hA : 0<1+φ := by linarith
  have hJ : 0<2+(1+φ)*c := by positivity
  have hH : 0<2+φ+(1+φ)*c := by positivity
  dsimp only [payoffTable]
  refine ⟨?_,?_,?_,?_⟩ <;> intro i <;>
    rw [eq_manufacturer_value μ θ Y a b c φ σ β hmodel hc hφ _ _ _ (hE _)]
  all_goals
    fin_cases i <;>
      simp [qBase,qSlope,wbar,alphaW,num_u,num_i,num_only,onlyInformed,other,
        status_ne,status_ne',piM0,piMU1,piMI1,piM2,piMbar] <;>
      field_simp [hβ.ne',hA.ne',hJ.ne',hH.ne'] <;> ring

theorem profit_retailer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) (E : (Fin 2 → Status) → PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    let P := payoffTable μ θ Y a b c φ E
    P.R (fun _ => Status.uninformed) = piR0 a b c φ σ β ∧
    (∀ i : Fin 2, P.R (onlyInformed i) = piR1 a b c φ σ β) ∧
    P.R (fun _ => Status.informed) = piR2 a b c φ σ β := by
  have hβ := (signal_moments μ θ Y σ β hmodel).2.2.2
  have hA : 0<1+φ := by linarith
  have hJ : 0<2+(1+φ)*c := by positivity
  have hH : 0<2+φ+(1+φ)*c := by positivity
  dsimp only [payoffTable]
  refine ⟨?_,?_,?_⟩
  · rw [eq_retailer_value μ θ Y a b c φ σ β hmodel hc hφ _ _ _ (hE _)]
    simp [qBase,qSlope,wbar,alphaW,num_u,piR0,piRbar]
    field_simp [hβ.ne',hA.ne',hJ.ne',hH.ne'] <;> ring
  · intro i
    rw [eq_retailer_value μ θ Y a b c φ σ β hmodel hc hφ _ _ _ (hE _)]
    fin_cases i <;>
      simp [qBase,qSlope,wbar,alphaW,num_only,onlyInformed,other,
        status_ne,status_ne',piR1,piRbar] <;>
      field_simp [hβ.ne',hA.ne',hJ.ne',hH.ne'] <;> ring
  · rw [eq_retailer_value μ θ Y a b c φ σ β hmodel hc hφ _ _ _ (hE _)]
    simp [qBase,qSlope,wbar,alphaW,num_i,piR2,piRbar]
    field_simp [hβ.ne',hA.ne',hJ.ne',hH.ne'] <;> ring


theorem closed_orderings (a b c φ σ β : ℝ) (hc : 0< c) (hφ : 0< φ)
    (hσ : 0< σ) (hβ : 0< β) :
    (piM2 a b c φ σ β > piMI1 a b c φ σ β ∧
      piMI1 a b c φ σ β > piM0 a b c φ σ β ∧
      piM0 a b c φ σ β > piMU1 a b c φ σ β) ∧
    (piR0 a b c φ σ β > piR1 a b c φ σ β ∧
      piR1 a b c φ σ β > piR2 a b c φ σ β) ∧
    piR1 a b c φ σ β-piR2 a b c φ σ β >
      piR0 a b c φ σ β-piR1 a b c φ σ β := by
  have hA : 0<1+φ := by positivity
  have hJ : 0<2+(1+φ)*c := by positivity
  have hH : 0<2+φ+(1+φ)*c := by positivity
  have hm21 : piM2 a b c φ σ β-piMI1 a b c φ σ β =
      φ*(1+(1+φ)*c)*((1+φ)*(φ+2)*c+3*φ+4)*β*σ^2/
        (4*(1+φ)*(2+(1+φ)*c)*(2+φ+(1+φ)*c)^2) := by
    unfold piM2 piMI1
    field_simp [hA.ne',hJ.ne',hH.ne'] <;> ring
  have hm10 : piMI1 a b c φ σ β-piM0 a b c φ σ β =
      (1+(1+φ)*c)^2*β*σ^2/(4*(1+φ)*(2+(1+φ)*c)) := by
    unfold piMI1 piM0
    field_simp [hA.ne',hJ.ne',hH.ne'] <;> ring
  have hm0u : piM0 a b c φ σ β-piMU1 a b c φ σ β =
      c*φ*(1+(1+φ)*c)*((3*φ+2)*(1+φ)*c+5*φ+4)*β*σ^2/
        (4*(1+φ)^2*(2+(1+φ)*c)^2) := by
    unfold piM0 piMU1
    field_simp [hA.ne',hJ.ne',hH.ne'] <;> ring
  have hr01 : piR0 a b c φ σ β-piR1 a b c φ σ β =
      (1+(1+φ)*c)*(3+(1+φ)*c)*β*σ^2/(4*(1+φ)*(2+(1+φ)*c)^2) := by
    unfold piR0 piR1
    field_simp [hA.ne',hJ.ne',hH.ne'] <;> ring
  have hrex : (piR1 a b c φ σ β-piR2 a b c φ σ β)-
      (piR0 a b c φ σ β-piR1 a b c φ σ β) =
      φ*(1+(1+φ)*c)^2*((1+φ)^2*c^2+2*(1+φ)*(φ+3)*c+5*φ+8)*β*σ^2/
        (2*(1+φ)*(2+(1+φ)*c)^2*(2+φ+(1+φ)*c)^2) := by
    unfold piR0 piR1 piR2
    field_simp [hA.ne',hJ.ne',hH.ne'] <;> ring
  have h₁ : 0< piM2 a b c φ σ β-piMI1 a b c φ σ β := by rw [hm21];positivity
  have h₂ : 0< piMI1 a b c φ σ β-piM0 a b c φ σ β := by rw [hm10];positivity
  have h₃ : 0< piM0 a b c φ σ β-piMU1 a b c φ σ β := by rw [hm0u];positivity
  have h₄ : 0< piR0 a b c φ σ β-piR1 a b c φ σ β := by rw [hr01];positivity
  have h₅ : 0<(piR1 a b c φ σ β-piR2 a b c φ σ β)-
      (piR0 a b c φ σ β-piR1 a b c φ σ β) := by rw [hrex];positivity
  exact ⟨⟨by linarith,by linarith,by linarith⟩,⟨by linarith,by linarith⟩,by linarith⟩

theorem profit_orderings {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) (E : (Fin 2 → Status) → PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) (i : Fin 2) :
    let P := payoffTable μ θ Y a b c φ E
    (P.M (fun _ => Status.informed) i > P.M (onlyInformed i) i ∧
      P.M (onlyInformed i) i > P.M (fun _ => Status.uninformed) i ∧
      P.M (fun _ => Status.uninformed) i > P.M (onlyInformed i) (other i)) ∧
    (P.R (fun _ => Status.uninformed) > P.R (onlyInformed i) ∧
      P.R (onlyInformed i) > P.R (fun _ => Status.informed)) ∧
    P.R (onlyInformed i) - P.R (fun _ => Status.informed) >
      P.R (fun _ => Status.uninformed) - P.R (onlyInformed i) := by
  have hm := profit_manufacturers μ θ Y a b c φ σ β hmodel hφ hb hc E hE
  have hr := profit_retailer μ θ Y a b c φ σ β hmodel hφ hb hc E hE
  dsimp only at hm hr ⊢
  rw [hm.2.2.2 i,hm.2.2.1 i,hm.1 i,hm.2.1 i,hr.1,hr.2.1 i,hr.2.2]
  exact closed_orderings a b c φ σ β hc hφ hmodel.2.2.2.2.2.2.2.1
    (signal_moments μ θ Y σ β hmodel).2.2.2


theorem profile_cases (X : Fin 2→Status) :
    X=(fun _=> Status.uninformed) ∨ X=onlyInformed 0 ∨ X=onlyInformed 1 ∨
      X=(fun _=> Status.informed) := by
  have hv : X=![X 0,X 1] := by funext i;fin_cases i <;> rfl
  rw [hv]
  cases h₀ : X 0 <;> cases h₁ : X 1 <;>
    simp [funext_iff,Fin.forall_fin_two,onlyInformed]

theorem no_free_sharing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) (E : (Fin 2 → Status) → PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    let P := payoffTable μ θ Y a b c φ E
    (∃ X : Fin 2 → Status, IsNoContractOutcome P X) ∧
    ∀ X : Fin 2 → Status, IsNoContractOutcome P X → numInformed X = 0 := by
  let P:=payoffTable μ θ Y a b c φ E
  have hr := profit_retailer μ θ Y a b c φ σ β hmodel hφ hb hc E hE
  have ho := closed_orderings a b c φ σ β hc hφ hmodel.2.2.2.2.2.2.2.1
    (signal_moments μ θ Y σ β hmodel).2.2.2
  have hv (X : Fin 2→Status) (hx : X≠(fun _=> Status.uninformed)) :
      P.R X< P.R (fun _=> Status.uninformed) := by
    rcases profile_cases X with h|h|h|h
    · exact (hx h).elim
    · rw [h];exact (hr.2.1 0).trans_lt (ho.2.1.1.trans_eq hr.1.symm)
    · rw [h];exact (hr.2.1 1).trans_lt (ho.2.1.1.trans_eq hr.1.symm)
    · rw [h];exact hr.2.2.trans_lt ((ho.2.1.2.trans ho.2.1.1).trans_eq hr.1.symm)
  refine ⟨⟨(fun _=> Status.uninformed),?_⟩,?_⟩
  · intro X
    by_cases hx : X=(fun _=> Status.uninformed)
    · rw [hx]
    · exact (hv X hx).le
  · intro X hx
    by_cases he : X=(fun _=> Status.uninformed)
    · rw [he];exact num_u
    · exact ((hv X he).not_ge (hx _)).elim

open InfoSharing.Diseconomy
theorem forall_status (p : Status→Prop) : (∀ s,p s) ↔ p Status.informed ∧ p Status.uninformed := by
  constructor
  · intro h;exact ⟨h _,h _⟩
  · rintro ⟨hi,hu⟩ s;cases s;exact hi;exact hu
def table (m0 mu mi m2 r0 r1 r2 : ℝ) : PayoffTable where
  M X i := if X i=Status.informed then (if X (other i)=Status.informed then m2 else mi)
    else (if X (other i)=Status.informed then mu else m0)
  R X := if numInformed X=0 then r0 else if numInformed X=1 then r1 else r2

theorem ne_table (m0 mu mi m2 r0 r1 r2 T : ℝ) (h : mu< m0 ∧ m0< mi ∧ mi< m2)
    (X : Fin 2→Status) :
    IsPureNE (table m0 mu mi m2 r0 r1 r2) T X ↔
      (X=(fun _=> Status.uninformed) ∧ mi-m0≤ T) ∨
      (X=(fun _=> Status.informed) ∧ T≤ m2-mu) := by
  rcases profile_cases X with rfl|rfl|rfl|rfl
  all_goals
    simp [IsPureNE,Fin.forall_fin_two,forall_status,concManufacturerPayoff,table,other,
      onlyInformed,Function.update,funext_iff,Fin.forall_fin_two,status_ne,status_ne']
    first | (constructor <;> intro hh <;> linarith [h.1,h.2.1,h.2.2]) | (intro hh;linarith [h.1,h.2.1,h.2.2])

theorem pareto_table (m0 mu mi m2 r0 r1 r2 T : ℝ) (h : mu< m0 ∧ m0< mi ∧ mi< m2)
    (X : Fin 2→Status) :
    IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) T X ↔
      (X=(fun _=> Status.uninformed) ∧ m2-m0≤ T) ∨
      (X=(fun _=> Status.informed) ∧ T≤ m2-m0) := by
  let P:=table m0 mu mi m2 r0 r1 r2
  have huu (i : Fin 2) : concManufacturerPayoff P T (fun _=> Status.uninformed) i=m0 := by
    simp [P,table,concManufacturerPayoff,status_ne']
  have hii (i : Fin 2) : concManufacturerPayoff P T (fun _=> Status.informed) i=m2-T := by
    simp [P,table,concManufacturerPayoff]
  change (IsPureNE P T X ∧ ¬∃ X',IsPureNE P T X' ∧
    (∀ i,concManufacturerPayoff P T X i≤ concManufacturerPayoff P T X' i) ∧
    ∃ i,concManufacturerPayoff P T X i< concManufacturerPayoff P T X' i) ↔ _
  constructor
  · rintro ⟨hn,hp⟩
    rcases (ne_table _ _ _ _ _ _ _ _ h X).mp hn with ⟨rfl,ht⟩|⟨rfl,ht⟩
    · left;refine ⟨rfl,?_⟩
      by_contra hh
      have hstrict : m0< m2-T := by linarith
      apply hp
      refine ⟨(fun _=> Status.informed),(ne_table _ _ _ _ _ _ _ _ h _).mpr (Or.inr ⟨rfl,by linarith [h.1]⟩),?_,?_⟩
      · intro i;rw [huu,hii];exact hstrict.le
      · exact ⟨0,by rw [huu,hii];exact hstrict⟩
    · right;refine ⟨rfl,?_⟩
      by_contra hh
      have hstrict : m2-T< m0 := by linarith
      apply hp
      refine ⟨(fun _=> Status.uninformed),(ne_table _ _ _ _ _ _ _ _ h _).mpr (Or.inl ⟨rfl,by linarith [h.2.2]⟩),?_,?_⟩
      · intro i;rw [huu,hii];exact hstrict.le
      · exact ⟨0,by rw [huu,hii];exact hstrict⟩
  · rintro (⟨rfl,ht⟩|⟨rfl,ht⟩)
    · refine ⟨(ne_table _ _ _ _ _ _ _ _ h _).mpr (Or.inl ⟨rfl,by linarith [h.2.2]⟩),?_⟩
      rintro ⟨X',hn,hw,i,hi⟩
      rcases (ne_table _ _ _ _ _ _ _ _ h X').mp hn with ⟨rfl,_⟩|⟨rfl,_⟩
      · exact (lt_irrefl _ hi)
      · rw [huu,hii] at hi;linarith
    · refine ⟨(ne_table _ _ _ _ _ _ _ _ h _).mpr (Or.inr ⟨rfl,by linarith [h.1]⟩),?_⟩
      rintro ⟨X',hn,hw,i,hi⟩
      rcases (ne_table _ _ _ _ _ _ _ _ h X').mp hn with ⟨rfl,_⟩|⟨rfl,_⟩
      · rw [huu,hii] at hi;linarith
      · exact (lt_irrefl _ hi)


theorem conc_numbers (m0 mu mi m2 r0 r1 r2 : ℝ) (h : mu< m0 ∧ m0< mi ∧ mi< m2) :
    let P:=table m0 mu mi m2 r0 r1 r2
    (r2+2*(m2-m0)< r0 → ConcOptN P={0}) ∧
    (r0≤ r2+2*(m2-m0) → 2∈ ConcOptN P) ∧
    (r0< r2+2*(m2-m0) → ConcOptN P={2}) := by
  let P:=table m0 mu mi m2 r0 r1 r2
  change (_ → ConcOptN P={0}) ∧ (_ → 2∈ ConcOptN P) ∧ (_ → ConcOptN P={2})
  have hv : 0≤ m2-m0 := by linarith [h.2.1,h.2.2]
  have h0 (T : ℝ) : concRetailer P T (fun _=> Status.uninformed)=r0 := by
    simp [concRetailer,P,table,num_u]
  have h2 (T : ℝ) : concRetailer P T (fun _=> Status.informed)=r2+2*T := by
    simp [concRetailer,P,table,num_i];ring
  have hne0 := (pareto_table m0 mu mi m2 r0 r1 r2 (m2-m0) h (fun _=> Status.uninformed)).mpr
    (Or.inl ⟨rfl,le_refl _⟩)
  have hne2 := (pareto_table m0 mu mi m2 r0 r1 r2 (m2-m0) h (fun _=> Status.informed)).mpr
    (Or.inr ⟨rfl,le_refl _⟩)
  have hout0 (hg : r2+2*(m2-m0)≤ r0) : IsConcurrentOutcome P (m2-m0) (fun _=> Status.uninformed) := by
    refine ⟨hv,hne0,?_⟩
    intro T X hT hX
    rcases (pareto_table _ _ _ _ _ _ _ _ h X).mp hX with ⟨rfl,ht⟩|⟨rfl,ht⟩
    · rw [h0,h0]
    · rw [h2,h0];linarith
  have hout2 (hg : r0≤ r2+2*(m2-m0)) : IsConcurrentOutcome P (m2-m0) (fun _=> Status.informed) := by
    refine ⟨hv,hne2,?_⟩
    intro T X hT hX
    rcases (pareto_table _ _ _ _ _ _ _ _ h X).mp hX with ⟨rfl,ht⟩|⟨rfl,ht⟩
    · rw [h0,h2];exact hg
    · rw [h2,h2];linarith
  refine ⟨?_,?_,?_⟩
  · intro hg
    ext n
    constructor
    · rintro ⟨T,X,hX,hn⟩
      rcases (pareto_table _ _ _ _ _ _ _ _ h X).mp hX.2.1 with ⟨rfl,ht⟩|⟨rfl,ht⟩
      · simpa [num_u] using hn.symm
      · have ho:=hX.2.2 (m2-m0) (fun _=> Status.uninformed) hv hne0
        rw [h0,h2] at ho
        linarith
    · intro hn
      have : n=0:=hn
      subst n
      exact ⟨m2-m0,(fun _=> Status.uninformed),hout0 hg.le,num_u⟩
  · intro hg
    exact ⟨m2-m0,(fun _=> Status.informed),hout2 hg,num_i⟩
  · intro hg
    ext n
    constructor
    · rintro ⟨T,X,hX,hn⟩
      rcases (pareto_table _ _ _ _ _ _ _ _ h X).mp hX.2.1 with ⟨rfl,ht⟩|⟨rfl,ht⟩
      · have ho:=hX.2.2 (m2-m0) (fun _=> Status.informed) hv hne2
        rw [h2,h0] at ho
        linarith
      · simpa [num_i] using hn.symm
    · intro hn
      have : n=2:=hn
      subst n
      exact ⟨m2-m0,(fun _=> Status.informed),hout2 hg.le,num_i⟩


theorem payoff_eq_table {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β)
    (hφ : 0< φ) (hb : 0< b) (hc : 0< c) (E : (Fin 2→Status)→PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    payoffTable μ θ Y a b c φ E=table (piM0 a b c φ σ β) (piMU1 a b c φ σ β)
      (piMI1 a b c φ σ β) (piM2 a b c φ σ β)
      (piR0 a b c φ σ β) (piR1 a b c φ σ β) (piR2 a b c φ σ β) := by
  have hm:=profit_manufacturers μ θ Y a b c φ σ β hmodel hφ hb hc E hE
  have hr:=profit_retailer μ θ Y a b c φ σ β hmodel hφ hb hc E hE
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

theorem concurrent_root (φ : ℝ) (hφ : 0< φ) :
    ∃ C : ℝ,0< C ∧ (1+φ)*C^2+(φ+2)*C-1=0 ∧
    ∀ c : ℝ,0< c →
      ((1+φ)*c^2+(φ+2)*c-1<0 ↔ c< C) ∧
      (0≤ (1+φ)*c^2+(φ+2)*c-1 ↔ C≤ c) ∧
      (0<(1+φ)*c^2+(φ+2)*c-1 ↔ C< c) := by
  let g : ℝ→ℝ:=fun c=>(1+φ)*c^2+(φ+2)*c-1
  have hg : Continuous g := by fun_prop
  have hh : (0:ℝ)∈Set.Icc (g 0) (g 1) := by dsimp [g];constructor <;> nlinarith
  obtain ⟨C,hC,hroot⟩:=intermediate_value_Icc (a:=0) (b:=1) (by norm_num) hg.continuousOn hh
  have hCpos : 0< C := by
    have : C≠0 := by intro h;subst C;norm_num [g] at hroot
    exact lt_of_le_of_ne hC.1 (Ne.symm this)
  refine ⟨C,hCpos,hroot,?_⟩
  intro c hc
  have hfac : 0<(1+φ)*(c+C)+(φ+2) := by positivity
  have hdiff : g c=(c-C)*((1+φ)*(c+C)+(φ+2)) := by dsimp [g] at *;nlinarith [hroot]
  change (g c<0 ↔ c< C) ∧ (0≤ g c ↔ C≤ c) ∧ (0< g c ↔ C< c)
  rw [hdiff]
  refine ⟨?_,?_,?_⟩
  · constructor
    · intro hh
      by_contra hcc
      have hp:=mul_nonneg (sub_nonneg.mpr (le_of_not_gt hcc)) hfac.le
      linarith
    · intro hh
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hh) hfac
  · simp only [mul_nonneg_iff_of_pos_right hfac,sub_nonneg]
  · simp only [mul_pos_iff_of_pos_right hfac,sub_pos]

universe u
theorem concurrent_threshold :
    ∀ φ : ℝ, 0 < φ → ∃ cC : ℝ,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ) (a b c σ β : ℝ)
      (E : (Fin 2 → Status) → PricingProfile),
      IsSignalModel μ θ Y σ β → 0 < b → 0 < c → IsPricingEqFamily μ θ Y a b c φ β E →
      let P := payoffTable μ θ Y a b c φ E
      (c < cC → ConcOptN P = {0}) ∧
      (cC ≤ c → 2 ∈ ConcOptN P) ∧
      (cC < c → ConcOptN P = {2}) := by
  intro φ hφ
  obtain ⟨C,hC,hroot,hsgn⟩:=concurrent_root φ hφ
  refine ⟨C,?_⟩
  intro Ω _ μ θ Y a b c σ β E hmodel hb hc hE
  have hβ:0< β:=(signal_moments μ θ Y σ β hmodel).2.2.2
  have hσ:0< σ:=hmodel.2.2.2.2.2.2.2.1
  have hH:0<2+φ+(1+φ)*c:=by positivity
  have ho:=closed_orderings a b c φ σ β hc hφ hσ hβ
  have hn:=conc_numbers (piM0 a b c φ σ β) (piMU1 a b c φ σ β)
    (piMI1 a b c φ σ β) (piM2 a b c φ σ β)
    (piR0 a b c φ σ β) (piR1 a b c φ σ β) (piR2 a b c φ σ β)
    ⟨ho.1.2.2,ho.1.2.1,ho.1.1⟩
  dsimp only
  rw [payoff_eq_table μ θ Y a b c φ σ β hmodel hφ hb hc E hE]
  let K:=(1+(1+φ)*c)*β*σ^2/(2*(2+φ+(1+φ)*c)^2)
  have hK:0< K:=by dsimp [K];positivity
  have hgap:piR2 a b c φ σ β+2*(piM2 a b c φ σ β-piM0 a b c φ σ β)-
      piR0 a b c φ σ β=K*((1+φ)*c^2+(φ+2)*c-1) := by
    dsimp [piR2,piR0,piM2,piM0,K]
    field_simp [hH.ne'] <;> ring
  refine ⟨?_,?_,?_⟩
  · intro hlt
    apply hn.1
    have hh:=mul_neg_of_pos_of_neg hK ((hsgn c hc).1.mpr hlt)
    linarith
  · intro hle
    apply hn.2.1
    have hh:=mul_nonneg hK.le ((hsgn c hc).2.1.mpr hle)
    linarith
  · intro hlt
    apply hn.2.2
    have hh:=mul_pos hK ((hsgn c hc).2.2.mpr hlt)
    linarith
end
end InfoBase

set_option maxHeartbeats 1000000
open InfoSharing.Shared
namespace InfoSeq
noncomputable section
abbrev I := Status.informed
abbrev U := Status.uninformed
@[simp] theorem U_ne_I : Status.uninformed ≠ Status.informed := by decide
@[simp] theorem I_ne_U : Status.informed ≠ Status.uninformed := by decide
def val (vi vu:ℝ) (d:Status) : ℝ := if d=I then vi else vu
def pay (t:ℝ) (d:Status) : ℝ := if d=I then t else 0
def buyer (mi mu t:ℝ) (d:Status) : ℝ := val mi mu d-pay t d
def seller (ri ru t:ℝ) (d:Status) : ℝ := val ri ru d+pay t d

 theorem buyer_threshold (mi mu:ℝ) (acc:ℝ → Status)
    (hacc:∀ t d,0 ≤ t → buyer mi mu t d ≤ buyer mi mu t (acc t))
    (t:ℝ) (ht:0 ≤ t) :
    (acc t=I → t ≤ mi-mu) ∧ (acc t=U → mi-mu ≤ t) := by
  have hi := hacc t I ht
  have hu := hacc t U ht
  constructor <;> intro heq <;> rw [heq] at hi hu <;>
    simp [buyer,val,pay,I,U] at hi hu <;> linarith

 theorem seller_opt_value (mi mu ri ru:ℝ) (hg:0 < mi-mu) (acc:ℝ → Status)
    (hacc:∀ t d,0 ≤ t → buyer mi mu t d ≤ buyer mi mu t (acc t))
    (t:ℝ) (ht:0 ≤ t)
    (hopt:∀ t',0 ≤ t' → seller ri ru t' (acc t') ≤ seller ri ru t (acc t)) :
    seller ri ru t (acc t)=max ru (ri+(mi-mu)) := by
  apply le_antisymm
  · cases h:acc t with
    | informed =>
      have hh := (buyer_threshold mi mu acc hacc t ht).1 h
      change ri+t ≤ max ru (ri+(mi-mu))
      exact (by linarith : ri+t ≤ ri+(mi-mu)).trans (le_max_right _ _)
    | uninformed => simpa [seller,val,pay,I,U,h] using le_max_left ru (ri+(mi-mu))
  · apply max_le
    · have hp:0 ≤ mi-mu+1 := by linarith
      have hu : acc (mi-mu+1)=U := by
        cases heq:acc (mi-mu+1) with
        | uninformed => rfl
        | informed =>
          have hh := (buyer_threshold mi mu acc hacc _ hp).1 heq
          linarith
      have hh := hopt (mi-mu+1) hp
      simpa [seller,val,pay,I,U,hu] using hh
    · apply le_of_forall_pos_le_add
      intro eps heps
      let eta := min ((mi-mu)/2) (eps/2)
      have heta : 0 < eta := by dsimp [eta]; positivity
      have hetag : eta ≤ (mi-mu)/2 := min_le_left _ _
      have hetae : eta ≤ eps/2 := min_le_right _ _
      have hp : 0 ≤ mi-mu-eta := by linarith
      have hi : acc (mi-mu-eta)=I := by
        cases heq:acc (mi-mu-eta) with
        | informed => rfl
        | uninformed =>
          have hh := (buyer_threshold mi mu acc hacc _ hp).2 heq
          linarith
      have hh := hopt (mi-mu-eta) hp
      rw [hi] at hh
      change ri+(mi-mu-eta) ≤ seller ri ru t (acc t) at hh
      linarith

 theorem seller_opt_status (mi mu ri ru:ℝ) (hg:0 < mi-mu) (acc:ℝ → Status)
    (hacc:∀ t d,0 ≤ t → buyer mi mu t d ≤ buyer mi mu t (acc t))
    (t:ℝ) (ht:0 ≤ t)
    (hopt:∀ t',0 ≤ t' → seller ri ru t' (acc t') ≤ seller ri ru t (acc t)) :
    (ri+(mi-mu) < ru → acc t=U) ∧ (ru < ri+(mi-mu) → acc t=I) ∧
      (acc t=I → t=mi-mu) := by
  have hv := seller_opt_value mi mu ri ru hg acc hacc t ht hopt
  have hb := buyer_threshold mi mu acc hacc t ht
  refine ⟨?_,?_,?_⟩
  · intro hlt
    cases heq:acc t with
    | uninformed => rfl
    | informed =>
      have hle := hb.1 heq
      rw [heq] at hv
      simp [seller,val,pay,I,U,max_eq_left hlt.le] at hv
      linarith
  · intro hlt
    cases heq:acc t with
    | informed => rfl
    | uninformed =>
      rw [heq] at hv
      simp [seller,val,pay,I,U,max_eq_right hlt.le] at hv
      linarith
  · intro hi
    have hle := hb.1 hi
    rw [hi] at hv
    change ri+t=max ru (ri+(mi-mu)) at hv
    have hge := le_max_right ru (ri+(mi-mu))
    linarith

 def accept (g t:ℝ) : Status := if t ≤ g then I else U
 theorem accept_opt (mi mu:ℝ) :
    ∀ t d,0 ≤ t → buyer mi mu t d ≤ buyer mi mu t (accept (mi-mu) t) := by
  intro t d ht
  unfold accept
  split_ifs with h
  · cases d <;> simp [buyer,val,pay,I,U] <;> linarith
  · cases d <;> simp [buyer,val,pay,I,U] <;> linarith

 def bestOffer (g ri ru:ℝ) : ℝ := if ru ≤ ri+g then g else g+1
 theorem bestOffer_opt (g ri ru:ℝ) (hg:0 < g) :
    0 ≤ bestOffer g ri ru ∧
    ∀ t,0 ≤ t → seller ri ru t (accept g t) ≤
      seller ri ru (bestOffer g ri ru) (accept g (bestOffer g ri ru)) := by
  unfold bestOffer
  split_ifs with h
  · refine ⟨hg.le,?_⟩
    intro t ht
    by_cases ht' : t ≤ g
    · simp [accept,seller,val,pay,I,U,ht'] <;> linarith
    · simpa [accept,seller,val,pay,I,U,ht'] using h
  · refine ⟨by linarith,?_⟩
    intro t ht
    have hh : ¬ g+1 ≤ g := by linarith
    by_cases ht' : t ≤ g
    · simp [accept,seller,val,pay,I,U,ht',hh];linarith
    · simp [accept,seller,val,pay,I,U,ht',hh]

def table (m0 mu mi m2 r0 r1 r2 : ℝ) : PayoffTable where
  M X i := if X i=I then (if X (other i)=I then m2 else mi)
    else (if X (other i)=I then mu else m0)
  R X := if numInformed X=0 then r0 else if numInformed X=1 then r1 else r2

 theorem second_pay (m0 mu mi m2 r0 r1 r2 Tf Ts:ℝ) (k:Fin 2) (dk ds:Status) :
    seqMfrPayoff (table m0 mu mi m2 r0 r1 r2) k Tf dk Ts ds (other k)=
      buyer (val m2 mi dk) (val mu m0 dk) Ts ds := by
  fin_cases k <;> cases dk <;> cases ds <;>
    norm_num [seqMfrPayoff,seqProfile,table,buyer,val,pay,I,U,other]

 theorem first_pay (m0 mu mi m2 r0 r1 r2 Tf Ts:ℝ) (k:Fin 2) (dk ds:Status) :
    seqMfrPayoff (table m0 mu mi m2 r0 r1 r2) k Tf dk Ts ds k=
      buyer (val m2 mi ds) (val mu m0 ds) Tf dk := by
  fin_cases k <;> cases dk <;> cases ds <;>
    norm_num [seqMfrPayoff,seqProfile,table,buyer,val,pay,I,U,other]

 theorem ret_pay (m0 mu mi m2 r0 r1 r2 Tf Ts:ℝ) (k:Fin 2) (dk ds:Status) :
    seqRetPayoff (table m0 mu mi m2 r0 r1 r2) k Tf dk Ts ds=
      seller (val r2 r1 dk) (val r1 r0 dk) Ts ds+pay Tf dk := by
  fin_cases k <;> cases dk <;> cases ds <;>
    norm_num [seqRetPayoff,seqProfile,table,seller,val,pay,I,U,other,numInformed,
      Finset.univ_fin2,Finset.filter_insert,Finset.filter_singleton] <;> ring

 theorem second_optimal (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2) (s:SeqStrategy)
    (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (Tf:ℝ) (hTf:0 ≤ Tf) (dk:Status) :
    (∀ t d,0 ≤ t → buyer (val m2 mi dk) (val mu m0 dk) t d ≤
      buyer (val m2 mi dk) (val mu m0 dk) t (s.accS Tf dk t)) ∧
    0 ≤ s.Ts Tf dk ∧
    (∀ t,0 ≤ t → seller (val r2 r1 dk) (val r1 r0 dk) t (s.accS Tf dk t) ≤
      seller (val r2 r1 dk) (val r1 r0 dk) (s.Ts Tf dk) (s.accS Tf dk (s.Ts Tf dk))) := by
  refine ⟨?_,(hs.2.1 Tf dk hTf).1,?_⟩
  · intro t d ht
    simpa only [second_pay] using hs.1 Tf dk t d hTf ht
  · intro t ht
    have hh := (hs.2.1 Tf dk hTf).2 t ht
    simpa only [ret_pay,add_le_add_iff_right] using hh

 theorem second_characterization (m0 mu mi m2 r0 r1 r2:ℝ)
    (hg0:0 < mi-m0) (hg1:0 < m2-mu) (k:Fin 2) (s:SeqStrategy)
    (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (Tf:ℝ) (hTf:0 ≤ Tf) (dk:Status) :
    let g:=val m2 mi dk-val mu m0 dk
    let ri:=val r2 r1 dk
    let ru:=val r1 r0 dk
    seller ri ru (s.Ts Tf dk) (s.accS Tf dk (s.Ts Tf dk))=max ru (ri+g) ∧
    (ri+g < ru → s.accS Tf dk (s.Ts Tf dk)=U) ∧
    (ru < ri+g → s.accS Tf dk (s.Ts Tf dk)=I) ∧
    (s.accS Tf dk (s.Ts Tf dk)=I → s.Ts Tf dk=g) := by
  dsimp only
  have hg : 0 < val m2 mi dk-val mu m0 dk := by
    cases dk
    · simpa [val,I,U] using hg1
    · simpa [val,I,U] using hg0
  obtain ⟨ha,ht,ho⟩ := second_optimal m0 mu mi m2 r0 r1 r2 k s hs Tf hTf dk
  exact ⟨seller_opt_value _ _ _ _ hg _ ha _ ht ho,
    seller_opt_status _ _ _ _ hg _ ha _ ht ho⟩

 theorem first_optimal (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2) (s:SeqStrategy)
    (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (q:Status → Status) (V:Status → ℝ)
    (hq:∀ Tf,0 ≤ Tf → ∀ dk,s.accS Tf dk (s.Ts Tf dk)=q dk)
    (hV:∀ Tf,0 ≤ Tf → ∀ dk,
      seller (val r2 r1 dk) (val r1 r0 dk) (s.Ts Tf dk) (s.accS Tf dk (s.Ts Tf dk))=V dk) :
    (∀ t d,0 ≤ t → buyer (val m2 mi (q I)) (val mu m0 (q U)) t d ≤
      buyer (val m2 mi (q I)) (val mu m0 (q U)) t (s.accF t)) ∧
    0 ≤ s.Tf ∧
    (∀ t,0 ≤ t → seller (V I) (V U) t (s.accF t) ≤
      seller (V I) (V U) s.Tf (s.accF s.Tf)) := by
  have hmfr (t:ℝ) (ht:0 ≤ t) (d:Status) :
      seqMfrPayoff (table m0 mu mi m2 r0 r1 r2) k t d (s.Ts t d)
        (s.accS t d (s.Ts t d)) k=buyer (val m2 mi (q I)) (val mu m0 (q U)) t d := by
    rw [first_pay,hq t ht d]
    cases d <;> simp [buyer,val,pay,I,U]
  have hret (t:ℝ) (ht:0 ≤ t) (d:Status) :
      seqRetPayoff (table m0 mu mi m2 r0 r1 r2) k t d (s.Ts t d)
        (s.accS t d (s.Ts t d))=seller (V I) (V U) t d := by
    rw [ret_pay,hV t ht d]
    cases d <;> simp [seller,val,pay,I,U]
  refine ⟨?_,hs.2.2.2.1,?_⟩
  · intro t d ht
    simpa only [hmfr t ht] using hs.2.2.1 t d ht
  · intro t ht
    simpa only [hret t ht,hret s.Tf hs.2.2.2.1] using hs.2.2.2.2 t ht

 def chosenOffer (g:ℝ) (d:Status) : ℝ := if d=I then g else g+1
 theorem chosen_opt (g ri ru:ℝ) (hg:0 < g) (d:Status)
    (hd : (d=I → ru ≤ ri+g) ∧ (d=U → ri+g ≤ ru)) :
    0 ≤ chosenOffer g d ∧ accept g (chosenOffer g d)=d ∧
    ∀ t,0 ≤ t → seller ri ru t (accept g t) ≤
      seller ri ru (chosenOffer g d) d := by
  cases d with
  | informed =>
    have h := hd.1 rfl
    refine ⟨by simpa [chosenOffer,I] using hg.le,by simp [chosenOffer,accept,I],?_⟩
    intro t ht
    by_cases htg:t ≤ g
    · simp [chosenOffer,accept,seller,val,pay,I,U,htg] <;> linarith
    · simpa [chosenOffer,accept,seller,val,pay,I,U,htg] using h
  | uninformed =>
    have h := hd.2 rfl
    have hgg : ¬ g+1 ≤ g := by linarith
    refine ⟨by simp [chosenOffer,I,U];linarith,by simp [chosenOffer,accept,I,U,hgg],?_⟩
    intro t ht
    by_cases htg:t ≤ g
    · simp [chosenOffer,accept,seller,val,pay,I,U,htg] <;> linarith
    · simp [chosenOffer,accept,seller,val,pay,I,U,htg]

 theorem exists_seq (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2)
    (q:Status → Status) (d:Status)
    (hg:∀ z:Status,0 < val m2 mi z-val mu m0 z)
    (hq:∀ z:Status,(q z=I → val r1 r0 z ≤ val r2 r1 z+(val m2 mi z-val mu m0 z)) ∧
      (q z=U → val r2 r1 z+(val m2 mi z-val mu m0 z) ≤ val r1 r0 z))
    (hgf:0 < val m2 mi (q I)-val mu m0 (q U))
    (hd : let V:=fun z=> val (val r2 r1 z+(val m2 mi z-val mu m0 z)) (val r1 r0 z) (q z)
      (d=I → V U ≤ V I+(val m2 mi (q I)-val mu m0 (q U))) ∧
      (d=U → V I+(val m2 mi (q I)-val mu m0 (q U)) ≤ V U)) :
    ∃ s:SeqStrategy,IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s ∧
      s.accF s.Tf=d ∧ s.accS s.Tf d (s.Ts s.Tf d)=q d := by
  let g := fun z=> val m2 mi z-val mu m0 z
  let V := fun z=> val (val r2 r1 z+g z) (val r1 r0 z) (q z)
  let gf := val m2 mi (q I)-val mu m0 (q U)
  let s : SeqStrategy := ⟨chosenOffer gf d,accept gf,
    (fun _ z=> chosenOffer (g z) (q z)),(fun _ z=> accept (g z))⟩
  have hsec (t:ℝ) (z:Status) : s.accS t z (s.Ts t z)=q z :=
    (chosen_opt (g z) (val r2 r1 z) (val r1 r0 z) (hg z) (q z) (hq z)).2.1
  have hsecV (t:ℝ) (z:Status) :
      seller (val r2 r1 z) (val r1 r0 z) (s.Ts t z) (s.accS t z (s.Ts t z))=V z := by
    rw [hsec]
    dsimp [s,V,chosenOffer,seller,val,pay]
    split_ifs <;> ring
  have hfirst := chosen_opt gf (V I) (V U) hgf d hd
  have hmfr (t:ℝ) (z:Status) :
      seqMfrPayoff (table m0 mu mi m2 r0 r1 r2) k t z (s.Ts t z)
        (s.accS t z (s.Ts t z)) k=buyer (val m2 mi (q I)) (val mu m0 (q U)) t z := by
    rw [first_pay,hsec]
    cases z <;> simp [buyer,val,pay,I,U]
  have hret (t:ℝ) (z:Status) :
      seqRetPayoff (table m0 mu mi m2 r0 r1 r2) k t z (s.Ts t z)
        (s.accS t z (s.Ts t z))=seller (V I) (V U) t z := by
    rw [ret_pay,hsecV]
    cases z <;> simp [seller,val,pay,I,U]
  refine ⟨s,⟨?_,?_,?_,hfirst.1,?_⟩,hfirst.2.1,hsec _ _⟩
  · intro Tf z Ts d' hTf hTs
    rw [second_pay,second_pay]
    exact accept_opt _ _ Ts d' hTs
  · intro Tf z hTf
    have hh := chosen_opt (g z) (val r2 r1 z) (val r1 r0 z) (hg z) (q z) (hq z)
    refine ⟨hh.1,?_⟩
    intro Ts hTs
    rw [ret_pay,ret_pay,hsec]
    exact add_le_add (hh.2.2 Ts hTs) (le_refl (pay Tf z))
  · intro Tf z hTf
    rw [hmfr,hmfr]
    exact accept_opt _ _ Tf z hTf
  · intro Tf hTf
    rw [hret,hret]
    change seller (V I) (V U) Tf (accept gf Tf) ≤ seller (V I) (V U) (chosenOffer gf d) (accept gf (chosenOffer gf d))
    rw [hfirst.2.1]
    exact hfirst.2.2 Tf hTf

 theorem seq_strict (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2)
    (q:Status → Status) (d:Status)
    (hg:∀ z:Status,0 < val m2 mi z-val mu m0 z)
    (hq:∀ z:Status,(q z=I → val r1 r0 z < val r2 r1 z+(val m2 mi z-val mu m0 z)) ∧
      (q z=U → val r2 r1 z+(val m2 mi z-val mu m0 z) < val r1 r0 z))
    (hgf:0 < val m2 mi (q I)-val mu m0 (q U))
    (hd : let V:=fun z=> max (val r1 r0 z) (val r2 r1 z+(val m2 mi z-val mu m0 z))
      (d=I → V U < V I+(val m2 mi (q I)-val mu m0 (q U))) ∧
      (d=U → V I+(val m2 mi (q I)-val mu m0 (q U)) < V U))
    (s:SeqStrategy) (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s) :
    s.accF s.Tf=d ∧ s.accS s.Tf d (s.Ts s.Tf d)=q d := by
  let V:=fun z=> max (val r1 r0 z) (val r2 r1 z+(val m2 mi z-val mu m0 z))
  have hg0 : 0 < mi-m0 := by simpa [val,I,U] using hg U
  have hg1 : 0 < m2-mu := by simpa [val,I,U] using hg I
  have hq' (Tf:ℝ) (hTf:0 ≤ Tf) (z:Status) : s.accS Tf z (s.Ts Tf z)=q z := by
    have hh := second_characterization m0 mu mi m2 r0 r1 r2 hg0 hg1 k s hs Tf hTf z
    cases heq:q z with
    | informed => exact hh.2.2.1 ((hq z).1 heq)
    | uninformed => exact hh.2.1 ((hq z).2 heq)
  have hV (Tf:ℝ) (hTf:0 ≤ Tf) (z:Status) :
      seller (val r2 r1 z) (val r1 r0 z) (s.Ts Tf z) (s.accS Tf z (s.Ts Tf z))=V z :=
    (second_characterization m0 mu mi m2 r0 r1 r2 hg0 hg1 k s hs Tf hTf z).1
  obtain ⟨ha,ht,ho⟩ := first_optimal m0 mu mi m2 r0 r1 r2 k s hs q V hq' hV
  have hc := seller_opt_status _ _ _ _ hgf _ ha _ ht ho
  have hd' : s.accF s.Tf=d := by
    cases d with
    | informed => exact hc.2.1 (hd.1 rfl)
    | uninformed => exact hc.1 (hd.2 rfl)
  exact ⟨hd',hq' s.Tf hs.2.2.2.1 d⟩

 theorem num_seq (k:Fin 2) (d e:Status) :
    numInformed (seqProfile k d e)=(if d=I then 1 else 0)+(if e=I then 1 else 0) := by
  fin_cases k <;> cases d <;> cases e <;> decide

 theorem mem_seq_number {P:PayoffTable} {k:Fin 2} {d e:Status}
    (hex:∃ s:SeqStrategy,IsSequentialSPE P k s ∧ s.accF s.Tf=d ∧ s.accS s.Tf d (s.Ts s.Tf d)=e) :
    (if d=I then 1 else 0)+(if e=I then 1 else 0) ∈ SeqOptN P k := by
  obtain ⟨s,hs,hf,he⟩ := hex
  refine ⟨s,hs,?_⟩
  simpa only [seqPath,hf,he] using num_seq k d e

 theorem seq_number_unique {P:PayoffTable} {k:Fin 2} {d e:Status}
    (hall:∀ s:SeqStrategy,IsSequentialSPE P k s → s.accF s.Tf=d ∧ s.accS s.Tf d (s.Ts s.Tf d)=e) :
    SeqOptN P k ⊆ {(if d=I then 1 else 0)+(if e=I then 1 else 0)} := by
  rintro n ⟨s,hs,hn⟩
  obtain ⟨hf,he⟩ := hall s hs
  have hv := num_seq k d e
  have heq : numInformed (seqPath k s)=(if d=I then 1 else 0)+(if e=I then 1 else 0) := by
    simpa only [seqPath,hf,he] using hv
  exact hn.symm.trans heq

 theorem seq_zero_mem (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2)
    (ha:r1+(mi-m0) ≤ r0) (hb:r2+(m2-mu) ≤ r1) :
    0 ∈ SeqOptN (table m0 mu mi m2 r0 r1 r2) k := by
  have hex := exists_seq m0 mu mi m2 r0 r1 r2 k (fun _=> U) U
    (by intro z;cases z <;> simp [val,I,U] <;> linarith [h.1,h.2.1,h.2.2])
    (by intro z;cases z <;> simp [val,I,U] <;> linarith)
    (by simp [val,I,U];linarith [h.2.1])
    (by simp [val,I,U];exact ha)
  simpa [I,U] using mem_seq_number hex
 theorem seq_zero_only (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2)
    (ha:r1+(mi-m0) < r0) (hb:r2+(m2-mu) < r1) :
    SeqOptN (table m0 mu mi m2 r0 r1 r2) k ⊆ {0} := by
  have hall := seq_strict m0 mu mi m2 r0 r1 r2 k (fun _=> U) U
    (by intro z;cases z <;> simp [val,I,U] <;> linarith [h.1,h.2.1,h.2.2])
    (by intro z;cases z <;> simp [val,I,U] <;> linarith)
    (by simp [val,I,U];linarith [h.2.1])
    (by simp [val,I,U,max_eq_left ha.le,max_eq_left hb.le];exact ha)
  simpa [I,U] using seq_number_unique hall

 theorem seq_one_mem (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2)
    (ha:r0 ≤ r1+(mi-m0)) (hb:r2+(m2-mu) ≤ r1) :
    1 ∈ SeqOptN (table m0 mu mi m2 r0 r1 r2) k := by
  let q := fun z:Status=> if z=I then U else I
  have hex := exists_seq m0 mu mi m2 r0 r1 r2 k q I
    (by intro z;cases z <;> simp [val,I,U] <;> linarith [h.1,h.2.1,h.2.2])
    (by intro z;cases z <;> simp [q,val,I,U] <;> linarith)
    (by simp [q,val,I,U];linarith [h.1,h.2.1])
    (by simp [q,val,I,U];linarith [h.1])
  simpa [q,I,U] using mem_seq_number hex
 theorem seq_one_only (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2)
    (ha:r0 < r1+(mi-m0)) (hb:r2+(m2-mu) < r1) :
    SeqOptN (table m0 mu mi m2 r0 r1 r2) k ⊆ {1} := by
  let q := fun z:Status=> if z=I then U else I
  have hall := seq_strict m0 mu mi m2 r0 r1 r2 k q I
    (by intro z;cases z <;> simp [val,I,U] <;> linarith [h.1,h.2.1,h.2.2])
    (by intro z;cases z <;> simp [q,val,I,U] <;> linarith)
    (by simp [q,val,I,U];linarith [h.1,h.2.1])
    (by simp [q,val,I,U,max_eq_right ha.le,max_eq_left hb.le];linarith [h.1])
  simpa [q,I,U] using seq_number_unique hall

 theorem seq_two_mem (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2)
    (ha:r0 ≤ r1+(mi-m0)) (hb:r1 ≤ r2+(m2-mu)) :
    2 ∈ SeqOptN (table m0 mu mi m2 r0 r1 r2) k := by
  have hex := exists_seq m0 mu mi m2 r0 r1 r2 k (fun _=> I) I
    (by intro z;cases z <;> simp [val,I,U] <;> linarith [h.1,h.2.1,h.2.2])
    (by intro z;cases z <;> simp [val,I,U] <;> linarith)
    (by simp [val,I,U];linarith [h.1,h.2.1,h.2.2])
    (by simp [val,I,U];linarith [h.1,h.2.2])
  simpa [I,U] using mem_seq_number hex
 theorem seq_two_only (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2)
    (ha:r0 < r1+(mi-m0)) (hb:r1 < r2+(m2-mu)) :
    SeqOptN (table m0 mu mi m2 r0 r1 r2) k ⊆ {2} := by
  have hall := seq_strict m0 mu mi m2 r0 r1 r2 k (fun _=> I) I
    (by intro z;cases z <;> simp [val,I,U] <;> linarith [h.1,h.2.1,h.2.2])
    (by intro z;cases z <;> simp [val,I,U] <;> linarith)
    (by simp [val,I,U];linarith [h.1,h.2.1,h.2.2])
    (by simp [val,I,U,max_eq_right ha.le,max_eq_right hb.le];linarith [h.1,h.2.2])
  simpa [I,U] using seq_number_unique hall
end
end InfoSeq

set_option maxHeartbeats 3000000
open InfoSharing.Shared
namespace InfoSeq
noncomputable section
 def qPoly (p z:ℝ) : ℝ :=
    (2*p+1)^2*z^4+(6*p^3+27*p^2+24*p+6)*z^3+
      (p^4+16*p^3+49*p^2+42*p+11)*z^2+
      (-2*p^4-4*p^3+5*p^2+10*p+4)*z-
      (5*p^4+22*p^3+33*p^2+20*p+4)
 theorem q_root (p:ℝ) (hp:0 < p) :
    ∃ Z:ℝ,0 < Z ∧ Z < 4 ∧ qPoly p Z=0 ∧ ∀ z:ℝ,0 < z →
      (qPoly p z < 0 ↔ z < Z) ∧ (0 ≤ qPoly p z ↔ Z ≤ z) ∧ (0 < qPoly p z ↔ Z < z) := by
  have hq0 : qPoly p 0 < 0 := by
    have hh:0 < 5*p^4+22*p^3+33*p^2+20*p+4 := by positivity
    dsimp [qPoly]
    nlinarith only [hh]
  have hq4 : 0 < qPoly p 4 := by
    have hh : qPoly p 4=3*p^4+602*p^3+3523*p^2+3252*p+828 := by unfold qPoly;ring
    rw [hh];positivity
  have hcont : Continuous (qPoly p) := by unfold qPoly;fun_prop
  obtain ⟨Z,hZ,hroot⟩ := intermediate_value_Icc (a:=0) (b:=4) (by norm_num) hcont.continuousOn ⟨hq0.le,hq4.le⟩
  have hZpos : 0 < Z := by
    have hne:Z ≠ 0 := by intro hh;rw [hh] at hroot;linarith
    exact lt_of_le_of_ne hZ.1 hne.symm
  have hZlt : Z < 4 := by
    have hne:Z ≠ 4 := by intro hh;rw [hh] at hroot;linarith
    exact lt_of_le_of_ne hZ.2 hne
  refine ⟨Z,hZpos,hZlt,hroot,?_⟩
  intro z hz
  let K := (2*p+1)^2*(z^3*Z+z^2*Z^2+z*Z^3)+
    (6*p^3+27*p^2+24*p+6)*(z^2*Z+z*Z^2)+
    (p^4+16*p^3+49*p^2+42*p+11)*z*Z+(5*p^4+22*p^3+33*p^2+20*p+4)
  have hK : 0 < K := by dsimp [K];positivity
  have hid : qPoly p z*Z=(z-Z)*K := by
    calc
      _ = (z-Z)*K+z*qPoly p Z := by dsimp [qPoly,K];ring
      _ = _ := by rw [hroot];ring
  have hn : qPoly p z < 0 ↔ qPoly p z*Z < 0 := by
    simpa only [not_le] using (not_congr (mul_nonneg_iff_of_pos_right hZpos)).symm
  have hnn : 0 ≤ qPoly p z ↔ 0 ≤ qPoly p z*Z := by simp [mul_nonneg_iff_of_pos_right hZpos]
  have hp' : 0 < qPoly p z ↔ 0 < qPoly p z*Z := by simp [mul_pos_iff_of_pos_right hZpos]
  rw [hn,hnn,hp',hid]
  refine ⟨?_,?_,?_⟩
  · rw [← not_le,mul_nonneg_iff_of_pos_right hK,not_le,sub_neg]
  · simp [mul_nonneg_iff_of_pos_right hK]
  · simp [mul_pos_iff_of_pos_right hK]

 theorem sequential_gaps (a b c p sig beta:ℝ) (hp:0 < p) (hc:0 < c) :
    piR1 a b c p sig beta+(piMI1 a b c p sig beta-piM0 a b c p sig beta)-piR0 a b c p sig beta=
      ((1+(1+p)*c)*beta*sig^2/(4*(1+p)*(2+(1+p)*c)^2))*(((1+p)*c)^2+2*((1+p)*c)-1) ∧
    piR2 a b c p sig beta+(piM2 a b c p sig beta-piMU1 a b c p sig beta)-piR1 a b c p sig beta=
      ((1+(1+p)*c)*beta*sig^2/(4*(1+p)^3*(2+(1+p)*c)^2*(2+p+(1+p)*c)^2))*qPoly p ((1+p)*c) := by
  have hA:1+p ≠ 0 := ne_of_gt (by positivity)
  have hJ:2+(1+p)*c ≠ 0 := ne_of_gt (by positivity)
  have hH:2+p+(1+p)*c ≠ 0 := ne_of_gt (by positivity)
  constructor
  · unfold piR1 piMI1 piM0 piR0
    field_simp [hA,hJ,hH] <;> ring
  · unfold piR2 piM2 piMU1 piR1 qPoly
    field_simp [hA,hJ,hH] <;> ring

 theorem first_root_sign (z:ℝ) (hz:0 < z) :
    (z^2+2*z-1 < 0 ↔ z < Real.sqrt 2-1) ∧
    (0 ≤ z^2+2*z-1 ↔ Real.sqrt 2-1 ≤ z) ∧
    (0 < z^2+2*z-1 ↔ Real.sqrt 2-1 < z) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hk : 0 < z+Real.sqrt 2+1 := by positivity
  have hid : z^2+2*z-1=(z-(Real.sqrt 2-1))*(z+Real.sqrt 2+1) := by nlinarith only [hs]
  rw [hid]
  refine ⟨?_,?_,?_⟩
  · rw [← not_le,mul_nonneg_iff_of_pos_right hk,not_le,sub_neg]
  · simp [mul_nonneg_iff_of_pos_right hk]
  · simp [mul_pos_iff_of_pos_right hk]

 theorem concurrent_normalized (p z:ℝ) (hp:0 < p) (hz:0 < z)
    (heq:z^2+(p+2)*z-(p+1)=0) :
    Real.sqrt 2-1 < z ∧ qPoly p z < 0 := by
  have hz1 : z < 1 := by
    by_contra hh
    have hzle : 1 ≤ z := le_of_not_gt hh
    have hprod := mul_nonneg hp.le (sub_nonneg.mpr hzle)
    nlinarith only [heq,hzle,hprod,sq_nonneg (z-1)]
  have hf : 0 < z^2+2*z-1 := by
    have hh := mul_pos hp (sub_pos.mpr hz1)
    nlinarith only [heq,hh]
  refine ⟨(first_root_sign z hz).2.2.mp hf,?_⟩
  have hid : qPoly p z =
      p*(p+1)*(p^3*(z-1)-4*p^2-p*z-5*p-z-3) := by
    have hh : qPoly p z-p*(p+1)*(p^3*(z-1)-4*p^2-p*z-5*p-z-3)=
        (z^2+(p+2)*z-(p+1))*
          ((4*p^2+4*p+1)*z^2+(2*p^3+15*p^2+15*p+4)*z-p^4+p^3+12*p^2+13*p+4) := by
      unfold qPoly
      ring
    rw [heq,zero_mul] at hh
    linarith only [hh]
  rw [hid]
  apply mul_neg_of_pos_of_neg (by positivity)
  have hterm : p^3*(z-1) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have hpz : 0 < p*z := mul_pos hp hz
  nlinarith only [hterm,hpz,hp,hz,sq_nonneg p]

 theorem thresholds_order (p C Z:ℝ) (hp:0 < p) (hC:0 < C)
    (hCeq:(1+p)*C^2+(p+2)*C-1=0)
    (hZ:∀ z:ℝ,0 < z → (qPoly p z < 0 ↔ z < Z)) :
    (Real.sqrt 2-1)/(1+p) < C ∧ C < Z/(1+p) := by
  have hA : 0 < 1+p := by positivity
  have hscaled := congrArg (fun x:ℝ=>(1+p)*x) hCeq
  have heq : ((1+p)*C)^2+(p+2)*((1+p)*C)-(p+1)=0 := by
    nlinarith only [hscaled]
  have hz := mul_pos hA hC
  have hh := concurrent_normalized p ((1+p)*C) hp hz heq
  constructor
  · apply (div_lt_iff₀ hA).mpr
    nlinarith only [hh.1]
  · apply (lt_div_iff₀ hA).mpr
    have hlt := (hZ _ hz).mp hh.2
    nlinarith only [hlt]
end
end InfoSeq

set_option maxHeartbeats 1500000
open InfoSharing.Shared
namespace InfoSeq
noncomputable section
 def stageValue (m0 mu mi m2 r0 r1 r2:ℝ) (d:Status) : ℝ :=
    max (val r1 r0 d) (val r2 r1 d+(val m2 mi d-val mu m0 d))
 theorem continuation_ret (m0 mu mi m2 r0 r1 r2:ℝ)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2) (k:Fin 2) (s:SeqStrategy)
    (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (t:ℝ) (ht:0 ≤ t) (d:Status) :
    seqRetPayoff (table m0 mu mi m2 r0 r1 r2) k t d (s.Ts t d) (s.accS t d (s.Ts t d))=
      stageValue m0 mu mi m2 r0 r1 r2 d+pay t d := by
  rw [ret_pay]
  congr 1
  exact (second_characterization m0 mu mi m2 r0 r1 r2
    (by linarith [h.2.1]) (by linarith [h.1,h.2.1,h.2.2]) k s hs t ht d).1

 theorem total_pay (m0 mu mi m2 r0 r1 r2 Tf Ts:ℝ) (k:Fin 2) (d e:Status) :
    (∑ i:Fin 2,seqMfrPayoff (table m0 mu mi m2 r0 r1 r2) k Tf d Ts e i)=
    if d=I then (if e=I then 2*m2-Tf-Ts else mi+mu-Tf)
    else (if e=I then mi+mu-Ts else 2*m0) := by
  fin_cases k <;> cases d <;> cases e <;>
    norm_num [Fin.sum_univ_two,seqMfrPayoff,seqProfile,table,I,U,other] <;> ring

 theorem reject_large_offer (m0 mu mi m2 r0 r1 r2:ℝ)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2) (k:Fin 2) (s:SeqStrategy)
    (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s) :
    s.accF (m2-mu+1)=U := by
  let t:=m2-mu+1
  have ht:0 ≤ t := by dsimp [t];linarith [h.1,h.2.1,h.2.2]
  cases hf:s.accF t with
  | uninformed => rfl
  | informed =>
    have hh:=hs.2.2.1 t U ht
    rw [hf,first_pay,first_pay] at hh
    cases h₁:s.accS t U (s.Ts t U) <;> cases h₂:s.accS t I (s.Ts t I) <;>
      simp [h₁,h₂,buyer,val,pay,I,U,t] at hh <;> linarith [h.1,h.2.1,h.2.2]

 theorem seq_ret_lower_U (m0 mu mi m2 r0 r1 r2:ℝ)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2) (k:Fin 2) (s:SeqStrategy)
    (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s) :
    stageValue m0 mu mi m2 r0 r1 r2 U ≤ seqRetailer (table m0 mu mi m2 r0 r1 r2) k s := by
  have ht:0 ≤ m2-mu+1 := by linarith [h.1,h.2.1,h.2.2]
  have hh:=hs.2.2.2.2 (m2-mu+1) ht
  rw [reject_large_offer _ _ _ _ _ _ _ h k s hs,continuation_ret _ _ _ _ _ _ _ h k s hs _ ht] at hh
  simpa only [seqRetailer,pay,U,I,U_ne_I,if_false,add_zero] using hh

 theorem seq_ret_lower_active (m0 mu mi m2 r0 r1 r2:ℝ)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2) (ha:r0 < r1+(mi-m0))
    (k:Fin 2) (s:SeqStrategy) (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s) :
    stageValue m0 mu mi m2 r0 r1 r2 I+(mi-mu) ≤ seqRetailer (table m0 mu mi m2 r0 r1 r2) k s := by
  have hsecU (t:ℝ) (ht:0 ≤ t) : s.accS t U (s.Ts t U)=I := by
    have hh:=(second_characterization m0 mu mi m2 r0 r1 r2
      (by linarith [h.2.1]) (by linarith [h.1,h.2.1,h.2.2]) k s hs t ht U).2.2.1
    apply hh
    simpa [val,I,U] using ha
  apply le_of_forall_pos_le_add
  intro eps heps
  let eta:=min ((mi-mu)/2) (eps/2)
  have heta:0 < eta := by dsimp [eta];apply lt_min <;> linarith [h.1,h.2.1]
  have hetag:eta ≤ (mi-mu)/2 := min_le_left _ _
  have hetae:eta ≤ eps/2 := min_le_right _ _
  let t:=mi-mu-eta
  have ht:0 ≤ t := by dsimp [t];linarith [h.1,h.2.1]
  have hf:s.accF t=I := by
    cases heq:s.accF t with
    | informed => rfl
    | uninformed =>
      have hh:=hs.2.2.1 t I ht
      rw [heq,hsecU t ht,first_pay,first_pay] at hh
      cases h₁:s.accS t I (s.Ts t I) <;>
        simp [h₁,buyer,val,pay,I,U,t] at hh <;> linarith [h.2.2]
  have hh:=hs.2.2.2.2 t ht
  rw [hf,continuation_ret _ _ _ _ _ _ _ h k s hs t ht I] at hh
  change stageValue m0 mu mi m2 r0 r1 r2 I+t ≤ seqRetailer (table m0 mu mi m2 r0 r1 r2) k s at hh
  dsimp [t] at hh
  linarith

 theorem seq_active_bounds (m0 mu mi m2 r0 r1 r2:ℝ)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2) (ha:r0 < r1+(mi-m0))
    (k:Fin 2) (s:SeqStrategy) (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s) :
    r1+(mi-mu) ≤ seqRetailer (table m0 mu mi m2 r0 r1 r2) k s ∧
    r2+(m2-mu)+(mi-mu) ≤ seqRetailer (table m0 mu mi m2 r0 r1 r2) k s ∧
    seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s ≤ 2*mu+(m2-mi) ∧
    (r2+(m2-mu) < r1 → seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s ≤ 2*mu) := by
  have hl:=seq_ret_lower_active m0 mu mi m2 r0 r1 r2 h ha k s hs
  have hi1:r1 ≤ stageValue m0 mu mi m2 r0 r1 r2 I := by simpa [stageValue,val,I] using le_max_left r1 (r2+(m2-mu))
  have hi2:r2+(m2-mu) ≤ stageValue m0 mu mi m2 r0 r1 r2 I := by simpa [stageValue,val,I] using le_max_right r1 (r2+(m2-mu))
  have hu:stageValue m0 mu mi m2 r0 r1 r2 U=r1+(mi-m0) := by simp [stageValue,val,I,U,max_eq_right ha.le]
  have hf:s.accF s.Tf=I := by
    cases heq:s.accF s.Tf with
    | informed => rfl
    | uninformed =>
      have hh:=continuation_ret m0 mu mi m2 r0 r1 r2 h k s hs s.Tf hs.2.2.2.1 U
      have hv:seqRetailer (table m0 mu mi m2 r0 r1 r2) k s=r1+(mi-m0) := by
        simpa only [seqRetailer,heq,hu,pay,U,I,U_ne_I,if_false,add_zero] using hh
      rw [hv] at hl
      linarith [h.1]
  have hr:seqRetailer (table m0 mu mi m2 r0 r1 r2) k s=
      stageValue m0 mu mi m2 r0 r1 r2 I+s.Tf := by
    simpa only [seqRetailer,hf,pay,ite_true] using
      continuation_ret m0 mu mi m2 r0 r1 r2 h k s hs s.Tf hs.2.2.2.1 I
  have hfee:mi-mu ≤ s.Tf := by rw [hr] at hl;linarith only [hl]
  have hsecond:=second_characterization m0 mu mi m2 r0 r1 r2
    (by linarith [h.2.1]) (by linarith [h.1,h.2.1,h.2.2]) k s hs s.Tf hs.2.2.2.1 I
  refine ⟨by linarith,by linarith,?_,?_⟩
  · cases he:s.accS s.Tf I (s.Ts s.Tf I) with
    | informed =>
      have ht:s.Ts s.Tf I=m2-mu := by simpa [val,I] using hsecond.2.2.2 he
      simp only [seqManufacturersTotal,hf,he,total_pay,ite_true]
      rw [ht]
      linarith
    | uninformed =>
      simp only [seqManufacturersTotal,hf,he,total_pay,I,U_ne_I,ite_true,if_false]
      linarith [h.2.2]
  · intro hb
    have he:s.accS s.Tf I (s.Ts s.Tf I)=U := hsecond.2.1 (by simpa [val,I] using hb)
    simp only [seqManufacturersTotal,hf,he,total_pay,I,U,U_ne_I,ite_true,if_false]
    linarith

 theorem seq_inactive_bounds (m0 mu mi m2 r0 r1 r2:ℝ)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2) (ha:r1+(mi-m0) ≤ r0) (hb:r2+(m2-mu) < r1)
    (k:Fin 2) (s:SeqStrategy) (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s) :
    r0 ≤ seqRetailer (table m0 mu mi m2 r0 r1 r2) k s ∧
    seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s ≤ 2*m0 := by
  have hu:stageValue m0 mu mi m2 r0 r1 r2 U=r0 := by simp [stageValue,val,I,U,max_eq_left ha]
  have hl:=seq_ret_lower_U m0 mu mi m2 r0 r1 r2 h k s hs
  rw [hu] at hl
  refine ⟨hl,?_⟩
  cases hf:s.accF s.Tf with
  | informed =>
    have hsI:=second_characterization m0 mu mi m2 r0 r1 r2
      (by linarith [h.2.1]) (by linarith [h.1,h.2.1,h.2.2]) k s hs s.Tf hs.2.2.2.1 I
    have he:s.accS s.Tf I (s.Ts s.Tf I)=U := hsI.2.1 (by simpa [val,I] using hb)
    have hr:seqRetailer (table m0 mu mi m2 r0 r1 r2) k s=r1+s.Tf := by
      simp only [seqRetailer,hf,he,ret_pay,seller,val,pay,I,U,U_ne_I,ite_true,if_false,add_zero]
    rw [hr] at hl
    simp only [seqManufacturersTotal,hf,he,total_pay,I,U,U_ne_I,ite_true,if_false]
    linarith [h.1]
  | uninformed =>
    cases he:s.accS s.Tf U (s.Ts s.Tf U) with
    | informed =>
      have hsU:=second_characterization m0 mu mi m2 r0 r1 r2
        (by linarith [h.2.1]) (by linarith [h.1,h.2.1,h.2.2]) k s hs s.Tf hs.2.2.2.1 U
      have ht:s.Ts s.Tf U=mi-m0 := by simpa [val,I,U] using hsU.2.2.2 he
      simp only [seqManufacturersTotal,hf,he,total_pay,I,U,U_ne_I,ite_true,if_false]
      rw [ht]
      linarith [h.1]
    | uninformed =>
      simp only [seqManufacturersTotal,hf,he,total_pay,I,U,U_ne_I,ite_true,if_false,le_refl]
end
end InfoSeq

set_option maxHeartbeats 3000000
open InfoSharing.Shared
namespace InfoSeq
noncomputable section
 def dPoly (p z:ℝ) : ℝ :=
    (6*p+4)*z^4+(12*p^2+42*p+24)*z^3+(5*p^3+44*p^2+91*p+46)*z^2+
      (5*p^3+30*p^2+51*p+24)*z-(6*p^3+20*p^2+22*p+8)
 theorem dPoly_pos (p Z z:ℝ) (hp:0 < p) (hZ:0 < Z) (hZz:Z ≤ z)
    (heq:Z^2+(p+2)*Z-(p+1)=0) : 0 < dPoly p z := by
  have hZ1 : Z < 1 := by
    by_contra hh
    have hzle : 1 ≤ Z := le_of_not_gt hh
    have hprod := mul_nonneg hp.le (sub_nonneg.mpr hzle)
    nlinarith only [heq,hzle,hprod,sq_nonneg (Z-1)]
  have hid : dPoly p Z=(p+1)*(p^2*(7-Z^2-2*Z)+5*p*Z+19*p+4*Z+10) := by
    have hh : dPoly p Z-(p+1)*(p^2*(7-Z^2-2*Z)+5*p*Z+19*p+4*Z+10)=
        (Z^2+(p+2)*Z-(p+1))*
          (6*p^2*Z+13*p^2+6*p*Z^2+26*p*Z+33*p+4*Z^2+16*Z+18) := by unfold dPoly;ring
    rw [heq,zero_mul] at hh
    linarith only [hh]
  have hbr : 0 < 7-Z^2-2*Z := by
    have hh:=mul_pos (sub_pos.mpr hZ1) (show 0 < 1+Z by linarith)
    nlinarith only [hh,hZ1]
  have hpos : 0 < dPoly p Z := by rw [hid];positivity
  have hmono : dPoly p Z ≤ dPoly p z := by unfold dPoly;gcongr
  exact hpos.trans_le hmono
 theorem manufacturing_gap_pos (a b c p sig beta C:ℝ)
    (hp:0 < p) (hc:0 < c) (hsig:0 < sig) (hbeta:0 < beta)
    (hC:0 < C) (hCc:C ≤ c) (hCeq:(1+p)*C^2+(p+2)*C-1=0) :
    0 < 2*(piM0 a b c p sig beta-piMU1 a b c p sig beta)-
      (piM2 a b c p sig beta-piMI1 a b c p sig beta) := by
  have hA:0 < 1+p := by positivity
  have hJ:0 < 2+(1+p)*c := by positivity
  have hH:0 < 2+p+(1+p)*c := by positivity
  have hscaled:=congrArg (fun x:ℝ=>(1+p)*x) hCeq
  have heq : ((1+p)*C)^2+(p+2)*((1+p)*C)-(p+1)=0 := by nlinarith only [hscaled]
  have hd:=dPoly_pos p ((1+p)*C) ((1+p)*c) hp (mul_pos hA hC)
    (mul_le_mul_of_nonneg_left hCc hA.le) heq
  have hid : 2*(piM0 a b c p sig beta-piMU1 a b c p sig beta)-
      (piM2 a b c p sig beta-piMI1 a b c p sig beta)=
      (p*(1+(1+p)*c)*beta*sig^2/(4*(1+p)^3*(2+(1+p)*c)^2*(2+p+(1+p)*c)^2))*dPoly p ((1+p)*c) := by
    unfold piM0 piMU1 piM2 piMI1 dPoly
    field_simp [hA.ne',hJ.ne',hH.ne'] <;> ring
  rw [hid]
  exact mul_pos (by positivity) hd
end
end InfoSeq

set_option maxHeartbeats 1500000
open InfoSharing.Shared InfoSharing.Diseconomy
namespace InfoSeq
noncomputable section
 theorem concurrent_values (m0 mu mi m2 r0 r1 r2:ℝ)
    (h:mu < m0 ∧ m0 < mi ∧ mi < m2) :
    (∃ T X,IsConcurrentOutcome (table m0 mu mi m2 r0 r1 r2) T X) ∧
    ∀ T X,IsConcurrentOutcome (table m0 mu mi m2 r0 r1 r2) T X →
      concRetailer (table m0 mu mi m2 r0 r1 r2) T X=max r0 (r2+2*(m2-m0)) ∧
      concManufacturersTotal (table m0 mu mi m2 r0 r1 r2) T X=2*m0 := by
  let P:=table m0 mu mi m2 r0 r1 r2
  have hg:0 ≤ m2-m0 := by linarith [h.2.1,h.2.2]
  have hne0:IsParetoOptimalNE P (m2-m0) (fun _=> U) :=
    (InfoBase.pareto_table m0 mu mi m2 r0 r1 r2 (m2-m0) h (fun _=> U)).mpr (Or.inl ⟨rfl,le_rfl⟩)
  have hne2:IsParetoOptimalNE P (m2-m0) (fun _=> I) :=
    (InfoBase.pareto_table m0 mu mi m2 r0 r1 r2 (m2-m0) h (fun _=> I)).mpr (Or.inr ⟨rfl,le_rfl⟩)
  have h0 (T:ℝ) : concRetailer P T (fun _=> U)=r0 := by simp [concRetailer,P,table,U,I,InfoBase.num_u]
  have h2 (T:ℝ) : concRetailer P T (fun _=> I)=r2+2*T := by simp [concRetailer,P,table,U,I,InfoBase.num_i];ring
  have hout0 (hh:r2+2*(m2-m0) ≤ r0) : IsConcurrentOutcome P (m2-m0) (fun _=> U) := by
    refine ⟨hg,hne0,?_⟩
    intro T X hT hX
    rcases (InfoBase.pareto_table m0 mu mi m2 r0 r1 r2 T h X).mp hX with ⟨rfl,ht⟩|⟨rfl,ht⟩
    · rw [h0,h0]
    · rw [h2,h0];linarith
  have hout2 (hh:r0 ≤ r2+2*(m2-m0)) : IsConcurrentOutcome P (m2-m0) (fun _=> I) := by
    refine ⟨hg,hne2,?_⟩
    intro T X hT hX
    rcases (InfoBase.pareto_table m0 mu mi m2 r0 r1 r2 T h X).mp hX with ⟨rfl,ht⟩|⟨rfl,ht⟩
    · rw [h0,h2];exact hh
    · rw [h2,h2];linarith
  refine ⟨?_,?_⟩
  · rcases le_total (r2+2*(m2-m0)) r0 with hh|hh
    · exact ⟨m2-m0,_,hout0 hh⟩
    · exact ⟨m2-m0,_,hout2 hh⟩
  · intro T X hX
    rcases (InfoBase.pareto_table m0 mu mi m2 r0 r1 r2 T h X).mp hX.2.1 with ⟨rfl,ht⟩|⟨rfl,ht⟩
    · have hh:=hX.2.2 (m2-m0) (fun _=> I) hg hne2
      rw [h2,h0] at hh
      refine ⟨by change concRetailer P T (fun _=> U)=_;rw [h0,max_eq_left hh],?_⟩
      simp [concManufacturersTotal,concManufacturerPayoff,table,I,U,Fin.sum_univ_two]
    · have hh:=hX.2.2 (m2-m0) (fun _=> I) hg hne2
      rw [h2,h2] at hh
      have hTeq:T=m2-m0 := by linarith
      have hh0:=hX.2.2 (m2-m0) (fun _=> U) hg hne0
      rw [h0,h2,hTeq] at hh0
      refine ⟨by change concRetailer P T (fun _=> I)=_;rw [h2,hTeq,max_eq_right hh0],?_⟩
      simp [concManufacturersTotal,concManufacturerPayoff,table,I,U,Fin.sum_univ_two,hTeq]
end
end InfoSeq

set_option maxHeartbeats 3000000
open InfoSharing.Shared InfoSharing.Diseconomy MeasureTheory
namespace InfoSeq
noncomputable section
theorem comparison {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c p sig beta : ℝ) (hmodel : IsSignalModel μ θ Y sig beta) (hp : 0 < p)
    (hb : 0 < b) (hc : 0 < c) :
    (∃ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c p beta E) ∧
    ∀ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c p beta E →
      let P := payoffTable μ θ Y a b c p E
      (∃ (T : ℝ) (X : Fin 2 → Status), IsConcurrentOutcome P T X) ∧
      (∀ k : Fin 2, ∃ s : SeqStrategy, IsSequentialSPE P k s) ∧
      ∀ (T : ℝ) (X : Fin 2 → Status) (k : Fin 2) (s : SeqStrategy),
        IsConcurrentOutcome P T X → IsSequentialSPE P k s →
          concRetailer P T X ≤ seqRetailer P k s ∧
          seqManufacturersTotal P k s ≤ concManufacturersTotal P T X ∧
          ((Real.sqrt 2 - 1) / (1 + p) < c →
            concRetailer P T X < seqRetailer P k s ∧
            seqManufacturersTotal P k s < concManufacturersTotal P T X) := by
  refine ⟨?_,?_⟩
  · refine ⟨fun X=>⟨(fun w y i=>(a+beta*y+w i)/2),InfoBase.candidatePrices a b c p beta X⟩,?_⟩
    intro X
    exact InfoBase.candidate_equilibrium μ θ Y a b c p sig beta hmodel hc hp X
  intro E hE
  obtain ⟨C,hC,hCeq,hCsign⟩ := InfoBase.concurrent_root p hp
  obtain ⟨Z,hZ,hZ4,hZeq,hZsign⟩ := q_root p hp
  let S1 := (Real.sqrt 2-1)/(1+p)
  let S2 := Z/(1+p)
  have hord : S1 < C ∧ C < S2 := thresholds_order p C Z hp hC hCeq (fun z hz=>(hZsign z hz).1)
  have h12 : S1 < S2 := hord.1.trans hord.2
  have hbeta:0 < beta := (InfoBase.signal_moments μ θ Y sig beta hmodel).2.2.2
  have hsig:0 < sig := hmodel.2.2.2.2.2.2.2.1
  have hA:0 < 1+p := by positivity
  have hH:0 < 2+p+(1+p)*c := by positivity
  have hJ:0 < 2+(1+p)*c := by positivity
  have hmul:0 < (1+p)*c := mul_pos hA hc
  let m0:=piM0 a b c p sig beta
  let mu:=piMU1 a b c p sig beta
  let mi:=piMI1 a b c p sig beta
  let m2:=piM2 a b c p sig beta
  let r0:=piR0 a b c p sig beta
  let r1:=piR1 a b c p sig beta
  let r2:=piR2 a b c p sig beta
  have ho := InfoBase.closed_orderings a b c p sig beta hc hp hsig hbeta
  have hm : mu < m0 ∧ m0 < mi ∧ mi < m2 := ⟨ho.1.2.2,ho.1.2.1,ho.1.1⟩
  have hgap := sequential_gaps a b c p sig beta hp hc
  let K1 := (1+(1+p)*c)*beta*sig^2/(4*(1+p)*(2+(1+p)*c)^2)
  let K2 := (1+(1+p)*c)*beta*sig^2/(4*(1+p)^3*(2+(1+p)*c)^2*(2+p+(1+p)*c)^2)
  have hK1:0 < K1 := by dsimp [K1];positivity
  have hK2:0 < K2 := by dsimp [K2];positivity
  have hga:r1+(mi-m0)-r0=K1*(((1+p)*c)^2+2*((1+p)*c)-1) := hgap.1
  have hgb:r2+(m2-mu)-r1=K2*qPoly p ((1+p)*c) := hgap.2
  have hz1lt : (1+p)*c < Real.sqrt 2-1 ↔ c < S1 := by
    dsimp [S1]
    rw [lt_div_iff₀ hA]
    constructor <;> intro hh <;> nlinarith only [hh]
  have hz1le : Real.sqrt 2-1 ≤ (1+p)*c ↔ S1 ≤ c := by
    dsimp [S1]
    rw [div_le_iff₀ hA]
    constructor <;> intro hh <;> nlinarith only [hh]
  have hz1gt : Real.sqrt 2-1 < (1+p)*c ↔ S1 < c := by
    dsimp [S1]
    rw [div_lt_iff₀ hA]
    constructor <;> intro hh <;> nlinarith only [hh]
  have hz2lt : (1+p)*c < Z ↔ c < S2 := by
    dsimp [S2]
    rw [lt_div_iff₀ hA]
    constructor <;> intro hh <;> nlinarith only [hh]
  have hz2le : Z ≤ (1+p)*c ↔ S2 ≤ c := by
    dsimp [S2]
    rw [div_le_iff₀ hA]
    constructor <;> intro hh <;> nlinarith only [hh]
  have hz2gt : Z < (1+p)*c ↔ S2 < c := by
    dsimp [S2]
    rw [div_lt_iff₀ hA]
    constructor <;> intro hh <;> nlinarith only [hh]
  have ha0 (h:c < S1) : r1+(mi-m0) < r0 := by
    have hh := mul_neg_of_pos_of_neg hK1 ((first_root_sign _ hmul).1.mpr (hz1lt.mpr h))
    linarith only [hga,hh]
  have ha1 (h:S1 ≤ c) : r0 ≤ r1+(mi-m0) := by
    have hh := mul_nonneg hK1.le ((first_root_sign _ hmul).2.1.mpr (hz1le.mpr h))
    linarith only [hga,hh]
  have ha2 (h:S1 < c) : r0 < r1+(mi-m0) := by
    have hh := mul_pos hK1 ((first_root_sign _ hmul).2.2.mpr (hz1gt.mpr h))
    linarith only [hga,hh]
  have hb0 (h:c < S2) : r2+(m2-mu) < r1 := by
    have hh := mul_neg_of_pos_of_neg hK2 ((hZsign _ hmul).1.mpr (hz2lt.mpr h))
    linarith only [hgb,hh]
  have hb1 (h:S2 ≤ c) : r1 ≤ r2+(m2-mu) := by
    have hh := mul_nonneg hK2.le ((hZsign _ hmul).2.1.mpr (hz2le.mpr h))
    linarith only [hgb,hh]
  have hb2 (h:S2 < c) : r1 < r2+(m2-mu) := by
    have hh := mul_pos hK2 ((hZsign _ hmul).2.2.mpr (hz2gt.mpr h))
    linarith only [hgb,hh]

  have ha_le (hh:c ≤ S1) : r1+(mi-m0) ≤ r0 := by
    by_contra hh2
    have hpos : 0 < ((1+p)*c)^2+2*((1+p)*c)-1 := by nlinarith only [hga,hK1,lt_of_not_ge hh2]
    have hcgt:=hz1gt.mp ((first_root_sign _ hmul).2.2.mp hpos)
    exact (not_lt_of_ge hh) hcgt
  let K:=(1+(1+p)*c)*beta*sig^2/(2*(2+p+(1+p)*c)^2)
  have hK:0 < K := by dsimp [K];positivity
  have hcgap:r2+2*(m2-m0)-r0=K*((1+p)*c^2+(p+2)*c-1) := by
    dsimp [r2,m2,m0,r0,piR2,piR0,piM2,piM0,K]
    field_simp [hH.ne'] <;> ring
  have hc0 (hh:c < C) : r2+2*(m2-m0) < r0 := by
    have ht:=mul_neg_of_pos_of_neg hK ((hCsign c hc).1.mpr hh)
    linarith only [hcgap,ht]
  have hc2 (hh:C ≤ c) : r0 ≤ r2+2*(m2-m0) := by
    have ht:=mul_nonneg hK.le ((hCsign c hc).2.1.mpr hh)
    linarith only [hcgap,ht]
  dsimp only
  rw [InfoBase.payoff_eq_table μ θ Y a b c p sig beta hmodel hp hb hc E hE]
  change (∃ T X,IsConcurrentOutcome (table m0 mu mi m2 r0 r1 r2) T X) ∧ _
  have hcv:=concurrent_values m0 mu mi m2 r0 r1 r2 hm
  refine ⟨hcv.1,?_,?_⟩
  · intro k
    by_cases hh:c < S1
    · obtain ⟨s,hs,hn⟩:=seq_zero_mem m0 mu mi m2 r0 r1 r2 k hm (ha0 hh).le (hb0 (hh.trans h12)).le
      exact ⟨s,hs⟩
    · by_cases hh2:c < S2
      · obtain ⟨s,hs,hn⟩:=seq_one_mem m0 mu mi m2 r0 r1 r2 k hm (ha1 (le_of_not_gt hh)) (hb0 hh2).le
        exact ⟨s,hs⟩
      · have hh2':S2 ≤ c:=le_of_not_gt hh2
        obtain ⟨s,hs,hn⟩:=seq_two_mem m0 mu mi m2 r0 r1 r2 k hm (ha2 (h12.trans_le hh2')).le (hb1 hh2')
        exact ⟨s,hs⟩
  · intro T X k s hX hs
    change concRetailer (table m0 mu mi m2 r0 r1 r2) T X ≤ seqRetailer (table m0 mu mi m2 r0 r1 r2) k s ∧
      seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s ≤ concManufacturersTotal (table m0 mu mi m2 r0 r1 r2) T X ∧
      (S1 < c → concRetailer (table m0 mu mi m2 r0 r1 r2) T X < seqRetailer (table m0 mu mi m2 r0 r1 r2) k s ∧
        seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s < concManufacturersTotal (table m0 mu mi m2 r0 r1 r2) T X)
    obtain ⟨hcr,hcm⟩:=hcv.2 T X hX
    rw [hcr,hcm]
    by_cases hact:S1 < c
    · have hsbound:=seq_active_bounds m0 mu mi m2 r0 r1 r2 hm (ha2 hact) k s hs
      have hstrict:max r0 (r2+2*(m2-m0)) < seqRetailer (table m0 mu mi m2 r0 r1 r2) k s ∧
          seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s < 2*m0 := by
        by_cases hsmall:c < C
        · rw [max_eq_left (hc0 hsmall).le]
          have hbnd:=hsbound.2.2.2 (hb0 (hsmall.trans hord.2))
          exact ⟨by linarith [hsbound.1,ha2 hact,hm.1],by linarith [hm.1]⟩
        · have hCle:C ≤ c:=le_of_not_gt hsmall
          rw [max_eq_right (hc2 hCle)]
          have hD:=manufacturing_gap_pos a b c p sig beta C hp hc hsig hbeta hC hCle hCeq
          change 0 < 2*(m0-mu)-(m2-mi) at hD
          exact ⟨by linarith [hsbound.2.1],by linarith [hsbound.2.2.1]⟩
      exact ⟨hstrict.1.le,hstrict.2.le,fun _=> hstrict⟩
    · have hle:c ≤ S1:=le_of_not_gt hact
      rw [max_eq_left (hc0 (hle.trans_lt hord.1)).le]
      have hsbound:=seq_inactive_bounds m0 mu mi m2 r0 r1 r2 hm (ha_le hle) (hb0 (hle.trans_lt h12)) k s hs
      exact ⟨hsbound.1,hsbound.2,fun hh=>(hact hh).elim⟩
end
end InfoSeq
open InfoSharing.Diseconomy
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) :
    (∃ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c φ β E) ∧
    ∀ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c φ β E →
      let P := payoffTable μ θ Y a b c φ E
      (∃ (T : ℝ) (X : Fin 2 → Status), IsConcurrentOutcome P T X) ∧
      (∀ k : Fin 2, ∃ s : SeqStrategy, IsSequentialSPE P k s) ∧
      ∀ (T : ℝ) (X : Fin 2 → Status) (k : Fin 2) (s : SeqStrategy),
        IsConcurrentOutcome P T X → IsSequentialSPE P k s →
          concRetailer P T X ≤ seqRetailer P k s ∧
          seqManufacturersTotal P k s ≤ concManufacturersTotal P T X ∧
          ((Real.sqrt 2 - 1) / (1 + φ) < c →
            concRetailer P T X < seqRetailer P k s ∧
            seqManufacturersTotal P k s < concManufacturersTotal P T X) := by
  exact InfoSeq.comparison μ θ Y a b c φ σ β hmodel hφ hb hc
