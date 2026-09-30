-- Prove2me | solution 1 for InfoSharing.Diseconomy.prop_2_concurrent_threshold
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:06:31.457245+00:00
-- url     : https://prove2.me/submissions/747b2e42-047b-4e7f-97a9-98bd6423cb21

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
open MeasureTheory Filter
open InfoSharing.Shared
noncomputable section
private theorem cond_mul_integral {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem signal_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem residual_orthogonal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem retailer_gap (a φ m : ℝ) (w p : Fin 2→ℝ) :
    retailerInterim a φ w m (fun i=>(a+m+w i)/2)-retailerInterim a φ w m p =
      (p 0-(a+m+w 0)/2)^2+(p 1-(a+m+w 1)/2)^2+
        φ*((p 0-(a+m+w 0)/2)-(p 1-(a+m+w 1)/2))^2 := by
  simp only [retailerInterim,Fin.sum_univ_two,other]
  norm_num
  ring

private theorem retailer_br (a φ β : ℝ) (hφ : 0< φ)
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


private def priceGradient (a b c φ β : ℝ) (f : Fin 2→ℝ→ℝ) (i : Fin 2) (y : ℝ) : ℝ :=
  (1+c*(1+φ))*((a+β*y-(1+φ)*f i y+φ*f (other i) y)/2)-(1+φ)/2*(f i y-b)

private theorem other_ne (i : Fin 2) : other i≠i := by fin_cases i <;> decide

private theorem demand_lp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem manufacturer_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (θ Y : Ω→ℝ) (hiθ : MemLp θ 2 μ) (hiY : MemLp Y 2 μ)
    (a b c φ β : ℝ) (hφ : 0< φ) (ρ : (Fin 2→ℝ)→ℝ→Fin 2→ℝ) (hr : IsRetailerBR a φ β ρ)
    (f : Fin 2→ℝ→ℝ) (hif : ∀ i,MemLp (fun ω=> f i (Y ω)) 2 μ) (i : Fin 2) :
    Integrable (fun ω=>(f i (Y ω)-b)*demand a φ θ Y ρ f i ω-c*(demand a φ θ Y ρ f i ω)^2) μ := by
  have hd := demand_lp μ θ Y hiθ hiY a φ β hφ ρ hr f hif i
  exact ((hif i).sub (memLp_const b) |>.integrable_mul hd).sub (hd.integrable_sq.const_mul c)

private theorem gradient_lp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem manufacturer_gain {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private def candidatePrices (a b c φ β : ℝ) (X : Fin 2→Status) : Fin 2→ℝ→ℝ :=
  fun i y=> wbar a b c φ+alphaW c φ β X i*y

private theorem status_ne : Status.informed≠Status.uninformed := by decide
private theorem status_ne' : Status.uninformed≠Status.informed := by decide
private theorem numInformed_vec (s t : Status) :
    numInformed ![s,t]=(if s=Status.informed then 1 else 0)+(if t=Status.informed then 1 else 0) := by
  cases s <;> cases t <;> decide

private theorem alphaW_uninformed (c φ β : ℝ) (X : Fin 2→Status) (i : Fin 2)
    (h : X i=Status.uninformed) : alphaW c φ β X i=0 := by
  have hX : X=![X 0,X 1] := by funext j;fin_cases j <;> rfl
  rw [hX] at h ⊢
  cases h0 : X 0 <;> cases h1 : X 1 <;> fin_cases i <;>
    simp [alphaW,numInformed_vec,status_ne,status_ne',h0,h1] at h ⊢

private theorem candidate_informed (a b c φ β : ℝ) (hc : 0< c) (hφ : 0< φ)
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

private theorem candidate_gradient_linear (a b c φ β : ℝ) (hc : 0< c) (hφ : 0< φ)
    (X : Fin 2→Status) (i : Fin 2) (y : ℝ) :
    priceGradient a b c φ β (candidatePrices a b c φ β X) i y =
      y*priceGradient a b c φ β (candidatePrices a b c φ β X) i 1 := by
  have h3 : 0<2+φ+(1+φ)*c := by positivity
  unfold priceGradient candidatePrices wbar
  field_simp [h3.ne']
  ring

private theorem candidate_admissible {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω→ℝ) (hiY : MemLp Y 2 μ)
    (a b c φ β : ℝ) (X : Fin 2→Status) (i : Fin 2) :
    IsAdmissible μ Y (X i) (candidatePrices a b c φ β X i) := by
  refine ⟨by unfold candidatePrices;fun_prop,?_,?_⟩
  · change MemLp (fun ω=> wbar a b c φ+alphaW c φ β X i*Y ω) 2 μ
    exact (memLp_const (wbar a b c φ)).add (hiY.const_mul (alphaW c φ β X i))
  · intro h
    refine ⟨wbar a b c φ,fun y=>?_⟩
    simp only [candidatePrices,alphaW_uninformed c φ β X i h,mul_zero,zero_mul,add_zero]

private theorem candidate_stationary {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem candidate_equilibrium {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem quad_linear_zero (l k : ℝ) (h : ∀ t : ℝ,t*l-t^2*k≤0) : l=0 := by
  have hmax : IsLocalMax (fun t : ℝ=> t*l-t^2*k) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa using h t
  have hd : HasDerivAt (fun t : ℝ=> t*l-t^2*k) l 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const l).sub (((hasDerivAt_id (0:ℝ)).pow 2).mul_const k) using 1 <;> norm_num
  exact hd.deriv.symm.trans hmax.deriv_eq_zero

private theorem admissible_variation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω→ℝ) (s : Status) (f g : ℝ→ℝ) (hf : IsAdmissible μ Y s f)
    (hg : IsAdmissible μ Y s g) (t : ℝ) : IsAdmissible μ Y s (fun y=> f y+t*(g y-f y)) := by
  refine ⟨hf.1.add ((hg.1.sub hf.1).const_mul t),hf.2.1.add ((hg.2.1.sub hf.2.1).const_mul t),?_⟩
  intro hs
  obtain ⟨a,ha⟩ := hf.2.2 hs
  obtain ⟨b,hb⟩ := hg.2.2 hs
  exact ⟨a+t*(b-a),fun y=> by dsimp;rw [ha,hb]⟩

private theorem equilibrium_first_order {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem equilibrium_unique {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem candidate_retail (a b c φ β : ℝ) (hc : 0< c) (hφ : 0< φ)
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

private theorem pricing_equilibrium {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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



private theorem quadratic_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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


private def qBase (a b c φ : ℝ) : ℝ := (a-wbar a b c φ)/2
private def qSlope (c φ β : ℝ) (X : Fin 2→Status) (i : Fin 2) : ℝ :=
  (-β-(1+φ)*alphaW c φ β X i+φ*alphaW c φ β X (other i))/2

private theorem eq_manufacturer_value {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem eq_retailer_value {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem num_u : numInformed (fun _=> Status.uninformed)=0 := by decide
private theorem num_i : numInformed (fun _=> Status.informed)=2 := by decide
private theorem num_only (i : Fin 2) : numInformed (onlyInformed i)=1 := by
  fin_cases i <;> decide

private theorem profit_manufacturers {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem profit_retailer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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


private theorem closed_orderings (a b c φ σ β : ℝ) (hc : 0< c) (hφ : 0< φ)
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

private theorem profit_orderings {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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


private theorem profile_cases (X : Fin 2→Status) :
    X=(fun _=> Status.uninformed) ∨ X=onlyInformed 0 ∨ X=onlyInformed 1 ∨
      X=(fun _=> Status.informed) := by
  have hv : X=![X 0,X 1] := by funext i;fin_cases i <;> rfl
  rw [hv]
  cases h₀ : X 0 <;> cases h₁ : X 1 <;>
    simp [funext_iff,Fin.forall_fin_two,onlyInformed]

private theorem no_free_sharing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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
private theorem forall_status (p : Status→Prop) : (∀ s,p s) ↔ p Status.informed ∧ p Status.uninformed := by
  constructor
  · intro h;exact ⟨h _,h _⟩
  · rintro ⟨hi,hu⟩ s;cases s;exact hi;exact hu
private def table (m0 mu mi m2 r0 r1 r2 : ℝ) : PayoffTable where
  M X i := if X i=Status.informed then (if X (other i)=Status.informed then m2 else mi)
    else (if X (other i)=Status.informed then mu else m0)
  R X := if numInformed X=0 then r0 else if numInformed X=1 then r1 else r2

private theorem ne_table (m0 mu mi m2 r0 r1 r2 T : ℝ) (h : mu< m0 ∧ m0< mi ∧ mi< m2)
    (X : Fin 2→Status) :
    IsPureNE (table m0 mu mi m2 r0 r1 r2) T X ↔
      (X=(fun _=> Status.uninformed) ∧ mi-m0≤ T) ∨
      (X=(fun _=> Status.informed) ∧ T≤ m2-mu) := by
  rcases profile_cases X with rfl|rfl|rfl|rfl
  all_goals
    simp [IsPureNE,Fin.forall_fin_two,forall_status,concManufacturerPayoff,table,other,
      onlyInformed,Function.update,funext_iff,Fin.forall_fin_two,status_ne,status_ne']
    first | (constructor <;> intro hh <;> linarith [h.1,h.2.1,h.2.2]) | (intro hh;linarith [h.1,h.2.1,h.2.2])

private theorem pareto_table (m0 mu mi m2 r0 r1 r2 T : ℝ) (h : mu< m0 ∧ m0< mi ∧ mi< m2)
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


private theorem conc_numbers (m0 mu mi m2 r0 r1 r2 : ℝ) (h : mu< m0 ∧ m0< mi ∧ mi< m2) :
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


private theorem payoff_eq_table {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
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

private theorem concurrent_root (φ : ℝ) (hφ : 0< φ) :
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
private theorem concurrent_threshold :
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

theorem solution :
    ∀ φ : ℝ, 0 < φ → ∃ cC : ℝ,
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ) (a b c σ β : ℝ)
      (E : (Fin 2 → Status) → PricingProfile),
      IsSignalModel μ θ Y σ β → 0 < b → 0 < c → IsPricingEqFamily μ θ Y a b c φ β E →
      let P := payoffTable μ θ Y a b c φ E
      (c < cC → ConcOptN P = {0}) ∧
      (cC ≤ c → 2 ∈ ConcOptN P) ∧
      (cC < c → ConcOptN P = {2}) := concurrent_threshold
