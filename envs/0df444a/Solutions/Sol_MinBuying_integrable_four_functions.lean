-- Prove2me | solution 1 for MinBuying.integrable_four_functions
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:06:56.129094+00:00
-- url     : https://prove2.me/submissions/6135f20c-3b67-4433-b793-609d52000532

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory Set MinBuying
open scoped BigOperators
noncomputable section

namespace MinBuyingIntegralFourFunctionsProof

private lemma cross_bound {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (h₀₀ : a₀*b₀ ≤ c₀*d₀) (h₁₀ : a₁*b₀ ≤ c₀*d₁)
    (h₀₁ : a₀*b₁ ≤ c₀*d₁) (h₁₁ : a₁*b₁ ≤ c₁*d₁) :
    a₀*b₁+a₁*b₀ ≤ c₀*d₁+c₁*d₀ := by
  by_cases hcd : c₀*d₁ = 0
  · nlinarith [mul_nonneg ha₀ hb₁,mul_nonneg ha₁ hb₀,mul_nonneg hc₁ hd₀]
  have hcdpos : 0 < c₀*d₁ := lt_of_le_of_ne (mul_nonneg hc₀ hd₁) (Ne.symm hcd)
  apply le_of_mul_le_mul_right _ hcdpos
  calc
    (a₀*b₁+a₁*b₀)*(c₀*d₁) = a₀*b₁*(c₀*d₁)+(c₀*d₁)*(a₁*b₀) := by ring
    _ ≤ a₀*b₁*(a₁*b₀)+(c₀*d₁)*(c₀*d₁) := mul_add_mul_le_mul_add_mul h₀₁ h₁₀
    _ = a₀*b₀*(a₁*b₁)+(c₀*d₁)*(c₀*d₁) := by ring
    _ ≤ c₀*d₀*(c₁*d₁)+(c₀*d₁)*(c₀*d₁) := by
      gcongr
    _ = (c₀*d₁+c₁*d₀)*(c₀*d₁) := by ring

private lemma cross_pointwise_on {α : Type*} [LinearOrder α] (a b c d : α → ℝ)
    (ha : ∀ x,0 ≤ a x) (hb : ∀ x,0 ≤ b x) (hc : ∀ x,0 ≤ c x) (hd : ∀ x,0 ≤ d x)
    (P : α → Prop)
    (h : ∀ x,P x → ∀ y,P y → a x*b y ≤ c (min x y)*d (max x y))
    (x y : α) (hx : P x) (hy : P y) :
    a x*b y+a y*b x ≤ c x*d y+c y*d x := by
  rcases le_total x y with hxy | hyx
  · exact cross_bound (ha x) (ha y) (hb x) (hb y) (hc x) (hc y) (hd x) (hd y)
      (by simpa using h x hx x hx)
      (by simpa [min_eq_right hxy,max_eq_left hxy] using h y hy x hx)
      (by simpa [min_eq_left hxy,max_eq_right hxy] using h x hx y hy)
      (by simpa using h y hy y hy)
  · have hh := cross_bound (ha y) (ha x) (hb y) (hb x) (hc y) (hc x) (hd y) (hd x)
      (by simpa using h y hy y hy)
      (by simpa [min_eq_right hyx,max_eq_left hyx] using h x hx y hy)
      (by simpa [min_eq_left hyx,max_eq_right hyx] using h y hy x hx)
      (by simpa using h x hx x hx)
    simpa only [add_comm] using hh

private lemma four_functions_integral_on {α : Type*} [LinearOrder α] [MeasurableSpace α]
    (μ : Measure α) (a b c d : α → ℝ)
    (ha : ∀ x,0 ≤ a x) (hb : ∀ x,0 ≤ b x) (hc : ∀ x,0 ≤ c x) (hd : ∀ x,0 ≤ d x)
    (P : α → Prop) (hP : ∀ᵐ x ∂μ,P x)
    (h : ∀ x,P x → ∀ y,P y → a x*b y ≤ c (min x y)*d (max x y))
    (ia : Integrable a μ) (ib : Integrable b μ) (ic : Integrable c μ) (id : Integrable d μ) :
    (∫ x,a x ∂μ)*(∫ x,b x ∂μ) ≤ (∫ x,c x ∂μ)*(∫ x,d x ∂μ) := by
  have hinner : ∀ x,P x → a x*(∫ y,b y ∂μ)+(∫ y,a y ∂μ)*b x ≤
      c x*(∫ y,d y ∂μ)+(∫ y,c y ∂μ)*d x := by
    intro x hx
    have hh := integral_mono_ae ((ib.const_mul (a x)).add (ia.mul_const (b x)))
      ((id.const_mul (c x)).add (ic.mul_const (d x)))
      (hP.mono (fun y hy => cross_pointwise_on a b c d ha hb hc hd P h x y hx hy))
    simpa only [Pi.add_apply,integral_add (ib.const_mul _) (ia.mul_const _),
      integral_add (id.const_mul _) (ic.mul_const _),integral_const_mul,integral_mul_const] using hh
  have hh := integral_mono_ae
    ((ia.mul_const (∫ y,b y ∂μ)).add (ib.const_mul (∫ y,a y ∂μ)))
    ((ic.mul_const (∫ y,d y ∂μ)).add (id.const_mul (∫ y,c y ∂μ))) (hP.mono hinner)
  simp only [Pi.add_apply,integral_add (ia.mul_const _) (ib.const_mul _),
    integral_add (ic.mul_const _) (id.const_mul _),integral_const_mul,integral_mul_const] at hh
  linarith

private lemma cons_integrable {n : ℕ} (f : Valuations (n+1) → ℝ) (hf : Integrable f volume) :
    Integrable (fun p : ℝ × Valuations n => f (Fin.cons p.1 p.2)) volume := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hh := (he.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hf
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Fin.insertNth_zero,Fin.zero_succAbove,Function.comp_def,Equiv.coe_fn_mk,cast_eq] using hh

private lemma cons_integral {n : ℕ} (f : Valuations (n+1) → ℝ) (hf : Integrable f volume) :
    (∫ v,f v) = ∫ t : ℝ,∫ v : Valuations n,f (Fin.cons t v) := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  rw [← he.integral_comp' f]
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Fin.insertNth_zero,Fin.zero_succAbove,Function.comp_def,Equiv.coe_fn_mk,cast_eq,
    Measure.volume_eq_prod] using
    integral_prod (fun p : ℝ × Valuations n => f (Fin.cons p.1 p.2)) (cons_integrable f hf)

private lemma cons_minmax {n : ℕ} (s t : ℝ) (v w : Valuations n) :
    (fun i : Fin (n+1) => min ((Fin.cons s v : Valuations (n+1)) i)
      ((Fin.cons t w : Valuations (n+1)) i)) =
      (Fin.cons (min s t) (fun i => min (v i) (w i)) : Valuations (n+1)) ∧
    (fun i : Fin (n+1) => max ((Fin.cons s v : Valuations (n+1)) i)
      ((Fin.cons t w : Valuations (n+1)) i)) =
      (Fin.cons (max s t) (fun i => max (v i) (w i)) : Valuations (n+1)) := by
  constructor <;> funext i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp

private lemma four_functions (n : ℕ) (a b c d : Valuations n → ℝ)
    (ha : ∀ v,0 ≤ a v) (hb : ∀ v,0 ≤ b v) (hc : ∀ v,0 ≤ c v) (hd : ∀ v,0 ≤ d v)
    (h : ∀ v w,a v*b w ≤
      c (fun i => min (v i) (w i))*d (fun i => max (v i) (w i)))
    (ia : Integrable a volume) (ib : Integrable b volume)
    (ic : Integrable c volume) (id : Integrable d volume) :
    (∫ v,a v)*(∫ v,b v) ≤ (∫ v,c v)*(∫ v,d v) := by
  induction n with
  | zero =>
    let v : Valuations 0 := Fin.elim0
    rw [Measure.volume_pi_eq_dirac v]
    simpa only [integral_dirac,min_self,max_self] using h v v
  | succ n ih =>
    let A : ℝ → Valuations n → ℝ := fun t v => a (Fin.cons t v)
    let B : ℝ → Valuations n → ℝ := fun t v => b (Fin.cons t v)
    let C : ℝ → Valuations n → ℝ := fun t v => c (Fin.cons t v)
    let D : ℝ → Valuations n → ℝ := fun t v => d (Fin.cons t v)
    have iA : Integrable (fun p : ℝ × Valuations n => A p.1 p.2) volume := cons_integrable a ia
    have iB : Integrable (fun p : ℝ × Valuations n => B p.1 p.2) volume := cons_integrable b ib
    have iC : Integrable (fun p : ℝ × Valuations n => C p.1 p.2) volume := cons_integrable c ic
    have iD : Integrable (fun p : ℝ × Valuations n => D p.1 p.2) volume := cons_integrable d id
    let P : ℝ → Prop := fun t => Integrable (A t) volume ∧ Integrable (B t) volume ∧
      Integrable (C t) volume ∧ Integrable (D t) volume
    have hP : ∀ᵐ t : ℝ,P t := by
      filter_upwards [iA.prod_right_ae,iB.prod_right_ae,iC.prod_right_ae,iD.prod_right_ae]
        with t htA htB htC htD
      exact ⟨htA,htB,htC,htD⟩
    have hout : ∀ s,P s → ∀ t,P t →
        (∫ v,A s v)*(∫ v,B t v) ≤ (∫ v,C (min s t) v)*(∫ v,D (max s t) v) := by
      intro s hs t ht
      have hmin : P (min s t) := by
        rcases le_total s t with hst | hts
        · simpa only [min_eq_left hst] using hs
        · simpa only [min_eq_right hts] using ht
      have hmax : P (max s t) := by
        rcases le_total s t with hst | hts
        · simpa only [max_eq_right hst] using ht
        · simpa only [max_eq_left hts] using hs
      apply ih (A s) (B t) (C (min s t)) (D (max s t))
        (fun v => ha _) (fun v => hb _) (fun v => hc _) (fun v => hd _)
        _ hs.1 ht.2.1 hmin.2.2.1 hmax.2.2.2
      intro v w
      have hh := h (Fin.cons s v) (Fin.cons t w)
      rw [(cons_minmax s t v w).1,(cons_minmax s t v w).2] at hh
      exact hh
    rw [cons_integral a ia,cons_integral b ib,cons_integral c ic,cons_integral d id]
    exact four_functions_integral_on volume
      (fun t => ∫ v,A t v) (fun t => ∫ v,B t v)
      (fun t => ∫ v,C t v) (fun t => ∫ v,D t v)
      (fun t => integral_nonneg (fun v => ha _)) (fun t => integral_nonneg (fun v => hb _))
      (fun t => integral_nonneg (fun v => hc _)) (fun t => integral_nonneg (fun v => hd _))
      P hP hout iA.integral_prod_left iB.integral_prod_left iC.integral_prod_left iD.integral_prod_left

end MinBuyingIntegralFourFunctionsProof

theorem solution (n : ℕ) (a b c d : Valuations n → ℝ)
    (ha : ∀ v,0 ≤ a v) (hb : ∀ v,0 ≤ b v) (hc : ∀ v,0 ≤ c v) (hd : ∀ v,0 ≤ d v)
    (h : ∀ v w,a v*b w ≤
      c (fun i => min (v i) (w i))*d (fun i => max (v i) (w i)))
    (ia : Integrable a volume) (ib : Integrable b volume)
    (ic : Integrable c volume) (id : Integrable d volume) :
    (∫ v,a v)*(∫ v,b v) ≤ (∫ v,c v)*(∫ v,d v) :=
  MinBuyingIntegralFourFunctionsProof.four_functions n a b c d ha hb hc hd h ia ib ic id
