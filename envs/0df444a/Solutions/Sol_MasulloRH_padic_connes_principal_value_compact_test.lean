-- Prove2me | solution 1 for MasulloRH.padic_connes_principal_value_compact_test
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T04:09:51.431652+00:00
-- url     : https://prove2.me/submissions/a9bf932b-b2e3-4843-933c-ee141bb88585

import Mathlib
import Theorems.Thm_MasulloRH_padic_log_fourier_compact_test
import Theorems.Thm_MasulloRH_padic_unit_connes_principal_value_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Set Metric Filter
open scoped Topology

namespace MasulloAudit.PadicConnes

variable {p : ℕ} [Fact p.Prime]
variable [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]

private lemma norm_eq_center_of_mem_smallBall {a x : ℚ_[p]} {r : ℝ}
    (hr : r < ‖a‖) (hx : x ∈ closedBall a r) : ‖x‖ = ‖a‖ := by
  have hxa : ‖x-a‖ < ‖a‖ := (show ‖x-a‖ ≤ r by simpa [mem_closedBall,dist_eq_norm] using hx).trans_lt hr
  have hax : ‖a-x‖ < ‖a‖ := by rw [norm_sub_rev]; exact hxa
  apply le_antisymm
  · calc
      ‖x‖ = ‖(x-a)+a‖ := by rw [sub_add_cancel]
      _ ≤ max ‖x-a‖ ‖a‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = _ := max_eq_right hxa.le
  · by_contra! ht
    have hA : ‖a‖ ≤ max ‖a-x‖ ‖x‖ := by
      simpa only [sub_add_cancel] using IsUltrametricDist.norm_add_le_max (a-x) x
    exact (max_lt hax ht).not_ge hA

private noncomputable def padicAdditiveFourier (ψ : AddChar ℚ_[p] Circle)
    (f : ℚ_[p] → ℂ) (y : ℚ_[p]) : ℂ :=
  ∫ x, f x*(ψ (x*y) : ℂ) ∂μ

private noncomputable def padicLogIntegrand (ψ : AddChar ℚ_[p] Circle)
    (f : ℚ_[p] → ℂ) (y : ℚ_[p]) : ℂ :=
  (Real.log ‖y‖ : ℂ)*padicAdditiveFourier μ ψ f y

private lemma padicAdditiveFourier_indicator (ψ : AddChar ℚ_[p] Circle)
    {S : Set ℚ_[p]} (hS : MeasurableSet S) (c : ℂ) (y : ℚ_[p]) :
    padicAdditiveFourier μ ψ (S.indicator (fun _ ↦ c)) y =
      c*(∫ x in S, (ψ (x*y) : ℂ) ∂μ) := by
  unfold padicAdditiveFourier
  have hPoint : (fun x : ℚ_[p] ↦ S.indicator (fun _ ↦ c) x*(ψ (x*y) : ℂ)) =
      S.indicator (fun x ↦ c*(ψ (x*y) : ℂ)) := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx,indicator_of_mem hx]
    · rw [indicator_of_notMem hx,indicator_of_notMem hx,zero_mul]
  rw [hPoint,integral_indicator hS,integral_const_mul]

private lemma integrable_padic_fourier_mul (ψ : AddChar ℚ_[p] Circle)
    (hcont : Continuous ψ) (y : ℚ_[p]) {f : ℚ_[p] → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x : ℚ_[p] ↦ f x*(ψ (x*y) : ℂ)) μ :=
  (hf.mul (continuous_subtype_val.comp (hcont.comp (continuous_id.mul_const y)))).integrable_of_hasCompactSupport
    hfc.mul_right

private lemma logIntegrand_add_const_mul
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    {f g : ℚ_[p] → ℂ} (hF : Continuous f) (hG : Continuous g)
    (hFC : HasCompactSupport f) (hGC : HasCompactSupport g) (c : ℂ) :
    padicLogIntegrand μ ψ (fun x ↦ f x+c*g x) =
      fun y ↦ padicLogIntegrand μ ψ f y+c*padicLogIntegrand μ ψ g y := by
  funext y
  have hF' := integrable_padic_fourier_mul μ ψ hcont y hF hFC
  have hG' := (integrable_padic_fourier_mul μ ψ hcont y hG hGC).const_mul c
  have he : (fun x : ℚ_[p] ↦ (f x+c*g x)*(ψ (x*y) : ℂ)) =
      fun x : ℚ_[p] ↦ f x*(ψ (x*y) : ℂ)+c*(g x*(ψ (x*y) : ℂ)) := by
    funext x
    ring
  unfold padicLogIntegrand padicAdditiveFourier
  rw [he,integral_add hF' hG',integral_const_mul]
  ring

private def unitsSet : Set ℚ_[p] := {x | ‖x‖ = 1}

private noncomputable def unitIndicator : ℚ_[p] → ℂ :=
  (unitsSet (p := p)).indicator (fun _ ↦ 1)

private lemma unitsSet_sphere : unitsSet (p := p) = sphere (0:ℚ_[p]) 1 := by
  ext x
  simp [unitsSet]

private lemma unitsSet_isClopen : IsClopen (unitsSet (p := p)) := by
  rw [unitsSet_sphere]
  exact ⟨isClosed_sphere, IsUltrametricDist.isOpen_sphere _ one_ne_zero⟩

private lemma unitIndicator_lc : IsLocallyConstant (unitIndicator (p := p)) := by
  have hC := unitsSet_isClopen (p := p)
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  by_cases hx : x ∈ unitsSet (p := p)
  · refine ⟨_,hC.isOpen,hx,fun y hy ↦ ?_⟩
    rw [unitIndicator,indicator_of_mem hx,indicator_of_mem hy]
  · refine ⟨_,hC.isClosed.isOpen_compl,hx,fun y hy ↦ ?_⟩
    rw [unitIndicator,indicator_of_notMem hx,indicator_of_notMem hy]

private lemma unitIndicator_compact : HasCompactSupport (unitIndicator (p := p)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:ℚ_[p]) 1)
  apply support_indicator_subset.trans
  rw [unitsSet_sphere]
  exact sphere_subset_closedBall

private noncomputable def sqrtWeightedTest (f : ℚ_[p] → ℂ) (x : ℚ_[p]) : ℂ :=
  f x/(Real.sqrt ‖x‖ : ℂ)

private lemma sqrtWeightedTest_lc (f : ℚ_[p] → ℂ) (hf : IsLocallyConstant f) (h0 : f 0 = 0) :
    IsLocallyConstant (sqrtWeightedTest f) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  by_cases hx : x = 0
  · subst x
    filter_upwards [hf.eventually_eq 0] with y hy
    simp [sqrtWeightedTest,hy,h0]
  · have hN : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hB : ∀ᶠ y in 𝓝 x, y ∈ closedBall x (‖x‖/2) :=
      closedBall_mem_nhds _ (half_pos hN)
    filter_upwards [hf.eventually_eq x, hB] with y hy h
    rw [sqrtWeightedTest,sqrtWeightedTest,hy,norm_eq_center_of_mem_smallBall (half_lt_self hN) h]

private lemma sqrtWeightedTest_compact (f : ℚ_[p] → ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (sqrtWeightedTest f) := by
  have hEq : sqrtWeightedTest f = f * fun x : ℚ_[p] ↦ (Real.sqrt ‖x‖ : ℂ)⁻¹ := by
    funext x
    exact div_eq_mul_inv _ _
  rw [hEq]
  exact hf.mul_right

private noncomputable def shiftedUnitIndicator (x : ℚ_[p]) : ℂ :=
  unitIndicator (1+x)

private lemma shiftedUnitIndicator_eq :
    shiftedUnitIndicator (p := p) = {x : ℚ_[p] | ‖1+x‖ = 1}.indicator (fun _ ↦ 1) := by
  funext x
  by_cases hx : ‖1+x‖ = 1 <;> simp [shiftedUnitIndicator,unitIndicator,unitsSet,indicator,hx]

private lemma shiftedUnitIndicator_lc : IsLocallyConstant (shiftedUnitIndicator (p := p)) :=
  unitIndicator_lc.comp_continuous (by fun_prop : Continuous (fun x : ℚ_[p] ↦ 1+x))

private lemma shiftedUnitIndicator_compact : HasCompactSupport (shiftedUnitIndicator (p := p)) :=
  unitIndicator_compact.comp_homeomorph (Homeomorph.addLeft 1)

private lemma padicLogIntegrand_shifted_unit_zero
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0:ℚ_[p]) 1) = 1) :
    Integrable (padicLogIntegrand μ ψ (shiftedUnitIndicator (p := p))) μ ∧
      (∫ y, padicLogIntegrand μ ψ (shiftedUnitIndicator (p := p)) y ∂μ) = 0 := by
  have hNorm : Measurable (fun x : ℚ_[p] ↦ ‖1+x‖) := by fun_prop
  have hM : MeasurableSet {x : ℚ_[p] | ‖1+x‖ = 1} := hNorm (measurableSet_singleton 1)
  have hE : padicLogIntegrand μ ψ (shiftedUnitIndicator (p := p)) = fun y : ℚ_[p] ↦
      (Real.log ‖y‖ : ℂ)*(∫ x in {x : ℚ_[p] | ‖1+x‖ = 1}, (ψ (x*y) : ℂ) ∂μ) := by
    funext y
    rw [padicLogIntegrand,shiftedUnitIndicator_eq,padicAdditiveFourier_indicator μ ψ hM,one_mul]
  rw [hE]
  exact MasulloRH.padic_unit_connes_principal_value_zero μ ψ hcont hψ hμ

private noncomputable def connesWeightedTest (f : ℚ_[p] → ℂ) (x : ℚ_[p]) : ℂ :=
  sqrtWeightedTest f (1+x)

private noncomputable def connesPhysicalKernel (f : ℚ_[p] → ℂ) (x : ℚ_[p]) : ℂ :=
  ((f x-f 1*unitIndicator x)/(Real.sqrt ‖x‖:ℂ))/(‖x-1‖:ℂ)

/-- Rational specialization of the Connes–Weil principal value at a finite prime.
Both local pairings use normalized additive Haar measure. -/
theorem padic_connes_principal_value_compact_test_aux
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (closedBall (0:ℚ_[p]) 1) = 1)
    (f : ℚ_[p] → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) (hf0 : f 0 = 0) :
    Integrable (padicLogIntegrand μ ψ (connesWeightedTest f)) μ ∧
      Integrable (connesPhysicalKernel f) μ ∧
      -(∫ y, padicLogIntegrand μ ψ (connesWeightedTest f) y ∂μ) =
        ((Real.log p/(1-(p:ℝ)⁻¹) : ℝ) : ℂ)*(∫ x, connesPhysicalKernel f x ∂μ) := by
  let u := connesWeightedTest f
  let U := shiftedUnitIndicator (p := p)
  let g (x : ℚ_[p]) := u x-f 1*U x
  have huL : IsLocallyConstant u := (sqrtWeightedTest_lc f hf hf0).comp_continuous
    (by fun_prop : Continuous (fun x : ℚ_[p] ↦ 1+x))
  have huC : HasCompactSupport u :=
    (sqrtWeightedTest_compact f hfc).comp_homeomorph (Homeomorph.addLeft 1)
  have hUL : IsLocallyConstant U := shiftedUnitIndicator_lc
  have hUC : HasCompactSupport U := shiftedUnitIndicator_compact
  have hgL : IsLocallyConstant g := huL.sub ((IsLocallyConstant.const (f 1)).mul hUL)
  have hgC : HasCompactSupport g := huC.sub hUC.mul_left
  have hg0 : g 0 = 0 := by
    simp [g,u,U,connesWeightedTest,sqrtWeightedTest,shiftedUnitIndicator_eq,indicator]
  have hgVal := MasulloRH.padic_log_fourier_compact_test μ ψ hcont hψ hμ g hgL hgC
  change Integrable (padicLogIntegrand μ ψ g) μ ∧
    Integrable (fun x : ℚ_[p] ↦
      (g x-g 0*(closedBall (0:ℚ_[p]) 1).indicator (fun _ ↦ (1:ℂ)) x)/(‖x‖:ℂ)) μ ∧ _ at hgVal
  simp only [hg0,zero_mul,sub_zero,mul_zero] at hgVal
  obtain ⟨hIg,hQg,hTg⟩ := hgVal
  obtain ⟨hIU,hTU⟩ := padicLogIntegrand_shifted_unit_zero μ ψ hcont hψ hμ
  have hF : u = fun x : ℚ_[p] ↦ g x+f 1*U x := by
    funext x
    unfold g
    ring
  have hLog := logIntegrand_add_const_mul μ ψ hcont hgL.continuous hUL.continuous hgC hUC (f 1)
  rw [← hF] at hLog
  have hPhys : (fun x : ℚ_[p] ↦ g x/(‖x‖:ℂ)) = fun x ↦ connesPhysicalKernel f (1+x) := by
    funext x
    have hAdd : (1:ℚ_[p])+x-1 = x := by ring
    unfold g u U connesWeightedTest sqrtWeightedTest connesPhysicalKernel shiftedUnitIndicator
    rw [hAdd]
    by_cases hx : ‖1+x‖ = 1 <;> simp [unitIndicator,unitsSet,indicator,hx]
  have hQ : Integrable (connesPhysicalKernel f) μ := by
    rw [hPhys] at hQg
    exact ((measurePreserving_add_left μ (1:ℚ_[p])).integrable_comp_emb
      (Homeomorph.addLeft (1:ℚ_[p])).measurableEmbedding).mp hQg
  refine ⟨hLog.symm ▸ hIg.add (hIU.const_mul _), hQ, ?_⟩
  change -(∫ y, padicLogIntegrand μ ψ u y ∂μ) = _
  rw [hLog,integral_add hIg (hIU.const_mul _),integral_const_mul,hTU,mul_zero,add_zero]
  change -(∫ y, padicLogIntegrand μ ψ g y ∂μ) = _
  rw [show (∫ y, padicLogIntegrand μ ψ g y ∂μ) =
        -(Real.log p/(1-(p:ℝ)⁻¹) : ℝ) * (∫ x, g x/(‖x‖:ℂ) ∂μ) from hTg,
      hPhys, integral_add_left_eq_self, neg_mul, neg_neg]

end MasulloAudit.PadicConnes

open MeasureTheory
open scoped Topology

theorem solution {p : ℕ} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] Circle) (hcont : Continuous ψ)
    (hψ : ∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1)
    (hμ : μ (Metric.closedBall (0 : ℚ_[p]) 1) = 1)
    (f : ℚ_[p] → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) (hf0 : f 0 = 0) :
    let F := fun y : ℚ_[p] ↦ (Real.log ‖y‖ : ℂ) *
      ∫ x : ℚ_[p], (f (1+x)/(Real.sqrt ‖1+x‖:ℂ)) * (ψ (x*y):ℂ) ∂μ
    let K := fun x : ℚ_[p] ↦
      ((f x-f 1*{x : ℚ_[p] | ‖x‖ = 1}.indicator (fun _ ↦ (1:ℂ)) x)/(Real.sqrt ‖x‖:ℂ))/(‖x-1‖:ℂ)
    Integrable F μ ∧ Integrable K μ ∧
      -(∫ y, F y ∂μ) = ((Real.log p/(1-(p:ℝ)⁻¹) : ℝ) : ℂ)*(∫ x, K x ∂μ) := by
  exact MasulloAudit.PadicConnes.padic_connes_principal_value_compact_test_aux μ ψ hcont hψ hμ f hf hfc hf0
