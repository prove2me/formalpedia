-- Prove2me | solution 1 for MasulloRH.printed_adelic_poisson_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:30:48.433986+00:00
-- url     : https://prove2.me/submissions/146f73d8-cf38-47d9-a31d-ae16c8bbf6f5

import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Theorems.Thm_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat
import Definitions.Def_NumberField_AdelicBox
import Mathlib
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology

set_option backward.isDefEq.respectTransparency.types false
open IsDedekindDomain NumberField NumberField.StandardAddChar NumberField.AdelicFourier MeasureTheory
open scoped NumberField.AdeleRing

open scoped SchwartzMap Topology
open Set Filter
noncomputable section

private theorem haar_involution {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (he : Function.Involutive e) (μ : Measure G) [μ.IsAddHaarMeasure] :
    MeasurePreserving e μ μ := by
  have hm : Measurable e := e.continuous.measurable
  let ν := μ.map e
  letI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have he2 : ν.map e = μ := by
    dsimp [ν]; rw [Measure.map_map hm hm, show (e ∘ e : G → G) = id from funext he,Measure.map_id]
  have hs := Measure.addHaarScalarFactor_map ν μ e
  have hs' : μ.addHaarScalarFactor ν = ν.addHaarScalarFactor μ := by
    simpa only [he2] using hs
  have h := Measure.addHaarScalarFactor_eq_mul μ ν μ
  rw [Measure.addHaarScalarFactor_self,hs'] at h
  have hh : (ν.addHaarScalarFactor μ : ℝ) = 1 := by
    have heq := congrArg NNReal.toReal h
    push_cast at heq
    nlinarith [NNReal.coe_nonneg (ν.addHaarScalarFactor μ)]
  have hh' : ν.addHaarScalarFactor μ = 1 := NNReal.coe_injective hh
  refine ⟨hm,?_⟩
  change ν = μ
  simpa only [hh',one_smul] using (Measure.isAddLeftInvariant_eq_smul ν μ)

private def unit_involution {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (u : A) (hu : u*u=1) : A ≃ₜ+ A where
  toFun := fun x => u*x
  invFun := fun x => u*x
  left_inv x := by change u*(u*x)=x; rw [←mul_assoc,hu,one_mul]
  right_inv x := by change u*(u*x)=x; rw [←mul_assoc,hu,one_mul]
  map_add' := mul_add u
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

private theorem finite_sign_rational (q : ℚ) :
    (psiQ.mulShift ((1,-1) : 𝔸[ℚ])) (algebraMap ℚ 𝔸[ℚ] q) = 1 ↔
      ∃ k : ℤ, 2*q = k := by
  change psiArch (1 * algebraMap ℚ (InfiniteAdeleRing ℚ) q) *
    psiFin ((-1) * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q) = 1 ↔ _
  rw [one_mul,neg_one_mul,←map_neg,psiArch_algebraMap,psiFin_algebraMap,←Complex.exp_add]
  push_cast
  let c : ℂ := 2*(Real.pi:ℂ)*Complex.I
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  change Complex.exp (c*(q:ℂ) + -c * -(q:ℂ)) = 1 ↔ _
  rw [show c*(q:ℂ)+ -c * -(q:ℂ)=(2*(q:ℂ))*c by ring,Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k,hk⟩
    have heq : 2*(q:ℂ)=(k:ℂ) := mul_right_cancel₀ hc hk
    exact ⟨k,by exact_mod_cast heq⟩
  · rintro ⟨k,hk⟩
    have heq : 2*(q:ℂ)=(k:ℂ) := by exact_mod_cast hk
    exact ⟨k,congrArg (fun z : ℂ => z*c) heq⟩

private abbrev AQ := 𝔸[ℚ]
private abbrev AF := FiniteAdeleRing (𝓞 ℚ) ℚ
private abbrev AM := mixedEmbedding.mixedSpace ℚ
private abbrev AI := InfiniteAdeleRing ℚ

private theorem separating_bump (x₀ : AQ) (hx : psiQ x₀ ≠ 1) :
    ∃ f ∈ schwartzBruhat ℚ, HasCompactSupport f ∧ f x₀=1 ∧
      (∀ x, 0 ≤ (f x).re) ∧ (∀ x, psiQ x=1 → f x=0) := by
  classical
  let e : AI ≃ₜ AM := IsHomeomorph.homeomorph _ (InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace ℚ)
  let W : Set AM := {y | psiArch (e.symm y) * psiFin x₀.2 ≠ 1}
  have hW : IsOpen W := isOpen_ne_fun ((continuous_psiArch.comp e.symm.continuous).mul continuous_const) continuous_const
  have hc : e x₀.1 ∈ W := by
    change psiArch (e.symm (e x₀.1)) * psiFin x₀.2 ≠ 1
    simpa only [e.symm_apply_apply,psiQ_apply] using hx
  obtain ⟨g,hgW,hgc,hgs,hgr,hgx⟩ := exists_contDiff_tsupport_subset (n:=⊤) (hW.mem_nhds hc)
  let G : 𝓢(AM,ℂ) := (hgc.comp_left (g:=Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hgs)
  let I := AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ
  let t : AF ≃ₜ AF := Homeomorph.addRight (-x₀.2)
  let V : Set AF := t ⁻¹' I
  have hVo : IsOpen V := (AdelicBox.isOpen_integralFiniteAdeles ℚ).preimage t.continuous
  have hVc : IsCompact V := t.isCompact_preimage.mpr (AdelicBox.isCompact_integralFiniteAdeles ℚ)
  have hVx : x₀.2 ∈ V := by
    change x₀.2 + -x₀.2 ∈ I
    rw [add_neg_cancel]
    exact fun v => zero_mem _
  let h : AF → ℂ := V.indicator (fun _ => 1)
  have hl : IsLocallyConstant h := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro y
    by_cases hy : y ∈ V
    · filter_upwards [hVo.mem_nhds hy] with z hz
      simp [h,Set.indicator_of_mem hy,Set.indicator_of_mem hz]
    · filter_upwards [hVc.isClosed.isOpen_compl.mem_nhds hy] with z hz
      have hz' : z ∉ V := hz
      simp [h,Set.indicator_of_notMem hy,Set.indicator_of_notMem hz']
  have hs : HasCompactSupport h := by
    apply hVc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal _ hVc.isClosed)
    exact fun x hx => by by_contra hn;exact hx (Set.indicator_of_notMem hn _)
  let f (x : AQ) := G (e x.1) * h x.2
  have hf : f ∈ schwartzBruhat ℚ := mem_schwartzBruhat_of_mem_pureTensorSet (tensor_mem_pureTensorSet G h hl hs)
  have hprod : IsCompact ((e ⁻¹' tsupport g) ×ˢ V) := (e.isCompact_preimage.mpr hgc).prod hVc
  have hfc : HasCompactSupport f := by
    apply hprod.of_isClosed_subset (isClosed_tsupport _) (closure_minimal _ hprod.isClosed)
    intro x hx'
    have hne : (g (e x.1):ℂ)*h x.2 ≠ 0 := hx'
    have hgz : g (e x.1) ≠ 0 := fun hz => hne (by simp [hz])
    refine ⟨subset_tsupport _ hgz,?_⟩
    by_contra hn
    exact hne (by simp [h,Set.indicator_of_notMem hn])
  refine ⟨f,hf,hfc,?_,?_,?_⟩
  · change (g (e x₀.1):ℂ)*h x₀.2=1
    simp [hgx,h,Set.indicator_of_mem hVx]
  · intro x
    change 0 ≤ ((g (e x.1):ℂ)*h x.2).re
    by_cases hv : x.2 ∈ V
    · simpa [h,Set.indicator_of_mem hv] using (hgr ⟨e x.1,rfl⟩).1
    · simp [h,Set.indicator_of_notMem hv]
  · intro x hx1
    change (g (e x.1):ℂ)*h x.2=0
    by_cases hv : x.2 ∈ V
    · have hfin : psiFin x.2 = psiFin x₀.2 := by
        have he : psiFin (x.2-x₀.2)=1 := by
          apply psiFin_eq_one_of_forall_mem
          rw [sub_eq_add_neg]
          exact hv
        calc _ = psiFin (x₀.2+(x.2-x₀.2)) := by congr 1; abel
             _ = _ := by rw [AddChar.map_add_eq_mul,he,mul_one]
      have hzero : g (e x.1)=0 := by
        by_contra hz
        have hW' := hgW (subset_tsupport _ hz)
        change psiArch (e.symm (e x.1))*psiFin x₀.2 ≠ 1 at hW'
        rw [e.symm_apply_apply,←hfin] at hW'
        exact hW' hx1
      simp [hzero]
    · simp [h,Set.indicator_of_notMem hv]

theorem solution [MeasurableSpace 𝔸[ℚ]] [BorelSpace 𝔸[ℚ]] :
    let u : 𝔸[ℚ] := (1,-1)
    let χ := psiQ.mulShift u
    ∃ f ∈ schwartzBruhat ℚ, HasCompactSupport f ∧
      f (u * algebraMap ℚ 𝔸[ℚ] (1/3)) = 1 ∧ (∀ x, 0 ≤ (f x).re) ∧
      (∀ r : ℚ, f (algebraMap ℚ 𝔸[ℚ] r) = 0) ∧
      ∀ (μ : Measure 𝔸[ℚ]) [μ.IsAddHaarMeasure],
        (1:ℝ) ≤ (((μ (AdelicBox.adelicBox ℚ)).toReal : ℂ)⁻¹ *
          ∑' r : ℚ, fourierIntegral χ μ f (algebraMap ℚ 𝔸[ℚ] r)).re := by
  classical
  let u : AQ := (1,-1)
  let χ := psiQ.mulShift u
  let D := algebraMap ℚ AQ
  have hu : u*u=1 := by
    apply Prod.ext
    · change (1:AI)*1=1; simp
    · change (-1:AF)*(-1)=1; simp
  have hx : psiQ (u*D (1/3)) ≠ 1 := by
    intro h
    obtain ⟨k,hk⟩ := (finite_sign_rational (1/3)).mp h
    have hpos : (0:ℚ) < (k:ℚ) := by linarith
    have hlt : (k:ℚ) < 1 := by linarith
    have hpos' : (0:ℤ) < k := by exact_mod_cast hpos
    have hlt' : k < 1 := by exact_mod_cast hlt
    omega
  obtain ⟨f,hf,hcs,h1,hpos,hvan⟩ := separating_bump _ hx
  refine ⟨f,hf,hcs,h1,hpos,fun r => hvan _ (psiQ_algebraMap r),?_⟩
  intro μ hμ
  let U : AQˣ := ⟨u,u,hu,hu⟩
  let J := unit_involution u hu
  let g (v : AQ) := f (u*v)
  have hg : g ∈ schwartzBruhat ℚ := comp_mul_mem_schwartzBruhat ℚ U hf
  letI := NumberField.AdeleRing.secondCountableTopology ℚ
  have hJ := haar_involution J (fun x => J.left_inv x) μ
  have ht (w : AQ) : fourierIntegral psiQ μ g w = fourierIntegral χ μ f w := by
    have h := hJ.integral_comp J.toHomeomorph.measurableEmbedding (fun v => χ (-(v*w))*f v)
    apply Eq.trans _ h
    unfold fourierIntegral
    apply integral_congr_ae <| Filter.Eventually.of_forall _
    intro v
    change psiQ (-(v*w))*f (u*v) = psiQ (u * -((u*v)*w))*f (u*v)
    rw [show u * -((u*v)*w) = -(v*w) by rw [mul_neg,show u*((u*v)*w)=(u*u)*(v*w) by ring,hu,one_mul]]
  have hps := tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral ℚ μ isGlobalAddChar_psiQ hg 0
  simp only [zero_add,mul_zero,AddChar.map_zero_eq_one,mul_one,ht] at hps
  change 1 ≤ (((μ (AdelicBox.adelicBox ℚ)).toReal : ℂ)⁻¹ * ∑' r : ℚ, fourierIntegral χ μ f (D r)).re
  rw [←hps]
  have hsum : Summable (fun r : ℚ => g (D r)) := by
    simpa only [zero_add] using summable_translate_of_mem_schwartzBruhat ℚ hg 0
  rw [Complex.re_tsum hsum]
  have hlow := (Complex.hasSum_re hsum.hasSum).summable.le_tsum (1/3:ℚ) (fun j _ => hpos (u*D j))
  change (f (u*D (1/3))).re ≤ _ at hlow
  simpa only [h1,Complex.one_re] using hlow

end
