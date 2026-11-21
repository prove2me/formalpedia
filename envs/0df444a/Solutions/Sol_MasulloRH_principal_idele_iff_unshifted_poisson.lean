-- Prove2me | solution 1 for MasulloRH.principal_idele_iff_unshifted_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T04:11:07.050503+00:00
-- url     : https://prove2.me/submissions/9baa74ce-5ef4-4dc2-b2b4-071b7680e145

import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_comp_mul_left
import Theorems.Thm_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one
import Definitions.Def_NumberField_TateGlobalZeta
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

namespace TwistProof
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

private abbrev D := algebraMap ℚ AQ
private abbrev I := AQˣ
private instance : Nontrivial AQ := (NumberField.AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ).nontrivial
private def vol [MeasurableSpace AQ] (μ : Measure AQ) : ℂ := ((μ (AdelicBox.adelicBox ℚ)).toReal : ℂ)⁻¹
private def modl (a : I) := NumberField.TateGlobal.ideleNorm ℚ a
private theorem modl_pos (a : I) : 0 < modl a := NumberField.TateGlobal.ideleNorm_pos a
private def chi (c : I) := psiQ.mulShift (c:AQ)
private def per (f : AQ→ℂ) (a : I) (x : AQ) := ∑' q : ℚ,f (x+(a:AQ)*D q)

private theorem shiftFT [MeasurableSpace AQ] (c : I) (μ : Measure AQ) (f : AQ→ℂ) (w : AQ) :
    fourierIntegral (chi c) μ f w = fourierIntegral psiQ μ f ((c:AQ)*w) := by
  unfold fourierIntegral
  apply integral_congr_ae <| Eventually.of_forall fun v => ?_
  change psiQ ((c:AQ)*(-(v*w)))*f v=psiQ (-(v*((c:AQ)*w)))*f v
  congr 2; ring

private theorem scaled [MeasurableSpace AQ] [BorelSpace AQ] (μ : Measure AQ) [μ.IsAddHaarMeasure]
    (a c : I) {f : AQ→ℂ} (hf : f∈schwartzBruhat ℚ) (x : AQ) :
    per f a x = vol μ * (modl a:ℂ)⁻¹ *
      ∑' q : ℚ, let w := (((a*c)⁻¹:I):AQ)*D q
        fourierIntegral (chi c) μ f w * chi c (w*x) := by
  let g (v : AQ) := f ((a:AQ)*v)
  have hg : g∈schwartzBruhat ℚ := comp_mul_mem_schwartzBruhat ℚ a hf
  have hps := tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral ℚ μ isGlobalAddChar_psiQ hg ((a⁻¹:AQˣ)*x)
  have hd (q : ℚ) : (c:AQ)*((((a*c)⁻¹:I):AQ)*D q) = (↑a⁻¹:AQ)*D q := by
    simp only [mul_inv_rev,Units.val_mul,←mul_assoc,Units.mul_inv,one_mul]
  have hphase (q : ℚ) : chi c (((((a*c)⁻¹:I):AQ)*D q)*x)=psiQ (D q*((↑a⁻¹:AQ)*x)) := by
    change psiQ ((c:AQ)*(((((a*c)⁻¹:I):AQ)*D q)*x)) = _
    rw [←mul_assoc,hd]; ring_nf
  have hgq (q : ℚ) : g ((↑a⁻¹:AQ)*x+D q)=f (x+(a:AQ)*D q) := by
    dsimp [g]; rw [mul_add,←mul_assoc,Units.mul_inv,one_mul]
  change _ = vol μ * (∑' q : ℚ, fourierIntegral psiQ μ g (D q)*psiQ (D q*((↑a⁻¹:AQ)*x))) at hps
  simp only [hgq] at hps
  apply hps.trans
  rw [mul_assoc]
  congr 1
  rw [←tsum_mul_left]
  apply tsum_congr
  intro q
  dsimp only
  rw [shiftFT,hd,hphase]
  unfold g
  rw [fourierIntegral_comp_mul_left]
  change (modl a:ℂ)⁻¹*_ * _ = _
  ring

private theorem inv_nonprincipal (c : I) (hc : (c:AQ)∉range D) : (↑c⁻¹:AQ)∉range D := by
  rintro ⟨r,hr⟩
  have h0 : r≠0 := by
    intro h; apply Units.ne_zero c⁻¹; rw [←hr,h,map_zero]
  apply hc
  refine ⟨r⁻¹,?_⟩
  have h : D r⁻¹ *(↑c⁻¹:AQ)=1 := by rw [←hr,←map_mul,inv_mul_cancel₀ h0,map_one]
  calc D r⁻¹ = (D r⁻¹*(↑c⁻¹:AQ))*(c:AQ) := by rw [mul_assoc,Units.inv_mul,mul_one]
       _ = _ := by rw [h,one_mul]

private theorem counter [MeasurableSpace AQ] [BorelSpace AQ] (c : I) (hc : (c:AQ)∉range D) :
    ∃ f ∈ schwartzBruhat ℚ, HasCompactSupport f ∧ (∀ x,0≤(f x).re) ∧
      (∀ q : ℚ,f (D q)=0) ∧
      ∀ (μ : Measure AQ) [μ.IsAddHaarMeasure],
        modl c⁻¹ ≤ (vol μ * ∑' q : ℚ,fourierIntegral (chi c) μ f (D q)).re := by
  classical
  have hn := inv_nonprincipal c hc
  have hx : ∃ q : ℚ,psiQ ((↑c⁻¹:AQ)*D q)≠1 := by
    by_contra! h
    exact hn (mem_range_algebraMap_of_forall_apply_mul_eq_one ℚ isGlobalAddChar_psiQ _ h)
  obtain ⟨q₀,hq⟩ := hx
  obtain ⟨f,hf,hcs,h1,hpos,hzero⟩ := separating_bump _ hq
  refine ⟨f,hf,hcs,hpos,fun q => hzero _ (psiQ_algebraMap q),?_⟩
  intro μ hμ
  have hps := scaled μ c⁻¹ c hf 0
  simp only [inv_mul_cancel,inv_one,Units.val_one,one_mul,mul_zero,AddChar.map_zero_eq_one,mul_one] at hps
  let g (v : AQ) := f ((↑c⁻¹:AQ)*v)
  have hg := comp_mul_mem_schwartzBruhat ℚ c⁻¹ hf
  have hs : Summable (fun q : ℚ => g (D q)) := by
    simpa only [zero_add] using summable_translate_of_mem_schwartzBruhat ℚ hg 0
  have hlow : 1≤(per f c⁻¹ 0).re := by
    change 1≤(∑' q : ℚ,f (0+(↑c⁻¹:AQ)*D q)).re
    simp only [zero_add]
    change 1≤(∑' q : ℚ,g (D q)).re
    rw [Complex.re_tsum hs]
    have h := (Complex.hasSum_re hs.hasSum).summable.le_tsum q₀ (fun q _ => hpos _)
    change (f ((↑c⁻¹:AQ)*D q₀)).re ≤ _ at h
    simpa only [h1,Complex.one_re] using h
  have hnon : (modl c⁻¹:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modl_pos _).ne'
  have heq : vol μ*(∑' q : ℚ,fourierIntegral (chi c) μ f (D q)) = (modl c⁻¹:ℂ)*per f c⁻¹ 0 := by
    rw [hps]; field_simp
  rw [heq,Complex.re_ofReal_mul]
  exact le_mul_of_one_le_right (modl_pos _).le hlow

private theorem principal_identity [MeasurableSpace AQ] [BorelSpace AQ] (μ : Measure AQ) [μ.IsAddHaarMeasure]
    (c : I) (hc : (c:AQ)∈range D) {f : AQ→ℂ} (hf : f∈schwartzBruhat ℚ) :
    (∑' q : ℚ,f (D q)) = vol μ*(∑' q : ℚ,fourierIntegral (chi c) μ f (D q)) := by
  obtain ⟨r,hr⟩ := hc
  have h0 : r≠0 := by intro h; apply Units.ne_zero c; rw [←hr,h,map_zero]
  have hps := tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral ℚ μ isGlobalAddChar_psiQ hf 0
  simp only [zero_add,mul_zero,AddChar.map_zero_eq_one,mul_one] at hps
  apply hps.trans
  congr 1
  simp_rw [shiftFT,←hr,←map_mul]
  exact ((Equiv.mulLeft₀ r h0).tsum_eq (fun q : ℚ => fourierIntegral psiQ μ f (D q))).symm
end TwistProof
open TwistProof
theorem solution
    [MeasurableSpace 𝔸[ℚ]] [BorelSpace 𝔸[ℚ]]
    (c : 𝔸[ℚ]ˣ) (μ : Measure 𝔸[ℚ]) [μ.IsAddHaarMeasure] :
    let D := algebraMap ℚ 𝔸[ℚ]
    let χ := psiQ.mulShift (c:𝔸[ℚ])
    let V (ν : Measure 𝔸[ℚ]) := ((ν (AdelicBox.adelicBox ℚ)).toReal : ℂ)⁻¹
    ((c:𝔸[ℚ]) ∈ Set.range D ↔ ∀ f ∈ schwartzBruhat ℚ,
      (∑' q : ℚ,f (D q)) = V μ*(∑' q : ℚ,fourierIntegral χ μ f (D q))) ∧
    ((c:𝔸[ℚ]) ∉ Set.range D →
      ∃ f ∈ schwartzBruhat ℚ, HasCompactSupport f ∧ (∀ x,0 ≤ (f x).re) ∧
        (∀ q : ℚ,f (D q)=0) ∧
        ∀ (ν : Measure 𝔸[ℚ]) [ν.IsAddHaarMeasure],
          NumberField.TateGlobal.ideleNorm ℚ c⁻¹ ≤ (V ν*∑' q : ℚ,fourierIntegral χ ν f (D q)).re) ∧
    ∀ (a : 𝔸[ℚ]ˣ) (f : 𝔸[ℚ]→ℂ), f∈schwartzBruhat ℚ → ∀ x : 𝔸[ℚ],
      (∑' q : ℚ,f (x+(a:𝔸[ℚ])*D q)) =
        V μ * (NumberField.TateGlobal.ideleNorm ℚ a:ℂ)⁻¹ *
          ∑' q : ℚ, let w := (((a*c)⁻¹:𝔸[ℚ]ˣ):𝔸[ℚ])*D q
              fourierIntegral χ μ f w * χ (w*x) := by
  dsimp only
  refine ⟨⟨fun h f hf => principal_identity μ c h hf,?_⟩,counter c,fun a f hf x => scaled μ a c hf x⟩
  intro h
  by_contra hn
  obtain ⟨f,hf,_,_,hz,hbad⟩ := counter c hn
  have he := h f hf
  change (∑' q : ℚ,f (D q))=vol μ*(∑' q : ℚ,fourierIntegral (chi c) μ f (D q)) at he
  simp only [hz,tsum_zero] at he
  have hh := hbad μ
  rw [←he,Complex.zero_re] at hh
  exact (modl_pos _).not_ge hh
end
