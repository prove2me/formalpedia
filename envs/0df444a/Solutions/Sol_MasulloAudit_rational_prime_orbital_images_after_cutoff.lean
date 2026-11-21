-- Prove2me | solution 1 for MasulloAudit.rational_prime_orbital_images_after_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:59:29.59842+00:00
-- url     : https://prove2.me/submissions/6e980ad6-7001-47b5-8e86-2f88ba5c78f8

import Mathlib
import Definitions.Def_Masullo_RationalSphericalCutoff
import Theorems.Thm_MasulloAudit_truncated_theta_admissible_test_interpolation
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_IdeleProductMeasure
open Finset Filter Topology MeasureTheory AutomorphicForm Metric
open scoped ContDiff SchwartzMap ENNReal
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RationalAdelicCutoffProof
open NumberField IsDedekindDomain Set
open scoped Classical
private abbrev A := AdeleRing (𝓞 ℚ) ℚ
private abbrev G := Aˣ
private abbrev M := mixedEmbedding.mixedSpace ℚ
private abbrev Af := FiniteAdeleRing (𝓞 ℚ) ℚ
private def integralAf := AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ
private def finTest : Af → ℂ := integralAf.indicator (fun _ => 1)
private theorem fin_lc : IsLocallyConstant finTest := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  by_cases hx : x∈integralAf
  · filter_upwards [(AdelicLevel.isOpen_integralFiniteAdeles (𝓞 ℚ) ℚ).mem_nhds hx] with y hy
    change y∈integralAf at hy
    simp [finTest,indicator_of_mem hx,indicator_of_mem hy]
  · filter_upwards [(AdelicLevel.isClosed_integralFiniteAdeles (𝓞 ℚ) ℚ).isOpen_compl.mem_nhds hx] with y hy
    change y∉integralAf at hy
    simp [finTest,indicator_of_notMem hx,indicator_of_notMem hy]
private theorem fin_cs : HasCompactSupport finTest := by
  apply (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 ℚ) ℚ).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (AdelicLevel.isClosed_integralFiniteAdeles (𝓞 ℚ) ℚ)
  intro x hx
  by_contra hh
  exact hx (indicator_of_notMem hh _)


private def rv : {w : InfinitePlace ℚ // w.IsReal} := ⟨Rat.infinitePlace,Rat.isReal_infinitePlace⟩
private def evalR : M→+*ℝ := (Pi.evalRingHom _ rv).comp (RingHom.fst _ _)
private def realE : M≃L[ℝ]ℝ := LinearEquiv.toContinuousLinearEquiv ({
  toFun := evalR
  invFun := fun r => r • (1:M)
  left_inv := by
    intro x;ext v
    · change evalR x * 1= x.1 v
      rw [mul_one];exact congrArg x.1 (Subtype.ext (Subsingleton.elim _ _))
    · exfalso
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr v.2) (by rw [Subsingleton.elim v.1 Rat.infinitePlace];exact Rat.isReal_infinitePlace)
  right_inv := by intro r;change r*1=r;ring
  map_add' := evalR.map_add
  map_smul' := by intro c v;rfl
  } : M ≃ₗ[ℝ] ℝ)
private def archR : A→+*ℝ := evalR.comp ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).toRingHom.comp (RingHom.fst _ _))
private def tensorF (f : ℝ→ℂ) (x : A) := f (archR x)*finTest x.2
private theorem tensor_mem {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : tensorF f ∈ AdelicFourier.schwartzBruhat ℚ := by
  let G₀ := (hc.comp_homeomorph realE.toHomeomorph).toSchwartzMap (hf.comp realE.contDiff)
  exact AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet (AdelicFourier.tensor_mem_pureTensorSet G₀ finTest fin_lc fin_cs)
private abbrev Ai := InfiniteAdeleRing ℚ
private theorem realplace (v : InfinitePlace ℚ) : v.IsReal := by
  rw [Subsingleton.elim v Rat.infinitePlace];exact Rat.isReal_infinitePlace
private def infReal : Ai ≃ₜ+ ℝ where
  toFun x := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace (x Rat.infinitePlace)
  invFun r v := (InfinitePlace.Completion.ringEquivRealOfIsReal (realplace v)).symm r
  left_inv x := by funext v;obtain rfl : v=Rat.infinitePlace := Subsingleton.elim _ _;exact RingEquiv.symm_apply_apply _ _
  right_inv r := RingEquiv.apply_symm_apply _ _
  map_add' x y := map_add _ _ _
  continuous_toFun := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp (continuous_apply _)
  continuous_invFun := continuous_pi (fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (realplace v)).symm.continuous)
local instance : SecondCountableTopology A := AdeleRing.secondCountableTopology ℚ
local instance : SecondCountableTopology (Ai×Af) := AdeleRing.secondCountableTopology ℚ
local instance : SecondCountableTopology Ai := (isEmbedding_prodMkLeft (0:Af)).secondCountableTopology
local instance : SecondCountableTopology Af := (isEmbedding_prodMkRight (0:Ai)).secondCountableTopology
local instance : MeasurableSpace Ai := borel Ai
local instance : BorelSpace Ai := ⟨rfl⟩
local instance : MeasurableSpace Af := borel Af
local instance : BorelSpace Af := ⟨rfl⟩
local instance : MeasurableSpace A := inferInstanceAs (MeasurableSpace (Ai×Af))
local instance : BorelSpace A := inferInstanceAs (BorelSpace (Ai×Af))
private theorem integral_tensor (f : ℝ→ℂ) (b : Af→ℂ) (h : (∫ x,f x)=0) (ν : Measure A) [ν.IsAddHaarMeasure] :
    (∫ x,f (archR x)*b x.2 ∂ν)=0 := by
  let νi : Measure Ai := Measure.addHaar
  let νf : Measure Af := Measure.addHaar
  haveI : νi.IsAddHaarMeasure := Measure.isAddHaarMeasure_addHaarMeasure _
  haveI : νf.IsAddHaarMeasure := Measure.isAddHaarMeasure_addHaarMeasure _
  haveI : (νi.map infReal).IsAddHaarMeasure := infReal.isAddHaarMeasure_map νi
  have hi : (∫ x,f (infReal x) ∂νi)=0 := by
    have he : MeasurableEmbedding (fun x : Ai => infReal x) := infReal.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    rw [←he.integral_map f]
    change (∫ x,f x ∂(νi.map infReal))=0
    rw [Measure.isAddLeftInvariant_eq_smul (νi.map infReal) (volume:Measure ℝ)]
    simp [integral_smul_measure,h]
  let ρ : Measure A := νi.prod νf
  haveI : ρ.IsAddHaarMeasure := inferInstanceAs ((νi.prod νf).IsAddHaarMeasure)
  have hp : (∫ x,f (archR x)*b x.2 ∂ρ)=0 := by
    change (∫ x : Ai×Af,f (infReal x.1)*b x.2 ∂(νi.prod νf))=0
    rw [integral_prod_mul (fun y => f (infReal y)) b,hi,zero_mul]
  rw [Measure.isAddLeftInvariant_eq_smul ν ρ]
  simp [integral_smul_measure,hp]

private noncomputable def liftLogTest (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  if 0 < t then g (Real.log t) else 0

private theorem liftLogTest_comp_exp (g : ℝ → ℂ) :
    liftLogTest g ∘ Real.exp = g := by
  funext x
  simp [liftLogTest, Real.exp_pos, Real.log_exp]

private theorem liftLogTest_support {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    tsupport (liftLogTest g) ⊆ Real.exp '' tsupport g := by
  have hC := hg.isCompact.image Real.continuous_exp
  apply closure_minimal _ hC.isClosed
  intro t ht
  have hnz : liftLogTest g t ≠ 0 := ht
  by_cases h : 0 < t
  · refine ⟨Real.log t, subset_tsupport _ ?_, Real.exp_log h⟩
    simpa [liftLogTest, h] using hnz
  · simp [liftLogTest, h] at hnz

private theorem liftLogTest_contDiff {g : ℝ → ℂ}
    (hg : HasCompactSupport g) (hG : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (liftLogTest g) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · have hU : ∀ᶠ x : ℝ in 𝓝 t, 0 < x := Ioi_mem_nhds ht
    apply ContDiffAt.congr_of_eventuallyEq
      (hG.contDiffAt.comp t ((Real.contDiffAt_log).mpr ht.ne'))
    exact hU.mono (fun x hx => if_pos hx)
  · let K := Real.exp '' tsupport g
    have hc : IsClosed K := (hg.isCompact.image Real.continuous_exp).isClosed
    have htK : t ∈ Kᶜ := by
      rintro ⟨x,_,rfl⟩
      exact ht (Real.exp_pos _)
    have hU : ∀ᶠ x : ℝ in 𝓝 t, x ∈ Kᶜ := hc.isOpen_compl.mem_nhds htK
    apply ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0:ℂ)))
    filter_upwards [hU] with x hx
    exact Function.notMem_support.mp (fun h => hx (liftLogTest_support hg (subset_tsupport _ h)))

private theorem liftLogTest_hasCompactSupport {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (liftLogTest g) :=
  (hg.isCompact.image Real.continuous_exp).of_isClosed_subset isClosed_closure (liftLogTest_support hg)


private abbrev V := HeightOneSpectrum (𝓞 ℚ)
private def place (p : Nat.Primes) : V := Rat.HeightOneSpectrum.primesEquiv.symm p
private def up (p : Nat.Primes) := uniformizerIdele ℚ (place p)
private theorem principal (p : Nat.Primes) : (place p).asIdeal=Ideal.span {(p:𝓞 ℚ)} := by
  change (Ideal.span {((p:ℕ):ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm=_
  rw [Ideal.map_span,Set.image_singleton,map_natCast]
private theorem val_prime (p : Nat.Primes) (v : V) :
    v.valuation ℚ (p:ℚ) = if v=place p then WithZero.exp (-1) else 1 := by
  have hh : algebraMap (𝓞 ℚ) ℚ (p:𝓞 ℚ)=(p:ℚ) := by simp
  rw [←hh,v.valuation_of_algebraMap]
  split_ifs with h
  · subst v;exact (place p).intValuation_singleton (by exact_mod_cast p.2.ne_zero) (principal p)
  · apply HeightOneSpectrum.intValuation_eq_one_iff.mpr
    intro hm
    have hle : (place p).asIdeal≤v.asIdeal := (principal p) ▸ (Ideal.span_le.mpr (singleton_subset_iff.mpr hm))
    exact h ((HeightOneSpectrum.asIdeal_injective ((place p).isMaximal.eq_of_le v.isPrime.ne_top hle)).symm)
private theorem val_shift (p : Nat.Primes) (v : V) :
    Valued.v ((↑(up p)⁻¹:A).2 v) = v.valuation ℚ (p:ℚ)⁻¹ := by
  have h : Idele.ord ℚ v (up p) = if v=place p then 1 else 0 := by
    by_cases hv : v=place p
    · subst v; simp [up,Idele.ord_uniformizerIdele_self]
    · simp [up,hv,Idele.ord_uniformizerIdele_of_ne _ hv]
  rw [Idele.valued_snd_eq_exp_neg_ord, Idele.ord_inv,neg_neg,map_inv₀,val_prime,h]
  split_ifs <;> simp
private theorem shift_integral (p : Nat.Primes) (y : A) :
    ((↑(up p)⁻¹:A)*y).2∈integralAf ↔
      (algebraMap ℚ A (p:ℚ)⁻¹).2*y.2∈integralAf := by
  apply forall_congr'; intro v
  change Valued.v (((↑(up p)⁻¹:A).2 v)*(y.2 v))≤1 ↔ Valued.v (((algebraMap ℚ A (p:ℚ)⁻¹).2 v)*(y.2 v))≤1
  rw [map_mul,map_mul,val_shift,AdeleRing.algebraMap_snd_apply,HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
private theorem shift_subset (p : Nat.Primes) (y : A)
    (h : (algebraMap ℚ A (p:ℚ)⁻¹).2*y.2∈integralAf) : y.2∈integralAf := by
  have h0 : (algebraMap ℚ A (p:ℚ)).2∈integralAf := by
    intro v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,AdeleRing.algebraMap_snd_apply,HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa using v.valuation_le_one (K:=ℚ) (p:𝓞 ℚ)
  have hh := AdelicLevel.mul_mem_integralFiniteAdeles h0 h
  have he : algebraMap ℚ A (p:ℚ) * algebraMap ℚ A (p:ℚ)⁻¹ = 1 := by rw [←map_mul,mul_inv_cancel₀ (by exact_mod_cast p.2.ne_zero),map_one]
  change ((algebraMap ℚ A (p:ℚ))*((algebraMap ℚ A (p:ℚ)⁻¹)*y)).2∈integralAf at hh
  rwa [←mul_assoc,he,one_mul] at hh
private theorem tensor_shift (p : Nat.Primes) (f : ℝ→ℂ) (y : A) :
    tensorF f y - tensorF f ((↑(up p)⁻¹:A)*y) =
    if y.2∈integralAf ∧ (algebraMap ℚ A (p:ℚ)⁻¹).2*y.2∉integralAf then f (archR y) else 0 := by
  have ha : archR ((↑(up p)⁻¹:A)*y)=archR y := by
    rw [map_mul,show archR (↑(up p)⁻¹:A)=1 from archR.map_one,one_mul]
  rw [tensorF,tensorF,ha]
  by_cases hs : (algebraMap ℚ A (p:ℚ)⁻¹).2*y.2∈integralAf
  · simp [finTest,indicator_of_mem (shift_subset p y hs),indicator_of_mem ((shift_integral p y).mpr hs),hs]
  · have hn := fun h => hs ((shift_integral p y).mp h)
    by_cases hy : y.2∈integralAf
    · simp [finTest,indicator_of_notMem hn,indicator_of_mem hy,hs,hy]
    · simp [finTest,indicator_of_notMem hn,indicator_of_notMem hy,hy]

section
variable {μ : Measure ℝ}
private abbrev H (μ : Measure ℝ) := Lp ℂ 2 μ
private def cutoff (s : Set ℝ) (hs : MeasurableSet s) (f : H μ) : H μ :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator f)
private theorem cutoff_ae {s : Set ℝ} (hs : MeasurableSet s) (f : H μ) :
    ⇑(cutoff s hs f)=ᵐ[μ] s.indicator f := MemLp.coeFn_toLp _
private def cutLin (s : Set ℝ) (hs : MeasurableSet s) : H μ→ₗ[ℂ]H μ where
  toFun := cutoff s hs
  map_add' f g := by
    apply Lp.ext
    filter_upwards [cutoff_ae hs (f+g),Lp.coeFn_add f g,Lp.coeFn_add (cutoff s hs f) (cutoff s hs g),cutoff_ae hs f,cutoff_ae hs g] with x h1 h2 h3 h4 h5
    by_cases hx : x∈s <;> simp_all [Set.indicator_apply,hx]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [cutoff_ae hs (c • f),Lp.coeFn_smul c f,Lp.coeFn_smul c (cutoff s hs f),cutoff_ae hs f] with x h1 h2 h3 h4
    change cutoff s hs (c • f) x=(c • cutoff s hs f) x
    by_cases hx : x∈s <;> simp_all [Set.indicator_apply,hx]
private def mask (s : Set ℝ) (hs : MeasurableSet s) : H μ→L[ℂ]H μ :=
  (cutLin s hs).mkContinuous 1 (fun f => by
    change ‖((Lp.memLp f).indicator hs).toLp (s.indicator f)‖≤1*‖f‖
    rw [one_mul,Lp.norm_toLp,Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.memLp f).2.ne (eLpNorm_indicator_le f))


end

private def adm (Φ : A→ℂ) : Prop := Φ ∈ AdelicFourier.schwartzBruhat ℚ ∧ Φ 0=0 ∧
  ∀ (m : Measure A) [m.IsAddHaarMeasure], (∫ x,Φ x ∂m)=0
private def purePV (p : Nat.Primes) : Set (A→ℂ) := {Φ | adm Φ ∧ ∃ (Ψ : A→ℂ) (f : ℝ→ℂ),
    adm Ψ ∧ ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (∀ y,Ψ y=if y.2∈integralAf then f (archR y) else 0) ∧
    ∀ y,Φ y=Ψ y-Ψ ((↑(up p)⁻¹:A)*y)}
private def radiusRep (t : ℝ) (z : G) : Prop :=
  (z:A).2∈integralAf ∧ (↑z⁻¹:A).2∈integralAf ∧ archR z=Real.exp t
private def orbImage (μ : Measure ℝ) (s : Set ℝ) (B : Set (A→ℂ)) : Set (H μ) :=
  {w | ∃ Φ∈B, ∀ᵐ t ∂μ, (t∉s → w t=0) ∧
    (t∈s → ∀ z : G,radiusRep t z → HasSum (fun q : ℚˣ => Φ (algebraMap ℚ A (q:ℚ)*z)) (w t))}
private theorem pv_interp (a : ℝ) (p : Nat.Primes) (g : ℝ→ℂ)
    (hd : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ Φ∈purePV p,∀ t : ℝ,a≤t → ∀ z : G,radiusRep t z →
      HasSum (fun q : ℚˣ => Φ (algebraMap ℚ A (q:ℚ)*z)) (g t) := by
  let h := liftLogTest g
  have hneg (x : ℝ) (hx : x≤0) : h x=0 := if_neg (not_lt.mpr hx)
  obtain ⟨f,Φ,hf,hfc,hf₀,hfi,hform,hm,hzero,hi,hθ⟩ :=
    MasulloAudit.truncated_theta_admissible_test_interpolation {p} (Real.exp a) (Real.exp_pos a) h
      (liftLogTest_contDiff hc hd) (liftLogTest_hasCompactSupport hc) hneg
  refine ⟨Φ,⟨⟨hm,hzero,hi⟩,tensorF f,f,⟨tensor_mem hf hfc,?_,?_⟩,hf,hfc,?_,?_⟩,?_⟩
  · simp [tensorF,hf₀ 0 le_rfl]
  · intro m _;exact integral_tensor f finTest hfi m
  · intro y;by_cases hy : y.2∈integralAf <;> simp [tensorF,finTest,hy]
  · intro y;rw [hform,tensor_shift]
    simp only [Finset.mem_singleton,forall_eq]
    rfl
  · rintro t ht z ⟨h1,h2,h3⟩
    have he : Real.exp a≤archR z := h3 ▸ Real.exp_le_exp.mpr ht
    have hval : h (archR z)=g t := by rw [h3];exact congrFun (liftLogTest_comp_exp g) t
    rw [←hval];exact hθ z h1 h2 he

private theorem normalized_exists (t : ℝ) : ∃ z : G,radiusRep t z := by
  let x (r : ℝ) : A := (fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (realplace v)).symm r,1)
  have hm (r s : ℝ) : x r*x s=x (r*s) := by
    apply Prod.ext
    · funext v; exact (map_mul (InfinitePlace.Completion.ringEquivRealOfIsReal (realplace v)).symm r s).symm
    · exact one_mul _
  have h1 : x 1=1 := by
    apply Prod.ext
    · funext v;exact map_one _
    · rfl
  let z : G := ⟨x (Real.exp t),x (Real.exp (-t)),by rw [hm,←Real.exp_add,add_neg_cancel,Real.exp_zero,h1],
    by rw [hm,←Real.exp_add,neg_add_cancel,Real.exp_zero,h1]⟩
  refine ⟨z,fun v => one_mem _,fun v => one_mem _,?_⟩
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply (Real.exp t)

private theorem fixed_iff {μ : Measure ℝ} {s : Set ℝ} (hs : MeasurableSet s) (w : H μ) :
    mask s hs w=w ↔ ∀ᵐ t ∂μ,t∉s → w t=0 := by
  have he : (fun t => mask s hs w t)=ᵐ[μ] s.indicator w := cutoff_ae hs w
  constructor
  · intro h;rw [h] at he
    filter_upwards [he] with t ht hts
    exact ht.trans (indicator_of_notMem hts _)
  · intro h;apply Lp.ext
    filter_upwards [he,h] with t ht hw
    rw [ht];by_cases hx : t∈s
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,hw hx]

private theorem image_closure (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (p : Nat.Primes) (a : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (hsa : s⊆Ici a)
    (B : Set (A→ℂ)) (hB : purePV p⊆B) :
    closure (orbImage μ s B)={w | ∀ᵐ t ∂μ,t∉s → w t=0} := by
  let M : H μ→L[ℂ]H μ := mask s hs
  have hset : {w : H μ | ∀ᵐ t ∂μ,t∉s → w t=0}={w | M w=w} :=
    Set.ext fun w => (fixed_iff hs w).symm
  apply le_antisymm
  · apply closure_minimal
    · rintro w ⟨Φ,hΦ,hw⟩
      exact hw.mono (fun t h => h.1)
    · rw [hset];exact isClosed_eq M.continuous continuous_id
  · intro w hw
    let X := {v : H μ | ∃ g : ℝ → ℂ,(v:ℝ→ℂ)=ᵐ[μ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g}
    have hd : Dense X := Lp.dense_hasCompactSupport_contDiff (by norm_num)
    have hmem : M w∈closure (M '' X) := image_closure_subset_closure_image M.continuous ⟨w,hd w,rfl⟩
    rw [(fixed_iff hs w).mpr hw] at hmem
    apply closure_mono _ hmem
    rintro _ ⟨v,⟨g,hv,hc,hg⟩,rfl⟩
    obtain ⟨Φ,hΦ,hθ⟩ := pv_interp a p g hg hc
    refine ⟨Φ,hB hΦ,?_⟩
    filter_upwards [cutoff_ae hs v,hv] with t ht hv
    constructor
    · intro hx;exact ht.trans (indicator_of_notMem hx _)
    · intro hx z hz
      have hw : M v t=g t := ht.trans ((indicator_of_mem hx _).trans hv)
      rw [hw];exact hθ t (hsa hx) z hz


end RationalAdelicCutoffProof

open NumberField IsDedekindDomain MeasureTheory Set Filter Topology
open scoped ContDiff Classical

noncomputable local instance : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) :=
  (borel (InfiniteAdeleRing ℚ)).prod (borel (FiniteAdeleRing (𝓞 ℚ) ℚ))


open RationalAdelicCutoffProof

open MasulloAudit.RationalSphericalCutoff

theorem solution (p : Nat.Primes) (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (a : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (hsa : s ⊆ Set.Ici a) :
    (∀ t : ℝ, ∃ z, Representative t z) ∧
    (∀ B, primeSources p ⊆ B →
      closure (MasulloAudit.RationalSphericalCutoff.image μ s B) = supported μ s) ∧
    closure (MasulloAudit.RationalSphericalCutoff.image μ s (primeSources p)) = supported μ s ∧
    closure (MasulloAudit.RationalSphericalCutoff.image μ s {test | Admissible test}) = supported μ s := by
  have hB (B : Set (Adele → ℂ)) (h : primeSources p ⊆ B) :
      closure (MasulloAudit.RationalSphericalCutoff.image μ s B) = supported μ s :=
    image_closure μ p a s hs hsa B h
  exact ⟨normalized_exists, hB, hB _ (Set.Subset.rfl), hB _ (fun _ h => h.1)⟩
