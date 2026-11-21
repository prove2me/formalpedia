-- Prove2me | solution 1 for MasulloAudit.rational_tate_one_line_nonintegrable
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:42:20.65766+00:00
-- url     : https://prove2.me/submissions/8d5f1bb5-addd-4421-a417-d184b85dd2a6

import Mathlib
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele

open NumberField IsDedekindDomain Set Filter Topology MeasureTheory AutomorphicForm
open scoped SchwartzMap ContDiff Classical
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private abbrev V := HeightOneSpectrum (𝓞 ℚ)
private abbrev A := AdeleRing (𝓞 ℚ) ℚ
private abbrev G := Aˣ
private abbrev Af := FiniteAdeleRing (𝓞 ℚ) ℚ
private abbrev M := mixedEmbedding.mixedSpace ℚ
private def place (p : Nat.Primes) : V := Rat.HeightOneSpectrum.primesEquiv.symm p
private theorem place_norm (p : Nat.Primes) : Ideal.absNorm (place p).asIdeal=p.val := by
  have hid : (place p).asIdeal=Ideal.span {(p.val:𝓞 ℚ)} := by
    change (Ideal.span {(p.val:ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm=_
    rw [Ideal.map_span,Set.image_singleton,map_natCast]
  rw [hid,Ideal.absNorm_span_singleton]
  simp [Algebra.norm_natCast,RingOfIntegers.rank]

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

private def testFn (g : 𝓢(M,ℂ)) (x : A) : ℂ :=
  g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) * finTest x.2

private theorem test_schwartz (g : 𝓢(M,ℂ)) : testFn g ∈ AdelicFourier.schwartzBruhat ℚ :=
  AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet
    (AdelicFourier.tensor_mem_pureTensorSet g finTest fin_lc fin_cs)

private def up (p : Nat.Primes) : G := uniformizerIdele ℚ (place p)
private def unitSet : Set G := AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ ∅
private theorem on_unit_ord {x : G} (hx : x∈unitSet) (v : V) : Idele.ord ℚ v x=0 := by
  apply (Idele.ord_eq_zero_iff ..).mpr
  exact hx v (by simp)
private theorem ord_up (p : Nat.Primes) (v : V) :
    Idele.ord ℚ v (up p) = if v=place p then 1 else 0 := by
  classical
  by_cases h : v=place p
  · subst v; simp [up,Idele.ord_uniformizerIdele_self]
  · simp [h,up,Idele.ord_uniformizerIdele_of_ne _ h]
private theorem up_integral (p : Nat.Primes) : ((up p:A)).2 ∈ integralAf := by
  intro v
  change Valued.v (((up p:A)).2 v) ≤ 1
  rw [Idele.valued_snd_eq_exp_neg_ord,ord_up]
  rw [←WithZero.exp_zero,WithZero.exp_le_exp]
  split_ifs <;> norm_num
private theorem up_arch (p : Nat.Primes) : (up p:A).1=1 := rfl
private theorem up_norm (p : Nat.Primes) : TateGlobal.ideleNorm ℚ (up p)=(p:ℝ)⁻¹ := by
  rw [up,TateGlobal.ideleNorm_uniformizerIdele,place_norm]
private def slab (p : Nat.Primes) := (fun x : G => up p*x) '' unitSet

private theorem slab_disjoint : Pairwise (Function.onFun Disjoint slab) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,he⟩ := hy
  have h := congrArg (Idele.ord ℚ (place p)) he
  have hp : place p ≠ place q := fun h => hpq (Rat.HeightOneSpectrum.primesEquiv.symm.injective h)
  simp [Idele.ord_mul,ord_up,hp,on_unit_ord hu,on_unit_ord hv] at h

private def mag (g : 𝓢(M,ℂ)) (x : G) : ℝ := ‖testFn g x‖ * TateGlobal.ideleNorm ℚ x
private theorem mag_pos_iff (g : 𝓢(M,ℂ)) {x : G} (hx : x∈unitSet) :
    0 < mag g x ↔ g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (x:A).1) ≠ 0 := by
  have hi : (x:A).2∈integralAf := fun v => (hx v (by simp)).1
  simp only [mag,testFn,finTest,indicator_of_mem hi,mul_one]
  simp [TateGlobal.ideleNorm_pos]

private theorem mag_scale (g : 𝓢(M,ℂ)) (p : Nat.Primes) {x : G} (hx : x∈unitSet) :
    mag g (up p*x)=(p:ℝ)⁻¹*mag g x := by
  have hi : (x:A).2∈integralAf := fun v => (hx v (by simp)).1
  have hj : ((↑(up p*x):A)).2∈integralAf := AdelicLevel.mul_mem_integralFiniteAdeles (up_integral p) hi
  have ha : ((↑(up p*x):A)).1=(x:A).1 := by change (up p:A).1*(x:A).1=_;rw [up_arch,one_mul]
  simp only [mag,testFn,finTest,ha,indicator_of_mem hi,indicator_of_mem hj,
    TateGlobal.ideleNorm_mul,up_norm,mul_one]
  ring

private theorem tate_failure [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure]
    (g : 𝓢(M,ℂ)) (hg : g 1≠0) (s : ℂ) (hs : s.re=1) :
    ¬Integrable (fun x : G => testFn g x * ((TateGlobal.ideleNorm ℚ x:ℝ):ℂ)^s) ν := by
  intro hI
  have he (x : G) : ‖testFn g x*((TateGlobal.ideleNorm ℚ x:ℝ):ℂ)^s‖=mag g x := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (TateGlobal.ideleNorm_pos _) _,hs,Real.rpow_one]
    rfl
  have hm : Integrable (mag g) ν := (hI.norm).congr <| .of_forall he
  have hU : IsOpen unitSet := Idele.isOpen_unitIdelesOutside ℚ ∅
  let C := ∫ x in unitSet, mag g x ∂ν
  have hC : 0<C := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae (.of_forall fun x =>
      mul_nonneg (norm_nonneg _) (TateGlobal.ideleNorm_pos x).le) hm.integrableOn).mpr
    let Ω := {x : G | g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (x:A).1) ≠ 0} ∩ unitSet
    have ha : Continuous (fun x : G => g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (x:A).1)) :=
      g.continuous.comp ((AdelicBox.continuous_ringEquiv_mixedSpace ℚ).comp
        (continuous_fst.comp Units.continuous_val))
    have hΩ : IsOpen Ω := (isOpen_ne_fun ha continuous_const).inter hU
    have harch : InfiniteAdeleRing.ringEquiv_mixedSpace ℚ ((1:G):A).1=(1:M) := (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).map_one
    have h1 : (1:G)∈Ω := ⟨by
      change g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ ((1:G):A).1) ≠ 0
      rwa [harch],Subgroup.one_mem _⟩
    apply lt_of_lt_of_le (hΩ.measure_pos ν ⟨1,h1⟩) (measure_mono ?_)
    intro x hx
    exact ⟨((mag_pos_iff g hx.2).mpr hx.1).ne',hx.2⟩
  have hsl (p : Nat.Primes) : (∫ x in slab p,mag g x ∂ν) = (p:ℝ)⁻¹*C := by
    rw [slab,(measurePreserving_mul_left ν (up p)).setIntegral_image_emb
      ((Homeomorph.mulLeft (up p)).measurableEmbedding) (mag g) unitSet,←integral_const_mul]
    exact setIntegral_congr_fun hU.measurableSet (fun x hx => mag_scale g p hx)
  have hsum := hasSum_integral_iUnion (μ := ν) (s := slab)
    (fun p => ((Homeomorph.mulLeft (up p)).isOpenMap _ hU).measurableSet) slab_disjoint hm.integrableOn
  have h := hsum.summable.mul_right C⁻¹
  exact Nat.Primes.not_summable_one_div (by simpa only [hsl,mul_assoc,mul_inv_cancel₀ hC.ne',mul_one,one_div] using h)

theorem solution [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ]
    (ν : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [ν.IsHaarMeasure] :
    ∃ f ∈ AdelicFourier.schwartzBruhat ℚ, f 1=1 ∧
      ∀ s : ℂ, s.re=1 → ¬Integrable (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        f x * ((TateGlobal.ideleNorm ℚ x : ℝ):ℂ)^s) ν := by
  obtain ⟨g,_,hcs,hsm,_,hg⟩ := exists_contDiff_tsupport_subset (n := ⊤) (x := (1:M)) (s := univ) univ_mem
  let G₀ : 𝓢(M,ℂ) := (hcs.comp_left (g:=Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hsm)
  have hG₀ : G₀ 1=1 := by change (g 1:ℂ)=1;rw [hg];simp
  refine ⟨testFn G₀,test_schwartz G₀,?_,fun s hs => tate_failure ν G₀ (hG₀ ▸ one_ne_zero) s hs⟩
  have h₁ : ((1:A).2) ∈ integralAf := AdelicLevel.one_mem_integralFiniteAdeles
  have harch : InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (1:A).1=(1:M) := (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).map_one
  simp only [testFn,finTest,harch,indicator_of_mem h₁,hG₀,mul_one]
