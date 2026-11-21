-- Prove2me | solution 1 for MasulloAudit.truncated_theta_admissible_test_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:32:12.807525+00:00
-- url     : https://prove2.me/submissions/ddb00ebf-b27c-436d-9302-54e00b2f8571

import Mathlib
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox

open Finset Filter Topology MeasureTheory ArithmeticFunction
open scoped Moebius ContDiff SchwartzMap
noncomputable section

private def coef (P d : ℕ) : ℂ := if d.Coprime P then (μ d:ℂ) else 0
private def truncInv (P M : ℕ) (g : ℝ→ℂ) (x : ℝ) := ∑ d∈Ioc 0 M,coef P d*g (d*x)
private def thetaTerm (P : ℕ) (f : ℝ→ℂ) (x : ℝ) (n : ℕ) := if 0<n ∧ n.Coprime P then f (n*x) else 0
private theorem sum_fiber (k : ℕ) : (∑ z∈k.divisorsAntidiagonal,(μ z.1:ℂ)) = if k=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f k) (coe_moebius_mul_coe_zeta (R:=ℂ))
  change _= (1:ArithmeticFunction ℂ) k at h
  rw [ArithmeticFunction.mul_apply,ArithmeticFunction.one_apply] at h
  convert h using 1
  apply sum_congr rfl;intro z hz
  have hpos := Nat.ne_zero_of_mem_divisorsAntidiagonal hz
  simp [ArithmeticFunction.zeta_apply,hpos.2]

private theorem finite_inv (P M : ℕ) (hM : 0<M) (v : ℕ→ℂ) (hv : ∀ k, M<k → v k=0) :
    (∑ d∈Ioc 0 M,∑ n∈Ioc 0 M, if (d*n).Coprime P then (μ d:ℂ)*v (d*n) else 0)=v 1 := by
  let S := Ioc 0 M
  let A := S ×ˢ S
  let m (z : ℕ×ℕ) := z.1*z.2
  let f (z : ℕ×ℕ) := if (m z).Coprime P then (μ z.1:ℂ)*v (m z) else 0
  change (∑ d∈S,∑ n∈S,f (d,n))=_
  rw [←sum_product']
  change (∑ z∈A,f z)=_
  have hcut : (∑ z∈A with m z∈S,f z)=∑ z∈A,f z := by
    rw [sum_filter];apply sum_congr rfl;intro z hz
    by_cases hm : m z∈S
    · simp [hm]
    have hj := mem_product.mp hz
    have hpos := Nat.mul_pos (mem_Ioc.mp hj.1).1 (mem_Ioc.mp hj.2).1
    have hlarge : M < m z := by simpa [S,mem_Ioc,m,hpos] using hm
    simp [hm,f,hv _ hlarge]
  rw [←hcut,←sum_fiberwise_eq_sum_filter]
  have hk (k : ℕ) (hk : k∈S) : (∑ z ∈ A with m z=k,f z)=(if k=1 then v 1 else 0) := by
    have hp := (mem_Ioc.mp hk).1
    have hf : A.filter (fun z => m z=k)=k.divisorsAntidiagonal := (Nat.divisorsAntidiagonal_eq_prod_filter_of_le hp.ne' (mem_Ioc.mp hk).2).symm
    rw [hf]
    have he (z : ℕ×ℕ) (h : z∈k.divisorsAntidiagonal) : m z=k := (Nat.mem_divisorsAntidiagonal.mp h).1
    by_cases hcop : k.Coprime P
    · calc _ = ∑ z∈k.divisorsAntidiagonal,(μ z.1:ℂ)*v k := by apply sum_congr rfl;intro z hz;simp [f,he z hz,hcop]
           _ = _ := by rw [←sum_mul,sum_fiber];split_ifs with hk <;> simp_all
    · have hn : k≠1 := by rintro rfl;exact hcop (by simp)
      rw [if_neg hn];apply sum_eq_zero;intro z hz;simp [f,he z hz,hcop]
  rw [sum_congr rfl hk]
  simp [S,hM.ne']

private theorem trunc_law {a : ℝ} (ha : 0<a) (P M : ℕ) (hM : 0<M) (g : ℝ→ℂ)
    (hg : ∀ y : ℝ,(M:ℝ)*a<y → g y=0) (x : ℝ) (hx : a≤x) :
    HasSum (thetaTerm P (truncInv P M g) x) (g x) := by
  have vanish (n : ℕ) (hn : M<n) : g (n*x)=0 := by
    apply hg;exact (mul_lt_mul_of_pos_right (by exact_mod_cast hn) ha).trans_le (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _))
  have hsum := finite_inv P M hM (fun n => g (n*x)) vanish
  have he : (∑ n∈Ioc 0 M,thetaTerm P (truncInv P M g) x n)=g x := by
    change (∑ n∈Ioc 0 M,thetaTerm P (truncInv P M g) x n)=_
    rw [sum_comm] at hsum
    convert hsum using 1
    · apply sum_congr rfl;intro n hn
      by_cases hnp : n.Coprime P
      · rw [thetaTerm,if_pos ⟨(mem_Ioc.mp hn).1,hnp⟩,truncInv]
        apply sum_congr rfl;intro d hd
        by_cases hdp : d.Coprime P
        · rw [coef,if_pos hdp,if_pos (Nat.coprime_mul_iff_left.mpr ⟨hdp,hnp⟩),Nat.cast_mul,mul_assoc]
        · rw [coef,if_neg hdp,if_neg (fun h => hdp (Nat.coprime_mul_iff_left.mp h).1),zero_mul]
      · simp [thetaTerm,hnp,Nat.coprime_mul_iff_left]
    · simp
  rw [←he]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  by_cases hn0 : 0<n
  · have hgt : M<n := by simpa [hn0] using hn
    by_cases hc : n.Coprime P
    · rw [thetaTerm,if_pos ⟨hn0,hc⟩,truncInv];apply sum_eq_zero;intro d hd
      have hn' : M<d*n := hgt.trans_le (Nat.le_mul_of_pos_left _ (mem_Ioc.mp hd).1)
      have hzero := vanish _ hn';push_cast at hzero;rw [←mul_assoc,hzero,mul_zero]
    · simp [thetaTerm,hc]
  · simp [thetaTerm,hn0]

private theorem correction {a : ℝ} (ha : 0<a) :
    ∃ b : ℝ→ℂ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ (∫ y,b y)=1 ∧
      ∀ x, x∉Set.Ioo 0 a → b x=0 := by
  obtain ⟨g,hs,hcs,hsm,hr,h1⟩ := exists_contDiff_tsupport_subset (n:=⊤) (x:=a/2)
    (isOpen_Ioo.mem_nhds (show a/2∈Set.Ioo 0 a by constructor <;> linarith))
  have hi : Integrable g volume := hsm.continuous.integrable_of_hasCompactSupport hcs
  have hp := integral_pos_of_integrable_nonneg_nonzero hsm.continuous hi (fun x => (hr (Set.mem_range_self x)).1) (h1 ▸ one_ne_zero)
  let c := ((∫ u,g u:ℝ):ℂ)⁻¹
  let v := fun x => (g x:ℂ)
  have hsV : HasCompactSupport v := hcs.comp_left (g:=Complex.ofReal) (by simp)
  refine ⟨fun x => c*v x,contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hsm),hsV.mul_left (f:=fun _ => c),?_,?_⟩
  · simp only [v,integral_const_mul,integral_complex_ofReal,c,inv_mul_cancel₀ (by exact_mod_cast hp.ne' : ((∫ u,g u:ℝ):ℂ)≠0)]
  · intro x hx
    have hz : g x=0 := by by_contra h;exact hx (hs (subset_closure h))
    simp [v,hz]

private theorem arch_inverse (P : ℕ) (a : ℝ) (ha : 0<a) (g : ℝ→ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hneg : ∀ x, x≤0 → g x=0) :
    ∃ f : ℝ→ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x, x≤0 → f x=0) ∧
      (∫ x,f x)=0 ∧ ∀ x, a≤x → HasSum (thetaTerm P f x) (g x) := by
  obtain ⟨b,hb⟩ := hc.bddAbove
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (b/a))
  have hN1 : 0<N := by have := (le_max_left 1 (b/a)).trans_lt hN;exact_mod_cast (by linarith : (0:ℝ)<N)
  have hbN : b<(N:ℝ)*a := (div_lt_iff₀ ha).mp ((le_max_right 1 _).trans_lt hN)
  have hlarge (y : ℝ) (hy : (N:ℝ)*a<y) : g y=0 := by
    by_contra hn;exact (not_lt_of_ge (hb (subset_closure hn))) (hbN.trans hy)
  let F := truncInv P N g
  have hF : ContDiff ℝ ∞ F := ContDiff.sum (fun d _ => contDiff_const.mul (hg.comp (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ => (d:ℝ)*x))))
  have hz (x : ℝ) (hx : x≤0) : F x=0 := sum_eq_zero (fun d _ => by rw [hneg _ (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) hx),mul_zero])
  have htail (x : ℝ) (hx : (N:ℝ)*a<x) : F x=0 := by
    apply sum_eq_zero;intro d hd
    have hd1 : (1:ℝ)≤d := by exact_mod_cast (mem_Ioc.mp hd).1
    have hxp : 0≤x := (mul_nonneg (Nat.cast_nonneg _) ha.le).trans hx.le
    rw [hlarge _ (hx.trans_le (le_mul_of_one_le_left hxp hd1)),mul_zero]
  have hcsF : HasCompactSupport F := by
    apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (s:=Set.Icc 0 ((N:ℝ)*a));apply closure_minimal _ isClosed_Icc
    intro x hx
    exact ⟨le_of_not_gt (fun h => hx (hz x h.le)),le_of_not_gt (fun h => hx (htail x h))⟩
  obtain ⟨w,hw,hcw,hiw,hws⟩ := correction ha
  let z := ∫ x,F x
  let f := fun x => F x-z*w x
  have hcf : HasCompactSupport f := hcsF.sub (hcw.mul_left (f:=fun _ => z))
  have hf : ContDiff ℝ ∞ f := hF.sub (contDiff_const.mul hw)
  refine ⟨f,hf,hcf,?_,?_,?_⟩
  · intro x hx;simp [f,hz x hx,hws x (fun h => (not_lt_of_ge hx) h.1)]
  · have hIF : Integrable F volume := hF.continuous.integrable_of_hasCompactSupport hcsF
    have hIw : Integrable w volume := hw.continuous.integrable_of_hasCompactSupport hcw
    rw [show (∫ x,f x)=(∫ x,F x)-∫ x,z*w x by exact integral_sub hIF (hIw.const_mul z),integral_const_mul,hiw,mul_one,sub_self]
  · intro x hx
    apply (trunc_law ha P N hN1 g hlarge x hx).congr_fun
    intro n
    by_cases hp : 0<n ∧ n.Coprime P
    · have h1 : (1:ℝ)≤n := by exact_mod_cast hp.1
      have hxa := hx.trans (le_mul_of_one_le_left (ha.le.trans hx) h1)
      rw [thetaTerm,thetaTerm,if_pos hp,if_pos hp]
      simp [f,F,hws _ (fun h => (not_lt_of_ge hxa) h.2)]
    · simp [thetaTerm,if_neg hp]

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
private theorem ar_rat (q : ℚ) : archR (algebraMap ℚ A q)=(q:ℝ) :=
  congrArg (fun F : ℚ→+*ℝ => F q) (Subsingleton.elim (archR.comp (algebraMap ℚ A)) (algebraMap ℚ ℝ))
private theorem int_fin (q : ℚ) : (algebraMap ℚ A q).2∈integralAf ↔ ∃ n : ℤ,(n:ℚ)=q := by
  constructor
  · intro h
    have hv (v : HeightOneSpectrum (𝓞 ℚ)) : (v.valuation ℚ) q≤1 := by
      have hh := h v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers,AdeleRing.algebraMap_snd_apply,HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hh
    obtain ⟨o,ho⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q hv
    obtain ⟨n,rfl⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) o
    exact ⟨n,by simpa using ho⟩
  · rintro ⟨n,rfl⟩ v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,AdeleRing.algebraMap_snd_apply,HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have h := v.valuation_le_one (K:=ℚ) (n:𝓞 ℚ)
    simpa using h
private theorem fin_unit (z : G) (hu : (z:A).2∈integralAf) (hv : (↑z⁻¹:A).2∈integralAf) (y : A) :
    (y*(z:A)).2∈integralAf ↔ y.2∈integralAf := by
  constructor
  · intro h
    have h' := AdelicLevel.mul_mem_integralFiniteAdeles h hv
    change ((y*(z:A))*(↑z⁻¹:A)).2∈integralAf at h'
    simpa [mul_assoc] using h'
  · intro h;exact AdelicLevel.mul_mem_integralFiniteAdeles h hu
private def indexQ (n : ℕ) : ℚˣ := Units.mk0 (n+1:ℚ) (by positivity)
private theorem indexQ_inj : Function.Injective indexQ := by
  intro i j h
  have he : (i+1:ℚ)=(j+1:ℚ) := congrArg Units.val h
  exact_mod_cast (add_right_cancel he : (i:ℚ)=(j:ℚ))
private def adelicTerm (P : ℕ) (F : A→ℂ) (z : G) (q : ℚˣ) :=
  if (q:ℚ).num.natAbs.Coprime P then F (algebraMap ℚ A (q:ℚ)*(z:A)) else 0
private theorem lift_orbit {a : ℝ} (ha : 0<a) (P : ℕ) {f g : ℝ→ℂ} (hneg : ∀ x,x≤0 → f x=0)
    (hf : ∀ x,a≤x → HasSum (thetaTerm P f x) (g x))
    (z : G) (hu : (z:A).2∈integralAf) (hv : (↑z⁻¹:A).2∈integralAf) (hz : a≤archR z) :
    HasSum (adelicTerm P (tensorF f) z) (g (archR z)) := by
  have h0 : thetaTerm P f (archR z) 0=0 := by simp [thetaTerm]
  have hnat := (hasSum_nat_add_iff' 1).mpr (hf (archR z) hz)
  simp only [Finset.sum_range_one,h0,sub_zero] at hnat
  apply (indexQ_inj.hasSum_iff _).mp
  · apply hnat.congr_fun
    intro n
    have he : ((indexQ n:ℚˣ):ℚ)=((n+1:ℕ):ℚ) := by simp [indexQ]
    have hfin := (fin_unit z hu hv (algebraMap ℚ A (indexQ n:ℚ))).mpr ((int_fin (indexQ n:ℚ)).mpr ⟨((n+1:ℕ):ℤ),by simp [he]⟩)
    have htest : finTest ((algebraMap ℚ A (indexQ n:ℚ)*(z:A)).2)=1 := indicator_of_mem hfin _
    change (if ((indexQ n:ℚ).num.natAbs).Coprime P then f (archR (algebraMap ℚ A (indexQ n:ℚ)*(z:A)))*finTest _ else 0)=thetaTerm P f (archR z) (n+1)
    rw [htest,mul_one,map_mul,ar_rat,he,Rat.num_natCast,Int.natAbs_natCast,Rat.cast_natCast];simp [thetaTerm]
  · intro q hq
    by_cases hp : (q:ℚ).num.natAbs.Coprime P
    · rw [adelicTerm,if_pos hp,tensorF]
      by_cases h : (algebraMap ℚ A (q:ℚ)*(z:A)).2∈integralAf
      · obtain ⟨k,hk⟩ := (int_fin _).mp ((fin_unit z hu hv _).mp h)
        have hk0 : k≤0 := by
          by_contra! hp
          have he : (k.toNat:ℤ)=k := Int.toNat_of_nonneg hp.le
          obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (show k.toNat≠0 by omega)
          apply hq;refine ⟨m,Units.ext ?_⟩
          change (m+1:ℚ)=_;rw [←hk];exact_mod_cast (show (m:ℤ)+1=k by omega)
        rw [map_mul,ar_rat,←hk,hneg _ (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hk0) (ha.le.trans hz)),zero_mul]
      · simp [finTest,indicator_of_notMem h]
    · simp [adelicTerm,if_neg hp]

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

private def scaled (p : ℕ) (x : Af) := (algebraMap ℚ A (p:ℚ)⁻¹).2*x
private def unitFilter (T : Finset Nat.Primes) (x : Af) := ∏ p∈T, (1-finTest (scaled p x))
private def sieved (T : Finset Nat.Primes) (x : Af) := finTest x*unitFilter T x
private def tensorT (T : Finset Nat.Primes) (f : ℝ→ℂ) (x : A) := f (archR x)*sieved T x.2
private def modulus (T : Finset Nat.Primes) := ∏ p∈T,(p:ℕ)
private theorem filter_lc (T : Finset Nat.Primes) : IsLocallyConstant (unitFilter T) := by
  induction T using Finset.induction with
  | empty =>
    rw [show unitFilter ∅=(fun _ : Af => (1:ℂ)) by funext x;simp [unitFilter]];exact IsLocallyConstant.const _
  | insert p s hp ih =>
    have h : IsLocallyConstant (fun x : Af => 1-finTest (scaled p x)) :=
      (IsLocallyConstant.const (1:ℂ)).sub (fin_lc.comp_continuous (by unfold scaled;fun_prop))
    rw [show unitFilter (insert p s)=(fun x : Af => 1-finTest (scaled p x))*unitFilter s by funext x;simp [unitFilter,Finset.prod_insert hp]]
    exact h.mul ih
private theorem tensorT_mem (T : Finset Nat.Primes) {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    tensorT T f ∈ AdelicFourier.schwartzBruhat ℚ := by
  let G₀ := (hc.comp_homeomorph realE.toHomeomorph).toSchwartzMap (hf.comp realE.contDiff)
  have hl : IsLocallyConstant (sieved T) := fin_lc.mul (filter_lc T)
  have hcs : HasCompactSupport (sieved T) := fin_cs.mul_right (f':=unitFilter T)
  exact AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet (AdelicFourier.tensor_mem_pureTensorSet G₀ (sieved T) hl hcs)
private theorem div_integral {p : ℕ} (hp : 0<p) (k : ℤ) :
    (∃ b : ℤ,(b:ℚ)=(p:ℚ)⁻¹*(k:ℚ)) ↔ p∣k.natAbs := by
  have hp' : (p:ℚ)≠0 := by exact_mod_cast hp.ne'
  rw [←Int.natCast_dvd_natCast,Int.dvd_natAbs]
  constructor
  · rintro ⟨b,hb⟩;refine ⟨b,?_⟩
    have h : (k:ℚ)=(p:ℚ)*(b:ℚ) := by rw [hb];field_simp
    exact_mod_cast h
  · rintro ⟨b,rfl⟩;exact ⟨b,by push_cast;field_simp⟩
private theorem one_filter (p : Nat.Primes) (z : G) (hu : (z:A).2∈integralAf) (hv : (↑z⁻¹:A).2∈integralAf) (k : ℤ) :
    1-finTest (scaled p ((algebraMap ℚ A (k:ℚ)*(z:A)).2))=(if (p:ℕ)∣k.natAbs then 0 else 1:ℂ) := by
  have he : scaled p ((algebraMap ℚ A (k:ℚ)*(z:A)).2) = ((algebraMap ℚ A ((p:ℚ)⁻¹*k))*(z:A)).2 := by
    rw [map_mul];change _=(((algebraMap ℚ A (p:ℚ)⁻¹)*(algebraMap ℚ A (k:ℚ)))*(z:A)).2;rw [mul_assoc];rfl
  have hi := (fin_unit z hu hv _).trans ((int_fin ((p:ℚ)⁻¹*k)).trans (div_integral p.2.pos k))
  rw [he];by_cases hd : (p:ℕ)∣k.natAbs
  · simp only [finTest,indicator_of_mem (hi.mpr hd),if_pos hd,sub_self]
  · simp only [finTest,indicator_of_notMem (fun h => hd (hi.mp h)),if_neg hd,sub_zero]
private theorem cop_eq (T : Finset Nat.Primes) (k : ℕ) : k.Coprime (modulus T) ↔ ∀ p∈T,¬(p:ℕ)∣k := by
  rw [modulus,Nat.coprime_prod_right_iff]
  exact forall₂_congr fun p _ => Nat.coprime_comm.trans p.2.coprime_iff_not_dvd
private theorem term_eq (T : Finset Nat.Primes) (z : G) (hu : (z:A).2∈integralAf) (hv : (↑z⁻¹:A).2∈integralAf) (f : ℝ→ℂ) (q : ℚˣ) :
    tensorT T f (algebraMap ℚ A (q:ℚ)*z)=adelicTerm (modulus T) (tensorF f) z q := by
  let x := algebraMap ℚ A (q:ℚ)*(z:A)
  by_cases hx : x.2∈integralAf
  · obtain ⟨k,hk⟩ := (int_fin _).mp ((fin_unit z hu hv _).mp hx)
    have hnum : (q:ℚ).num.natAbs=k.natAbs := by rw [←hk,Rat.num_intCast]
    have hprod : unitFilter T x.2=∏ p∈T,(if (p:ℕ)∣k.natAbs then 0 else 1:ℂ) := by
      apply prod_congr rfl;intro p hp;dsimp [x];rw [←hk];exact one_filter p z hu hv k
    have hfin : finTest x.2=1 := indicator_of_mem hx _
    change f (archR x)*(finTest x.2*unitFilter T x.2) = if (q:ℚ).num.natAbs.Coprime (modulus T) then f (archR x)*finTest x.2 else 0
    rw [hnum,hfin,hprod];by_cases hn : ∀ p∈T,¬(p:ℕ)∣k.natAbs
    · rw [if_pos ((cop_eq T _).mpr hn),Finset.prod_eq_one (fun p hp => if_neg (hn p hp))];ring
    · rw [if_neg (fun h => hn ((cop_eq T _).mp h))];push Not at hn;obtain ⟨p,hp,hd⟩ := hn
      rw [Finset.prod_eq_zero (f := fun r : Nat.Primes => if (r:ℕ)∣k.natAbs then (0:ℂ) else 1) hp (if_pos hd)];ring
  · have hfin : finTest x.2=0 := indicator_of_notMem hx _
    change f (archR x)*(finTest x.2*unitFilter T x.2)=if _ then f (archR x)*finTest x.2 else 0
    simp only [hfin,zero_mul,mul_zero,ite_self]

private theorem sieve_value (T : Finset Nat.Primes) (x : Af) :
    sieved T x=if x∈integralAf ∧ ∀ p∈T,scaled p x∉integralAf then 1 else 0 := by
  by_cases hx : x∈integralAf
  · have h1 : finTest x=1 := indicator_of_mem hx _
    rw [sieved,h1,one_mul,unitFilter]
    by_cases ht : ∀ p∈T,scaled p x∉integralAf
    · rw [if_pos ⟨hx,ht⟩];apply prod_eq_one;intro p hp
      rw [show finTest (scaled p x)=0 from indicator_of_notMem (ht p hp) _,sub_zero]
    · rw [if_neg (fun h => ht h.2)];push Not at ht;obtain ⟨p,hp,hu⟩ := ht
      apply prod_eq_zero hp;rw [show finTest (scaled p x)=1 from indicator_of_mem hu _,sub_self]
  · rw [sieved,show finTest x=0 from indicator_of_notMem hx _,zero_mul,if_neg (fun h => hx h.1)]

theorem solution (T : Finset Nat.Primes) (a : ℝ) (ha : 0<a) (g : ℝ→ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hg₀ : ∀ x,x≤0 → g x=0) :
    let r := fun y : AdeleRing (𝓞 ℚ) ℚ => (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ y.1).1 ⟨Rat.infinitePlace,Rat.isReal_infinitePlace⟩
    let U := AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ
    ∃ (f : ℝ→ℂ) (Φ : AdeleRing (𝓞 ℚ) ℚ→ℂ),
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x,x≤0 → f x=0) ∧ (∫ x,f x)=0 ∧
      (∀ y,Φ y=if y.2∈U ∧ ∀ p∈T,(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (p:ℚ)⁻¹).2*y.2∉U then f (r y) else 0) ∧
      Φ∈AdelicFourier.schwartzBruhat ℚ ∧ Φ 0=0 ∧
      (∀ (ν : Measure (AdeleRing (𝓞 ℚ) ℚ)) [ν.IsAddHaarMeasure], (∫ x,Φ x ∂ν)=0) ∧
      ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (z:AdeleRing (𝓞 ℚ) ℚ).2∈U → (↑z⁻¹:AdeleRing (𝓞 ℚ) ℚ).2∈U → a≤r z →
        HasSum (fun q : ℚˣ => Φ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (q:ℚ)*z)) (g (r z)) := by
  dsimp only
  obtain ⟨f,hs,hcs,hneg,hi,hθ⟩ := arch_inverse (modulus T) a ha g hg hc hg₀
  refine ⟨f,tensorT T f,hs,hcs,hneg,hi,?_,tensorT_mem T hs hcs,?_,?_,?_⟩
  · intro y
    change f (archR y)*sieved T y.2 = if y.2∈integralAf ∧ ∀ p∈T,scaled p y.2∉integralAf then f (archR y) else 0
    rw [sieve_value]
    split_ifs <;> simp
  · simp [tensorT,hneg 0 le_rfl]
  · intro ν _;exact integral_tensor f (sieved T) hi ν
  · intro z hu hv hz;apply (lift_orbit ha _ hneg hθ z hu hv hz).congr_fun
    exact fun q => term_eq T z hu hv f q
