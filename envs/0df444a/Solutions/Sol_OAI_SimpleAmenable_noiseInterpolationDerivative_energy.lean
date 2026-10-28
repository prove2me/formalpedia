-- Prove2me | solution 1 for OAI.SimpleAmenable.noiseInterpolationDerivative_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:49:38.784995+00:00
-- url     : https://prove2.me/submissions/73e3550b-b86a-48c9-8324-ee6ee59c87ec

import Mathlib
import Definitions.Def_OAIQ65Sa001
import Definitions.Def_OAIQ65Sa002

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_NoiseTensor
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section NoiseTensor
open Classical MeasureTheory

theorem noiseTensor_inner {ι : Type*} [Fintype ι] (u v : ι → ℝ → ℝ) :
    (∫x : ι → ℝ,noiseTensor u x*noiseTensor v x ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=∏i,∫t : ℝ,u i t*v i t := by
  simp only [noiseTensor,← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i x => u i x*v i x)

theorem noiseTensor_integrable_inner {ι : Type*} [Fintype ι] (u v : ι → ℝ → ℝ)
    (h : ∀i,Integrable (fun t : ℝ => u i t*v i t)) :
    Integrable (fun x : ι → ℝ => noiseTensor u x*noiseTensor v x) (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
  simpa only [noiseTensor,← Finset.prod_mul_distrib] using Integrable.fintype_prod h

theorem noiseTensor_energy {ι : Type*} [Fintype ι] (u : ι → ℝ → ℝ) :
    (∫x : ι → ℝ,noiseTensor u x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=∏i,∫t : ℝ,u i t^2 := by
  simpa only [pow_two] using noiseTensor_inner u u

theorem centeredNoiseTensor_orthogonal {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (s t : Finset ι) (u v : ι → ℝ → ℝ)
    (hu : ∀i∈s,(∫x : ℝ,u i x*f x)=0)
    (hv : ∀i∈t,(∫x : ℝ,v i x*f x)=0) (hne : s≠t) :
    (∫x : ι → ℝ,centeredNoiseTensor f s u x*centeredNoiseTensor f t v x ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=0 := by
  rw [centeredNoiseTensor,centeredNoiseTensor,noiseTensor_inner]
  obtain ⟨i,hi⟩ := not_forall.mp (Finset.ext_iff.not.mp hne)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hs : i∈s
  · have ht : i∉t := by tauto
    simpa only [ite_eq_left hs,ite_eq_right ht] using hu i hs
  · have ht : i∈t := by tauto
    simpa only [ite_eq_right hs,ite_eq_left ht,mul_comm] using hv i ht

theorem centeredNoiseTensor_energy {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (hf : (∫x : ℝ,f x^2)=1) (s : Finset ι) (u : ι → ℝ → ℝ) :
    (∫x : ι → ℝ,centeredNoiseTensor f s u x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=∏i∈s,∫t : ℝ,u i t^2 := by
  rw [centeredNoiseTensor,noiseTensor_energy]
  calc
    _ = ∏i : ι,if i∈s then (∫t : ℝ,u i t^2) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      split_ifs with hi
      · rfl
      · exact hf
    _ = _ := by simp

end NoiseTensor

section NoiseMoments
open Classical MeasureTheory

theorem noiseFactor_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (i : NoiseFactor) :
    Continuous (noiseFactor f i) := by
  have hc := hf.continuous
  have hd := hf.continuous_deriv le_rfl
  cases i <;> dsimp [noiseFactor] <;> fun_prop

theorem noiseFactor_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) (i : NoiseFactor) :
    HasCompactSupport (noiseFactor f i) := by
  cases i
  · exact hf
  · exact hf.deriv
  · exact hf.mul_left
  · have hh : HasCompactSupport (fun x => f x/2) := by
      convert! (hf.mul_right (f':=fun _ => (2:ℝ)⁻¹)) using 1
      all_goals try with_reducible_and_instances rfl
    exact hf.deriv.mul_left.add hh

theorem noiseFactor_integrable_product {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (i j : NoiseFactor) :
    Integrable (fun x => noiseFactor f i x*noiseFactor f j x) :=
  ((noiseFactor_continuous hf i).mul (noiseFactor_continuous hf j)).integrable_of_hasCompactSupport
    (noiseFactor_compact hc i).mul_right

theorem noiseFactor_centered {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (he : Function.Even f) (i : NoiseFactor) (hi : i≠.base) :
    (∫x : ℝ,noiseFactor f i x*f x)=0 := by
  have hd (x : ℝ) : HasDerivAt f (deriv f x) x := (hf.differentiable (by norm_num) x).hasDerivAt
  have hff := noiseFactor_integrable_product hf hc .base .base
  have hfd := noiseFactor_integrable_product hf hc .base .score
  have hdf := noiseFactor_integrable_product hf hc .score .base
  dsimp only [noiseFactor] at hff hfd hdf
  cases i
  · exact (hi rfl).elim
  · have h := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hd x) (fun x _ => hd x) hfd hdf hff
    have heq : (∫x : ℝ,f x*deriv f x)=(∫x : ℝ,deriv f x*f x) := by
      congr 1
      funext x
      ring
    dsimp [noiseFactor] at h ⊢
    linarith
  · have h := integral_neg_eq_self (fun x : ℝ => x*f x*f x) volume
    have heq : (fun x : ℝ => (-x)*f (-x)*f (-x))=(fun x : ℝ => -(x*f x*f x)) := by
      funext x
      rw [he x]
      ring
    change (∫x : ℝ,(-x)*f (-x)*f (-x))=(∫x : ℝ,x*f x*f x) at h
    rw [heq,integral_neg] at h
    dsimp [noiseFactor]
    linarith
  · have hup (x : ℝ) : HasDerivAt (fun x => x*f x) (f x+x*deriv f x) x := by
      convert! (hasDerivAt_id x).mul (hd x) using 1; simp only [one_mul,id_eq]
    have hp := noiseFactor_integrable_product hf hc .position .score
    have hp₀ := noiseFactor_integrable_product hf hc .position .base
    dsimp only [noiseFactor] at hp hp₀
    have hp' : Integrable (fun x : ℝ => (f x+x*deriv f x)*f x) := by
      have hj := noiseFactor_integrable_product hf hc .diagonal .base
      apply (hj.add (hff.div_const 2)).congr
      filter_upwards with x
      dsimp [noiseFactor]
      ring
    have h := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hup x) (fun x _ => hd x) hp hp' hp₀
    let I := ∫x : ℝ,x*f x*deriv f x
    have hright : (∫x : ℝ,(f x+x*deriv f x)*f x)=(∫x : ℝ,f x*f x)+I := by
      have hi : Integrable (fun x : ℝ => x*deriv f x*f x) := by
        apply hp.congr
        filter_upwards with x
        ring
      rw [show (fun x : ℝ => (f x+x*deriv f x)*f x)=
        (fun x : ℝ => f x*f x+x*deriv f x*f x) by ext x; ring,integral_add hff hi]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      ring
    change I=-(∫x : ℝ,(f x+x*deriv f x)*f x) at h
    rw [hright] at h
    have hgoal : (∫x : ℝ,noiseFactor f .diagonal x*f x)=I+(∫x : ℝ,f x*f x)/2 := by
      have hi : Integrable (fun x : ℝ => x*f x*deriv f x) := hp
      have hb : Integrable (fun x : ℝ => (f x*f x)/2) := hff.div_const 2
      rw [show (fun x : ℝ => noiseFactor f .diagonal x*f x)=
        (fun x : ℝ => x*f x*deriv f x+(f x*f x)/2) by ext x; dsimp [noiseFactor]; ring,
        integral_add hi hb,integral_div]
    rw [hgoal]
    linarith

end NoiseMoments

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteOrthogonalEnergy
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteOrthogonalEnergy
open Classical MeasureTheory

theorem integral_finite_energy {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (F : I → X → ℝ)
    (h : ∀i j,Integrable (fun x => F i x*F j x) μ) :
    (∫x,(∑i,F i x)^2 ∂μ)=∑i,∑j,∫x,F i x*F j x ∂μ := by
  simp only [pow_two,Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => h i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => h i j)]

theorem integral_product_le_half_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable (fun x => f x*f x) μ)
    (hg : Integrable (fun x => g x*g x) μ)
    (hfg : Integrable (fun x => f x*g x) μ) :
    (∫x,f x*g x ∂μ)≤((∫x,(f x)^2 ∂μ)+(∫x,(g x)^2 ∂μ))/2 := by
  have hh : Integrable (fun x => f x*f x+g x*g x) μ := hf.add hg
  have hb : Integrable (fun x => 2*(f x*g x)) μ := hfg.const_mul 2
  have hp : 0 ≤ ∫x,f x*f x+g x*g x-2*(f x*g x) ∂μ := by
    apply integral_nonneg
    intro x
    change 0 ≤ f x*f x+g x*g x-2*(f x*g x)
    nlinarith [sq_nonneg (f x-g x)]
  rw [integral_sub hh hb,integral_add hf hg,integral_const_mul] at hp
  simp only [pow_two]
  linarith

theorem finite_overlap_energy {I X S : Type*} [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (F : I → X → ℝ) (s : I → S)
    (h : ∀i j,Integrable (fun x => F i x*F j x) μ)
    (ho : ∀i j,s i≠s j → (∫x,F i x*F j x ∂μ)=0)
    (k : ℕ) (hcard : ∀i,(Finset.univ.filter (fun j => s i=s j)).card≤k) :
    (∫x,(∑i,F i x)^2 ∂μ)≤(k:ℝ)*∑i,∫x,F i x^2 ∂μ := by
  let E := fun i => ∫x,F i x^2 ∂μ
  have hE (i : I) : 0≤E i := integral_nonneg (fun _ => sq_nonneg _)
  have hc (i : I) : (∑j,if s i=s j then E i else 0)≤(k:ℝ)*E i := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard i) (hE i)
  have hsum : (∑i,∑j,if s i=s j then E i else 0)≤(k:ℝ)*∑i,E i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hc i)
  have hswap : (∑i,∑j,if s i=s j then E j else 0)=(∑i,∑j,if s i=s j then E i else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [eq_comm]
  rw [integral_finite_energy μ F h]
  calc
    _ ≤ ∑i,∑j,((if s i=s j then E i else 0)+(if s i=s j then E j else 0))/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hij
      · exact integral_product_le_half_energy μ (F i) (F j) (h i i) (h j j) (h i j)
      · rw [ho i j hij]
        norm_num
    _ = ((∑i,∑j,if s i=s j then E i else 0)+(∑i,∑j,if s i=s j then E j else 0))/2 := by
      simp only [← Finset.sum_div,Finset.sum_add_distrib]
    _ ≤ (k:ℝ)*∑i,E i := by rw [hswap]; linarith

end FiniteOrthogonalEnergy

section NoiseCenteredEnergy
open Classical MeasureTheory

theorem noiseEnergy_nonneg (f : ℝ → ℝ) (i : NoiseFactor) : 0≤noiseEnergy f i :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem noise_centered_energy {ι I : Type*} [Fintype ι] [Fintype I]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (he : Function.Even f)
    (hn : (∫x : ℝ,f x^2)=1) (s : I → Finset ι) (p : I → ι → NoiseFactor) (c : I → ℝ)
    (hp : ∀i j,j∈s i → p i j≠.base)
    (k : ℕ) (hcard : ∀i,(Finset.univ.filter (fun j => s i=s j)).card≤k) :
    (∫x : ι → ℝ,(∑i,c i*centeredNoiseTensor f (s i) (fun j => noiseFactor f (p i j)) x)^2
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ)))) ≤
        (k:ℝ)*∑i,c i^2*∏j∈s i,noiseEnergy f (p i j) := by
  let T := fun i => centeredNoiseTensor f (s i) (fun j => noiseFactor f (p i j))
  have hT (i j : I) : Integrable (fun x : ι → ℝ => T i x*T j x)
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
    apply noiseTensor_integrable_inner
    intro l
    split_ifs
    · exact noiseFactor_integrable_product hf hc _ _
    · exact noiseFactor_integrable_product hf hc (p i l) .base
    · exact noiseFactor_integrable_product hf hc .base (p j l)
    · exact noiseFactor_integrable_product hf hc .base .base
  have hF (i j : I) : Integrable (fun x : ι → ℝ => (c i*T i x)*(c j*T j x))
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
    apply ((hT i j).const_mul (c i*c j)).congr
    filter_upwards with x
    ring
  have ho (i j : I) (hne : s i≠s j) :
      (∫x : ι → ℝ,(c i*T i x)*(c j*T j x) ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))=0 := by
    have hh := centeredNoiseTensor_orthogonal f (s i) (s j)
      (fun l => noiseFactor f (p i l)) (fun l => noiseFactor f (p j l))
      (fun l hl => noiseFactor_centered hf hc he _ (hp i l hl))
      (fun l hl => noiseFactor_centered hf hc he _ (hp j l hl)) hne
    rw [show (fun x : ι → ℝ => (c i*T i x)*(c j*T j x))=
      (fun x : ι → ℝ => (c i*c j)*(T i x*T j x)) by ext x; ring,
      integral_const_mul,hh,mul_zero]
  have hbound := finite_overlap_energy (Measure.pi (fun _ : ι => (volume : Measure ℝ)))
    (fun i x => c i*T i x) s hF ho k (by convert! hcard)
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show (fun x : ι → ℝ => (c i*T i x)^2)=
    (fun x : ι → ℝ => c i^2*(T i x)^2) by ext x; ring,integral_const_mul]
  rw [centeredNoiseTensor_energy f hn]
  rfl

theorem singletonNoise_energy_bound {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (he : Function.Even f)
    (hn : (∫x : ℝ,f x^2)=1) (q : NoiseFactor) (hq : q≠.base) (c : ι → ℝ) :
    (∫x : ι → ℝ,(∑i,c i*singletonNoise f q i x)^2
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))≤
        noiseEnergy f q*∑i,c i^2 := by
  have h := noise_centered_energy hf hc he hn (fun i : ι => {i}) (fun _ _ => q) c
    (fun _ _ _ => hq) 1 (by
      intro i
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact Finset.singleton_inj.mp (ha'.symm.trans hb'))
  simpa only [singletonNoise,Finset.prod_singleton,Nat.cast_one,one_mul,Finset.mul_sum,mul_comm] using h

theorem noisePair_card {ι : Type*} [Fintype ι] (p : NoisePair ι) :
    (Finset.univ.filter (fun q : NoisePair ι => ({p.val.1,p.val.2} : Finset ι)={q.val.1,q.val.2})).card≤2 := by
  have hsub : Finset.univ.filter (fun q : NoisePair ι => ({p.val.1,p.val.2} : Finset ι)={q.val.1,q.val.2})
      ⊆ {p,noisePairSwap p} := by
    intro q hq
    have he := (Finset.mem_filter.mp hq).2
    have h₁ : p.val.1=q.val.1 ∨ p.val.1=q.val.2 := by
      have hh : p.val.1∈({q.val.1,q.val.2} : Finset ι) := by rw [← he]; simp
      simpa using hh
    have h₂ : p.val.2=q.val.1 ∨ p.val.2=q.val.2 := by
      have hh : p.val.2∈({q.val.1,q.val.2} : Finset ι) := by rw [← he]; simp
      simpa using hh
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact (p.property (h₁.trans h₂.symm)).elim
    · have hqp : q=p := Subtype.ext (Prod.ext h₁.symm h₂.symm)
      simp [hqp]
    · have hqp : q=noisePairSwap p := Subtype.ext (Prod.ext h₂.symm h₁.symm)
      simp [hqp]
    · exact (p.property (h₁.trans h₂.symm)).elim
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem pairNoise_energy_bound {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (he : Function.Even f)
    (hn : (∫x : ℝ,f x^2)=1) (c : NoisePair ι → ℝ) :
    (∫x : ι → ℝ,(∑i,c i*pairNoise f i x)^2
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))≤
        2*(noiseEnergy f .score*noiseEnergy f .position)*∑i,c i^2 := by
  have h := noise_centered_energy hf hc he hn (fun p : NoisePair ι => {p.val.1,p.val.2})
    (fun p i => if i=p.val.1 then .score else .position) c
    (by intro i j _; split_ifs <;> decide) 2 noisePair_card
  have he (p : NoisePair ι) :
      (∏j∈({p.val.1,p.val.2} : Finset ι),noiseEnergy f (if j=p.val.1 then .score else .position))=
        noiseEnergy f .score*noiseEnergy f .position := by
    rw [Finset.prod_pair p.property]
    simp only [ite_true,ite_eq_right (Ne.symm p.property)]
  simp_rw [he] at h
  simpa only [pairNoise,Nat.cast_ofNat,← Finset.sum_mul,mul_assoc,mul_comm,mul_left_comm] using h

end NoiseCenteredEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AffineNoiseEnergy
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AffineNoiseEnergy
open Classical MeasureTheory

theorem noise_centered_integrable_product {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (s t : Finset ι) (p q : ι → NoiseFactor) :
    Integrable (fun x : ι → ℝ =>
      centeredNoiseTensor f s (fun i => noiseFactor f (p i)) x*
      centeredNoiseTensor f t (fun i => noiseFactor f (q i)) x)
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
  apply noiseTensor_integrable_inner
  intro i
  split_ifs
  · exact noiseFactor_integrable_product hf hc _ _
  · exact noiseFactor_integrable_product hf hc (p i) .base
  · exact noiseFactor_integrable_product hf hc .base (q i)
  · exact noiseFactor_integrable_product hf hc .base .base

theorem integrable_sum_product {I J X : Type*} [Fintype I] [Fintype J] [MeasurableSpace X]
    (μ : Measure X) (f : I → X → ℝ) (g : J → X → ℝ)
    (h : ∀i j,Integrable (fun x => f i x*g j x) μ) :
    Integrable (fun x => (∑i,f i x)*(∑j,g j x)) μ := by
  simp only [Finset.sum_mul_sum]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => h i j))

theorem integrable_three_energy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a b c : X → ℝ) (h : ∀u∈({a,b,c} : Finset (X → ℝ)),
      ∀v∈({a,b,c} : Finset (X → ℝ)),Integrable (fun x => u x*v x) μ) :
    (∫x,(a x+b x+c x)^2 ∂μ)≤
      3*((∫x,a x^2 ∂μ)+(∫x,b x^2 ∂μ)+(∫x,c x^2 ∂μ)) := by
  have haa := h a (by simp) a (by simp)
  have hbb := h b (by simp) b (by simp)
  have hcc := h c (by simp) c (by simp)
  have hab := h a (by simp) b (by simp)
  have hac := h a (by simp) c (by simp)
  have hbc := h b (by simp) c (by simp)
  have hleft : Integrable (fun x => (a x+b x+c x)^2) μ := by
    apply ((((haa.add hbb).add hcc).add (hab.const_mul 2)).add
      ((hac.const_mul 2).add (hbc.const_mul 2))).congr
    filter_upwards with x
    dsimp only [Pi.add_apply]
    ring
  have hright : Integrable (fun x => 3*(a x^2+b x^2+c x^2)) μ := by
    convert! ((haa.add hbb).add hcc).const_mul 3 using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.add_apply,pow_two]
  have hh := integral_mono hleft hright (fun x => by
    nlinarith [sq_nonneg (a x-b x),sq_nonneg (b x-c x),sq_nonneg (a x-c x)])
  rwa [integral_const_mul,integral_add (by convert! haa.add hbb using 1; ext x; simp only [Pi.add_apply,pow_two])
    (by convert! hcc using 1; ext x; simp only [pow_two]),integral_add
    (by convert! haa using 1; ext x; simp only [pow_two]) (by convert! hbb using 1; ext x; simp only [pow_two])] at hh

theorem affineNoiseEnergyConstant_nonneg (f : ℝ → ℝ) : 0≤affineNoiseEnergyConstant f := by
  unfold affineNoiseEnergyConstant
  have := noiseEnergy_nonneg f .diagonal
  have := noiseEnergy_nonneg f .score
  have := noiseEnergy_nonneg f .position
  positivity

theorem noise_sum_integrable_product {ι I J : Type*} [Fintype ι] [Fintype I] [Fintype J]
  {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (s : I → Finset ι) (t : J → Finset ι) (p : I → ι → NoiseFactor)
    (q : J → ι → NoiseFactor) (u : I → ℝ) (w : J → ℝ) :
    Integrable (fun x : ι → ℝ =>
      (∑i,u i*centeredNoiseTensor f (s i) (fun j => noiseFactor f (p i j)) x)*
      (∑i,w i*centeredNoiseTensor f (t i) (fun j => noiseFactor f (q i j)) x))
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
  apply integrable_sum_product
  intro i j
  apply ((noise_centered_integrable_product hf hc (s i) (t j) (p i) (q j)).const_mul (u i*w j)).congr
  filter_upwards with x
  ring

theorem affineNoiseGenerator_energy {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (he : Function.Even f)
    (hn : (∫x : ℝ,f x^2)=1) (L : Matrix ι ι ℝ) (v : ι → ℝ) :
    (∫x : ι → ℝ,affineNoiseGenerator f L v x^2
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))≤
        affineNoiseEnergyConstant f*((∑i,∑j,L i j^2)+∑i,v i^2) := by
  let a : (ι → ℝ) → ℝ := fun x => ∑i,L i i*singletonNoise f .diagonal i x
  let b : (ι → ℝ) → ℝ := fun x => ∑i,v i*singletonNoise f .score i x
  let c : (ι → ℝ) → ℝ := fun x => ∑p : NoisePair ι,L p.val.1 p.val.2*pairNoise f p x
  have habc : ∀u∈({a,b,c} : Finset ((ι → ℝ) → ℝ)),
      ∀w∈({a,b,c} : Finset ((ι → ℝ) → ℝ)),Integrable (fun x => u x*w x)
        (Measure.pi (fun _ : ι => (volume : Measure ℝ))) := by
    intro u hu w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hw
    rcases hu with rfl|rfl|rfl <;> rcases hw with rfl|rfl|rfl <;>
      dsimp only [a,b,c,singletonNoise,pairNoise] <;> apply noise_sum_integrable_product hf hc
  have H := integrable_three_energy (Measure.pi (fun _ : ι => (volume : Measure ℝ))) a b c habc
  have ha := singletonNoise_energy_bound hf hc he hn .diagonal (by decide) (fun i => L i i)
  have hb := singletonNoise_energy_bound hf hc he hn .score (by decide) v
  have hc' := pairNoise_energy_bound hf hc he hn (fun p : NoisePair ι => L p.val.1 p.val.2)
  let M := ∑i,∑j,L i j^2
  let V := ∑i,v i^2
  have hM : 0≤M := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hV : 0≤V := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdiag : (∑i,L i i^2)≤M := Finset.sum_le_sum (fun i _ =>
    Finset.single_le_sum (fun j _ => sq_nonneg (L i j)) (Finset.mem_univ i))
  have hoff : (∑p : NoisePair ι,L p.val.1 p.val.2^2)≤M := by
    change (∑p : {p : ι×ι // p.1≠p.2},L p.val.1 p.val.2^2)≤M
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : ι×ι => p.1≠p.2)) (by simp) (fun p : ι×ι => L p.1 p.2^2),Finset.sum_filter]
    calc
      _ ≤ ∑p : ι×ι,L p.1 p.2^2 := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs
        · exact le_rfl
        · exact sq_nonneg _
      _ = M := by simp only [Fintype.sum_prod_type,M]
  have hD := noiseEnergy_nonneg f .diagonal
  have hS := noiseEnergy_nonneg f .score
  have hP := noiseEnergy_nonneg f .position
  have hSP : 0≤2*(noiseEnergy f .score*noiseEnergy f .position) := by positivity
  have ha' := ha.trans (mul_le_mul_of_nonneg_left hdiag hD)
  have hc'' := hc'.trans (mul_le_mul_of_nonneg_left hoff hSP)
  change (∫x : ι → ℝ,(a x+b x+c x)^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))≤_
  apply H.trans
  have hs : (∫x,a x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))+
      (∫x,b x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))+
      (∫x,c x^2 ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))))≤
      noiseEnergy f .diagonal*M+noiseEnergy f .score*V+2*(noiseEnergy f .score*noiseEnergy f .position)*M :=
    add_le_add (add_le_add ha' hb) hc''
  unfold affineNoiseEnergyConstant
  change 3*_≤3*_*(M+V)
  nlinarith [mul_nonneg hD hV,mul_nonneg hS hM,mul_nonneg hSP hV]

end AffineNoiseEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_MatrixInverseCalculus
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section AffineVolume
open Classical Matrix MeasureTheory
open scoped ENNReal

theorem matrixAffineEquiv_apply {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a x : ι → ℝ) (hA : IsUnit A.det) :
    matrixAffineEquiv A a hA x=a+A*ᵥx := by
  change a+Matrix.toLin (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι) A x=_
  rw [Matrix.toLin_eq_toLin',Matrix.toLin'_apply]

theorem map_matrix_affine_volume {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) :
    Measure.map (fun x => a+A*ᵥx) (volume : Measure (ι → ℝ))=
      ENNReal.ofReal |A.det⁻¹| • volume := by
  change Measure.map ((fun y => a+y) ∘ (Matrix.toLin' A)) volume=_
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    Real.map_matrix_volume_pi_eq_smul_volume_pi hA.ne_zero,
    Measure.map_smul,map_add_left_eq_self]

theorem integral_matrix_affine {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) (f : (ι → ℝ) → ℝ) :
    (∫x,f (a+A*ᵥx))=|A.det⁻¹| *(∫y,f y) := by
  have h := integral_map_equiv (μ := (volume : Measure (ι → ℝ)))
    (matrixAffineEquiv A a hA) f
  rw [show (matrixAffineEquiv A a hA : (ι → ℝ) → (ι → ℝ))=
    (fun x => a+A*ᵥx) from funext (fun x => matrixAffineEquiv_apply A a x hA),map_matrix_affine_volume A a hA,
    integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul] at h
  exact h.symm

theorem integral_matrix_affine_inverse {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) (f : (ι → ℝ) → ℝ) :
    (∫y,f (A⁻¹*ᵥ(y-a)))=|A.det| *(∫x,f x) := by
  have h := integral_matrix_affine A⁻¹ (-(A⁻¹*ᵥa))
    (isUnit_iff_ne_zero.mpr (by rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]; exact inv_ne_zero hA.ne_zero)) f
  convert! h using 1
  · congr 1
    ext y
    rw [Matrix.mulVec_sub]
    simp only [sub_eq_add_neg,add_comm]
  · rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,inv_inv]

end AffineVolume

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PolygonApproxIdentity
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FiniteResolvent
open Classical Matrix

theorem finiteL2Norm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ finiteL2Norm x := norm_nonneg _

theorem finiteL2Norm_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    finiteL2Norm x^2=∑i,x i^2 := by
  simp [finiteL2Norm,PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs]

theorem finiteL2Norm_sub {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    finiteL2Norm (x-y) ≤ finiteL2Norm x+finiteL2Norm y := by
  simpa only [finiteL2Norm,WithLp.toLp_sub] using norm_sub_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

theorem finiteL2Norm_smul {ι : Type*} [Fintype ι] (c : ℝ) (x : ι → ℝ) :
    finiteL2Norm (c • x)=|c| * finiteL2Norm x := by
  simp only [finiteL2Norm,WithLp.toLp_smul,norm_smul,Real.norm_eq_abs]

theorem finiteL2Norm_one_add_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (x : ι → ℝ) :
    finiteL2Norm x ≤ finiteL2Norm ((1+B)*ᵥx) := by
  let y := (1+B)*ᵥx
  let S := ∑i,x i^2
  let T := ∑i,y i^2
  let P := ∑i,x i*y i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hp : 0 ≤ ∑i,x i*(B*ᵥx) i := by
    simpa only [dotProduct,star_trivial] using hB.dotProduct_mulVec_nonneg x
  have he : P=S+(∑i,x i*(B*ᵥx) i) := by
    simp only [P,S,y,Matrix.add_mulVec,Matrix.one_mulVec,Pi.add_apply,mul_add,Finset.sum_add_distrib,pow_two]
  have hSP : S ≤ P := by linarith
  have hP : 0 ≤ P := hS.trans hSP
  have hcs : P^2 ≤ S*T := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hST : S ≤ T := by
    by_cases h : S=0
    · simpa only [h] using hT
    · have hS' : 0<S := lt_of_le_of_ne hS (Ne.symm h)
      have hsq := pow_le_pow_left₀ hS hSP 2
      nlinarith
  apply (sq_le_sq₀ (finiteL2Norm_nonneg _) (finiteL2Norm_nonneg _)).mp
  simpa only [finiteL2Norm_sq] using hST

theorem one_add_psd_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) : IsUnit (1+B).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.PosDef.one.add_posSemidef hB).isUnit

theorem finiteL2Norm_inverse_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (x : ι → ℝ) :
    finiteL2Norm ((1+B)⁻¹*ᵥx) ≤ finiteL2Norm x := by
  have hh := finiteL2Norm_one_add_le B hB ((1+B)⁻¹*ᵥx)
  rwa [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (one_add_psd_isUnit_det B hB),Matrix.one_mulVec] at hh

end FiniteResolvent

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_NoiseContinuity
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section CovarianceResolvent
open Classical Matrix

theorem matrixHSNorm_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    0≤ matrixHSNorm A := Real.sqrt_nonneg _

theorem matrixHSNorm_sq {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    matrixHSNorm A^2=∑i,∑j,A i j^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j))))

theorem finiteL2Norm_matrix_mulVec {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    finiteL2Norm (A*ᵥx)≤ matrixHSNorm A*finiteL2Norm x := by
  apply (sq_le_sq₀ (finiteL2Norm_nonneg _) (mul_nonneg (matrixHSNorm_nonneg _) (finiteL2Norm_nonneg _))).mp
  rw [mul_pow,matrixHSNorm_sq,finiteL2Norm_sq,finiteL2Norm_sq,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) x

theorem matrixHSNorm_inverse_contraction {ι : Type*} [Fintype ι]
    (B D : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    matrixHSNorm ((1+B)⁻¹*D)≤ matrixHSNorm D := by
  apply (sq_le_sq₀ (matrixHSNorm_nonneg _) (matrixHSNorm_nonneg _)).mp
  rw [matrixHSNorm_sq,matrixHSNorm_sq,Finset.sum_comm,Finset.sum_comm (f:=fun i j => D i j^2)]
  apply Finset.sum_le_sum
  intro j _
  have h := pow_le_pow_left₀ (finiteL2Norm_nonneg _) (finiteL2Norm_inverse_contraction B hB (fun i => D i j)) 2
  simpa only [finiteL2Norm_sq,Matrix.mul_apply,Matrix.mulVec,dotProduct] using h

theorem covarianceSegment_posSemidef {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) : (covarianceSegment B C t).PosSemidef :=
  (hB.smul (sub_nonneg.mpr ht.2)).add (hC.smul ht.1)

theorem covarianceSegment_affine {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (t : ℝ) : 1+covarianceSegment B C t=(1+B)+t • (C-B) := by
  unfold covarianceSegment
  module

theorem covarianceSegment_inverse_signal {ι : Type*} [Fintype ι]
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (h : ι → ℝ) {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) :
    finiteL2Norm ((1+covarianceSegment B C t)⁻¹*ᵥh)≤
      (1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh) := by
  let P := covarianceSegment B C t
  let x := (1+B)⁻¹*ᵥh
  let y := (1+P)⁻¹*ᵥ((C-B)*ᵥx)
  have hP := covarianceSegment_posSemidef B C hB hC ht
  have hx : (1+B)*ᵥx=h := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (one_add_psd_isUnit_det B hB),Matrix.one_mulVec]
  have he : (1+P)*ᵥx=h+t • ((C-B)*ᵥx) := by
    rw [show 1+P=(1+B)+t • (C-B) from covarianceSegment_affine B C t,
      Matrix.add_mulVec,Matrix.smul_mulVec,hx]
  have hi := congrArg (fun v => (1+P)⁻¹*ᵥv) he
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (one_add_psd_isUnit_det P hP),
    Matrix.one_mulVec,Matrix.mulVec_add,Matrix.mulVec_smul] at hi
  have hv : (1+P)⁻¹*ᵥh=x-t • y := by
    exact eq_sub_of_add_eq (Eq.symm hi)
  rw [hv]
  calc
    _ ≤ finiteL2Norm x+finiteL2Norm (t • y) := finiteL2Norm_sub _ _
    _ = finiteL2Norm x+t*finiteL2Norm y := by rw [finiteL2Norm_smul,abs_of_nonneg ht.1]
    _ ≤ finiteL2Norm x+finiteL2Norm y := by
      exact add_le_add le_rfl (mul_le_of_le_one_left (finiteL2Norm_nonneg y) ht.2)
    _ ≤ finiteL2Norm x+matrixHSNorm (C-B)*finiteL2Norm x := by
      apply add_le_add le_rfl
      exact (finiteL2Norm_inverse_contraction P hP _).trans (finiteL2Norm_matrix_mulVec _ _)
    _ = _ := by ring

end CovarianceResolvent

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AffineGeneratorIntegrability
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section NoiseInterpolation
open Classical Matrix MeasureTheory Set
open scoped Matrix.Norms.Elementwise

theorem noiseInterpolationDerivative_energy_oai {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hn : (∫x : ℝ,f x^2)=1) (he : Function.Even f)
    (B C : Matrix ι ι ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef) (a h : ι → ℝ)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (∫y : ι → ℝ,noiseInterpolationDerivative f B C a h t y^2)≤
      affineNoiseEnergyConstant f*(matrixHSNorm (C-B)^2+
        ((1+matrixHSNorm (C-B))*finiteL2Norm ((1+B)⁻¹*ᵥh))^2) := by
  let P := covarianceSegment B C t
  have hP := covarianceSegment_posSemidef B C hB hC ht
  have hp := (Matrix.PosDef.one.add_posSemidef hP).det_pos
  have hd : (∫y : ι → ℝ,noiseInterpolationDerivative f B C a h t y^2)≤
      affineNoiseEnergyConstant f*(matrixHSNorm ((1+P)⁻¹*(C-B))^2+
        finiteL2Norm ((1+P)⁻¹*ᵥh)^2) := by
    simp only [noiseInterpolationDerivative,div_pow,neg_sq,Real.sq_sqrt hp.le]
    rw [integral_div,integral_matrix_affine_inverse (1+covarianceSegment B C t) (a+t • h)
      (isUnit_iff_ne_zero.mpr hp.ne')
      (fun x => affineNoiseGenerator f ((1+covarianceSegment B C t)⁻¹*(C-B))
        ((1+covarianceSegment B C t)⁻¹*ᵥh) x^2),abs_of_pos hp,mul_div_cancel_left₀ _ hp.ne']
    rw [matrixHSNorm_sq,finiteL2Norm_sq]
    convert! affineNoiseGenerator_energy hf hc he hn ((1+P)⁻¹*(C-B)) ((1+P)⁻¹*ᵥh) using 1
    all_goals try with_reducible_and_instances rfl
  apply hd.trans
  apply mul_le_mul_of_nonneg_left _ (affineNoiseEnergyConstant_nonneg f)
  exact add_le_add
    (pow_le_pow_left₀ (matrixHSNorm_nonneg _) (matrixHSNorm_inverse_contraction P (C-B) hP) 2)
    (pow_le_pow_left₀ (finiteL2Norm_nonneg _) (covarianceSegment_inverse_signal B C hB hC h ht) 2)

end NoiseInterpolation

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SimpleAmenable.noiseInterpolationDerivative_energy_oai.{u_1} := @OAI.SimpleAmenable.noiseInterpolationDerivative_energy_oai.{u_1}
