-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.nearCut_old_positive_seed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:14.74433+00:00
-- url     : https://prove2.me/submissions/667ce6ac-3162-4e59-996c-15f28c0e0e6f

import Mathlib
import Definitions.Def_OAIQ368Chrom009
import Definitions.Def_OAIQ368Chrom011
import Definitions.Def_OAIQ368Chrom012

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInverse
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma inverse_mul (F G : PowerSeries A) (hF : constantCoeff F=1) (hG : constantCoeff G=1) :
    invOfUnit (F*G) 1=invOfUnit G 1*invOfUnit F 1 := by
  have hh : F*G*(invOfUnit G 1*invOfUnit F 1)=1:=by
    calc
      _=F*(G*invOfUnit G 1)*invOfUnit F 1:=by simp only [mul_assoc]
      _=1:=by rw [mul_invOfUnit G 1 hG,mul_one,mul_invOfUnit F 1 hF]
  calc
    _=invOfUnit (F*G) 1*(F*G*(invOfUnit G 1*invOfUnit F 1)):=by rw [hh,mul_one]
    _=(invOfUnit (F*G) 1*(F*G))*(invOfUnit G 1*invOfUnit F 1):=by simp only [mul_assoc]
    _=invOfUnit G 1*invOfUnit F 1:=by rw [invOfUnit_mul _ 1 (by simp [hF,hG]),one_mul]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries

section Field
variable {K : Type*} [Field K]

theorem rescale_inv_of_const_one (a : K) (F : PowerSeries K)
    (hF : PowerSeries.constantCoeff F = 1) :
    PowerSeries.rescale a F⁻¹ = (PowerSeries.rescale a F)⁻¹ := by
  have hR : PowerSeries.constantCoeff (PowerSeries.rescale a F) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
      pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff, hF]
    exact one_ne_zero
  apply (PowerSeries.eq_inv_iff_mul_eq_one hR).2
  rw [← map_mul, PowerSeries.inv_mul_cancel F (by simp [hF]), map_one]

end Field

end ElementaryPositivity.WallUnits
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ChartRefinement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
theorem chart_negative_refinement (h k H : M→+ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hsign : ∀n≤N,∀m,HasRootDegree C n m→LexSigns h k H m) :
    ∀n≤N,coeff n (chartNegative v Ω C H F).val=
      coeff n ((chartNegative v Ω C k (chartZero v Ω C h F)).val *
        (chartNegative v Ω C h F).val) :=by
  let A:=chartPositive v Ω C h F
  let B:=chartZero v Ω C h F
  let D:=chartNegative v Ω C h F
  let A0:=chartPositive v Ω C k B
  let B0:=chartZero v Ω C k B
  let D0:=chartNegative v Ω C k B
  have hfact : (A.val*A0.val)*B0.val*(D0.val*D.val)=F.val :=by
    calc
      _=A.val*(A0.val*B0.val*D0.val)*D.val:=by simp only [mul_assoc]
      _=A.val*B.val*D.val:=by rw [chart_three_factorization v Ω C k B]
      _=F.val:=chart_three_factorization v Ω C h F
  have hs:=chart_three_support v Ω C h F
  have hs0:=chart_three_support v Ω C k B
  have hker:=chartThree_supported v Ω C k h.ker.toAddSubmonoid B
    (chartZero_supported_kernel v Ω C h F)
  have hA : ∀n,n+1≤N→SupportedOn v Ω (fun m=>0<H m) (coeff (n+1) A.val):=by
    intro n hn m hm
    by_contra hx
    exact hm ((hsign _ hn m (chart_root_of_ne v Ω C A _ m hx)).1 (hs.1 n m hx))
  have hA0 : ∀n,n+1≤N→SupportedOn v Ω (fun m=>0<H m) (coeff (n+1) A0.val):=by
    intro n hn m hm
    by_contra hx
    have hz : h m=0:=by by_contra hh; exact hx (hker.1 (n+1) m hh)
    exact hm (((hsign _ hn m (chart_root_of_ne v Ω C A0 _ m hx)).2.2 hz).1 (hs0.1 n m hx))
  have hD : ∀n,n+1≤N→SupportedOn v Ω (fun m=>H m<0) (coeff (n+1) D.val):=by
    intro n hn m hm
    by_contra hx
    exact hm ((hsign _ hn m (chart_root_of_ne v Ω C D _ m hx)).2.1 (hs.2.2 n m hx))
  have hD0 : ∀n,n+1≤N→SupportedOn v Ω (fun m=>H m<0) (coeff (n+1) D0.val):=by
    intro n hn m hm
    by_contra hx
    have hz : h m=0:=by by_contra hh; exact hx (hker.2.2 (n+1) m hh)
    exact hm (((hsign _ hn m (chart_root_of_ne v Ω C D0 _ m hx)).2.2 hz).2.2 (hs0.2.2 n m hx))
  have hB0 : ∀n,n+1≤N→∀m,coeff (n+1) B0.val m≠0→H m=0:=by
    intro n hn m hm
    have hz : h m=0:=by by_contra hh; exact hm (hker.2.1 (n+1) m hh)
    exact ((hsign _ hn m (chart_root_of_ne v Ω C B0 _ m hm)).2.2 hz).2.1 (hs0.2.1 n m hm)
  have hAA:=strict_mul_through v Ω (fun m=>0<H m)
    (fun a b ha hb=>by rw [map_add]; linarith) A.val A0.val N A.property.1 A0.property.1 hA hA0
  have hDD:=strict_mul_through v Ω (fun m=>H m<0)
    (fun a b ha hb=>by rw [map_add]; linarith) D0.val D.val N D0.property.1 D.property.1 hD0 hD
  have hu:=chart_three_truncated_unique v Ω C H F (A.val*A0.val) B0.val (D0.val*D.val) N
    (by simp [A.property.1,A0.property.1]) B0.property.1
    (by simp [D0.property.1,D.property.1]) hfact
    (fun n hn m hm=>by by_contra hh; exact hm (hAA n hn m hh)) hB0
    (fun n hn m hm=>by by_contra hh; exact hm (hDD n hn m hh))
  exact fun n hn=>(hu n hn).2.2.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteSignCharts
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
omit [Algebra ℚ R] in
lemma RayGeneric.ray_supported {N : ℕ} {r : M} {h : M →+ ℝ}
    (H : RayGeneric C N r h) (F : CompletedPositive v Ω C) :
    ∀n,0 < n → n ≤ N → SupportedOn v Ω (OnPositiveRay r)
      (coeff n (chartZero v Ω C h F).val) := by
  intro n hn hN m hm
  by_contra hx
  have hr:=chart_root_of_ne v Ω C _ _ m hx
  cases n with
  | zero => omega
  | succ n => exact hm (H.2 (n+1) hn hN m hr ((chart_three_support v Ω C h F).2.1 n m hx))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalPureCocycle
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RationalFiber.pureAction_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open WallUnits PowerSeries
noncomputable section
variable {K : Type*} [Field K]
variable (v : Kˣ)
lemma shiftedElementary_zero : shiftedElementary v 0=
    elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K) := by
  simp [shiftedElementary]
lemma shiftedElementary_step
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    shiftedElementary v t=(1+C (↑(v^(-2*t-1)):K)*X)*shiftedElementary v (t+1) := by
  conv_lhs => rw [shiftedElementary,elementary_tail _ _ hq]
  rw [_root_.map_mul,_root_.map_add,_root_.map_one,_root_.map_mul,rescale_C,rescale_X,rescale_rescale]
  rw [←mul_assoc,←(PowerSeries.C (R:=K)).map_mul,←Units.val_mul,←zpow_neg_one,←zpow_add]
  have H1 : -1+(-2*t)= -2*t-1:=by ring
  rw [H1]
  unfold shiftedElementary
  simp only [zpow_neg_one]
  congr 2
  rw [←Units.val_mul,←zpow_add]
  congr 2
  ring_nf
lemma expandedPure_step (t : ℤ) :
    expandZero (pureRatio v (t+1):RatFunc K)=
      expandZero (pureRatio v t:RatFunc K)*
        HahnSeries.ofPowerSeries ℤ K (1+C (↑(v^(-2*t-1)):K)*X) := by
  rw [pureRatio_add,Units.val_mul,pureRatio_one,scaleAction_val]
  change expandZero ((pureRatio v t:RatFunc K)*
    scale (v^(-2*t)) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X))=_
  rw [_root_.map_add,_root_.map_one,_root_.map_mul,_root_.map_mul,scale_constant,scale_X,
    ←mul_assoc,←RatFunc.C.map_mul,←Units.val_mul,←zpow_neg_one,←zpow_add]
  rw [show -1+(-2*t)= -2*t-1 by ring]
  simp only [_root_.map_mul,_root_.map_add,_root_.map_one,expandZero_constant,
    expandZero_X,HahnSeries.ofPowerSeries_C,HahnSeries.ofPowerSeries_X]
lemma expandedPure_times_shift
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    expandZero (pureRatio v t:RatFunc K)*
      HahnSeries.ofPowerSeries ℤ K (shiftedElementary v t)=
        HahnSeries.ofPowerSeries ℤ K (shiftedElementary v 0) := by
  induction t using Int.induction_on with
  | zero=>simp
  | succ t ih=>
    rw [expandedPure_step,mul_assoc,←_root_.map_mul,←shiftedElementary_step v hq]
    exact ih
  | pred t ih=>
    rw [shiftedElementary_step v hq (-↑t-1)]
    have H : (-↑t-1)+(1:ℤ)= -↑t:=by ring
    rw [H,_root_.map_mul,←mul_assoc,←expandedPure_step,H]
    exact ih
lemma ofPowerSeries_inv_constant_one (f : PowerSeries K) (hf : constantCoeff f=1) :
    HahnSeries.ofPowerSeries ℤ K f⁻¹=(HahnSeries.ofPowerSeries ℤ K f)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←_root_.map_mul,PowerSeries.inv_mul_cancel f (by rw [hf]; exact one_ne_zero),_root_.map_one]
lemma expandedPure_ratio
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    expandZero (pureRatio v t:RatFunc K)=HahnSeries.ofPowerSeries ℤ K
      (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K)*(shiftedElementary v t)⁻¹) := by
  have H:=expandedPure_times_shift v hq t
  have H0 : HahnSeries.ofPowerSeries ℤ K (shiftedElementary v t)≠0 := by
    intro h
    have he:shiftedElementary v t=0:=HahnSeries.ofPowerSeries_injective (Γ:=ℤ)
      (by simpa only [_root_.map_zero] using h)
    have hc:=congrArg constantCoeff he
    rw [shiftedElementary_constant,_root_.map_zero] at hc
    exact one_ne_zero hc
  rw [shiftedElementary_zero] at H
  rw [_root_.map_mul,ofPowerSeries_inv_constant_one _ (shiftedElementary_constant v t)]
  calc
    _ = (expandZero (pureRatio v t:RatFunc K)*
      HahnSeries.ofPowerSeries ℤ K (shiftedElementary v t))*
        (HahnSeries.ofPowerSeries ℤ K (shiftedElementary v t))⁻¹ := by
      rw [mul_assoc,mul_inv_cancel₀ H0,mul_one]
    _ = _ := by rw [H]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalCenteredAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits Polynomial
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)

variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
include hΩ in
lemma complement_pairing (m : M) : complementAlpha k p Ω (off k p hp m)=Ω p m := by
  change Ω p (m-k m • p)=_
  rw [map_sub,map_zsmul,hΩ,smul_zero,sub_zero]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_RationalTorusFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gaugeAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gauge_monomial _root_.OAI.ElementaryPositivity.RationalFiber.pureAction_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
lemma expand_centeredScalar (n a : ℤ) (b : K) :
    expandZero (RatFunc.C b*centeredScalar v n a)=
      HahnSeries.single n (b*(↑(v^(-n*a)):K)) := by
  rw [centeredScalar,←mul_assoc,←map_mul,map_mul,expandZero_constant,expandZero_X_zpow]
  simp [HahnSeries.C]

lemma split_injective {m n : M} (hk : k m=k n) (ho : off k p hp m=off k p hp n) : m=n := by
  rw [←split_sum k p hp m,←split_sum k p hp n,hk,ho]
lemma readFiber_monomial (m n : M) (a : K) :
    readFiber v Ω k p hp m (embedAdd v Ω k p hp (Torus.monomial v Ω n a))=
      (Torus.monomial v Ω n a) m := by
  classical
  rw [embedAdd_monomial]
  change (expandZero ((Finsupp.single (off k p hp n)
    (RatFunc.C a*centeredScalar v (k n) (complementAlpha k p Ω (off k p hp n))))
    (off k p hp m))).coeff (k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)=Finsupp.single n a m
  by_cases ho : off k p hp n=off k p hp m
  · rw [Finsupp.single_apply,ite_eq_left ho,expand_centeredScalar]
    by_cases hk : k n=k m
    · have hn : n=m:=split_injective k p hp hk ho
      subst n
      rw [HahnSeries.coeff_single,ite_eq_left rfl,Finsupp.single_eq_same]
      rw [mul_assoc,←Units.val_mul,←zpow_add]
      simp
    · have hn : n≠m:=fun h=>hk (congrArg k h)
      simp [Ne.symm hk,Finsupp.single_eq_of_ne (Ne.symm hn)]
  · have hn : n≠m:=fun h=>ho (congrArg (off k p hp) h)
    rw [Finsupp.single_apply,ite_eq_right ho]
    simp [Finsupp.single_eq_of_ne (Ne.symm hn)]
lemma readFiber_embedAdd (f : Torus v Ω) (m : M) :
    readFiber v Ω k p hp m (embedAdd v Ω k p hp f)=f m := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp [map_add,hf,hg]
  | single n a=>exact readFiber_monomial v Ω k p hp m n a
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CenteredUnitRatio
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
include hΩ in
lemma ray_twisted_coefficient (p m : M) (f : PowerSeries K) (j : ℕ) :
    coeff j (PowerSeries.C (Torus.X v Ω m)*raySeries v Ω p f)=
      Torus.monomial v Ω (m+j • p) (coeff j (rescale (↑(v^(-Ω p m)):K) f)) := by
  have hs : Ω m p= -Ω p m:=by
    have H:=hΩ (m+p)
    simp only [map_add,AddMonoidHom.add_apply,hΩ] at H
    omega
  rw [coeff_C_mul,coeff_raySeries,Torus.X,Torus.monomial_mul_monomial,one_mul,coeff_rescale]
  congr 1
  rw [map_nsmul,hs,nsmul_eq_mul,←Units.val_pow_eq_pow_val,←zpow_natCast,←zpow_mul]
  rw [mul_comm (j:ℤ),mul_comm]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalPureCoefficients
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)
lemma centeredRatio_eq (t : ℤ) : centeredRatio v t=
    rescale (↑(v^t):K) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K)*
      (shiftedElementary v t)⁻¹) := by
  have hc := shiftedElementary_constant v t
  unfold shiftedElementary at hc
  unfold centeredRatio shiftedElementary
  rw [map_mul,map_mul,rescale_inv_of_const_one _ _ (constant_elementary _ _),
    rescale_inv_of_const_one _ _ hc,rescale_rescale,rescale_rescale]
  congr 1
  · rw [←Units.val_mul,←zpow_add]
    congr 2
    ring_nf
  · rw [←Units.val_mul,←zpow_add]
    congr 3
    ring_nf
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
include hΩ in
lemma read_pure_monomial_shift
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (m : M) (j : ℕ) :
    readFiber v Ω k p hp (m+j • p)
      (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
        (embed v Ω hΩ k p hp (Torus.X v Ω m)))=coeff j (centeredRatio v (Ω p m)) := by
  rw [Torus.X,embed_monomial,pureAction_monomial,map_one,one_mul,
    complement_pairing Ω hΩ k p hp m]
  change (expandZero ((Finsupp.single (off k p hp m)
    (centeredScalar v (k m) (Ω p m)*(pureRatio v (Ω p m):RatFunc K)))
      (off k p hp (m+j • p)))).coeff (k (m+j • p))*
        (↑(v^(k (m+j • p)*complementAlpha k p Ω (off k p hp (m+j • p)))):K)=_
  simp only [map_add,map_nsmul,off_p,smul_zero,add_zero,hp,nsmul_eq_mul,mul_one,
    Finsupp.single_eq_same,complement_pairing Ω hΩ k p hp m]
  rw [map_mul,show expandZero (centeredScalar v (k m) (Ω p m))=
      HahnSeries.single (k m) (↑(v^(-k m*Ω p m)):K) by
      simpa using expand_centeredScalar v (k m) (Ω p m) (1:K),
    expandedPure_ratio v hq]
  rw [add_comm (k m),HahnSeries.coeff_single_mul_add,HahnSeries.ofPowerSeries_apply_coeff,
    centeredRatio_eq,coeff_rescale]
  rw [mul_assoc, mul_comm (coeff j _),←mul_assoc,←Units.val_mul,←zpow_add]
  rw [show -k m*Ω p m+((j:ℤ)+k m)*Ω p m=(Ω p m)*(j:ℤ) by ring,
    zpow_mul,zpow_natCast,Units.val_pow_eq_pow_val]
include hΩ in
lemma old_pure_coeff (m : M) (j : ℕ) :
    coeff j ((rayUnit v Ω p (hΩ p) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))
        (constant_elementary _ _)).val*PowerSeries.C (Torus.X v Ω m)*
      (rayUnit v Ω p (hΩ p) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))
        (constant_elementary _ _)).inv)=
      Torus.monomial v Ω (m+j • p) (coeff j (centeredRatio v (Ω p m))) := by
  rw [ray_adjoint v Ω hΩ,ray_twisted_coefficient v Ω hΩ]
  rfl
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus
local instance instAddCommMonoidTorus_1_rd6f74a_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_rd6f74a_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_rd6f74a_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_rd6f74a_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma mul_X_coeff (f : Torus v Ω) (r m : M) :
    (f*Torus.X v Ω m) (r+m)=f r*(↑(v^(Ω r m)):K) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [add_mul,Finsupp.add_apply,hf,hg]
  | single t a=>
    change (Torus.monomial v Ω t a*Torus.monomial v Ω m 1) (r+m)=_
    rw [Torus.monomial_mul_monomial]
    by_cases ht : t=r
    · subst t; simp [Torus.monomial]
    · simp [Torus.monomial,Ne.symm ht]

lemma X_mul_coeff (f : Torus v Ω) (r m : M) :
    (Torus.X v Ω m*f) (r+m)=f r*(↑(v^(Ω m r)):K) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simpa only [mul_add,Finsupp.add_apply,hf,hg] using (_root_.add_mul (f r) (g r) _).symm
  | single t a=>
    change (Torus.monomial v Ω m 1*Torus.monomial v Ω t a) (r+m)=_
    rw [Torus.monomial_mul_monomial]
    by_cases ht : t=r
    · subst t; simp [Torus.monomial,add_comm]
    · have hmt : m+t≠r+m:=by intro hh; apply ht; simpa only [add_comm m t,add_right_cancel_iff] using hh
      simp [Torus.monomial,Ne.symm ht,Ne.symm hmt]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MonomialConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)

include hΩ
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.monomialConjugationRing
local instance monomialConjugationAddCommMonoid_rd6f74a_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_rd6f74a_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
lemma X_mul_X_neg (b:M) : Torus.X v Ω b*Torus.X v Ω (-b)=1 := by
  rw [Torus.X_mul_X_of_pairing_zero v Ω b (-b) (by simp only [map_neg,hΩ,neg_zero])]
  simp only [add_neg_cancel]
  rfl

lemma monomialConjugate_coeff (b:M) (f:PowerSeries (Torus v Ω)) (n:ℕ) (r:M) :
    coeff n (monomialConjugate v Ω b f) r=coeff n f r*(↑(v^(2*Ω b r)):K) := by
  rw [monomialConjugate,coeff_mul_C,coeff_C_mul]
  have H:=mul_X_coeff v Ω (Torus.X v Ω b*coeff n f) (r+b) (-b)
  rw [add_neg_cancel_right,X_mul_coeff] at H
  rw [H,map_add,AddMonoidHom.add_apply,map_neg,map_neg,hΩ,neg_zero,add_zero,
    alternating_skew Ω hΩ r b,neg_neg,mul_assoc,←Units.val_mul,←zpow_add]
  congr 3
  ring

end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
include hΩ in
lemma monomialConjugate_graded (C:(I → ℤ) →+ M) (b:M) {f:PowerSeries (Torus v Ω)}
    (hf:SeriesGraded v Ω C f) : SeriesGraded v Ω C (monomialConjugate v Ω b f) := by
  intro n m hm
  rw [monomialConjugate_coeff v Ω hΩ,hf n m hm,zero_mul]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NormalizedMonomialAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus_1
local instance instAddCommMonoidTorus_2_rd6f74a_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_rd6f74a_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
include hΩ in
lemma adjoint_monomial_normalized (f:PowerSeries (Torus v Ω)) (b:M) :
    adjoint f (PowerSeries.C (Torus.X v Ω b))=
      normalizedMonomialAction v Ω f b*PowerSeries.C (Torus.X v Ω b) := by
  have H:PowerSeries.C (Torus.X v Ω (-b))*PowerSeries.C (Torus.X v Ω b)=
      (1:PowerSeries (Torus v Ω)):=by
    rw [←map_mul]
    simpa only [neg_neg,map_one] using congrArg
      (PowerSeries.C : Torus v Ω → PowerSeries (Torus v Ω)) (X_mul_X_neg v Ω hΩ (-b))
  simp only [normalizedMonomialAction,monomialConjugate,adjoint,mul_assoc,H,mul_one]

include hΩ in
lemma adjoint_monomial_coeff (f:PowerSeries (Torus v Ω)) (b r:M) (n:ℕ) :
    coeff n (adjoint f (PowerSeries.C (Torus.X v Ω b))) (r+b)=
      coeff n (normalizedMonomialAction v Ω f b) r*(↑(v^(Ω r b)):K) := by
  rw [adjoint_monomial_normalized v Ω hΩ,coeff_mul_C,mul_X_coeff]
end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
include hΩ in
lemma normalizedMonomialAction_graded (C:(I → ℤ) →+ M) (f:CompletedPositive v Ω C) (b:M) :
    SeriesGraded v Ω C (normalizedMonomialAction v Ω f.val b) :=
  SeriesGraded.mul v Ω C f.property.2 (monomialConjugate_graded v Ω hΩ C b
    (SeriesGraded.inverse v Ω C f.property.2))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleIncomingElement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
include hcoord in
lemma nonp_zero_of_simple_ray {m : M} (hm : OnPositiveRay (simpleRoot C pc) m) :
    nonpDegree coord pc m=0 := by
  obtain ⟨a,b,ha,hb,he⟩:=hm
  have HH:=congrArg (nonpDegree coord pc) he
  rw [map_nsmul,map_nsmul,nonpDegree_simple_self C coord hcoord,nsmul_zero,nsmul_eq_mul] at HH
  exact (mul_eq_zero.mp HH).resolve_left (by exact_mod_cast Nat.ne_of_gt ha)

include hcoord in
lemma pure_simple_wall (hΩ : ∀m,Ω m m=0) (N : ℕ) (h : M →+ ℝ)
    (hg : RayGeneric C N (simpleRoot C pc) h) :
    ∀j≤N,coeff j (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val=
      coeff j (normalizedSimple Ω (simpleRoot C pc)) := by
  let F:=chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)
  have HF:=pureFace_chartZero Ω C coord hcoord pc h hg.1 (simpleTotalTransport Ω C)
  have HR : ∀j≤N,∀m,coeff j F.val m≠0 → nonpDegree coord pc m=0:=by
    intro j hj m hm
    cases j with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply,F.property.1] at hm
      have hm0 : m=0:=by
        by_contra hh
        exact hm (Finsupp.single_eq_of_ne hh)
      rw [hm0,map_zero]
    | succ j=>
      have hmroot : HasRootDegree C (j+1) m:=by by_contra hh; exact hm (F.property.2 _ m hh)
      have hmzero : h m=0:=(chart_three_support LaurentRay.vUnit Ω C h _).2.1 j m hm
      exact nonp_zero_of_simple_ray C coord hcoord pc (hg.2 (j+1) (by omega) hj m hmroot hmzero)
  intro j hj
  rw [←pureFaceSeries_eq_through Ω coord pc F.val N HR j hj]
  change coeff j (pureFace Ω C coord pc F).val=_
  rw [HF,pureFace_simpleTransport_value Ω C coord hcoord pc hΩ]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PureComparisonIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
lemma laurent_shiftedElementary_zero : shiftedElementary LaurentRay.vUnit 0=
    elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (1:ℤ) (1:ℚ)) := by
  rw [shiftedElementary_zero,←zpow_neg_one, LaurentRay.vUnit_zpow,LaurentRay.vUnit_zpow]
  rfl

lemma completedBiUnit_pure (h : M →+ ℝ)
    (hg : ∀N,RayGeneric C N (simpleRoot C pc) h) :
    completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
      (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C))=
    oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) := by
  apply Units.ext
  apply Subtype.ext
  change (chartZero LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val=
    raySeries LaurentRay.vUnit Ω (simpleRoot C pc) (shiftedElementary LaurentRay.vUnit 0)
  rw [laurent_shiftedElementary_zero]
  apply PowerSeries.ext
  intro n
  exact pure_simple_wall Ω C coord hcoord pc hΩ n h (hg n) n le_rfl
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SectionCharts
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma negative_sign_congr_through (h k : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hs : ∀n,0<n → n≤N → ∀m,HasRootDegree C n m →
      (0<h m → 0<k m) ∧ (h m=0 → k m=0) ∧ (h m<0 → k m<0)) :
    ∀n≤N,coeff n (chartNegative v Ω C h F).val=coeff n (chartNegative v Ω C k F).val := by
  have H:=chart_three_support v Ω C h F
  have HU:=chart_three_truncated_unique v Ω C k F
    (chartPositive v Ω C h F).val (chartZero v Ω C h F).val (chartNegative v Ω C h F).val N
    (chartPositive v Ω C h F).property.1 (chartZero v Ω C h F).property.1
    (chartNegative v Ω C h F).property.1 (chart_three_factorization v Ω C h F)
    (fun n hn m hm=>(hs (n+1) (by omega) hn m (chart_root_of_ne v Ω C _ _ _ hm)).1 (H.1 n m hm))
    (fun n hn m hm=>(hs (n+1) (by omega) hn m (chart_root_of_ne v Ω C _ _ _ hm)).2.1 (H.2.1 n m hm))
    (fun n hn m hm=>(hs (n+1) (by omega) hn m (chart_root_of_ne v Ω C _ _ _ hm)).2.2 (H.2.2 n m hm))
  exact fun n hn=>(HU n hn).2.2
lemma chartNegative_of_positive_through (h : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hpos : ∀n,n+1≤N → ∀m,coeff (n+1) F.val m≠0 → 0<h m) :
    ∀n≤N,coeff n (chartNegative v Ω C h F).val=coeff n 1 := by
  have H:=chart_three_truncated_unique v Ω C h F F.val 1 1 N F.property.1 (by simp)
    (by simp) (by simp) hpos (by intro n hn m hm; simp at hm) (by intro n hn m hm; simp at hm)
  exact fun n hn=>(H n hn).2.2.symm
lemma chartNegative_of_negative_through (h : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hneg : ∀n,n+1≤N → ∀m,coeff (n+1) F.val m≠0 → h m<0) :
    ∀n≤N,coeff n (chartNegative v Ω C h F).val=coeff n F.val := by
  have H:=chart_three_truncated_unique v Ω C h F 1 1 F.val N (by simp) (by simp)
    F.property.1 (by simp) (by intro n hn m hm; simp at hm) (by intro n hn m hm; simp at hm) hneg
  exact fun n hn=>(H n hn).2.2.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionRayTransition
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry PowerSeriesSplit PowerSeriesAdjoint
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hdeg in
lemma section_offset_generic (N : ℕ) (v k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) 0 v k) :
    ChamberGeneric C N (k.toAddMonoidHom.comp e) := by
  intro n hn hnN m hm
  apply H.avoid _ (realRoot_mem e C N n hnN m hm)
  simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using realRoot_ne_zero C e L hdeg n hn m hm
lemma line_covector_add (v k : Module.Dual ℝ E) (a δ : ℝ) :
    ((k+(a+δ) • v).toAddMonoidHom.comp e)=
      (k+a • v).toAddMonoidHom.comp e+δ • (v.toAddMonoidHom.comp e) := by
  ext m
  change k (e m)+((a+δ)*v (e m))=(k (e m)+a*v (e m))+δ*v (e m)
  ring
lemma line_covector_sub (v k : Module.Dual ℝ E) (a δ : ℝ) :
    ((k+(a-δ) • v).toAddMonoidHom.comp e)=
      (k+a • v).toAddMonoidHom.comp e+δ • (-(v.toAddMonoidHom.comp e)) := by
  ext m
  change k (e m)+((a-δ)*v (e m))=(k (e m)+a*v (e m))+δ*(-v (e m))
  ring
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationMonomialAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

include he hdeg H in
lemma actualLineLetter_old (a : ℝ)
    (ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k) :
    ∃r d,0<d ∧ HasRootDegree C d r ∧ v (e r)≠0 ∧
      (∀N,RayGeneric C N r ((k+a • v).toAddMonoidHom.comp e)) ∧
      comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)=
      if v (e r)<0 then completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
        (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C))
      else (completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
        (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C)))⁻¹ := by
  classical
  let data:=lineRayData C e he L hdeg v k H a ha
  by_cases hp : (k+a • v) (e (simpleRoot C pc))=0
  · have Hrp : OnPositiveRay data.root (simpleRoot C pc):=
      (data.generic 1).2 1 one_pos le_rfl (simpleRoot C pc) (simpleRoot_degree C pc) hp
    have HG : ∀N,RayGeneric C N (simpleRoot C pc) ((k+a • v).toAddMonoidHom.comp e):=by
      intro N
      exact ⟨hp,fun n hn hnN m hm hm0=>Hrp.symm.trans ((data.generic N).2 n hn hnN m hm hm0)⟩
    have HV : v (e (simpleRoot C pc))≠0:=by
      intro hz
      have hk : k (e (simpleRoot C pc))=0:=by
        change k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))=0 at hp
        simpa only [hz,mul_zero,add_zero] using hp
      exact section_offset_generic C e L hdeg 1 v k (H 1) 1 one_pos le_rfl
        (simpleRoot C pc) (simpleRoot_degree C pc) hk
    refine ⟨simpleRoot C pc,1,one_pos,simpleRoot_degree C pc,HV,HG,?_⟩
    have HU:=completedBiUnit_pure Ω hΩ C coord hcoord pc ((k+a • v).toAddMonoidHom.comp e) HG
    unfold actualLineLetter
    simp only [dite_eq_left ha,dite_eq_left hp]
    rw [HU]
    by_cases hn : v (e (simpleRoot C pc))<0
    · simp only [hn,decide_true,ite_eq_left,comparisonOld]
    · simp only [hn,decide_false,comparisonOld,↓reduceIte]
  · refine ⟨data.root,data.degree,data.degree_pos,data.root_degree,data.transverse,data.generic,?_⟩
    unfold actualLineLetter
    simp only [dite_eq_left ha,dite_eq_right hp]
    change comparisonOld _ _ _ _ _ _ _ _ _
      (orientedBounded _ _ _ _ _ _ _ _ (decide (v (e data.root)<0)))=_
    by_cases hn : v (e data.root)<0
    · simp only [hn,decide_true,orientedBounded,↓reduceIte,comparisonOld]
    · simp only [hn,decide_false,orientedBounded,Bool.false_eq_true,↓reduceIte,comparisonOld]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_NegativeRayCrossing
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma negative_ray_positive_side (F : CompletedPositive v Ω C)
    (N : ℕ) (p : M) (h k H : M →+ ℝ)
    (hg : RayGeneric C N p h) (hkp : 0<k p)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k H m) :
    ∀n≤N,coeff n (chartNegative v Ω C H F).val=coeff n (chartNegative v Ω C h F).val := by
  have HD:=RayGeneric.ray_supported v Ω C hg F
  have Hneg:=chartNegative_of_positive_through v Ω C k (chartZero v Ω C h F) N (by
    intro n hn m hm
    exact ((by_contra fun hr=>hm (HD (n+1) (by omega) hn m hr) : OnPositiveRay p m).eval k).1.mpr hkp)
  intro n hn
  rw [chart_negative_refinement v Ω C h k H F N hs n hn]
  have HE:=FormalLog.mul_coeff_congr
    (chartNegative v Ω C k (chartZero v Ω C h F)).val (chartNegative v Ω C h F).val
    1 (chartNegative v Ω C h F).val n (fun j hj=>Hneg j (hj.trans hn)) (fun _ _=>rfl)
  simpa only [one_mul] using HE

lemma negative_ray_negative_side (F : CompletedPositive v Ω C)
    (N : ℕ) (p : M) (h k H : M →+ ℝ)
    (hg : RayGeneric C N p h) (hkp : k p<0)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k H m) :
    ∀n≤N,coeff n (chartNegative v Ω C H F).val=
      coeff n ((chartZero v Ω C h F).val*(chartNegative v Ω C h F).val) := by
  have HD:=RayGeneric.ray_supported v Ω C hg F
  have Hneg:=chartNegative_of_negative_through v Ω C k (chartZero v Ω C h F) N (by
    intro n hn m hm
    exact ((by_contra fun hr=>hm (HD (n+1) (by omega) hn m hr) : OnPositiveRay p m).eval k).2.2.mpr hkp)
  intro n hn
  rw [chart_negative_refinement v Ω C h k H F N hs n hn]
  exact FormalLog.mul_coeff_congr _ _ _ _ n (fun j hj=>Hneg j (hj.trans hn)) (fun _ _=>rfl)

lemma negative_ray_forward (F : CompletedPositive v Ω C)
    (N : ℕ) (p : M) (h k Hplus Hminus : M →+ ℝ)
    (hg : RayGeneric C N p h) (hk : k p≠0)
    (hsplus : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k Hplus m)
    (hsminus : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h (-k) Hminus m) :
    ∀n≤N,coeff n ((if k p<0 then (chartZero v Ω C h F).val else
      invOfUnit (chartZero v Ω C h F).val 1)*(chartNegative v Ω C Hminus F).val)=
      coeff n (chartNegative v Ω C Hplus F).val := by
  intro n hn
  split_ifs with hkp
  · rw [negative_ray_negative_side v Ω C F N p h k Hplus hg hkp hsplus n hn]
    exact FormalLog.mul_coeff_congr _ _ _ _ n (fun _ _=>rfl)
      (fun j hj=>negative_ray_positive_side v Ω C F N p h (-k) Hminus hg
        (by simpa using neg_pos.mpr hkp) hsminus j (hj.trans hn))
  · have hpos : 0<k p:=lt_of_le_of_ne (le_of_not_gt hkp) (Ne.symm hk)
    rw [negative_ray_positive_side v Ω C F N p h k Hplus hg hpos hsplus n hn]
    have Hm:=FormalLog.mul_coeff_congr
      (invOfUnit (chartZero v Ω C h F).val 1) (chartNegative v Ω C Hminus F).val
      (invOfUnit (chartZero v Ω C h F).val 1)
      ((chartZero v Ω C h F).val*(chartNegative v Ω C h F).val) n (fun _ _=>rfl)
      (fun j hj=>negative_ray_negative_side v Ω C F N p h (-k) Hminus hg
        (by simpa using neg_neg_of_pos hpos) hsminus j (hj.trans hn))
    simpa only [←mul_assoc,invOfUnit_mul (chartZero v Ω C h F).val 1
      (chartZero v Ω C h F).property.1,one_mul] using Hm
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.FiniteEventTraversal
noncomputable section
variable {A : Type*} [Monoid A]

theorem intervalWord_transport (Q : A→A→Prop) (hQ : Equivalence Q)
    (hmul : ∀a b c d,Q a b → Q c d → Q (a*c) (b*d))
    (S : Finset ℝ) (L W : ℝ → A)
    (cell : ∀a b,a∉S → b∉S → (∀s∈S,a < s ↔ b < s) → Q (W a) (W b))
    (step : ∀a∈S,∃ε>0,∀δ,0<δ → δ<ε → Q (L a*W (a-δ)) (W (a+δ)))
    (lo hi : ℝ) (hlo : lo∉S) (hhi : hi∉S) (horder : lo<hi) :
    Q (intervalWord S lo hi L*W lo) (W hi) := by
  classical
  suffices ∀n,∀hi:ℝ,hi∉S → lo<hi → (S.filter (fun a=>lo<a ∧ a<hi)).card=n →
      Q (intervalWord S lo hi L*W lo) (W hi) from this _ hi hhi horder rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    intro hi hhi horder hn
    let U:=S.filter (fun a=>lo<a ∧ a<hi)
    by_cases hU : U.Nonempty
    · let a:=U.max' hU
      have haU : a∈U:=Finset.max'_mem _ _
      have haS : a∈S:=(Finset.mem_filter.mp haU).1
      have hla : lo<a:=(Finset.mem_filter.mp haU).2.1
      have hah : a<hi:=(Finset.mem_filter.mp haU).2.2
      obtain ⟨ε,hε,Hε⟩:=step a haS
      obtain ⟨η,hη,Hη⟩:=finite_gap S a
      let δ:=min (min ε η) (min (a-lo) (hi-a))/2
      have hmin : 0< min (min ε η) (min (a-lo) (hi-a)):=
        lt_min (lt_min hε hη) (lt_min (sub_pos.mpr hla) (sub_pos.mpr hah))
      have hd : 0<δ:=by dsimp [δ] <;> positivity
      have hsmall : δ< min (min ε η) (min (a-lo) (hi-a)):=by dsimp [δ] <;> linarith
      have hδε : δ<ε:=hsmall.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      have hδη : δ<η:=hsmall.trans_le ((min_le_left _ _).trans (min_le_right _ _))
      have hδlo : δ<a-lo:=hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hδhi : δ<hi-a:=hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have hnear:=near_not_mem S a δ η hd hδη Hη
      let V:=S.filter (fun s=>lo < s ∧ s<a-δ)
      have hVU : V⊆U:=by
        intro s hs
        obtain ⟨hs,hls,hsa⟩:=Finset.mem_filter.mp hs
        exact Finset.mem_filter.mpr ⟨hs,hls,by linarith⟩
      have haV : a∉V:=by
        intro hh
        have hh':=(Finset.mem_filter.mp hh).2.2
        linarith
      have hUV : U=insert a V:=by
        ext s
        constructor
        · intro hs
          by_cases hsa : s=a
          · exact Finset.mem_insert.mpr (Or.inl hsa)
          · have hle : s≤a:=Finset.le_max' U s hs
            have hlt : s<a:=lt_of_le_of_ne hle hsa
            have hgap:=Hη s (Finset.mem_filter.mp hs).1 hsa
            rw [abs_of_neg (sub_neg.mpr hlt)] at hgap
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hs).1,(Finset.mem_filter.mp hs).2.1,by linarith⟩))
        · intro hs
          rcases Finset.mem_insert.mp hs with rfl|hs
          · exact haU
          · exact hVU hs
      have hcard : V.card<n:=by
        have heq : U.card=n:=hn
        rw [hUV,Finset.card_insert_of_notMem haV] at heq
        omega
      have HI:=ih V.card hcard (a-δ) hnear.2 (by linarith) rfl
      have HC : Q (W (a+δ)) (W hi):=by
        apply cell _ _ hnear.1 hhi
        intro s hs
        constructor
        · intro hlt
          by_contra hh
          have hshi : s<hi:=lt_of_le_of_ne (le_of_not_gt hh) (fun he=>hhi (he ▸ hs))
          have hsU : s∈U:=Finset.mem_filter.mpr ⟨hs,by linarith,hshi⟩
          have hsa:=Finset.le_max' U s hsU
          linarith
        · intro hlt
          linarith
      have Hprod : intervalWord S lo hi L=L a*intervalWord S lo (a-δ) L:=by
        unfold intervalWord
        change ((U.sort (· ≥ ·)).map L).prod=L a*((V.sort (· ≥ ·)).map L).prod
        rw [hUV,Finset.sort_insert]
        · simp
        · intro s hs
          exact Finset.le_max' U s (hVU hs)
        · exact haV
      rw [Hprod,mul_assoc]
      exact hQ.trans (hmul _ _ _ _ (hQ.refl _) HI) (hQ.trans (Hε δ hd hδε) HC)
    · have hU0 : U=∅:=Finset.not_nonempty_iff_eq_empty.mp hU
      have Hz : intervalWord S lo hi L=1:=by
        unfold intervalWord
        change ((U.sort (· ≥ ·)).map L).prod=1
        rw [hU0]
        simp
      rw [Hz,one_mul]
      apply cell _ _ hlo hhi
      intro s hs
      constructor
      · intro hls
        by_contra hh
        have hshi : s<hi:=lt_of_le_of_ne (le_of_not_gt hh) (fun he=>hhi (he ▸ hs))
        have hsU : s∈U:=Finset.mem_filter.mpr ⟨hs,hls,hshi⟩
        rw [hU0] at hsU
        exact Finset.notMem_empty _ hsU
      · intro hhs
        linarith
end
end ElementaryPositivity.FiniteEventTraversal

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LineOldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

lemma oldCoefficientsEqual_equivalence (N : ℕ) :
    Equivalence (oldCoefficientsEqual Ω coord pc N) := by
  refine ⟨fun _ _ _=>rfl,?_,?_⟩
  · intro a b hab n hn; exact (hab n hn).symm
  · intro a b c hab hbc n hn; exact (hab n hn).trans (hbc n hn)
lemma oldCoefficientsEqual_mul (N : ℕ)
    (a b c d : (biSupportedSubring LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc))ˣ)
    (hab : oldCoefficientsEqual Ω coord pc N a b) (hcd : oldCoefficientsEqual Ω coord pc N c d) :
    oldCoefficientsEqual Ω coord pc N (a*c) (b*d) := by
  intro n hn
  exact FormalLog.mul_coeff_congr a.val.val c.val.val b.val.val d.val.val n
    (fun j hj=>hab j (hj.trans hn)) (fun j hj=>hcd j (hj.trans hn))

include he hdeg H in
lemma actualLine_old_step (N : ℕ) (a : ℝ)
    (ha : a∈lineEvents (realRootsThrough e C N) v k) :
    ∃ε>0,∀δ,0<δ → δ<ε → oldCoefficientsEqual Ω coord pc N
    (comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)*
      lineNegativeUnit Ω C coord hcoord pc e v k (a-δ))
    (lineNegativeUnit Ω C coord hcoord pc e v k (a+δ)) := by
  obtain ⟨r,d,hd,hr,hv,Hg,HOld⟩:=actualLineLetter_old Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a ⟨N,ha⟩
  let h:=(k+a • v).toAddMonoidHom.comp e
  let V:=v.toAddMonoidHom.comp e
  obtain ⟨ε,hε,Hε⟩:=root_lex_epsilon C N h V
  obtain ⟨η,hη,Hη⟩:=root_lex_epsilon C N h (-V)
  refine ⟨min ε η,lt_min hε hη,?_⟩
  intro δ hδ hsmall n hn
  have Hp : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h V
      ((k+(a+δ) • v).toAddMonoidHom.comp e) m:=by
    rw [line_covector_add]
    exact Hε δ hδ (hsmall.trans_le (min_le_left _ _))
  have Hm : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h (-V)
      ((k+(a-δ) • v).toAddMonoidHom.comp e) m:=by
    rw [line_covector_sub]
    exact Hη δ hδ (hsmall.trans_le (min_le_right _ _))
  have HH:=negative_ray_forward LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) N r h V
    ((k+(a+δ) • v).toAddMonoidHom.comp e) ((k+(a-δ) • v).toAddMonoidHom.comp e)
    (Hg N) hv Hp Hm n hn
  change coeff n ((comparisonOld _ _ _ _ _ _ _ _ _ _).val.val*
    (lineNegativeUnit Ω C coord hcoord pc e v k (a-δ)).val.val)=_
  rw [HOld]
  by_cases hk : v (e r)<0
  · rw [ite_eq_left hk]
    rw [ite_eq_left (show V r<0 from hk)] at HH
    exact HH
  · rw [ite_eq_right hk]
    rw [ite_eq_right (show ¬V r<0 from hk)] at HH
    exact HH

lemma actualLine_old_cell (N : ℕ) (a b : ℝ)
    (ha : a∉lineEvents (realRootsThrough e C N) v k)
    (hb : b∉lineEvents (realRootsThrough e C N) v k)
    (hc : ∀z∈lineEvents (realRootsThrough e C N) v k,a<z ↔ b<z) :
    oldCoefficientsEqual Ω coord pc N
      (lineNegativeUnit Ω C coord hcoord pc e v k a)
      (lineNegativeUnit Ω C coord hcoord pc e v k b) := by
  apply negative_sign_congr_through
  intro n hn hnN m hm
  exact line_cell_signs _ v k a b ha hb hc (e m) (realRoot_mem e C N n hnN m hm)

include he hdeg H in
theorem actualLine_old_transport (lo hi : ℝ) (N : ℕ)
    (hlo : lo∉lineEvents (realRootsThrough e C N) v k)
    (hhi : hi∉lineEvents (realRootsThrough e C N) v k) (horder : lo<hi) :
    oldCoefficientsEqual Ω coord pc N
      (comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N)*
        lineNegativeUnit Ω C coord hcoord pc e v k lo)
      (lineNegativeUnit Ω C coord hcoord pc e v k hi) := by
  have HH:=FiniteEventTraversal.intervalWord_transport
    (oldCoefficientsEqual Ω coord pc N) (oldCoefficientsEqual_equivalence Ω coord pc N)
    (oldCoefficientsEqual_mul Ω coord pc N)
    (lineEvents (realRootsThrough e C N) v k)
    (fun a=>comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a))
    (lineNegativeUnit Ω C coord hcoord pc e v k)
    (actualLine_old_cell Ω C coord hcoord pc e v k N)
    (actualLine_old_step Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H N)
    lo hi hlo hhi horder
  simpa only [FiniteEventTraversal.intervalWord,comparisonWordOld,actualLineWord,
    intervalEventList,intervalLineEvents,List.map_map,Function.comp_def] using HH
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PathOldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

lemma comparisonWordOld_append {K M : Type*} [Field K] [AddCommGroup M]
    (u : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
    (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)
    (l l' : List (ComparisonCrossing u Ω δ k B)) :
    comparisonWordOld u Ω hΩ δ k p hp hδ B (l++l')=
    comparisonWordOld u Ω hΩ δ k p hp hδ B l*comparisonWordOld u Ω hΩ δ k p hp hδ B l' := by
  simp only [comparisonWordOld,List.map_append,List.prod_append]

include he hdeg in
theorem actualPath_old_transport {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    oldCoefficientsEqual Ω coord pc N
      (comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N)*
        covectorNegativeUnit Ω C coord hcoord pc e a)
      (covectorNegativeUnit Ω C coord hcoord pc e b) := by
  induction p with
  | nil=>
    simpa only [actualPathWord,comparisonWordOld,List.map_nil,List.prod_nil,one_mul]
      using (oldCoefficientsEqual_equivalence Ω coord pc N).refl
        _
  | append s p ih=>
    rw [actualPathWord,comparisonWordOld_append,mul_assoc]
    apply (oldCoefficientsEqual_equivalence Ω coord pc N).trans
      (oldCoefficientsEqual_mul Ω coord pc N _ _ _ _
        ((oldCoefficientsEqual_equivalence Ω coord pc N).refl _) ih)
    exact actualLine_old_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi N (s.start_regular N) (s.finish_regular N) s.ordered

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_AffineCutTelescoping
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.AffineCut
noncomputable section

lemma sides_eq_of_ne (u v t : ℝ) (h : u+t*v≠0) :
    beforeSide u v t=decide (0<u+t*v) ∧
    afterSide u v t=decide (0<u+t*v) := by
  simp [beforeSide,afterSide,h]

lemma sides_at_zero (u v t : ℝ) (h : u+t*v=0) :
    beforeSide u v t=decide (v<0) ∧
    afterSide u v t=decide (0<v) := by
  simp [beforeSide,afterSide,h]

lemma gap_sides (u v lo hi : ℝ) (h : lo<hi) (hne : u≠0 ∨ v≠0)
    (hz : ∀t,lo<t → t<hi → u+t*v≠0) :
    afterSide u v lo=beforeSide u v hi := by
  have hstraddle : ¬(u+lo*v<0 ∧ 0<u+hi*v) := by
    rintro ⟨hl,hh⟩
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc h.le
      (show ContinuousOn (fun t : ℝ => u+t*v) (Set.Icc lo hi) by fun_prop)
      (show (0:ℝ)∈Set.Icc (u+lo*v) (u+hi*v) from ⟨hl.le,hh.le⟩)
    have hl' : lo<t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
    have hh' : t<hi := lt_of_le_of_ne ht.2 (by rintro rfl; linarith)
    exact hz t hl' hh' he
  have hstraddle' : ¬(u+hi*v<0 ∧ 0<u+lo*v) := by
    rintro ⟨hh,hl⟩
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' h.le
      (show ContinuousOn (fun t : ℝ => u+t*v) (Set.Icc lo hi) by fun_prop)
      (show (0:ℝ)∈Set.Icc (u+hi*v) (u+lo*v) from ⟨hh.le,hl.le⟩)
    have hl' : lo<t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
    have hh' : t<hi := lt_of_le_of_ne ht.2 (by rintro rfl; linarith)
    exact hz t hl' hh' he
  unfold afterSide beforeSide
  apply Bool.decide_congr
  rcases lt_trichotomy v 0 with hv | hv | hv
  · have hm : u+hi*v<u+lo*v := by nlinarith
    constructor
    · rintro (hl | ⟨hl,hv'⟩)
      · by_cases hh : 0<u+hi*v
        · exact Or.inl hh
        · exact Or.inr ⟨le_antisymm (le_of_not_gt hh)
            (not_lt.mp (fun H=>hstraddle' ⟨H,hl⟩)),hv⟩
      · linarith
    · rintro (hh | ⟨hh,_⟩) <;> exact Or.inl (by linarith)
  · subst v
    have hu : u≠0 := hne.resolve_right (by simp)
    simp
  · have hm : u+lo*v<u+hi*v := by nlinarith
    constructor
    · rintro (hl | ⟨hl,_⟩) <;> exact Or.inl (by linarith)
    · rintro (hh | ⟨hh,hv'⟩)
      · by_cases hl : 0<u+lo*v
        · exact Or.inl hl
        · exact Or.inr ⟨le_antisymm (le_of_not_gt hl)
            (not_lt.mp (fun H=>hstraddle ⟨H,hh⟩)),hv⟩
      · linarith

theorem telescope {A B : Type*} (u v : ℝ) (hne : u≠0 ∨ v≠0)
    (old : ℝ → A → A) (new : ℝ → B → B) (chart : Bool → A → B)
    (l : List ℝ) (hsort : l.Pairwise (· > ·)) (lo hi : ℝ) (hlohi : lo<hi)
    (hmem : ∀t∈l,lo<t ∧ t<hi)
    (hcut : ∀t,lo<t → t<hi → u+t*v=0 → t∈l)
    (hlocal : ∀t∈l,∀x,new t (chart (beforeSide u v t) x)=
      chart (afterSide u v t) (old t x)) (x : A) :
    l.foldr new (chart (afterSide u v lo) x)=
      chart (beforeSide u v hi) (l.foldr old x) := by
  induction l generalizing lo hi with
  | nil =>
    simp only [List.foldr_nil]
    rw [gap_sides u v lo hi hlohi hne]
    intro t hlt hth ht
    exact List.not_mem_nil (hcut t hlt hth ht)
  | cons a l ih =>
    obtain ⟨has,hsort⟩:=List.pairwise_cons.mp hsort
    obtain ⟨hla,hah⟩:=hmem a (by simp)
    have hlmem : ∀t∈l,lo<t ∧ t<a := by
      intro t ht
      exact ⟨(hmem t (by simp [ht])).1,has t ht⟩
    have hlcut : ∀t,lo<t → t<a → u+t*v=0 → t∈l := by
      intro t hlt hta ht
      have H:=hcut t hlt (hta.trans hah) ht
      rcases List.mem_cons.mp H with rfl | H
      · exact False.elim (lt_irrefl _ hta)
      · exact H
    have hg : afterSide u v a=beforeSide u v hi := by
      apply gap_sides u v a hi hah hne
      intro t hat hth ht
      have H:=hcut t (hla.trans hat) hth ht
      rcases List.mem_cons.mp H with rfl | H
      · exact lt_irrefl _ hat
      · exact (lt_asymm hat (has t H))
    simp only [List.foldr_cons]
    rw [ih hsort lo a hla hlmem hlcut (fun t ht=>hlocal t (by simp [ht])),
      hlocal a (by simp),hg]

lemma sort_strict (S : Finset ℝ) : (S.sort (· ≥ ·)).Pairwise (· > ·) := by
  have hn : (S.sort (· ≥ ·)).Pairwise (· ≠ ·) := S.sort_nodup _
  exact ((S.pairwise_sort (· ≥ ·)).and hn).imp (fun h=>lt_of_le_of_ne h.1 (Ne.symm h.2))

theorem telescope_sort {A B : Type*} (u v : ℝ) (hne : u≠0 ∨ v≠0)
    (old : ℝ → A → A) (new : ℝ → B → B) (chart : Bool → A → B)
    (S : Finset ℝ) (lo hi : ℝ) (hlohi : lo<hi)
    (hmem : ∀t∈S,lo<t ∧ t<hi)
    (hcut : ∀t,lo<t → t<hi → u+t*v=0 → t∈S)
    (hlocal : ∀t∈S,∀x,new t (chart (beforeSide u v t) x)=
      chart (afterSide u v t) (old t x)) (x : A) :
    (S.sort (· ≥ ·)).foldr new (chart (afterSide u v lo) x)=
      chart (beforeSide u v hi) ((S.sort (· ≥ ·)).foldr old x) := by
  exact telescope u v hne old new chart (S.sort (· ≥ ·)) (sort_strict S) lo hi hlohi
    (by simpa only [Finset.mem_sort] using hmem)
    (by simpa only [Finset.mem_sort] using hcut)
    (by simpa only [Finset.mem_sort] using hlocal) x
end
end ElementaryPositivity.AffineCut

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

include hdeg H in
lemma line_cut_offset_ne : k (e (simpleRoot C pc))≠0 := by
  have hr : e (simpleRoot C pc)∈realRootsThrough e C 1 := by
    exact realRoot_mem e C 1 1 le_rfl (simpleRoot C pc) (simpleRoot_degree C pc)
  apply (H 1).avoid _ hr
  rw [Submodule.span_singleton_eq_bot.mpr rfl,Submodule.mem_bot]
  intro hz
  have HH:=hdeg 1 (simpleRoot C pc) (simpleRoot_degree C pc)
  rw [hz,map_zero] at HH
  norm_num at HH

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedPathIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)

lemma GenericLinePath.InRegion.trans {U : Set (Module.Dual ℝ E)} {a b c : Module.Dual ℝ E}
    {p : GenericLinePath C e a b} {q : GenericLinePath C e b c}
    (hp : p.InRegion C e U) (hq : q.InRegion C e U) :
    (p.trans C e q).InRegion C e U := by
  induction q with
  | nil=>exact hp
  | append s q ih=>exact ⟨hq.1,ih hq.2⟩

lemma GenericLinePath.InRegion.castEnds {U : Set (Module.Dual ℝ E)}
    {a b a' b' : Module.Dual ℝ E} (h0 : a=a') (h1 : b=b')
    {p : GenericLinePath C e a b} (hp : p.InRegion C e U) :
    (p.castEnds C e h0 h1).InRegion C e U := by
  subst a'; subst b'; exact hp

lemma segmentBetween_inRegion {U : Set (Module.Dual ℝ E)} (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 (b-a) a)
    (hU : ∀t:ℝ,0≤t → t≤1 → (1-t) • a+t • b∈U) :
    (GenericLinePath.single C e (segmentBetween C e a b HA HB H)).InRegion C e U := by
  refine ⟨?_,trivial⟩
  intro t hlo hhi
  change a+t • (b-a)∈U
  have heq : a+t • (b-a)=(1-t) • a+t • b := by
    module
  rw [heq]
  exact hU t hlo hhi
end

end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedAnchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)

omit [FiniteDimensional ℝ E] in
lemma covector_root_pos (J:Module.Dual ℝ E)
    (hJ:∀i,0<J (e (simpleRoot C i))) {n:ℕ} (hn:0<n) {m:M} (hm:HasRootDegree C n m) :
    0<J (e m) := by
  obtain ⟨a,ha,rfl⟩:=hm
  rw [coefficient_simple_expansion C,map_sum,map_sum]
  simp only [map_zsmul,zsmul_eq_mul]
  have hp:∃i,0<a i:=by
    by_contra H
    push Not at H
    have hh:(∑i,a i)≤0:=Finset.sum_nonpos (fun i _=>H i)
    rw [ha] at hh
    omega
  obtain ⟨i,hi⟩:=hp
  exact Finset.sum_pos' (fun j _=>mul_nonneg (by exact_mod_cast Nat.zero_le (a j)) (hJ j).le)
    ⟨i,Finset.mem_univ i,mul_pos (by exact_mod_cast hi) (hJ i)⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PureCoefficient
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (k:M →+ ℤ) (p:M) (hp:k p=1)

lemma ofPowerSeries_negative (f:PowerSeries K) (j:ℤ) (hj:j<0) :
    (HahnSeries.ofPowerSeries ℤ K f).coeff j=0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨n,_,hn⟩
  have he : (n:ℤ)=j := hn
  omega

include hΩ in
lemma read_pure_monomial_support
    (hq:∀n:ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (b m:M)
    (hm:readFiber v Ω k p hp m
      (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
        (embed v Ω hΩ k p hp (Torus.X v Ω b)))≠0) :
    ∃j:ℕ,m=b+j • p := by
  classical
  rw [Torus.X,embed_monomial,pureAction_monomial,map_one,one_mul,
    complement_pairing Ω hΩ k p hp b] at hm
  change (expandZero ((Finsupp.single (off k p hp b)
    (centeredScalar v (k b) (Ω p b)*(pureRatio v (Ω p b):RatFunc K)))
      (off k p hp m))).coeff (k m)*
        (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)≠0 at hm
  have ho:off k p hp b=off k p hp m:=by
    by_contra hh
    simp only [Finsupp.single_apply,ite_eq_right hh,map_zero,HahnSeries.coeff_zero,zero_mul,ne_eq,not_true_eq_false] at hm
  rw [Finsupp.single_apply,ite_eq_left ho,map_mul] at hm
  rw [show expandZero (centeredScalar v (k b) (Ω p b))=
      HahnSeries.single (k b) (↑(v^(-k b*Ω p b)):K) by
      simpa using expand_centeredScalar v (k b) (Ω p b) (1:K),
    expandedPure_ratio v hq,HahnSeries.coeff_single_mul] at hm
  have hk:0≤k m-k b:=by
    by_contra hh
    rw [ofPowerSeries_negative _ _ (lt_of_not_ge hh),mul_zero,zero_mul] at hm
    exact hm rfl
  refine ⟨(k m-k b).toNat,split_injective k p hp ?_ ?_⟩
  · simp only [map_add,map_nsmul,nsmul_eq_mul,hp,mul_one,Int.toNat_of_nonneg hk]
    omega
  · simp only [map_add,map_nsmul,off_p,smul_zero,add_zero]
    exact ho.symm
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_LatticeHahn
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint
noncomputable section
variable {R M:Type*} [CommRing R] [AddCommGroup M]
variable (v:Rˣ) (Ω:M →+ M →+ ℤ) (τ:M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.latticeHahnRing
local instance latticeHahnAddCommMonoid_rd6f74a_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_rd6f74a_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.latticeHahnNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.latticeHahnNonUnitalNonAssocSemiring
lemma latticeHahn_monomial (b:M) (c:R) :
    latticeHahn v Ω τ (Torus.monomial v Ω b c)=
      HahnSeries.single (τ b) (Torus.monomial v Ω b c) := by
  change constantCoeff (laurentHomogenize v Ω 0 τ (Torus.monomial v Ω b c))=_
  rw [laurentHomogenize_monomial]
  simp only [AddMonoidHom.zero_apply,Int.toNat_zero,monomial_zero_eq_C_apply,constantCoeff_C]

lemma latticeHahn_coeff (F:Torus v Ω) (j:ℤ) (m:M) :
    (latticeHahn v Ω τ F).coeff j m=if j=τ m then F m else 0 := by
  change (constantCoeff (laurentHomogenize v Ω 0 τ F)).coeff j m=_
  rw [←coeff_zero_eq_constantCoeff,laurentHomogenize_coeff]
  simp

lemma hahn_single_shift_adjoint (f:PowerSeries (Torus v Ω)) (j:ℤ) (F:Torus v Ω) :
    HahnSeries.ofPowerSeries ℤ (Torus v Ω) f * HahnSeries.single j F *
      HahnSeries.ofPowerSeries ℤ (Torus v Ω) (invOfUnit f 1)=
    HahnSeries.single j (1:Torus v Ω)*
      HahnSeries.ofPowerSeries ℤ (Torus v Ω) (adjoint f (PowerSeries.C F)) := by
  have H (g:HahnSeries ℤ (Torus v Ω)):
      g*HahnSeries.single j (1:Torus v Ω)=HahnSeries.single j (1:Torus v Ω)*g:=by
    apply HahnSeries.ext
    funext n
    rw [HahnSeries.coeff_mul_single,HahnSeries.coeff_single_mul,mul_one,one_mul]
  rw [adjoint,map_mul,map_mul,HahnSeries.ofPowerSeries_C]
  have HS:HahnSeries.single j F=HahnSeries.single j (1:Torus v Ω)*HahnSeries.C F:=by
    change HahnSeries.single j F=HahnSeries.single j (1:Torus v Ω)*HahnSeries.single 0 F
    rw [HahnSeries.single_mul_single,add_zero,one_mul]
  rw [HS,←mul_assoc,H, mul_assoc,mul_assoc,mul_assoc]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialAdjointCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.polynomialAdjointCoefficientsRing
local instance polynomialAdjointCoefficientsAddCommMonoid_rd6f74a_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_rd6f74a_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma actualPolynomialAdjointCoefficient_add (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F G:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ f (F+G) m=
      actualPolynomialAdjointCoefficient Ω τ f F m+actualPolynomialAdjointCoefficient Ω τ f G m := by
  exact Finsupp.sum_add_index' (fun _=>zero_mul _) (fun _ _ _=>add_mul _ _ _)

lemma actualPolynomialAdjointCoefficient_monomial (τ:M →+ ℤ)
    (f:PowerSeries (Torus LaurentRay.vUnit Ω)) (b m:M) (c:LaurentSeries ℚ) :
    actualPolynomialAdjointCoefficient Ω τ f (Torus.monomial LaurentRay.vUnit Ω b c) m=
      c*actualMonomialAdjointCoefficient Ω τ f b m := by
  exact Finsupp.sum_single_index (zero_mul _)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PureActualCoefficients
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber
noncomputable section
variable {M:Type*} [AddCommGroup M]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (τ:M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.pureActualCoefficientsRing
local instance pureActualCoefficientsAddCommMonoid_rd6f74a_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_rd6f74a_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hΩ in
lemma actualMonomialAdjointCoefficient_read (f:PowerSeries (Torus LaurentRay.vUnit Ω)) (b m:M) :
    actualMonomialAdjointCoefficient Ω τ f b m=
      if 0≤τ (m-b) then
        coeff (τ (m-b)).toNat (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m else 0 := by
  unfold actualMonomialAdjointCoefficient actualRootCoefficient
  split_ifs with h
  · simpa only [sub_add_cancel] using
      (adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ f b (m-b) (τ (m-b)).toNat).symm
  · exact zero_mul _

include hΩ in
lemma normalizedSimple_adjoint_coefficient (p b:M) (j:ℕ) :
    coeff j (adjoint (normalizedSimple Ω p) (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b)))=
      Torus.monomial LaurentRay.vUnit Ω (b+j • p) (coeff j (centeredRatio LaurentRay.vUnit (Ω p b))) := by
  rw [adjoint,normalizedSimple_inverse Ω hΩ p]
  have H:=old_pure_coeff LaurentRay.vUnit Ω hΩ p b j
  simpa only [rayUnit,normalizedSimple,←shiftedElementary_zero,laurent_shiftedElementary_zero] using H

include hΩ in
lemma actual_pure_monomial (k:M →+ ℤ) (p:M) (hp:k p=1) (hτ:τ p=1) (b m:M) :
    actualMonomialAdjointCoefficient Ω τ (normalizedSimple Ω p) b m=
      readFiber LaurentRay.vUnit Ω k p hp m
        (pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
          (embed LaurentRay.vUnit Ω hΩ k p hp (Torus.X LaurentRay.vUnit Ω b))) := by
  classical
  have hq:∀n:ℕ,1-(↑(LaurentRay.vUnit^(-2:ℤ)):LaurentSeries ℚ)^(n+1)≠0:=by
    intro n
    rw [LaurentRay.vUnit_zpow]
    exact UnitSelections.laurent_q_not_root n
  by_cases hm:∃j:ℕ,m=b+j • p
  · obtain ⟨j,rfl⟩:=hm
    rw [actualMonomialAdjointCoefficient_read Ω hΩ τ]
    have ht:τ (b+j • p-b)=(j:ℤ):=by simp only [map_sub,map_add,map_nsmul,hτ,nsmul_eq_mul,mul_one]; omega
    rw [ht,ite_eq_left (Int.natCast_nonneg j),Int.toNat_natCast,normalizedSimple_adjoint_coefficient Ω hΩ,
      read_pure_monomial_shift LaurentRay.vUnit Ω hΩ k p hp hq]
    exact Finsupp.single_eq_same
  · rw [actualMonomialAdjointCoefficient_read Ω hΩ τ]
    have hr:readFiber LaurentRay.vUnit Ω k p hp m
        (pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
          (embed LaurentRay.vUnit Ω hΩ k p hp (Torus.X LaurentRay.vUnit Ω b)))=0:=by
      by_contra hh
      exact hm (read_pure_monomial_support LaurentRay.vUnit Ω hΩ k p hp hq b m hh)
    rw [hr]
    split_ifs
    · rw [normalizedSimple_adjoint_coefficient Ω hΩ]
      exact Finsupp.single_eq_of_ne (fun he=>hm ⟨_,he⟩)
    · rfl
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries HahnSeries
noncomputable section
variable {A:Type*} [Ring A]
lemma hahnAction_add (f:PowerSeries A) (x y:HahnSeries ℤ A) :
    hahnAction f (x+y)=hahnAction f x+hahnAction f y := by
  simp only [hahnAction,mul_add,add_mul]
lemma hahnAction_zero (f:PowerSeries A) : hahnAction f (0:HahnSeries ℤ A)=0 := by
  simp only [hahnAction,mul_zero,zero_mul]
lemma hahnAction_one (x:HahnSeries ℤ A) : hahnAction 1 x=x := by
  have hi:invOfUnit (1:PowerSeries A) 1=1:=by simpa using mul_invOfUnit (1:PowerSeries A) 1 (by simp)
  simp only [hahnAction,hi,map_one,one_mul,mul_one]
lemma hahnAction_mul (f g:PowerSeries A) (x:HahnSeries ℤ A)
    (hf:constantCoeff f=1) (hg:constantCoeff g=1) :
    hahnAction (f*g) x=hahnAction f (hahnAction g x) := by
  simp only [hahnAction,inverse_mul f g hf hg,map_mul,mul_assoc]
lemma hahnAction_inverse_cancel (f:PowerSeries A) (x:HahnSeries ℤ A)
    (hf:constantCoeff f=1) : hahnAction (invOfUnit f 1) (hahnAction f x)=x := by
  rw [←hahnAction_mul _ _ _ (by simp) hf,invOfUnit_mul f 1 hf,hahnAction_one]
lemma ofPowerSeries_coeff_int (f:PowerSeries A) (j:ℤ) :
    (ofPowerSeries ℤ A f).coeff j=if 0≤j then coeff j.toNat f else 0 := by
  by_cases hj:0≤j
  · rw [ite_eq_left hj,←Int.toNat_of_nonneg hj,HahnSeries.ofPowerSeries_apply_coeff,Int.toNat_natCast]
  · rw [ite_eq_right hj,HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨n,_,hn⟩
    have he:(n:ℤ)=j:=hn
    omega
end
end ElementaryPositivity.PowerSeriesAdjoint
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0) (τ:M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.pureActualScalarCoefficientsRing
local instance pureActualScalarCoefficientsAddCommMonoid_rd6f74a_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_rd6f74a_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_rd6f74a_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.pureActualScalarCoefficientsNonUnitalNonAssocSemiring
lemma adjoint_scalar_monomial_coeff (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (b m:M) (c:LaurentSeries ℚ) (n:ℕ) :
    coeff n (adjoint f (PowerSeries.C (Torus.monomial LaurentRay.vUnit Ω b c))) m=
      c*coeff n (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m := by
  rw [adjoint_torus_expansion]
  change (Finsupp.single b c).sum (fun d a=>a*coeff n (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω d))) m)=_
  exact Finsupp.sum_single_index (zero_mul _)

lemma hahnAction_monomial_coeff (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (b m:M) (c:LaurentSeries ℚ) (j:ℤ) :
    (hahnAction f (latticeHahn LaurentRay.vUnit Ω τ (Torus.monomial LaurentRay.vUnit Ω b c))).coeff j m=
      if 0≤j-τ b then c*coeff (j-τ b).toNat (adjoint f (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m else 0 := by
  rw [latticeHahn_monomial,hahnAction,hahn_single_shift_adjoint,
    HahnSeries.coeff_single_mul,one_mul,ofPowerSeries_coeff_int]
  split_ifs
  · exact adjoint_scalar_monomial_coeff Ω f b m c _
  · rfl

include hΩ in
lemma hahnAction_actual_coeff (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    (hahnAction f (latticeHahn LaurentRay.vUnit Ω τ F)).coeff (τ m) m=
      actualPolynomialAdjointCoefficient Ω τ f F m := by
  classical
  induction F using Finsupp.induction_linear with
  | zero=>simp [hahnAction_zero,actualPolynomialAdjointCoefficient]
  | add F G hF hG=>rw [map_add,hahnAction_add,HahnSeries.coeff_add,
      Finsupp.add_apply,actualPolynomialAdjointCoefficient_add,hF,hG]
  | single b c=>
    change (hahnAction f (latticeHahn LaurentRay.vUnit Ω τ (Torus.monomial LaurentRay.vUnit Ω b c))).coeff (τ m) m=
      actualPolynomialAdjointCoefficient Ω τ f (Torus.monomial LaurentRay.vUnit Ω b c) m
    rw [hahnAction_monomial_coeff,actualPolynomialAdjointCoefficient_monomial,
      actualMonomialAdjointCoefficient_read Ω hΩ τ,map_sub]
    split_ifs <;> simp

omit [DecidableEq I] in
include hΩ in
lemma adjoint_monomial_degree (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
    (hcoord:∀d,coord (C d)=d) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (b m:M) (n:ℕ)
    (hm:coeff n (adjoint f.val (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m≠0) :
    rootOrder coord (m-b)=(n:ℤ) := by
  have H:=normalizedMonomialAction_graded LaurentRay.vUnit Ω hΩ C f b
  have he:=adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ f.val b (m-b) n
  simp only [sub_add_cancel] at he
  rw [he] at hm
  apply rootOrder_eq C coord hcoord
  by_contra hh
  exact hm (by rw [H n (m-b) hh,zero_mul])

omit [DecidableEq I] in
include hΩ in
lemma hahnAction_diagonal (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
    (hcoord:∀d,coord (C d)=d) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (F:Torus LaurentRay.vUnit Ω) (j:ℤ) (m:M) (hj:j≠rootOrder coord m) :
    (hahnAction f.val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) F)).coeff j m=0 := by
  classical
  induction F using Finsupp.induction_linear with
  | zero=>simp [hahnAction_zero]
  | add F G hF hG=>rw [map_add,hahnAction_add,HahnSeries.coeff_add,Finsupp.add_apply,hF,hG,add_zero]
  | single b c=>
    change (hahnAction f.val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) (Torus.monomial LaurentRay.vUnit Ω b c))).coeff j m=0
    rw [hahnAction_monomial_coeff]
    split_ifs with hn
    · have hz:coeff (j-rootOrder coord b).toNat
          (adjoint f.val (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) m=0:=by
        by_contra hh
        have H:=adjoint_monomial_degree Ω hΩ C coord hcoord f b m _ hh
        rw [map_sub,Int.toNat_of_nonneg hn] at H
        exact hj (by omega)
      rw [hz,mul_zero]
    · rfl

omit [DecidableEq I] in
include hΩ in
lemma hahnAction_finite_iff (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
    (hcoord:∀d,coord (C d)=d) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (F G:Torus LaurentRay.vUnit Ω) :
    hahnAction f.val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) F)=
        latticeHahn LaurentRay.vUnit Ω (rootOrder coord) G ↔
      ∀m,actualPolynomialAdjointCoefficient Ω (rootOrder coord) f.val F m=G m := by
  constructor
  · intro h m
    have H:=congrArg (fun x:HahnSeries ℤ (Torus LaurentRay.vUnit Ω)=>x.coeff (rootOrder coord m) m) h
    simpa only [hahnAction_actual_coeff Ω hΩ,latticeHahn_coeff,ite_true, if_true] using H
  · intro h
    apply HahnSeries.ext
    funext j
    apply Finsupp.ext
    intro m
    by_cases hj:j=rootOrder coord m
    · subst j
      rw [hahnAction_actual_coeff Ω hΩ,latticeHahn_coeff,ite_eq_left rfl,h]
    · rw [hahnAction_diagonal Ω hΩ C coord hcoord f F j m hj,latticeHahn_coeff,ite_eq_right hj]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HalfspacePolynomialCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits HahnSeries
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.halfspacePolynomialCoefficientsCoeffRing
local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid_rd6f74a_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup_rd6f74a_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring_rd6f74a_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring_rd6f74a_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
lemma rootSectionChart_negative (h:M →+ ℝ)
    (hh:∀n,0<n → ∀m,HasRootDegree C n m → h m<0) :
    (rootSectionChart Ω C h).val=1 := by
  have H:(chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).val=
      (simpleTotalTransport Ω C).val:=by
    apply PowerSeries.ext
    intro n
    apply chartNegative_of_negative_through LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C) n _ n le_rfl
    intro j hj m hm
    exact hh (j+1) (by omega) m (chart_root_of_ne LaurentRay.vUnit Ω C _ _ _ hm)
  dsimp [rootSectionChart]
  rw [H,mul_invOfUnit _ 1 (simpleTotalTransport Ω C).property.1]

lemma rootChartRatio_section (a b:M →+ ℝ) :
    (rootChartRatio Ω C a b).val=
      (rootSectionChart Ω C b).val*invOfUnit (rootSectionChart Ω C a).val 1 := by
  dsimp [rootChartRatio,rootSectionChart]
  rw [inverse_mul _ _ (chartNegative LaurentRay.vUnit Ω C a (simpleTotalTransport Ω C)).property.1 (by simp),
    inverse_inverse _ (simpleTotalTransport Ω C).property.1]
  simp only [mul_assoc]
  rw [←mul_assoc (invOfUnit (simpleTotalTransport Ω C).val 1),
    invOfUnit_mul _ 1 (simpleTotalTransport Ω C).property.1,one_mul]

omit [DecidableEq I] in
include hΩ hcoord in
lemma actualPolynomialAdjoint_inverse_finite (f:CompletedPositive LaurentRay.vUnit Ω C)
    (F G:Torus LaurentRay.vUnit Ω)
    (h:∀m,actualPolynomialAdjointCoefficient Ω (rootOrder coord) f.val F m=G m) (m:M) :
    actualPolynomialAdjointCoefficient Ω (rootOrder coord) (invOfUnit f.val 1) G m=F m := by
  have H:=(hahnAction_finite_iff Ω hΩ C coord hcoord f F G).mpr h
  have H':=congrArg (hahnAction (invOfUnit f.val 1)) H
  rw [hahnAction_inverse_cancel _ _ f.property.1] at H'
  have HM:=congrArg (fun x:HahnSeries ℤ (Torus LaurentRay.vUnit Ω)=>x.coeff (rootOrder coord m) m) H'
  simpa only [hahnAction_actual_coeff Ω hΩ,latticeHahn_coeff,ite_true, if_true] using HM.symm

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HomogeneousElementaryExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E)

include hcoord in
lemma root_eval_split (h:Module.Dual ℝ E) {n:ℕ} {m:M} (hm:HasRootDegree C n m) :
    h (e m)=(coord m pc:ℝ)*h (e (simpleRoot C pc))+
      ∑i∈Finset.univ.erase pc,(coord m i:ℝ)*h (e (simpleRoot C i)) := by
  obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
  conv_lhs=>rw [←he,coefficient_simple_expansion C,map_sum,map_sum]
  simp only [map_zsmul,zsmul_eq_mul,hc]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ pc),add_comm]

include hcoord in
lemma nearCut_fiber_negative (h:Module.Dual ℝ E) (hh:NearCut Ω C pc e h)
    (pos:Bool) {n:ℕ} (hn:0<n) {m:M} (hm:HasRootDegree C n m)
    (hb:m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) : h (e m)<0 := by
  have hp0:0≤(coord m pc:ℝ):=by exact_mod_cast hb.1
  have hnp:0<nonpDegree coord pc m:=by
    have H:=fiber_full_degree_bound Ω C coord hcoord pc pos hm hb
    have H0:=nonpDegree_root_nonneg C coord hcoord pc hm
    by_contra hnot
    have hz:nonpDegree coord pc m=0:=le_antisymm (le_of_not_gt hnot) H0
    rw [hz,mul_zero] at H
    omega
  have hnpR:0<(nonpDegree coord pc m:ℝ):=by exact_mod_cast hnp
  have HK:(coord m pc:ℝ)≤(mutationSize Ω C pc:ℝ)*(nonpDegree coord pc m:ℝ):=by
    exact_mod_cast hb.2.trans (fiberUpper_degree_bound Ω C coord hcoord pc pos hm)
  have Habs:(mutationSize Ω C pc:ℝ)*|h (e (simpleRoot C pc))|<1:=by
    have H0:(0:ℝ)<(mutationSize Ω C pc:ℝ)+1:=by positivity
    have H:= (lt_div_iff₀ H0).mp hh.1
    nlinarith [abs_nonneg (h (e (simpleRoot C pc)))]
  have Hsum:(∑i∈Finset.univ.erase pc,(coord m i:ℝ)*h (e (simpleRoot C i)))≤
      -(nonpDegree coord pc m:ℝ):=by
    have hc:∀i,0≤(coord m i:ℝ):=by
      obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
      intro i; rw [hc]; positivity
    change _≤-((∑i∈Finset.univ.erase pc,coord m i:ℤ):ℝ)
    push_cast
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have H:=mul_le_mul_of_nonneg_left (le_of_lt (hh.2 i (Finset.mem_erase.mp hi).1)) (hc i)
    simpa only [mul_neg,mul_one] using H
  have Hk:(coord m pc:ℝ)*h (e (simpleRoot C pc))≤
      (mutationSize Ω C pc:ℝ)*(nonpDegree coord pc m:ℝ)*|h (e (simpleRoot C pc))|:=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hp0).trans
      (mul_le_mul_of_nonneg_right HK (abs_nonneg _))
  rw [root_eval_split C coord hcoord pc e h hm]
  nlinarith [mul_lt_mul_of_pos_right Habs hnpR]

variable (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hcoord he hS hcomp hdeg in
lemma nearCut_noncut_wall (h:Module.Dual ℝ E) (hh:NearCut Ω C pc e h)
    (r:M) (dr:ℕ) (hdr:0<dr) (hr:HasRootDegree C dr r)
    (hg:∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos:Bool) (hp:cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero=>simpa only [coeff_zero_eq_constantCoeff,constantCoeff_one] using
      (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).property.1
  | succ n=>
    rw [coeff_one,ite_eq_right (Nat.succ_ne_zero _)]
    apply Finsupp.ext
    intro m
    change coeff (n+1) (chartZero LaurentRay.vUnit Ω C
      (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val m=0
    by_contra hm
    have HR:=chart_root_of_ne LaurentRay.vUnit Ω C _ _ _ hm
    have HB:=simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg r dr hdr hr h hg pos hp _ _ hm
    have Hneg:=nearCut_fiber_negative Ω C coord hcoord pc e h hh pos (by omega) HR HB
    have Hzero: h (e m)=0:=(chart_three_support LaurentRay.vUnit Ω C
      (h.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).2.1 n m hm
    linarith
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PurePolynomialCoefficients
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (k:M →+ ℤ) (p:M) (hp:k p=1)
lemma read_pure_scalar_monomial (b m:M) (c:K) :
    readFiber v Ω k p hp m
      (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
        (embed v Ω hΩ k p hp (Torus.monomial v Ω b c)))=
    c*readFiber v Ω k p hp m
      (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
        (embed v Ω hΩ k p hp (Torus.X v Ω b))) := by
  classical
  rw [Torus.X,embed_monomial,embed_monomial,pureAction_monomial,pureAction_monomial,map_one,one_mul]
  change (expandZero ((Finsupp.single (off k p hp b)
    ((RatFunc.C c*centeredScalar v (k b) (complementAlpha k p Ω (off k p hp b)))*
      (pureRatio v (complementAlpha k p Ω (off k p hp b)):RatFunc K)))
      (off k p hp m))).coeff (k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)=
    c*((expandZero ((Finsupp.single (off k p hp b)
      (centeredScalar v (k b) (complementAlpha k p Ω (off k p hp b))*
        (pureRatio v (complementAlpha k p Ω (off k p hp b)):RatFunc K)))
      (off k p hp m))).coeff (k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K))
  by_cases ho:off k p hp b=off k p hp m
  · simp only [Finsupp.single_apply,ite_eq_left ho]
    rw [mul_assoc,map_mul,expandZero_constant]
    change ((HahnSeries.single 0 c:HahnSeries ℤ K)*_).coeff (k m)*_=c*(_*_)
    rw [HahnSeries.coeff_single_mul,sub_zero,mul_assoc]
  · simp only [Finsupp.single_apply,ite_eq_right ho,map_zero,HahnSeries.coeff_zero,zero_mul,mul_zero]
end
end ElementaryPositivity.RationalFiber
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber
noncomputable section
variable {M:Type*} [AddCommGroup M]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0) (τ:M →+ ℤ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.purePolynomialCoefficientsRing
local instance purePolynomialCoefficientsAddCommMonoid_rd6f74a_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance purePolynomialCoefficientsAddGroup_rd6f74a_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hΩ in
lemma actual_pure_polynomial (k:M →+ ℤ) (p:M) (hp:k p=1) (hτ:τ p=1)
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ (normalizedSimple Ω p) F m=
      readFiber LaurentRay.vUnit Ω k p hp m
        (pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
          (embed LaurentRay.vUnit Ω hΩ k p hp F)) := by
  classical
  induction F using Finsupp.induction_linear with
  | zero=>simp [actualPolynomialAdjointCoefficient]
  | add F G hF hG=>rw [actualPolynomialAdjointCoefficient_add,map_add,map_add,map_add,hF,hG]
  | single b c=>
    change actualPolynomialAdjointCoefficient Ω τ (normalizedSimple Ω p)
      (Torus.monomial LaurentRay.vUnit Ω b c) m=_
    rw [actualPolynomialAdjointCoefficient_monomial,actual_pure_monomial Ω hΩ τ k p hp hτ]
    exact (read_pure_scalar_monomial LaurentRay.vUnit Ω hΩ k p hp b m c).symm
include hΩ in
lemma actual_pure_finite (k:M →+ ℤ) (p:M) (hp:k p=1) (hτ:τ p=1)
    (F G:Torus LaurentRay.vUnit Ω)
    (h:embed LaurentRay.vUnit Ω hΩ k p hp G=
      pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
        (embed LaurentRay.vUnit Ω hΩ k p hp F)) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ (normalizedSimple Ω p) F m=G m := by
  rw [actual_pure_polynomial Ω hΩ τ k p hp hτ,←h]
  exact readFiber_embedAdd LaurentRay.vUnit Ω k p hp G m
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_CovectorPrescriptions
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (C:(I → ℤ) →+ M) (e:M →+ E)
lemma real_covector_prescribe (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) (w:I → ℝ) :
    ∃J:Module.Dual ℝ E,∀i,J (e (simpleRoot C i))=w i := by
  classical
  obtain ⟨D,hD⟩:=realRootCoordinates_exists C e hC
  refine ⟨∑i,w i • (LinearMap.proj i).comp D,fun i=>?_⟩
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    real_coordinate_simple C e D hD,LinearMap.proj_apply,smul_eq_mul,Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji; simp [hji]
  · simp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GenericAffineProbes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FiniteRayGeometry
noncomputable section
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma generic_for_two_directions_with_probes (T : ℕ → Finset E) (a b k : Module.Dual ℝ E)
    (P : Finset (ℝ×E)) (v:Module.Dual ℝ E) :
    ∃h : Module.Dual ℝ E,(∀N,GenericOffset (T N) 0 a h) ∧
      (∀N,GenericOffset (T N) 0 b h) ∧
      ∀s∈P,(0<(k+s.1 • v) s.2 → 0<(h+s.1 • v) s.2) ∧
        ((k+s.1 • v) s.2<0 → (h+s.1 • v) s.2<0) := by
  classical
  let W : Set E:=⋃N,↑(forbidden (T N) 0 a∪forbidden (T N) 0 b)
  have hc : W.Countable:=Set.countable_iUnion (fun N=>(forbidden (T N) 0 a∪forbidden (T N) 0 b).countable_toSet)
  have hp : ∀w∈W,w∉Submodule.span ℝ {(0:E)}:=by
    intro w hw
    obtain ⟨N,hN⟩:=Set.mem_iUnion.mp hw
    rcases Finset.mem_union.mp hN with hh|hh
    · exact (Finset.mem_filter.mp hh).2
    · exact (Finset.mem_filter.mp hh).2
  obtain ⟨h,h0,havoid,hprobe⟩:=countable_avoid_with_probes W hc 0 hp
    P v k (map_zero k)
  have hGa : ∀N,GenericOffset (T N) 0 a h:=by
    intro N
    refine ⟨h0,?_,?_⟩
    · intro s hs hn
      exact havoid s (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs,hn⟩)⟩)
    · intro s hs t ht hn
      exact havoid _ (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,rfl⟩),hn⟩)⟩)
  have hGb : ∀N,GenericOffset (T N) 0 b h:=by
    intro N
    refine ⟨h0,?_,?_⟩
    · intro s hs hn
      exact havoid s (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs,hn⟩)⟩)
    · intro s hs t ht hn
      exact havoid _ (Set.mem_iUnion.mpr ⟨N,Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,rfl⟩),hn⟩)⟩)
  exact ⟨h,hGa,hGb,hprobe⟩
end
end ElementaryPositivity.FiniteRayGeometry
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C:(I → ℤ) →+ M) (e:M →+ E)
lemma generic_region_path_via_probes (a b k : Module.Dual ℝ E) (P : Finset (ℝ×E)) (v:Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (U : Set (Module.Dual ℝ E))
    (hU : ∀h : Module.Dual ℝ E,
      (∀x∈P,(0<(k+x.1 • v) x.2 → 0<(h+x.1 • v) x.2) ∧
        ((k+x.1 • v) x.2<0 → (h+x.1 • v) x.2<0)) →
      (∀t:ℝ,0≤t → t≤1 → (1-t) • a+t • h∈U) ∧
      (∀t:ℝ,0≤t → t≤1 → (1-t) • h+t • b∈U)) :
    ∃p : GenericLinePath C e a b,p.InRegion C e U := by
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions_with_probes (realRootsThrough e C) a b k P v
  have HH : RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  let s:=segmentBetween C e a h HA HH (fun N=>(Ha N).join (HA N))
  let t:=segmentBetween C e h b HH HB (fun N=>(Hb N).join_reverse (HB N))
  let p:=(GenericLinePath.single C e s).castEnds C e
    (segmentBetween_start C e a h HA HH _) (segmentBetween_finish C e a h HA HH _)
  let q:=(GenericLinePath.single C e t).castEnds C e
    (segmentBetween_start C e h b HH HB _) (segmentBetween_finish C e h b HH HB _)
  have hp : p.InRegion C e U :=
    (segmentBetween_inRegion C e a h HA HH _ (hU h HP).1).castEnds C e _ _
  have hq : q.InRegion C e U :=
    (segmentBetween_inRegion C e h b HH HB _ (hU h HP).2).castEnds C e _ _
  exact ⟨p.trans C e q,hp.trans C e hq⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NearCutGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)

omit [FiniteDimensional ℝ E] in
lemma nearCut_convex {a b:Module.Dual ℝ E} (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (t:ℝ) (ht:0≤t) (ht':t≤1) : NearCut Ω C pc e ((1-t) • a+t • b) := by
  by_cases ht1:t=1
  · subst t
    simpa using hb
  have htt:0<1-t:=sub_pos.mpr (lt_of_le_of_ne ht' ht1)
  constructor
  · rw [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.smul_apply,smul_eq_mul,smul_eq_mul]
    have A:=abs_lt.mp ha.1
    have B:=abs_lt.mp hb.1
    apply abs_lt.mpr
    constructor
    · nlinarith [mul_pos htt (sub_pos.mpr A.1),mul_nonneg ht (sub_nonneg.mpr B.1.le)]
    · nlinarith [mul_pos htt (sub_pos.mpr A.2),mul_nonneg ht (sub_nonneg.mpr B.2.le)]
  · intro i hi
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
    nlinarith [mul_pos htt (sub_pos.mpr (ha.2 i hi)),
      mul_nonneg ht (sub_nonneg.mpr (hb.2 i hi).le)]

omit [FiniteDimensional ℝ E] in
lemma nearCut_of_probes (J k h:Module.Dual ℝ E) (hJ:∀i,J (e (simpleRoot C i))=1)
    (hk:NearCut Ω C pc e k)
    (hh:∀x∈nearCutProbes Ω C pc e,
      (0<(k+x.1 • J) x.2 → 0<(h+x.1 • J) x.2) ∧
      ((k+x.1 • J) x.2<0 → (h+x.1 • J) x.2<0)) : NearCut Ω C pc e h := by
  classical
  have Hp: (1/((mutationSize Ω C pc:ℝ)+1),e (simpleRoot C pc))∈nearCutProbes Ω C pc e:=by
    simp [nearCutProbes]
  have Hn: (-1/((mutationSize Ω C pc:ℝ)+1),e (simpleRoot C pc))∈nearCutProbes Ω C pc e:=by
    simp [nearCutProbes]
  have Hk:=abs_lt.mp hk.1
  constructor
  · apply abs_lt.mpr
    have A:0<(h+(1/((mutationSize Ω C pc:ℝ)+1)) • J) (e (simpleRoot C pc)):=by
      apply (hh _ Hp).1
      simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hJ,mul_one]
      linarith
    have B:(h+(-1/((mutationSize Ω C pc:ℝ)+1)) • J) (e (simpleRoot C pc))<0:=by
      apply (hh _ Hn).2
      simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hJ,mul_one,neg_div]
      linarith
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hJ,mul_one,neg_div] at A B
    constructor <;> linarith
  · intro i hi
    have Hi:(1,e (simpleRoot C i))∈nearCutProbes Ω C pc e:=by
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩,rfl⟩)
    have A:(h+(1:ℝ) • J) (e (simpleRoot C i))<0:=by
      apply (hh _ Hi).2
      simp only [one_smul,LinearMap.add_apply,hJ]
      linarith [hk.2 i hi]
    simp only [one_smul,LinearMap.add_apply,hJ] at A
    linarith

lemma nearCut_path (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b) :
    ∃p:GenericLinePath C e a b,p.InRegion C e {h | NearCut Ω C pc e h} := by
  obtain ⟨J,hJ⟩:=real_covector_prescribe C e hC (fun _=>1)
  apply generic_region_path_via_probes C e a b a (nearCutProbes Ω C pc e) J HA HB
  intro h hh
  have Hh:=nearCut_of_probes Ω C pc e J a h hJ ha hh
  exact ⟨fun t ht ht'=>nearCut_convex Ω C pc e ha Hh t ht ht',
    fun t ht ht'=>nearCut_convex Ω C pc e Hh hb t ht ht'⟩

omit [FiniteDimensional ℝ E] in
lemma nearCut_old_negative {h:Module.Dual ℝ E} (hh:NearCut Ω C pc e h)
    (hp:h (e (simpleRoot C pc))<0) : ∀n,0<n → ∀m,HasRootDegree C n m → h (e m)<0 := by
  have H:∀i,0<(-h) (e (simpleRoot C i)):=by
    intro i
    simp only [LinearMap.neg_apply,neg_pos]
    by_cases hi:i=pc
    · simpa only [hi] using hp
    · linarith [hh.2 i hi]
  intro n hn m hm
  simpa only [LinearMap.neg_apply,neg_pos] using covector_root_pos C e (-h) H hn hm

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PureCutGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.AffineCut
noncomputable section
variable {G:Type*} [Group G]
lemma oldFactor_local (g:G) (u v t:ℝ) (hne:u≠0 ∨ v≠0) (x:G) :
    oldFactor g u v t*(oldGauge g (beforeSide u v t)*x)=oldGauge g (afterSide u v t)*x := by
  by_cases hz:u+t*v=0
  · have hv:v≠0:=by rintro rfl; simp_all
    rw [oldFactor,ite_eq_left hz,(sides_at_zero u v t hz).1,(sides_at_zero u v t hz).2]
    rcases lt_or_gt_of_ne hv with hn|hp
    · simp [oldGauge,hn,show ¬0<v by linarith,←mul_assoc]
    · simp [oldGauge,hp,show ¬v<0 by linarith]
  · rw [oldFactor,ite_eq_right hz,(sides_eq_of_ne u v t hz).1,(sides_eq_of_ne u v t hz).2,one_mul]
lemma oldFactor_telescope (g:G) (u v lo hi:ℝ) (hlohi:lo<hi) (hne:u≠0 ∨ v≠0)
    (hlo:u+lo*v≠0) (hhi:u+hi*v≠0) (T:Finset ℝ) (hmem:∀t∈T,lo<t ∧ t<hi)
    (hcut:∀t,lo<t → t<hi → u+t*v=0 → t∈T) :
    ((T.sort (· ≥ ·)).map (oldFactor g u v)).prod*oldGauge g (decide (0<u+lo*v))=
      oldGauge g (decide (0<u+hi*v)) := by
  classical
  have H:=telescope_sort u v hne (fun _ (x:G)=>x) (fun t x=>oldFactor g u v t*x)
    (fun side x=>oldGauge g side*x) T lo hi hlohi hmem hcut
    (fun t _ x=>oldFactor_local g u v t hne x) 1
  have hid:(T.sort (· ≥ ·)).foldr (fun _ (x:G)=>x) 1=1:=by
    generalize T.sort (· ≥ ·)=l
    induction l <;> simp_all
  have hmul:∀l:List ℝ,∀x:G,l.foldr (fun t x=>oldFactor g u v t*x) x=
      (l.map (oldFactor g u v)).prod*x:=by
    intro l x
    induction l with
    | nil=>simp
    | cons a l ih=>simp only [List.foldr_cons,List.map_cons,List.prod_cons,ih,mul_assoc]
  rw [(sides_eq_of_ne u v lo hlo).2,(sides_eq_of_ne u v hi hhi).1,hid,mul_one,mul_one,hmul] at H
  exact H
end
end ElementaryPositivity.AffineCut

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k:Module.Dual ℝ E) (H:∀N,GenericOffset (realRootsThrough e C N) 0 v k)

include he hdeg H in
omit [FiniteDimensional ℝ E] in
lemma nearCut_letter (a:ℝ) (hh:NearCut Ω C pc e (k+a • v)) :
    comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)=
    AffineCut.oldFactor (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc))
      (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) a := by
  classical
  by_cases hp:(k+a • v) (e (simpleRoot C pc))=0
  · have ha:∃N,a∈lineEvents (realRootsThrough e C N) v k:=⟨1,line_cut_event C pc e L hdeg v k H a hp⟩
    unfold actualLineLetter
    simp only [dite_eq_left ha,dite_eq_left hp]
    have hp':k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))=0:=hp
    rw [AffineCut.oldFactor,ite_eq_left hp']
    by_cases hv:v (e (simpleRoot C pc))<0 <;> simp only [hv,decide_true,decide_false,comparisonOld,↓reduceIte]
  · have hp':k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))≠0:=hp
    rw [AffineCut.oldFactor,ite_eq_right hp']
    by_cases ha:∃N,a∈lineEvents (realRootsThrough e C N) v k
    · obtain ⟨r,d,hd,hr,hv,hg,HE⟩:=actualLineLetter_old Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a ha
      have HC:=nearCut_noncut_wall Ω C coord hcoord pc e he S hS hcomp L hdeg (k+a • v) hh
        r d hd hr hg (decide (0<(k+a • v) (e (simpleRoot C pc))))
        (cutSide_decide ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc) hp)
      have HU:completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
          (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C))=1:=by
        apply Units.ext
        apply Subtype.ext
        exact HC
      rw [HE,HU]
      split_ifs <;> simp
    · simp only [actualLineLetter,dite_eq_right ha,comparisonOld]

include he hdeg H in
omit [FiniteDimensional ℝ E] in
lemma nearCut_line_word (lo hi:ℝ) (hlohi:lo<hi)
    (hlo:lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi:hi∉lineEvents (realRootsThrough e C 1) v k)
    (hh:∀t,lo≤t → t≤hi → NearCut Ω C pc e (k+t • v)) (N:ℕ) (hN:1≤N) :
    comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N)*
      AffineCut.oldGauge (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc)) (decide (0<(k+lo • v) (e (simpleRoot C pc))))=
      AffineCut.oldGauge (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc)) (decide (0<(k+hi • v) (e (simpleRoot C pc)))) := by
  classical
  unfold comparisonWordOld actualLineWord
  rw [List.map_map]
  have HH:=AffineCut.oldFactor_telescope
    (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc))
    (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) lo hi hlohi
    (Or.inl (line_cut_offset_ne C pc e L hdeg v k H))
    (fun hz=>hlo (line_cut_event C pc e L hdeg v k H lo hz))
    (fun hz=>hhi (line_cut_event C pc e L hdeg v k H hi hz))
    (intervalLineEvents C e v k lo hi N) (fun a ha=>(Finset.mem_filter.mp ha).2)
    (fun a hla hah hz=>Finset.mem_filter.mpr ⟨lineEvents_mono (realRootsThrough_mono C e hN) v k
      (line_cut_event C pc e L hdeg v k H a hz),hla,hah⟩)
  rw [show (intervalEventList C e v k lo hi N).map
      ((comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)) ∘
      actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H)=_ from
    List.map_congr_left (fun a ha=>nearCut_letter Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a
      (hh a (Finset.mem_filter.mp ((Finset.mem_sort _).mp ha)).2.1.le
        (Finset.mem_filter.mp ((Finset.mem_sort _).mp ha)).2.2.le))]
  exact HH
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

include he hdeg in
omit [FiniteDimensional ℝ E] in
lemma nearCut_path_word {a b:Module.Dual ℝ E} (p:GenericLinePath C e a b)
    (hh:p.InRegion C e {h | NearCut Ω C pc e h}) (N:ℕ) (hN:1≤N) :
    comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N)*
      AffineCut.oldGauge (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc)) (decide (0<a (e (simpleRoot C pc))))=
      AffineCut.oldGauge (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc)) (decide (0<b (e (simpleRoot C pc)))) := by
  induction p with
  | nil=>simp only [actualPathWord,comparisonWordOld,List.map_nil,List.prod_nil,one_mul]
  | append s p ih=>
    rw [actualPathWord,comparisonWordOld_append,mul_assoc,ih hh.2]
    exact nearCut_line_word Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi s.ordered (s.start_regular 1) (s.finish_regular 1) hh.1 N hN

include he hdeg S hS hcomp in
lemma nearCut_chart_ratio (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc))) :
    covectorNegativeUnit Ω C coord hcoord pc e b*(covectorNegativeUnit Ω C coord hcoord pc e a)⁻¹=
      (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc))⁻¹ := by
  obtain ⟨p,hp⟩:=nearCut_path Ω C pc e hC HA HB ha hb
  have HW:∀N,1≤N → comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N)=
      (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc))⁻¹:=by
    intro N hN
    have H:=nearCut_path_word Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p hp N hN
    simpa only [AffineCut.oldGauge,decide_eq_false (not_lt.mpr hap.le),Bool.false_eq_true,ite_false, if_false,
      decide_eq_true hbp,ite_true, if_true,mul_one] using H
  apply Units.ext
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  have HH:=actualPath_old_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p (max 1 n)
  have Hx:=(oldCoefficientsEqual_equivalence Ω coord pc (max 1 n)).refl
    (covectorNegativeUnit Ω C coord hcoord pc e a)⁻¹
  have H:=oldCoefficientsEqual_mul Ω coord pc (max 1 n) _ _ _ _ HH Hx
  rw [mul_assoc,mul_inv_cancel,mul_one,HW _ (le_max_left _ _)] at H
  exact (H n (le_max_right _ _)).symm
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NearCutSectionCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.nearCutSectionChartsRing
local instance nearCutSectionChartsAddCommMonoid_rd6f74a_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutSectionChartsAddGroup_rd6f74a_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hΩ hcoord he hdeg S hS hcomp in
lemma nearCut_old_section_chart (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc))) :
    (rootSectionChart Ω C (b.toAddMonoidHom.comp e)).val=
      invOfUnit (normalizedSimple Ω (simpleRoot C pc)) 1 := by
  have H:=nearCut_chart_ratio Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hC HA HB ha hb hap hbp
  have HH:=congrArg (fun u:(biSupportedSubring LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc))ˣ=>u.val.val) H
  change (rootChartRatio Ω C (a.toAddMonoidHom.comp e) (b.toAddMonoidHom.comp e)).val=
    raySeries LaurentRay.vUnit Ω (simpleRoot C pc) (shiftedElementary LaurentRay.vUnit 0)⁻¹ at HH
  rw [laurent_shiftedElementary_zero,←normalizedSimple_inverse Ω hΩ] at HH
  rw [rootChartRatio_section,rootSectionChart_negative Ω C (a.toAddMonoidHom.comp e) (nearCut_old_negative Ω C pc e ha hap)] at HH
  have hi:invOfUnit (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1=1:=by
    simpa using mul_invOfUnit (1:PowerSeries (Torus LaurentRay.vUnit Ω)) 1 (by simp)
  simpa only [hi,mul_one] using HH

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NearCutPolynomialSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

include hcoord in
lemma rootOrder_simple : rootOrder coord (simpleRoot C pc)=1 :=
  rootOrder_eq C coord hcoord (simpleRoot_degree C pc)

local instance nearCutPolynomialSeedsRing_rd6f74a_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance nearCutPolynomialSeedsAddCommMonoid_rd6f74a_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutPolynomialSeedsAddGroup_rd6f74a_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include he hdeg hS hcomp in
lemma nearCut_old_positive_seed_oai (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc)))
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (m:M) :
    polynomialSectionCoefficient Ω C coord (b.toAddMonoidHom.comp e) F m=F' m := by
  unfold polynomialSectionCoefficient
  rw [nearCut_old_section_chart Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hC HA HB ha hb hap hbp]
  apply actualPolynomialAdjoint_inverse_finite Ω hΩ C coord hcoord (simpleCompleted Ω C coord hcoord pc) F' F
  intro x
  exact actual_pure_finite Ω hΩ (rootOrder coord) (pureDegree coord pc) (simpleRoot C pc)
    (pureDegree_simple_self C coord hcoord pc) (rootOrder_simple C coord hcoord pc) F' F hF x

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.QuantumTorus.nearCut_old_positive_seed_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.QuantumTorus.nearCut_old_positive_seed_oai.{u_1, u_2, u_3}
