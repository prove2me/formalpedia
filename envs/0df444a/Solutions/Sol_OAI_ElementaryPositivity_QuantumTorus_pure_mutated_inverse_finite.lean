-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.pure_mutated_inverse_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:16.233597+00:00
-- url     : https://prove2.me/submissions/a825e6b4-cae2-4e66-810f-7b71687dd2fd

import Mathlib
import Definitions.Def_OAIQ368Chrom009
import Definitions.Def_OAIQ368Chrom012
import Definitions.Def_OAIQ368Chrom014

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
noncomputable section
variable {K : Type*} [Field K]

lemma pureRatio_neg (v : Kˣ) (t : ℤ) :
    scaleAction v (Multiplicative.ofAdd t) (pureRatio v (-t))=(pureRatio v t)⁻¹ := by
  apply mul_left_cancel (a:=pureRatio v t)
  rw [←pureRatio_add,add_neg_cancel,pureRatio_zero,mul_inv_cancel]
end
end ElementaryPositivity.RationalFiber

end
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalCocycleExt
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K] (v : Kˣ)
lemma cocycle_eq_zpow (c : ℤ → (RatFunc K)ˣ) (h0 : c 0=1)
    (hc : ∀t u,c (t+u)=c t*scaleAction v (Multiplicative.ofAdd t) (c u)) (t : ℤ) :
    c t=((⟨c 1,Multiplicative.ofAdd 1⟩ : PureExtension v)^t).left := by
  have H:=map_zpow (cocycleLift v c h0 hc) (Multiplicative.ofAdd 1) t
  rw [←ofAdd_zsmul,smul_eq_mul,mul_one] at H
  exact congrArg SemidirectProduct.left H
lemma cocycle_ext (c d : ℤ → (RatFunc K)ˣ) (hc0 : c 0=1) (hd0 : d 0=1)
    (hc : ∀t u,c (t+u)=c t*scaleAction v (Multiplicative.ofAdd t) (c u))
    (hd : ∀t u,d (t+u)=d t*scaleAction v (Multiplicative.ofAdd t) (d u))
    (h1 : c 1=d 1) : c=d := by
  funext t
  rw [cocycle_eq_zpow v c hc0 hc,cocycle_eq_zpow v d hd0 hd,h1]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalCutIdentity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)
lemma oppositeInverseRatio_one_val : (oppositeInverseRatio v 1:RatFunc K)=
    1+RatFunc.C (v:K)*(RatFunc.X:RatFunc K)⁻¹ := by
  have H:=pureRatio_neg v (-1)
  change scaleAction v (Multiplicative.ofAdd (-1)) (pureRatio v 1)=(pureRatio v (-1))⁻¹ at H
  rw [pureRatio_one] at H
  change reciprocal (↑((pureRatio v (-1))⁻¹):RatFunc K)=_
  rw [←H,scaleAction_val]
  change reciprocal (scale (v^(-2*(-1:ℤ))) (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X))=_
  simp only [map_add,map_one,map_mul,scale_constant,scale_X,
    reciprocal_constant,reciprocal_X]
  rw [←mul_assoc,←map_mul,←Units.val_mul,←zpow_neg_one,←zpow_add]
  norm_num
lemma cutRatio_one : shearRatio v 1*pureRatio v 1=oppositeInverseRatio v 1 := by
  apply Units.ext
  rw [Units.val_mul,shearRatio_val,pureRatio_one,oppositeInverseRatio_one_val]
  change RatFunc.C (↑(v^((1:ℤ)*1)):K)*RatFunc.X^(-(1:ℤ))*
    (1+RatFunc.C (↑(v⁻¹):K)*RatFunc.X)=_
  simp only [mul_one,zpow_one,zpow_neg_one,Units.val_inv_eq_inv_val,map_inv₀]
  have hx : (RatFunc.X:RatFunc K)≠0:=RatFunc.X_ne_zero
  have hv : RatFunc.C (v:K)≠0:=(map_ne_zero RatFunc.C).2 v.ne_zero
  field_simp
  ring
lemma cutRatio (t : ℤ) : shearRatio v t*pureRatio v t=oppositeInverseRatio v t := by
  have H:=cocycle_ext v (fun t=>shearRatio v t*pureRatio v t) (oppositeInverseRatio v)
    (by simp) (by simp) (by
      intro t u
      rw [shearRatio_add,pureRatio_add,map_mul]
      simp only [mul_assoc,mul_left_comm,mul_comm]) (oppositeInverseRatio_add v) (cutRatio_one v)
  exact congrFun H t

variable (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
lemma rational_cut_identity :
    (shearActionHom v Ω α).comp (pureActionHom v Ω α)=oppositeInverseActionHom v Ω α := by
  apply RingHom.ext
  intro f
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=
    FiberTorus.gaugeAdd v Ω α _ f
  rw [FiberTorus.gauge_comp]
  have HH : (fun t=>(pureRatio v t:RatFunc K)*(shearRatio v t:RatFunc K))=
      fun t=>(oppositeInverseRatio v t:RatFunc K) := by
    funext t
    rw [mul_comm,←Units.val_mul,cutRatio]
  rw [HH]
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
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalShearEmbedding
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
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
lemma centeredScalar_shear (n t : ℤ) :
    centeredScalar v (n-t) t=centeredScalar v n t*(shearRatio v t:RatFunc K) := by
  rw [shearRatio_val,centeredScalar,centeredScalar]
  rw [show -(n-t)*t= -n*t+t*t by ring,zpow_add,Units.val_mul,map_mul,
    sub_eq_add_neg,zpow_add₀ RatFunc.X_ne_zero]
  ring
include hΩ in
lemma shearAction_embed_monomial (m : M) (a : K) :
    shearActionHom v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.monomial v Ω m a))=
      embed v Ω hΩ k p hp (Torus.monomial v Ω (mutationShear Ω p m) a) := by
  rw [embed_monomial,embed_monomial]
  change FiberTorus.gauge v _ _ _ _ _ (FiberTorus.monomial v _ _ _ _)=_
  rw [FiberTorus.gauge_monomial]
  have Hoff : off k p hp (mutationShear Ω p m)=off k p hp m := by
    change off k p hp (m-Ω p m • p)=_
    rw [map_sub,map_zsmul,off_p,smul_zero,sub_zero]
  have Hk : k (mutationShear Ω p m)=k m-Ω p m := by
    change k (m-Ω p m • p)=_
    rw [map_sub,map_zsmul,hp,smul_eq_mul,mul_one]
  rw [Hoff,Hk,complement_pairing Ω hΩ k p hp m,centeredScalar_shear]
  rw [mul_assoc]
include hΩ in
lemma shearAction_embed (f : Torus v Ω) :
    shearActionHom v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp f)=
      embed v Ω hΩ k p hp
        (Torus.push v Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p) f) := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,hf,hg]
  | single m a=>
    change _=embed v Ω hΩ k p hp (Torus.push v Ω Ω _ _ (Torus.monomial v Ω m a))
    rw [Torus.push_monomial]
    exact shearAction_embed_monomial v Ω hΩ k p hp m a
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_RationalTorusFaithful
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
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
local instance instAddCommMonoidTorus_1_re9aac5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_re9aac5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_re9aac5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_re9aac5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance monomialConjugationAddCommMonoid_re9aac5_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_re9aac5_1 : AddGroup (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_2_re9aac5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_re9aac5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalLaurentFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance rationalLaurentFaithfulRing_re9aac5_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rationalLaurentFaithfulNonUnitalSemiring_re9aac5_1 : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.rationalLaurentFaithfulNonUnitalNonAssocSemiring
lemma expandFiber_monomial_coeff (l : k.ker) (a : RatFunc K) (n : ℤ) :
    (expandFiber v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff n=
      Torus.monomial v Ω (n • p+(l:M)) ((expandZero a).coeff n*(↑(v^(n*Ω p l)):K)) := by
  change (expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff n=_
  rw [expandFiberAdd_monomial,HahnSeries.coeff_mul_single_zero]
  change Torus.monomial v Ω (n • p) ((expandZero a).coeff n)*Torus.X v Ω l=_
  simp only [Torus.X,Torus.monomial_mul_monomial,mul_one,map_zsmul,AddMonoidHom.zsmul_apply,
    smul_eq_mul]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentPureAction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0) (p : M)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_2
local instance instAddCommMonoidTorus_re9aac5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_re9aac5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalSemiringTorus_2
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorus_2
lemma purePower_eq (f : PowerSeries K) :
    purePower v Ω hΩ p f=HahnSeries.ofPowerSeries ℤ (Torus v Ω) (raySeries v Ω p f) := by
  apply HahnSeries.ext
  funext n
  change Torus.monomial v Ω (n • p) ((HahnSeries.ofPowerSeries ℤ K f).coeff n)=_
  rcases le_or_gt 0 n with hn|hn
  · lift n to ℕ using hn with j hj
    rw [HahnSeries.ofPowerSeries_apply_coeff,HahnSeries.ofPowerSeries_apply_coeff,coeff_raySeries]
    simp only [natCast_zsmul]
  · have H : (HahnSeries.ofPowerSeries ℤ K f).coeff n=0 := by
      rw [HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_of_notMem_range
      rintro ⟨a,ha⟩
      change (a:ℤ)=n at ha
      omega
    have H' : (HahnSeries.ofPowerSeries ℤ (Torus v Ω) (raySeries v Ω p f)).coeff n=0 := by
      rw [HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_of_notMem_range
      rintro ⟨a,ha⟩
      change (a:ℤ)=n at ha
      omega
    rw [H,H',Torus.monomial_zero]
lemma purePower_commutation (m : M) (f : PowerSeries K) :
    HahnSeries.single 0 (Torus.X v Ω m)*purePower v Ω hΩ p f=
      purePower v Ω hΩ p (rescale (↑(v^(-2*Ω p m)):K) f)*
        HahnSeries.single 0 (Torus.X v Ω m) := by
  have H:=raySeries_twist v Ω hΩ p m (rescale (↑(v^(-2*Ω p m)):K) f)
  rw [rescale_rescale,←Units.val_mul,←zpow_add,
    show -2*Ω p m+2*Ω p m=0 by ring,zpow_zero,Units.val_one,rescale_one] at H
  have HH:=congrArg (HahnSeries.ofPowerSeries ℤ (Torus v Ω)) H
  rw [purePower_eq,purePower_eq]
  simpa only [map_mul,HahnSeries.ofPowerSeries_C,HahnSeries.C_apply,RingHom.id_apply] using HH.symm
lemma purePower_scalar_commute (a : RatFunc K) (f : PowerSeries K) :
    expandScalar v Ω hΩ p a*purePower v Ω hΩ p f=
      purePower v Ω hΩ p f*expandScalar v Ω hΩ p a := by
  change (laurentRayHom v Ω p (hΩ p)) (expandZero a)*
    (laurentRayHom v Ω p (hΩ p)) (HahnSeries.ofPowerSeries ℤ K f)=_
  rw [←map_mul,mul_comm,map_mul]
  rfl
lemma expandedPure_shifted
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    expandScalar v Ω hΩ p (pureRatio v t:RatFunc K)*
      purePower v Ω hΩ p (shiftedElementary v t)=purePower v Ω hΩ p (shiftedElementary v 0) := by
  have H:=congrArg (laurentRayHom v Ω p (hΩ p)) (expandedPure_times_shift v hq t)
  simpa only [map_mul,expandScalar,purePower,RingHom.comp_apply] using H

variable (k : M →+ ℤ)
lemma expand_pure_intertwine
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :
    expandFiber v Ω hΩ k p (pureAction v (complementOmega k Ω) (complementAlpha k p Ω) f)*
      (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))=
    (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*expandFiber v Ω hΩ k p f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,add_mul,mul_add,hf,hg]
  | single l a=>
    change expandFiber v Ω hΩ k p
      (pureAction v _ _ (FiberTorus.monomial v _ _ l a))*_=_
    rw [pureAction_monomial]
    change expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l
      (a*(pureRatio v (Ω p l):RatFunc K)))*_= _*expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a)
    rw [expandFiberAdd_monomial,expandFiberAdd_monomial]
    change (expandScalar v Ω hΩ p (a*(pureRatio v (Ω p l):RatFunc K))*
      HahnSeries.single 0 (Torus.X v Ω l))*purePower v Ω hΩ p (shiftedElementary v 0)=
      purePower v Ω hΩ p (shiftedElementary v 0)*
        (expandScalar v Ω hΩ p a*HahnSeries.single 0 (Torus.X v Ω l))
    rw [map_mul,mul_assoc,mul_assoc,purePower_commutation]
    have H : rescale (↑(v^(-2*Ω p l)):K) (shiftedElementary v 0)=shiftedElementary v (Ω p l) := by
      rw [shiftedElementary_zero]
      rfl
    rw [H,←mul_assoc (expandScalar v Ω hΩ p (pureRatio v (Ω p l):RatFunc K)),
      expandedPure_shifted v Ω hΩ p hq,←mul_assoc,purePower_scalar_commute,mul_assoc]
lemma expand_pure_conjugate
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :
    expandFiber v Ω hΩ k p (pureAction v (complementOmega k Ω) (complementAlpha k p Ω) f)=
      innerHom (pureLaurentUnit v Ω hΩ p) (expandFiber v Ω hΩ k p f) := by
  have H:=congrArg (fun x : HahnSeries ℤ (Torus v Ω)=>x*↑((pureLaurentUnit v Ω hΩ p)⁻¹))
    (expand_pure_intertwine v Ω hΩ p k hq f)
  have hu : (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*↑((pureLaurentUnit v Ω hΩ p)⁻¹)=1 :=
    (pureLaurentUnit v Ω hΩ p).val_inv
  change _=(↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*
    expandFiber v Ω hΩ k p f*↑((pureLaurentUnit v Ω hΩ p)⁻¹)
  simpa only [mul_assoc,hu,mul_one] using H
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedPureComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_4
local instance instNonUnitalSemiringTorus_4_re9aac5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_4_re9aac5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma completed_expand_pure
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p) (completedPureAction v _ _ f)=
      innerHom (completedPureUnit v Ω hΩ p) (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  apply PowerSeries.ext
  intro d
  change expandFiber v Ω hΩ k p
    (coeff d (completedPureAction v (complementOmega k Ω) (complementAlpha k p Ω) f))=
    coeff d (PowerSeries.C (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*
      PowerSeries.map (expandFiber v Ω hΩ k p) f*
        PowerSeries.C (↑((pureLaurentUnit v Ω hΩ p)⁻¹):HahnSeries ℤ (Torus v Ω)))
  change expandFiber v Ω hΩ k p
    (coeff d (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).toRingHom f))=_
  rw [coeff_map,coeff_mul_C,coeff_C_mul,coeff_map]
  exact expand_pure_conjugate v Ω hΩ p k hq (coeff d f)
lemma innerHom_one {A : Type*} [Ring A] (a : A) : innerHom (1:Aˣ) a=a := by
  simp [innerHom]
lemma innerHom_mul {A : Type*} [Ring A] (u w : Aˣ) (a : A) :
    innerHom (u*w) a=innerHom u (innerHom w a) := by
  simp [innerHom,mul_assoc]
lemma innerHom_inv_cancel {A : Type*} [Ring A] (u : Aˣ) (a : A) :
    innerHom u⁻¹ (innerHom u a)=a := by
  rw [←innerHom_mul,inv_mul_cancel,innerHom_one]
lemma innerHom_cancel_inv {A : Type*} [Ring A] (u : Aˣ) (a : A) :
    innerHom u (innerHom u⁻¹ a)=a := by
  rw [←innerHom_mul,mul_inv_cancel,innerHom_one]
lemma completed_expand_pure_inverse
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiber v Ω hΩ k p) ((completedPureAction v _ _).symm f)=
      innerHom (completedPureUnit v Ω hΩ p)⁻¹ (PowerSeries.map (expandFiber v Ω hΩ k p) f) := by
  have H:=completed_expand_pure v Ω hΩ k p hq ((completedPureAction v _ _).symm f)
  rw [RingEquiv.apply_symm_apply] at H
  have HH:=congrArg (innerHom (completedPureUnit v Ω hΩ p)⁻¹) H
  rw [innerHom_inv_cancel] at HH
  exact HH.symm
end
end ElementaryPositivity.RationalFiber

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
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedCutAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)

lemma completed_cut_identity (f : PowerSeries (FiberTorus v Ω α)) :
    completedShearAction v Ω α (completedPureAction v Ω α f)=
      PowerSeries.map (oppositeInverseActionHom v Ω α) f := by
  apply PowerSeries.ext
  intro D
  change coeff D (PowerSeries.map (shearActionHom v Ω α)
    (PowerSeries.map (pureActionHom v Ω α) f))=_
  simp only [coeff_map]
  exact congrArg (fun F : FiberTorus v Ω α →+* FiberTorus v Ω α=>F (coeff D f))
    (rational_cut_identity v Ω α)

lemma completedOppositeInverseAction_eq (f : PowerSeries (FiberTorus v Ω α)) :
    completedOppositeInverseAction v Ω α f=
      PowerSeries.map (oppositeInverseActionHom v Ω α) f :=
  completed_cut_identity v Ω α f

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteFiberInfinity
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
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
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
lemma expandInfinity_centeredScalar (n a : ℤ) (b : K) :
    expandInfinity (RatFunc.C b*centeredScalar v n a)=
      HahnSeries.single (-n) (b*(↑(v^(-n*a)):K)) := by
  rw [centeredScalar,←mul_assoc,←map_mul,map_mul,expandInfinity_constant,expandInfinity_X_zpow]
  simp [HahnSeries.C]

lemma readFiberInfinity_monomial (m n : M) (a : K) :
    readFiberInfinity v Ω k p hp m (embedAdd v Ω k p hp (Torus.monomial v Ω n a))=
      (Torus.monomial v Ω n a) m := by
  classical
  rw [embedAdd_monomial]
  change (expandInfinity ((Finsupp.single (off k p hp n)
    (RatFunc.C a*centeredScalar v (k n) (complementAlpha k p Ω (off k p hp n))))
    (off k p hp m))).coeff (-k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)=Finsupp.single n a m
  by_cases ho : off k p hp n=off k p hp m
  · rw [Finsupp.single_apply,ite_eq_left ho,expandInfinity_centeredScalar]
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
lemma readFiberInfinity_embedAdd (f : Torus v Ω) (m : M) :
    readFiberInfinity v Ω k p hp m (embedAdd v Ω k p hp f)=f m := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp [map_add,hf,hg]
  | single n a=>exact readFiberInfinity_monomial v Ω k p hp m n a
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_PureCutTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α β : M →+ ℤ) (hβ : ∀m,β m= -α m)

lemma fiberReciprocal_oppositeInverse (f : FiberTorus v Ω α) :
    fiberReciprocal v Ω α β hβ (oppositeInverseActionHom v Ω α f)=
      pureActionInvHom v Ω β (fiberReciprocal v Ω α β hβ f) := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,hf,hg]
  | single m a=>
    change fiberReciprocalAdd v Ω α β (FiberTorus.gaugeAdd v Ω α _
      (FiberTorus.monomial v Ω α m a))=
      FiberTorus.gaugeAdd v Ω β _ (fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α m a))
    rw [FiberTorus.gaugeAdd_monomial,fiberReciprocalAdd_monomial,
      fiberReciprocalAdd_monomial,FiberTorus.gaugeAdd_monomial]
    congr 1
    rw [map_mul,hβ]
    congr 1
    simp only [oppositeInverseRatio,Units.val_inv_eq_inv_val,reciprocalUnit_val,map_inv₀]
    have H:=congrArg (fun F : RatFunc K →+* RatFunc K=>F (↑(pureRatio v (-α m)):RatFunc K))
      reciprocal_involutive
    change reciprocal (reciprocal (↑(pureRatio v (-α m)):RatFunc K))=_ at H
    rw [H]
    rfl

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInfinityCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_10
local instance instNonUnitalSemiringTorus_10_re9aac5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_10_re9aac5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma completed_expand_opposite_inverse
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (completedOppositeInverseAction v _ _ f)=
    innerHom (completedPureUnit v Ω hΩ (-p))⁻¹
      (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) f) := by
  calc
    _=PowerSeries.map (expandFiber v Ω hΩ k (-p))
        ((completedPureAction v (complementOmega k Ω) (complementAlpha k (-p) Ω)).symm
          (PowerSeries.map (reciprocalFiber v Ω k p) f)) := by
      rw [completedOppositeInverseAction_eq]
      apply PowerSeries.ext
      intro d
      change expandFiber v Ω hΩ k (-p)
        (reciprocalFiber v Ω k p (oppositeInverseActionHom v _ _ (coeff d f)))=
        expandFiber v Ω hΩ k (-p)
          (pureActionInvHom v _ _ (reciprocalFiber v Ω k p (coeff d f)))
      exact congrArg (expandFiber v Ω hΩ k (-p))
        (fiberReciprocal_oppositeInverse v (complementOmega k Ω) (complementAlpha k p Ω)
          (complementAlpha k (-p) Ω) (complementAlpha_neg_p Ω k p) (coeff d f))
    _=innerHom (completedPureUnit v Ω hΩ (-p))⁻¹
        (PowerSeries.map (expandFiber v Ω hΩ k (-p))
          (PowerSeries.map (reciprocalFiber v Ω k p) f)) :=
      completed_expand_pure_inverse v Ω hΩ k (-p) hq _
    _=_ := by
      congr 1
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_InfinityExpansionFaithful
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_11
local instance instNonUnitalSemiringTorus_11_re9aac5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_11_re9aac5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma expandFiberInfinity_monomial_coeff (l : k.ker) (a : RatFunc K) (n : ℤ) :
    (expandFiberInfinity v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff n=
      Torus.monomial v Ω (n • (-p)+(l:M)) ((expandInfinity a).coeff n*(↑(v^(n*Ω (-p) l)):K)) := by
  change (expandFiber v Ω hΩ k (-p) (fiberReciprocalAdd v (complementOmega k Ω)
    (complementAlpha k p Ω) (complementAlpha k (-p) Ω) (FiberTorus.monomial v _ _ l a))).coeff n=_
  rw [fiberReciprocalAdd_monomial,expandFiber_monomial_coeff]
  rfl

lemma expandFiberInfinity_read_monomial (m : M) (l : k.ker) (a : RatFunc K) :
    ((expandFiberInfinity v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff (-k m)) m=
      readFiberInfinity v Ω k p hp m (FiberTorus.monomial v _ _ l a) := by
  classical
  rw [expandFiberInfinity_monomial_coeff]
  simp only [neg_smul,smul_neg,neg_neg,map_neg,AddMonoidHom.neg_apply,neg_mul_neg]
  change Finsupp.single (k m • p+(l:M))
      ((expandInfinity a).coeff (-k m)*(↑(v^(k m*Ω p l)):K)) m=
    (expandInfinity ((Finsupp.single l a) (off k p hp m))).coeff (-k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)
  by_cases H : l=off k p hp m
  · subst l
    rw [split_sum k p hp,Finsupp.single_eq_same,Finsupp.single_eq_same]
    rfl
  · have hm : k m • p+(l:M)≠m:=by
      intro hh
      have HO:=congrArg (off k p hp) hh
      simp only [map_add,map_zsmul,off_p,smul_zero,off_complement,zero_add] at HO
      exact H HO
    rw [Finsupp.single_eq_of_ne (Ne.symm hm),Finsupp.single_eq_of_ne (Ne.symm H),map_zero,
      HahnSeries.coeff_zero,zero_mul]
lemma expandFiberInfinity_read (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) (m : M) :
    ((expandFiberInfinity v Ω hΩ k p f).coeff (-k m)) m=readFiberInfinity v Ω k p hp m f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [_root_.map_add,HahnSeries.coeff_add,Finsupp.add_apply,hf,hg]
  | single l a=>exact expandFiberInfinity_read_monomial v Ω hΩ k p hp m l a

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InfinityLaurentFinite
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.infinityLaurentFiniteRing
local instance infinityLaurentFiniteAddCommMonoid_re9aac5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance infinityLaurentFiniteAddGroup_re9aac5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance infinityLaurentFiniteNonUnitalSemiring_re9aac5_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance infinityLaurentFiniteNonUnitalNonAssocSemiring_re9aac5_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
include hp in
lemma expandFiberInfinity_off_diagonal
    (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))
    (z : ℤ) (m : M) (h : z≠-k m) :
    ((expandFiberInfinity v Ω hΩ k p f).coeff z) m=0 := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,HahnSeries.coeff_add,Finsupp.add_apply,hf,hg,add_zero]
  | single l a=>
    change ((expandFiberInfinity v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff z) m=0
    rw [expandFiberInfinity_monomial_coeff v Ω hΩ k p l a z]
    apply Finsupp.single_eq_of_ne
    intro hm
    apply h
    have H:=congrArg k hm
    have hl : k (l:M)=0 := l.property
    simp only [map_add,map_zsmul,map_neg,hp,hl,smul_eq_mul,add_zero,mul_neg,mul_one] at H
    omega

lemma expandFiberInfinity_embed_coeff (f : Torus v Ω) (z : ℤ) (m : M) :
    ((expandFiberInfinity v Ω hΩ k p (embed v Ω hΩ k p hp f)).coeff z) m=
      if z=-k m then f m else 0 := by
  by_cases hz : z=-k m
  · rw [ite_eq_left hz,hz,expandFiberInfinity_read v Ω hΩ k p hp]
    exact readFiberInfinity_embedAdd v Ω k p hp f m
  · rw [ite_eq_right hz]
    exact expandFiberInfinity_off_diagonal v Ω hΩ k p hp _ z m hz

end
end ElementaryPositivity.RationalFiber

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
local instance latticeHahnAddCommMonoid_re9aac5_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_re9aac5_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance polynomialAdjointCoefficientsAddCommMonoid_re9aac5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_re9aac5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualCoefficientsAddCommMonoid_re9aac5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_re9aac5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualScalarCoefficientsAddCommMonoid_re9aac5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_re9aac5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_re9aac5_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid_re9aac5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup_re9aac5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring_re9aac5_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring_re9aac5_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
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
local instance purePolynomialCoefficientsAddCommMonoid_re9aac5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance purePolynomialCoefficientsAddGroup_re9aac5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
lemma actual_pure_order_independent (σ:M →+ ℤ) (p:M) (hτ:τ p=1) (hσ:σ p=1)
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ (normalizedSimple Ω p) F m=
      actualPolynomialAdjointCoefficient Ω σ (normalizedSimple Ω p) F m := by
  rw [actual_pure_polynomial Ω hΩ τ τ p hτ hτ,
    actual_pure_polynomial Ω hΩ σ τ p hτ hσ]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FinitePureMutation
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
noncomputable section
lemma constantCoeff_inner_const_inv {A:Type*} [Ring A] (u:Aˣ) (f:PowerSeries A) :
    constantCoeff (innerHom (Units.map (PowerSeries.C (R:=A)) u)⁻¹ f)=
      innerHom u⁻¹ (constantCoeff f) := by
  change constantCoeff (PowerSeries.C u.inv*f*PowerSeries.C u.val)=u.inv*constantCoeff f*u.val
  rw [map_mul,map_mul,constantCoeff_C,constantCoeff_C]

variable {M:Type*} [AddCommGroup M]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (k:M →+ ℤ) (p:M) (hp:k p=1)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.finitePureMutationRing
local instance finitePureMutationAddCommMonoid_re9aac5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance finitePureMutationAddGroup_re9aac5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance finitePureMutationNonUnitalSemiring_re9aac5_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.finitePureMutationNonUnitalNonAssocSemiring
lemma expandFiberInfinity_lattice (F:Torus LaurentRay.vUnit Ω) :
    expandFiberInfinity LaurentRay.vUnit Ω hΩ k p (embed LaurentRay.vUnit Ω hΩ k p hp F)=
      latticeHahn LaurentRay.vUnit Ω (-k) F := by
  apply HahnSeries.ext
  funext j
  apply Finsupp.ext
  intro m
  rw [expandFiberInfinity_embed_coeff LaurentRay.vUnit Ω hΩ k p hp,latticeHahn_coeff]
  rfl

lemma pureLaurentUnit_actual_val (q:M) :
    (pureLaurentUnit LaurentRay.vUnit Ω hΩ q).val=
      ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) (normalizedSimple Ω q) := by
  change purePower LaurentRay.vUnit Ω hΩ q (shiftedElementary LaurentRay.vUnit 0)=_
  rw [purePower_eq,laurent_shiftedElementary_zero]
  rfl
lemma pureLaurentUnit_actual_inv (q:M) :
    ((pureLaurentUnit LaurentRay.vUnit Ω hΩ q)⁻¹).val=
      ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) (invOfUnit (normalizedSimple Ω q) 1) := by
  change purePower LaurentRay.vUnit Ω hΩ q (shiftedElementary LaurentRay.vUnit 0)⁻¹=_
  rw [purePower_eq,laurent_shiftedElementary_zero,normalizedSimple_inverse Ω hΩ]

lemma inner_pure_hahn (q:M) (x:HahnSeries ℤ (Torus LaurentRay.vUnit Ω)) :
    innerHom (pureLaurentUnit LaurentRay.vUnit Ω hΩ q) x=hahnAction (normalizedSimple Ω q) x := by
  change (pureLaurentUnit LaurentRay.vUnit Ω hΩ q).val*x*((pureLaurentUnit LaurentRay.vUnit Ω hΩ q)⁻¹).val=_
  rw [pureLaurentUnit_actual_val,pureLaurentUnit_actual_inv]
  rfl

lemma expand_opposite_inverse_actual
    (f:FiberTorus LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)) :
    expandFiberInfinity LaurentRay.vUnit Ω hΩ k p
      (oppositeInverseActionHom LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω) f)=
      innerHom (pureLaurentUnit LaurentRay.vUnit Ω hΩ (-p))⁻¹
        (expandFiberInfinity LaurentRay.vUnit Ω hΩ k p f) := by
  have hq:∀n:ℕ,1-(↑(LaurentRay.vUnit^(-2:ℤ)):LaurentSeries ℚ)^(n+1)≠0:=by
    intro n
    rw [LaurentRay.vUnit_zpow]
    exact UnitSelections.laurent_q_not_root n
  have H:=completed_expand_opposite_inverse LaurentRay.vUnit Ω hΩ k p hq (PowerSeries.C f)
  rw [completedOppositeInverseAction_eq,PowerSeries.map_C,PowerSeries.map_C] at H
  have H0:=congrArg constantCoeff H
  rw [constantCoeff_C,completedPureUnit,constantCoeff_inner_const_inv,PowerSeries.map_C,constantCoeff_C] at H0
  exact H0

include hΩ in
lemma finite_cut_hahn (F F':Torus LaurentRay.vUnit Ω)
    (hF:embed LaurentRay.vUnit Ω hΩ k p hp F=
      pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
        (embed LaurentRay.vUnit Ω hΩ k p hp F')) :
    hahnAction (normalizedSimple Ω (-p))
      (latticeHahn LaurentRay.vUnit Ω (-k)
        (Torus.push LaurentRay.vUnit Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p) F))=
      latticeHahn LaurentRay.vUnit Ω (-k) F' := by
  have HC:=congrArg (fun g:FiberTorus LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω) →+*
      FiberTorus LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)=>
        g (embed LaurentRay.vUnit Ω hΩ k p hp F'))
      (rational_cut_identity LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω))
  change shearActionHom LaurentRay.vUnit _ _
      (pureAction LaurentRay.vUnit _ _ (embed LaurentRay.vUnit Ω hΩ k p hp F'))=
      oppositeInverseActionHom LaurentRay.vUnit _ _ (embed LaurentRay.vUnit Ω hΩ k p hp F') at HC
  rw [←hF,shearAction_embed LaurentRay.vUnit Ω hΩ k p hp F] at HC
  have HE:=expand_opposite_inverse_actual Ω hΩ k p (embed LaurentRay.vUnit Ω hΩ k p hp F')
  rw [←HC] at HE
  have HH:=congrArg (innerHom (pureLaurentUnit LaurentRay.vUnit Ω hΩ (-p))) HE
  rw [innerHom_cancel_inv,inner_pure_hahn,expandFiberInfinity_lattice Ω hΩ k p hp,
    expandFiberInfinity_lattice Ω hΩ k p hp] at HH
  exact HH

include hΩ in
lemma finite_cut_actual (τ:M →+ ℤ) (hτ:τ (-p)=1) (F F':Torus LaurentRay.vUnit Ω)
    (hF:embed LaurentRay.vUnit Ω hΩ k p hp F=
      pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
        (embed LaurentRay.vUnit Ω hΩ k p hp F')) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ (normalizedSimple Ω (-p))
      (Torus.push LaurentRay.vUnit Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p) F) m=F' m := by
  have HH:=congrArg (fun x:HahnSeries ℤ (Torus LaurentRay.vUnit Ω)=>x.coeff ((-k) m) m)
    (finite_cut_hahn Ω hΩ k p hp F F' hF)
  rw [hahnAction_actual_coeff Ω hΩ,latticeHahn_coeff,ite_eq_left rfl] at HH
  rw [actual_pure_order_independent Ω hΩ τ (-k) (-p) hτ (by simp [hp])]
  exact HH
end
end ElementaryPositivity.RationalFiber

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

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.nearCutPolynomialSeedsRing
local instance nearCutPolynomialSeedsAddCommMonoid_re9aac5_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutPolynomialSeedsAddGroup_re9aac5_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma pure_mutated_inverse_finite_oai
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (m:M) :
    actualPolynomialAdjointCoefficient Ω (rootOrder (mutatedCoordinates Ω C coord pc))
      (invOfUnit (normalizedSimple Ω (-simpleRoot C pc)) 1) F' m=
      mutationTorusPush Ω hΩ C pc false LaurentRay.vUnit F m := by
  let C':=(mutatedRoots Ω C pc)
  let coord':=mutatedCoordinates Ω C coord pc
  have hc:∀d,coord' (C' d)=d:=mutatedCoordinates_retraction Ω C coord hcoord pc
  have hp:rootOrder coord' (-simpleRoot C pc)=1:=by
    rw [←mutatedRoot_p Ω C pc]
    exact rootOrder_simple C' coord' hc pc
  have H:=actualPolynomialAdjoint_inverse_finite Ω hΩ C' coord' hc (simpleCompleted Ω C' coord' hc pc)
    (mutationTorusPush Ω hΩ C pc false LaurentRay.vUnit F) F' ?_ m
  · change actualPolynomialAdjointCoefficient Ω (rootOrder coord')
      (invOfUnit (normalizedSimple Ω (simpleRoot C' pc)) 1) _ m=_ at H
    rw [show simpleRoot C' pc= -simpleRoot C pc from mutatedRoot_p Ω C pc] at H
    exact H
  · intro x
    change actualPolynomialAdjointCoefficient Ω (rootOrder coord') (normalizedSimple Ω (simpleRoot C' pc)) _ x=_
    rw [show simpleRoot C' pc= -simpleRoot C pc from mutatedRoot_p Ω C pc]
    exact finite_cut_actual Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (pureDegree_simple_self C coord hcoord pc) (rootOrder coord') hp F F' hF x

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_3} : type_of% @OAI.ElementaryPositivity.QuantumTorus.pure_mutated_inverse_finite_oai.{u_1, u_3} := @OAI.ElementaryPositivity.QuantumTorus.pure_mutated_inverse_finite_oai.{u_1, u_3}
