-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:21.658044+00:00
-- url     : https://prove2.me/submissions/1ff2b11e-a6b7-40af-9980-1ab624bd716f

import Mathlib
import Definitions.Def_OAIQ368Chrom009
import Definitions.Def_OAIQ368Chrom011
import Definitions.Def_OAIQ368Chrom013
import Definitions.Def_OAIQ368Chrom057
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_halfspace_canonical_polynomial_coefficients
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_mutatedTransport_canonical
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_nearCut_old_positive_seed
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_pure_mutated_inverse_finite
import Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_actualInfinityPath_product_square
import Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_finite_refinement_import

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
lemma adjoint_mul (F G X : PowerSeries A) (hF : constantCoeff F=1) (hG : constantCoeff G=1) :
    adjoint (F*G) X=adjoint F (adjoint G X) := by
  simp only [adjoint,inverse_mul F G hF hG,mul_assoc]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ChartRefinement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (p : M) (hp : Ω p p=0)

lemma mutationIncomingLabel_nonnegative (m : M) (hm : 0≤Ω p m) : mutationIncomingLabel Ω p m=m := by
  rw [mutationIncomingLabel,max_eq_left (by omega),zero_zsmul,add_zero]
lemma mutationIncomingLabel_nonpositive (m : M) (hm : Ω p m≤0) :
    mutationIncomingLabel Ω p m=mutationShear Ω p m := by
  rw [mutationIncomingLabel,max_eq_right (by omega),neg_zsmul]
  exact (sub_eq_add_neg _ _).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutationConvexSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
variable (e : M →+ E) (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M)

lemma realShearCovector_eval (h : Module.Dual ℝ E) (x : E) :
    realShearCovector e S p h x=h (realShearVector e S p x) := by
  simp only [realShearCovector,realShearVector,LinearMap.add_apply,LinearMap.smul_apply,
    map_add,map_smul,smul_eq_mul]
  ring

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_RationalTorusFaithful
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
lemma split_injective {m n : M} (hk : k m=k n) (ho : off k p hp m=off k p hp n) : m=n := by
  rw [←split_sum k p hp m,←split_sum k p hp n,hk,ho]
end
end ElementaryPositivity.RationalFiber

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
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus
local instance instAddCommMonoidTorus_1_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_r361ae7_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_r361ae7_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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

include v Ω in
lemma central_support_zero
    (hv : Function.Injective (fun z : ℤ=>(↑(v^z):K)))
    (hΩ : ∀m,Ω m m=0) (hnd : ∀r≠0,∃m,Ω r m≠0)
    (f : Torus v Ω) (hf : ∀m,f*Torus.X v Ω m=Torus.X v Ω m*f) :
    ∀r≠0,f r=0 := by
  intro r hr
  obtain ⟨m,hm⟩:=hnd r hr
  have H:=congrArg (fun t : Torus v Ω=>t (r+m)) (hf m)
  rw [mul_X_coeff,X_mul_coeff] at H
  by_contra hf
  have he : Ω r m=Ω m r:=hv (mul_left_cancel₀ hf H)
  have hs:=alternating_skew Ω hΩ r m
  omega
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
local instance monomialConjugationAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_r361ae7_1 : AddGroup (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_2_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance rationalLaurentFaithfulRing_r361ae7_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rationalLaurentFaithfulNonUnitalSemiring_r361ae7_1 : NonUnitalSemiring (Torus v Ω) :=
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleIncomingElement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.rationalThroughRing
local instance rationalThroughAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rationalThroughAddGroup_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance rationalThroughNonUnitalSemiring_r361ae7_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance rationalThroughNonUnitalNonAssocSemiring_r361ae7_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma regrade_congr_through (D : ℕ) {f g : PowerSeries (Torus v Ω)}
    (he : ∀n≤B*D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (regrade v Ω δ B f)=coeff d (regrade v Ω δ B g) := by
  intro d hd
  rw [regrade_coeff,regrade_coeff]
  apply Finset.sum_congr rfl
  intro n hn
  rw [he n (by have H:=Finset.mem_range.mp hn; have HH:=Nat.mul_le_mul_left B hd; omega)]
lemma rationalRegrade_congr_through (D : ℕ) {f g : PowerSeries (Torus v Ω)}
    (he : ∀n≤B*D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (rationalRegrade v Ω hΩ k p hp δ B f)=
      coeff d (rationalRegrade v Ω hΩ k p hp δ B g) := by
  intro d hd
  simp only [rationalRegrade,coeff_map]
  rw [regrade_congr_through v Ω δ B D he d hd]
lemma oldUnit_inverse_congr (u w : (biSupportedSubring v Ω δ k)ˣ) (N : ℕ)
    (h : ∀n≤N,coeff n u.val.val=coeff n w.val.val) :
    ∀n≤N,coeff n u.inv.val=coeff n w.inv.val := by
  intro n hn
  have HE:=FormalLog.mul_coeff_congr u.inv.val (u.val.val*w.inv.val)
    u.inv.val (w.val.val*w.inv.val) n (fun _ _=>rfl) (by
      intro j hj
      exact FormalLog.mul_coeff_congr _ _ _ _ j (fun t ht=>h t (ht.trans (hj.trans hn))) (fun _ _=>rfl))
  have hu : u.inv.val*u.val.val=1:=congrArg (fun a : biSupportedSubring v Ω δ k=>a.val) u.inv_val
  have hw : w.val.val*w.inv.val=1:=congrArg (fun a : biSupportedSubring v Ω δ k=>a.val) w.val_inv
  rw [←mul_assoc,hu,one_mul,hw,mul_one] at HE
  exact HE.symm
lemma innerHom_coeff_congr {A : Type*} [Ring A] (u w : (PowerSeries A)ˣ)
    (f g : PowerSeries A) (N : ℕ)
    (hv : ∀n≤N,coeff n u.val=coeff n w.val)
    (hi : ∀n≤N,coeff n u.inv=coeff n w.inv)
    (hf : ∀n≤N,coeff n f=coeff n g) :
    coeff N (innerHom u f)=coeff N (innerHom w g) := by
  change coeff N (u.val*f*u.inv)=coeff N (w.val*g*w.inv)
  apply FormalLog.mul_coeff_congr
  · intro j hj
    exact FormalLog.mul_coeff_congr _ _ _ _ j (fun t ht=>hv t (ht.trans hj))
      (fun t ht=>hf t (ht.trans hj))
  · exact hi
lemma comparisonAction_input_congr (c : ComparisonCrossing v Ω δ k B)
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (N : ℕ) (hg : ∀n≤N,coeff n f=coeff n g) :
    coeff N (comparisonAction v Ω hΩ δ k p hp B c f)=
      coeff N (comparisonAction v Ω hΩ δ k p hp B c g) := by
  cases c with
  | bounded u hf hi=>exact innerHom_coeff_congr _ _ _ _ N (fun _ _=>rfl) (fun _ _=>rfl) hg
  | pure b=>
    cases b
    · change coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).symm.toRingHom f)=
        coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).symm.toRingHom g)
      rw [coeff_map,coeff_map,hg N le_rfl]
    · change coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).toRingHom f)=
        coeff N (PowerSeries.map (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)).toRingHom g)
      rw [coeff_map,coeff_map,hg N le_rfl]
lemma bounded_action_congr (D : ℕ) (u w : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
    (hf' : RegradeBound v Ω δ B w.val.val) (hi' : RegradeBound v Ω δ B w.inv.val)
    (he : ∀n≤B*D,coeff n u.val.val=coeff n w.val.val)
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (hg : ∀n≤D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (comparisonAction v Ω hΩ δ k p hp B (.bounded u hf hi) f)=
      coeff d (comparisonAction v Ω hΩ δ k p hp B (.bounded w hf' hi') g) := by
  intro d hd
  apply innerHom_coeff_congr
  · intro n hn
    exact rationalRegrade_congr_through v Ω hΩ δ k p hp B D he n (hn.trans hd)
  · intro n hn
    exact rationalRegrade_congr_through v Ω hΩ δ k p hp B D
      (oldUnit_inverse_congr v Ω δ k u w (B*D) he) n (hn.trans hd)
  · exact fun n hn=>hg n (hn.trans hd)
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SectionTrace
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
local instance sectionTraceAddCommGroup_r361ae7_1 : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance sectionTraceAddGroup_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance sectionTraceSub_r361ae7_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma torus_eval_sum {J : Type*} (s : Finset J) (f : J → Torus v Ω) (r : M) :
    (∑j∈s,f j) r=∑j∈s,f j r := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    change f j r+(∑j∈s,f j) r=_
    rw [ih]
include hΩ in
lemma series_coefficient_trace (r : M) (F X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF : ∀n≤N,∀m,Ω m r≠0 → (coeff n F) m=0) :
    (coeff N (F*X)) r=(coeff N (X*F)) r := by
  classical
  rw [coeff_mul,coeff_mul]
  change (∑p∈Finset.HasAntidiagonal.antidiagonal N, ((coeff p.1 F)*(coeff p.2 X) : Torus v Ω)) r =
    (∑p∈Finset.HasAntidiagonal.antidiagonal N, ((coeff p.1 X)*(coeff p.2 F) : Torus v Ω)) r
  rw [torus_eval_sum,torus_eval_sum]
  rw [←Finset.Nat.sum_antidiagonal_swap (f:=fun p=>((coeff p.1 X)*(coeff p.2 F)) r)]
  apply Finset.sum_congr rfl
  intro p hp
  apply coefficient_trace v Ω hΩ r
  exact hF p.1 (by have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega)
include hΩ in
lemma adjoint_coefficient_trace (r : M) (F X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hF0 : constantCoeff F=1)
    (hF : ∀n≤N,∀m,Ω m r≠0 → (coeff n F) m=0) :
    (coeff N (adjoint F X)) r=(coeff N X) r := by
  unfold adjoint
  rw [mul_assoc,series_coefficient_trace v Ω hΩ r F (X*invOfUnit F 1) N hF,
    mul_assoc,invOfUnit_mul F 1 hF0,mul_one]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SectionCharts
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
lemma section_refinement_through (h k H : M →+ ℝ) (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k H m) :
    ∀n≤N,coeff n (sectionValue v Ω C F H X)=
      coeff n (adjoint (chartNegative v Ω C k (chartZero v Ω C h F)).val
        (sectionValue v Ω C F h X)) := by
  intro n hn
  unfold sectionValue
  rw [←adjoint_mul _ _ _ (chartNegative v Ω C k (chartZero v Ω C h F)).property.1
    (chartNegative v Ω C h F).property.1]
  exact adjoint_coeff_congr _ _ _ _ n
    (fun j hj=>chart_negative_refinement v Ω C h k H F N hs j (hj.trans hn)) (fun _ _=>rfl)
lemma section_incoming_perturbation (hΩ : ∀m,Ω m m=0) (r : M) (k H : M →+ ℝ)
    (F : CompletedPositive v Ω C) (X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns (incomingCovector Ω r) k H m) :
    (coeff N (sectionValue v Ω C F H X)) r=
      (coeff N (sectionValue v Ω C F (incomingCovector Ω r) X)) r := by
  rw [section_refinement_through v Ω C _ _ _ F X N hs N le_rfl]
  apply adjoint_coefficient_trace v Ω hΩ r _ _ N
    (chartNegative v Ω C k (chartZero v Ω C (incomingCovector Ω r) F)).property.1
  have hker:=chartThree_supported v Ω C k (incomingCovector Ω r).ker.toAddSubmonoid
    (chartZero v Ω C (incomingCovector Ω r) F) (chartZero_supported_kernel v Ω C _ F)
  intro n hn m hm
  apply hker.2.2 n m
  intro hh
  apply hm
  change (Ω m r:ℝ)=0 at hh
  exact_mod_cast hh
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
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ComparisonRefinement
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
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_7
local instance instAddCommMonoidTorus_4_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_r361ae7_2 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_7_r361ae7_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_7_r361ae7_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma CrossingClose.action {D : ℕ} {c c' : ComparisonCrossing v Ω δ k B}
    (hc : CrossingClose v Ω δ k B D c c')
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (hf : ∀n≤D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (comparisonAction v Ω hΩ δ k p hp B c f)=
      coeff d (comparisonAction v Ω hΩ δ k p hp B c' g) := by
  cases hc with
  | pure b=>
    intro d hd
    exact comparisonAction_input_congr v Ω hΩ δ k p hp B (.pure b) f g d
      (fun n hn=>hf n (hn.trans hd))
  | bounded u w hf hi hf' hi' he=>exact bounded_action_congr v Ω hΩ δ k p hp B D u w hf hi hf' hi' he f g ‹_›
lemma bounded_action_trivial (D : ℕ) (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
    (he : ∀n≤B*D,coeff n u.val.val=coeff n 1)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    ∀d≤D,coeff d (comparisonAction v Ω hΩ δ k p hp B (.bounded u hf hi) f)=coeff d f := by
  have H:=bounded_action_congr v Ω hΩ δ k p hp B D u 1 hf hi
    (RegradeBound.one v Ω δ B) (RegradeBound.one v Ω δ B) he f f (fun _ _=>rfl)
  intro d hd
  have HE:=H d hd
  change coeff d (comparisonAction v Ω hΩ δ k p hp B (.bounded u hf hi) f)=
    coeff d (rationalRegrade v Ω hΩ k p hp δ B 1*f*rationalRegrade v Ω hΩ k p hp δ B 1) at HE
  simpa only [rationalRegrade_one,one_mul,mul_one] using HE
lemma WordRefines.action {D : ℕ} {l l' : List (ComparisonCrossing v Ω δ k B)}
    (hl : WordRefines v Ω δ k B D l l')
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (hf : ∀n≤D,coeff n f=coeff n g) :
    ∀d≤D,coeff d (comparisonWordAction v Ω hΩ δ k p hp B l f)=
      coeff d (comparisonWordAction v Ω hΩ δ k p hp B l' g) := by
  induction hl with
  | nil=>exact hf
  | cons hc hl ih=>exact hc.action v Ω hΩ δ k p hp B _ _ ih
  | insert u hv hi he hl ih=>
    intro d hd
    rw [ih d hd]
    exact (bounded_action_trivial v Ω hΩ δ k p hp B D u hv hi he _ d hd).symm
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (δ k : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_8
local instance instAddCommMonoidTorus_5_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_5_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_8_r361ae7_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_8_r361ae7_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma CrossingTrivial.mono {N K : ℕ} {c : ComparisonCrossing v Ω δ k B}
    (hc : CrossingTrivial v Ω δ k B N c) (h : K≤N) :
    CrossingTrivial v Ω δ k B K c := by
  cases hc with
  | bounded u hf hi he=>exact .bounded u hf hi (fun n hn=>he n (hn.trans h))

lemma CrossingClose.refl (D : ℕ) (c : ComparisonCrossing v Ω δ k B) :
    CrossingClose v Ω δ k B D c c := by
  cases c with
  | pure b=>exact .pure b
  | bounded u hf hi=>exact .bounded u u hf hi hf hi (fun _ _=>rfl)

lemma orientedBounded_trivial (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
    (b : Bool) (N : ℕ) (he : ∀n≤N,coeff n u.val.val=coeff n 1) :
    CrossingTrivial v Ω δ k B N (orientedBounded v Ω δ k B u hf hi b) := by
  cases b
  · exact .bounded u⁻¹ hi hf (oldUnit_inverse_congr v Ω δ k u 1 N he)
  · exact .bounded u hf hi he

lemma CrossingTrivial.insert {D : ℕ} {c : ComparisonCrossing v Ω δ k B}
    (hc : CrossingTrivial v Ω δ k B (B*D) c)
    {l l' : List (ComparisonCrossing v Ω δ k B)}
    (hl : WordRefines v Ω δ k B D l l') :
    WordRefines v Ω δ k B D l (c::l') := by
  cases hc with
  | bounded u hf hi he=>exact .insert u hf hi he hl

lemma filter_word_refines {A : Type*} (keep : A → Bool)
    (letter : A → ComparisonCrossing v Ω δ k B) (D : ℕ) (l : List A)
    (H : ∀a∈l,keep a=false → CrossingTrivial v Ω δ k B (B*D) (letter a)) :
    WordRefines v Ω δ k B D ((l.filter keep).map letter) (l.map letter) := by
  induction l with
  | nil=>exact .nil
  | cons a l ih=>
    have ih':=ih (fun a ha=>H a (List.mem_cons_of_mem _ ha))
    cases hh : keep a
    · simp only [List.filter_cons,hh,List.map_cons]
      exact (H a List.mem_cons_self hh).insert v Ω δ k B ih'
    · simp only [List.filter_cons,hh,↓reduceIte,List.map_cons]
      exact .cons (CrossingClose.refl v Ω δ k B D (letter a)) ih'
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ComparisonLine
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
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

lemma actualLineLetter_high (a : ℝ) (N : ℕ) (hN : 1≤N)
    (ha : a∉lineEvents (realRootsThrough e C N) v k) :
    CrossingTrivial LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) N
      (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a) := by
  classical
  unfold actualLineLetter
  split
  · next hh=>
    split
    · next hp=>
      exact False.elim (ha (lineEvents_mono
        (realRootsThrough_mono C e hN) v k (line_cut_event C pc e L hdeg v k H a hp)))
    · apply orientedBounded_trivial
      exact line_chart_trivial C e L hdeg LaurentRay.vUnit Ω (simpleTotalTransport Ω C)
        N v k (H N) a ha
  · exact .bounded 1 (RegradeBound.one _ _ _ _) (RegradeBound.one _ _ _ _) (fun _ _=>rfl)
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRefinementImportAll
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
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

lemma actualLineWord_refines (lo hi : ℝ) (D A N : ℕ)
    (hA : 1≤A) (hDA : (mutationSize Ω C pc+1)*D≤A) (hAN : A≤N) :
    WordRefines LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) D
      (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi A)
      (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N) := by
  classical
  unfold actualLineWord
  rw [←intervalEventList_filter C e v k lo hi hAN]
  apply filter_word_refines
  intro a ha hn
  have hnot : a∉intervalLineEvents C e v k lo hi A:=of_decide_eq_false hn
  exact (actualLineLetter_high Ω C coord hcoord pc e he S hS hcomp L hdeg v k H
    a A hA (event_not_retained C e v k lo hi a ha hnot)).mono _ _ _ _ _ hDA

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationRegradeCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d)
variable (pc : I) (pos : Bool)

local instance mutationRegradeCompatibilityRing_r361ae7_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutationRegradeCompatibilityAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance mutationRegradeCompatibilityAddGroup_r361ae7_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
omit [DecidableEq I] in
include hcoord in
lemma completed_full_homogeneous (f : CompletedPositive v Ω C) :
    FullHomogeneous v Ω (rootOrder coord) f.val := by
  intro n m hm
  exact rootOrder_eq C coord hcoord (by by_contra hh; exact hm (f.property.2 n m hh))

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
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
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

include he hdeg in
theorem actualPath_old_loop {a : Module.Dual ℝ E} (p : GenericLinePath C e a a) (N : ℕ) :
    ∀n≤N,coeff n (comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N)).val.val=coeff n 1 := by
  have HH:=actualPath_old_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N
  have HI:=(oldCoefficientsEqual_equivalence Ω coord pc N).refl
    (covectorNegativeUnit Ω C coord hcoord pc e a)⁻¹
  have HX:=oldCoefficientsEqual_mul Ω coord pc N _ _ _ _ HH HI
  simpa only [mul_assoc,mul_inv_cancel,mul_one,oldCoefficientsEqual,Units.val_one,OneMemClass.coe_one] using HX
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
lemma WordRefines.append {K M : Type*} [Field K] [AddCommGroup M]
    (u : Kˣ) (Ω : M →+ M →+ ℤ) (δ k : M →+ ℤ) (B D : ℕ)
    {l l' s s' : List (ComparisonCrossing u Ω δ k B)}
    (hl : WordRefines u Ω δ k B D l l') (hs : WordRefines u Ω δ k B D s s') :
    WordRefines u Ω δ k B D (l++s) (l'++s') := by
  induction hl with
  | nil=>exact hs
  | cons hc hl ih=>exact .cons hc ih
  | insert a hf hi he hl ih=>exact .insert a hf hi he ih

variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

lemma actualPathWord_refines {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (D A N : ℕ) (hA : 1≤A) (hDA : (mutationSize Ω C pc+1)*D≤A) (hAN : A≤N) :
    WordRefines LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc)
      (mutationSize Ω C pc+1) D
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p A)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N) := by
  induction p with
  | nil=>exact .nil
  | append s p ih=>
    exact WordRefines.append _ _ _ _ _ _
      (actualLineWord_refines Ω C coord hcoord pc e he S hS hcomp L hdeg
        s.direction s.offset s.generic s.lo s.hi D A N hA hDA hAN) ih

include he hdeg in
theorem actualPath_rational_loop_coefficient {a : Module.Dual ℝ E}
    (p : GenericLinePath C e a a) (D : ℕ)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    coeff D (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p
        (max 1 ((mutationSize Ω C pc+1)*D))) f)=coeff D f := by
  apply finite_refinement_import LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
    (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
    (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1) _ D _ _ f
  · intro n
    rw [LaurentRay.vUnit_zpow]
    exact UnitSelections.laurent_q_not_root n
  · intro N
    let A:=max 1 ((mutationSize Ω C pc+1)*D)
    refine ⟨actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p (max N A),?_,?_⟩
    · exact actualPathWord_refines Ω C coord hcoord pc e he S hS hcomp L hdeg p D A (max N A)
        (le_max_left _ _) (le_max_right _ _) (le_max_right _ _)
    · intro n hn
      exact actualPath_old_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p (max N A)
        n (hn.trans (le_max_left _ _))
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedPathAction
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

lemma actualPathAction_coeff {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)))
    (D A : ℕ) (hA : 1≤A) (hDA : (mutationSize Ω C pc+1)*D≤A) :
    coeff D (actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f)=
    coeff D (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p A) f) := by
  simp only [actualPathAction,PowerSeries.coeff_mk]
  exact (actualPathWord_refines Ω C coord hcoord pc e he S hS hcomp L hdeg p D
    (max 1 ((mutationSize Ω C pc+1)*D)) A (le_max_left _ _) (le_max_right _ _)
    (max_le hA hDA)).action _ _ _ _ _ _ _ _ f f (fun _ _=>rfl) D le_rfl

include he hdeg in
theorem actualPathAction_loop {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    actualPathAction Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p f=f := by
  apply PowerSeries.ext
  intro D
  simp only [actualPathAction,PowerSeries.coeff_mk]
  exact actualPath_rational_loop_coefficient Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p D f

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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedPathCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_4
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma mutatedPathCompletion_coeff {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (D N : ℕ) (hN : 1≤N) (hDN : (mutationSize Ω C pc+1)*D≤N) :
    ∀d≤D,coeff d (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p)=
      coeff d (mutatedPathProduct Ω hΩ C coord pc e he L hdeg p N) := by
  induction p with
  | nil=>exact fun _ _=>rfl
  | append s p ih=>
    intro d hd
    apply FormalLog.mul_coeff_congr
    · intro j hj
      exact mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic
        s.lo s.hi j N hN ((Nat.mul_le_mul_left _ (hj.trans hd)).trans hDN)
    · intro j hj
      exact ih j (hj.trans hd)

lemma mutatedPathCompletion_trans {a b c : Module.Dual ℝ E}
    (p : GenericLinePath C e a b) (q : GenericLinePath C e b c) :
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg (p.trans C e q)=
      mutatedPathCompletion Ω hΩ C coord pc e he L hdeg q*
      mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p := by
  induction q with
  | nil=>exact (one_mul _).symm
  | append s q ih=>
    simp only [GenericLinePath.trans,mutatedPathCompletion,ih,mul_assoc]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GeometricMutationLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
variable (Ω : M →+ M →+ ℤ) (e : M →+ E)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M)
variable (hS : ∀x,S x x=0) (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
include hS hcomp in
lemma realShearCovector_incoming (r : M) :
    realShearCovector e S p (S.flip (e r))=S.flip (e (mutationShear Ω p r)) := by
  have hs : ∀a b,S a b= -S b a:=by
    intro a b
    have H:=hS (a+b)
    simp only [map_add,LinearMap.add_apply,hS] at H
    linarith
  ext x
  change S x (e r)+S (e p) (e r)*S (e p) x=S x (e (r-Ω p r • p))
  rw [map_sub,map_zsmul,map_sub,map_zsmul,hcomp,hs x (e p)]
  simp only [zsmul_eq_mul]
  ring
lemma realMutationCovector_eq_side (pos : Bool) (h : Module.Dual ℝ E)
    (hside : if pos then 0≤h (e p) else h (e p)≤0) :
    realMutationCovector e S p h=realSideCovector e S p pos h := by
  cases pos
  · change h (e p)≤0 at hside
    change (if 0≤h (e p) then h else realShearCovector e S p h)=realShearCovector e S p h
    by_cases hh : 0≤h (e p)
    · rw [ite_eq_left hh,realShearCovector,le_antisymm hside hh,zero_smul,add_zero]
    · rw [ite_eq_right hh]
  · change 0≤h (e p) at hside
    exact ite_eq_left hside

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_InfinityUnitAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {A B : Type*} [Ring A] [Ring B]

lemma coeff_commute_of_adjoints (u : (PowerSeries B)ˣ) (x : PowerSeries B) (D : ℕ)
    (h : ∀d≤D,coeff d (innerHom u x)=coeff d x) :
    coeff D (u.val*x)=coeff D (x*u.val) := by
  have H : coeff D (innerHom u x*u.val)=coeff D (x*u.val) := by
    apply ElementaryPositivity.FormalLog.mul_coeff_congr
    · exact h
    · exact fun _ _=>rfl
  change coeff D (((u.val*x)*u.inv)*u.val)=coeff D (x*u.val) at H
  simpa only [mul_assoc,u.inv_val,mul_one] using H
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_AffineCutTelescoping
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
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
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_PureCutTelescoping
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {A J:Type*} [Ring A]
lemma foldr_left_mul (l:List J) (f:J → A) (z:A) :
    l.foldr (fun a x=>f a*x) z=(l.map f).prod*z := by
  induction l with
  | nil=>simp
  | cons a l ih=>simp only [List.foldr_cons,List.map_cons,List.prod_cons,ih,mul_assoc]
omit [Ring A] in
lemma foldr_identity (l:List J) (x:A) : l.foldr (fun _ y=>y) x=x := by
  induction l <;> simp_all

lemma pureCut_local (f:PowerSeries A) (hf:constantCoeff f=1) (u v t:ℝ)
    (hne:u≠0 ∨ v≠0) (x:PowerSeries A) :
    (if u+t*v=0 then orientPowerSeries (!(decide (v<0))) f else 1)*
      (pureCutGauge f (AffineCut.beforeSide u v t)*x)=
      pureCutGauge f (AffineCut.afterSide u v t)*x := by
  by_cases hz:u+t*v=0
  · have hv:v≠0:=by rintro rfl; simp_all
    rw [ite_eq_left hz,(AffineCut.sides_at_zero u v t hz).1,(AffineCut.sides_at_zero u v t hz).2]
    rcases lt_or_gt_of_ne hv with hn|hp
    · simp only [hn,decide_true,Bool.not_true,pureCutGauge,ite_true, if_true,
        show ¬0<v by linarith,decide_false,Bool.false_eq_true,ite_false, if_false,orientPowerSeries]
      rw [←mul_assoc,PowerSeries.invOfUnit_mul f 1 hf,one_mul]
    · simp [pureCutGauge,orientPowerSeries,hp,show ¬v<0 by linarith]
  · rw [ite_eq_right hz,(AffineCut.sides_eq_of_ne u v t hz).1,
      (AffineCut.sides_eq_of_ne u v t hz).2,one_mul]

lemma pureCut_telescope (f:PowerSeries A) (hf:constantCoeff f=1)
    (u v lo hi:ℝ) (hlohi:lo<hi) (hne:u≠0 ∨ v≠0)
    (hlo:u+lo*v≠0) (hhi:u+hi*v≠0) (T:Finset ℝ)
    (hmem:∀t∈T,lo<t ∧ t<hi)
    (hcut:∀t,lo<t → t<hi → u+t*v=0 → t∈T) :
    ((T.sort (· ≥ ·)).map (fun t=>if u+t*v=0 then
      orientPowerSeries (!(decide (v<0))) f else 1)).prod *
      pureCutGauge f (decide (0<u+lo*v))=pureCutGauge f (decide (0<u+hi*v)) := by
  classical
  have HH:=AffineCut.telescope_sort u v hne (fun _ (x:PowerSeries A)=>x)
    (fun t x=>(if u+t*v=0 then orientPowerSeries (!(decide (v<0))) f else 1)*x)
    (fun side x=>pureCutGauge f side*x) T lo hi hlohi hmem hcut
    (fun t _ x=>pureCut_local f hf u v t hne x) 1
  rw [(AffineCut.sides_eq_of_ne u v lo hlo).2,(AffineCut.sides_eq_of_ne u v hi hhi).1,
    foldr_identity,mul_one,mul_one,foldr_left_mul] at HH
  exact HH
end
end ElementaryPositivity.QuantumTorus

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
local instance instNonUnitalSemiringTorus_11_r361ae7_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_11_r361ae7_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance infinityLaurentFiniteAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance infinityLaurentFiniteAddGroup_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance infinityLaurentFiniteNonUnitalSemiring_r361ae7_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance infinityLaurentFiniteNonUnitalNonAssocSemiring_r361ae7_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RootLaurentCompletion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ η : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.rootLaurentCompletionRing
local instance rootLaurentCompletionAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rootLaurentCompletionAddGroup_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma laurentRegrade_read {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hhom : FullHomogeneous v Ω η f)
    (n d : ℕ) (z : ℤ) (m : M) (hn : η m=(n:ℤ))
    (hd : δ m=(d:ℤ)) (hz : κ m=z) :
    (coeff d (laurentRegrade v Ω δ κ B f hf)).coeff z m=coeff n f m := by
  rw [laurentRegrade_coeff,nonp_torus_eval_sum]
  have H (j : ℕ) : (coeff d (laurentHomogenize v Ω δ κ (coeff j f))).coeff z m=coeff j f m := by
    rw [laurentHomogenize_coeff,hd,hz]
    simp
  simp_rw [H]
  apply Finset.sum_eq_single n
  · intro j hj hjn
    by_contra h
    have HH:=hhom j m h
    rw [hn] at HH
    exact hjn (by omega)
  · intro hn'
    by_contra h
    have HH:=(hf n m h).2.2
    rw [hd,hz] at HH
    simp only [Finset.mem_range,not_lt] at hn'
    omega

lemma laurentRegrade_coeff_congr {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g)
    (d : ℕ) (z : ℤ)
    (H : ∀n≤(z+(B+1:ℤ)*(d:ℤ)).toNat,coeff n f=coeff n g) :
    (coeff d (laurentRegrade v Ω δ κ B f hf)).coeff z=
      (coeff d (laurentRegrade v Ω δ κ B g hg)).coeff z := by
  rw [laurentRegrade_coeff,laurentRegrade_coeff]
  apply Finset.sum_congr rfl
  intro n hn
  rw [H n (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn)]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationInfinityAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RationalFiber WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (v : (LaurentSeries ℚ)ˣ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRat
local instance instAddCommMonoidTorusLaurentSeriesRat_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRat_4_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma mutatedLaurent_coeff_congr
    (F G : CompletedPositive v Ω (mutatedRoots Ω C pc)) (d : ℕ) (z : ℤ)
    (h : ∀n≤(z+(mutationSize Ω C pc+1:ℤ)*(d:ℤ)).toNat,coeff n F.val=coeff n G.val) :
    (coeff d (mutatedLaurent Ω C coord hcoord pc v F)).coeff z=
      (coeff d (mutatedLaurent Ω C coord hcoord pc v G)).coeff z := by
  exact laurentRegrade_coeff_congr v Ω _ _ _
    (mutated_series_laurentBounded Ω C coord hcoord pc v F.property.2)
    (mutated_series_laurentBounded Ω C coord hcoord pc v G.property.2) d z h

end
end ElementaryPositivity.QuantumTorus

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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityPath
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

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_14
local instance instAddCommMonoidTorus_7_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_7_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma infinitySideHom_coeff_congr (pos : Bool)
    (f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)))
    (d : ℕ) (h : coeff d f=coeff d g) :
    coeff d (infinitySideHom v Ω hΩ k p pos f)=coeff d (infinitySideHom v Ω hΩ k p pos g) := by
  cases pos
  · change coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (PowerSeries.map (shearAction v _ _).toRingHom f))=
      coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (PowerSeries.map (shearAction v _ _).toRingHom g))
    simp only [coeff_map,h]
  · change coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) f)=
      coeff d (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) g)
    simp only [coeff_map,h]

lemma infinity_embed_X (m : M) :
    expandFiberInfinity v Ω hΩ k p (embed v Ω hΩ k p hp (Torus.X v Ω m))=
      HahnSeries.single (-k m) (Torus.X v Ω m) := by
  classical
  apply HahnSeries.ext
  funext z
  ext n
  rw [expandFiberInfinity_embed_coeff]
  by_cases hm : m=n
  · subst n
    simp only [HahnSeries.coeff_single,Torus.X,Torus.monomial,Finsupp.single_eq_same]
    split <;> simp_all
  · simp only [Torus.X,Torus.monomial,Finsupp.single_eq_of_ne (Ne.symm hm),ite_self,
      HahnSeries.coeff_single]
    split <;> simp_all

lemma infinitySideHom_test (pos : Bool) (m : M) :
    infinitySideHom v Ω hΩ k p pos (infinityTestInput v Ω hΩ k p hp pos m)=
      PowerSeries.C (HahnSeries.single (-k m) (Torus.X v Ω m)) := by
  change PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
    (mutationSideAction v _ _ pos ((mutationSideAction v _ _ pos).symm _))=_
  rw [RingEquiv.apply_symm_apply,PowerSeries.map_C,infinity_embed_X]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityFiniteLoop
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

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_7
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_r361ae7_2 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_r361ae7_2 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_1_r361ae7_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorusLaurentSeriesRatVUnit_1
lemma actualInfinityPath_loop_commute {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (d N : ℕ) (hN : 1≤N) (hdN : (mutationSize Ω C pc+1)*d≤N) (m : M) :
    coeff d ((actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N).val*
      PowerSeries.C (HahnSeries.single (-pureDegree coord pc m) (Torus.X LaurentRay.vUnit Ω m)))=
    coeff d (PowerSeries.C (HahnSeries.single (-pureDegree coord pc m) (Torus.X LaurentRay.vUnit Ω m))*
      (actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N).val) := by
  classical
  let pos:=decide (0<a (e (simpleRoot C pc)))
  let x:=infinityTestInput LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
    (pureDegree_simple_self C coord hcoord pc) pos m
  have hs:=actualInfinityPath_product_square Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N hN x
  have ht:=infinitySideHom_test LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
    (pureDegree_simple_self C coord hcoord pc) pos m
  apply coeff_commute_of_adjoints
  intro j hj
  rw [←ht]
  rw [hs]
  apply infinitySideHom_coeff_congr
  rw [←actualPathAction_coeff Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p x j N hN
    ((Nat.mul_le_mul_left _ hj).trans hdN)]
  rw [actualPathAction_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p x]

lemma actualInfinityPath_loop_row_commute {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (d N : ℕ) (hN : 1≤N) (hdN : (mutationSize Ω C pc+1)*d≤N) (z : ℤ) (m : M) :
    ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit
      (mutatedPathProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N))).coeff z)*
      Torus.X LaurentRay.vUnit Ω m=
    Torus.X LaurentRay.vUnit Ω m*
      ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit
      (mutatedPathProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N))).coeff z) := by
  have H:=congrArg (fun f : HahnSeries ℤ (Torus LaurentRay.vUnit Ω)=>f.coeff (z-pureDegree coord pc m))
    (actualInfinityPath_loop_commute Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p d N hN hdN m)
  rw [coeff_mul_C,coeff_C_mul,HahnSeries.coeff_mul_single,HahnSeries.coeff_single_mul] at H
  have heq : z-pureDegree coord pc m-(-pureDegree coord pc m)=z:=by omega
  rw [heq] at H
  exact H
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M I : Type*} [Field K] [AddCommGroup M] [Fintype I]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

lemma positive_root_ne_zero (hC : Function.Injective C) {n : ℕ} (hn : 0<n)
    (h : HasRootDegree C n (0:M)) : False := by
  obtain ⟨d,hd,hc⟩:=h
  have hz : (fun i=>(d i:ℤ))=0:=hC (hc.trans (map_zero C).symm)
  have hd0 : d=0:=by
    funext i
    have H:=congrFun hz i
    change (d i:ℤ)=0 at H
    change d i=0
    exact_mod_cast H
  have hn0 : n=0:=by simpa only [hd0,Pi.zero_apply,Finset.sum_const_zero] using hd.symm
  omega

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LaurentCompletionFaithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M I : Type*} [Field K] [AddCommGroup M] [Fintype I]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (δ κ η : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.laurentCompletionFaithfulRing
local instance laurentCompletionFaithfulAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentCompletionFaithfulAddGroup_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentCompletionFaithfulNonUnitalSemiring_r361ae7_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.laurentCompletionFaithfulNonUnitalNonAssocSemiring
lemma laurentRegrade_central_faithful
    (hv : Function.Injective (fun z : ℤ=>(↑(v^z):K)))
    (hΩ : ∀m,Ω m m=0) (hnd : ∀r≠0,∃m,Ω r m≠0) (hC : Function.Injective C)
    (F : CompletedPositive v Ω C) (hF : LaurentBounded v Ω δ κ B F.val)
    (hhom : FullHomogeneous v Ω η F.val) (z : M → ℤ)
    (hcentral : ∀m,laurentRegrade v Ω δ κ B F.val hF*
        PowerSeries.C (HahnSeries.single (z m) (Torus.X v Ω m))=
      PowerSeries.C (HahnSeries.single (z m) (Torus.X v Ω m))*
        laurentRegrade v Ω δ κ B F.val hF) : F.val=1 := by
  have hcoeff (d : ℕ) (w : ℤ) :
      ∀m,((coeff d (laurentRegrade v Ω δ κ B F.val hF)).coeff w)*Torus.X v Ω m=
        Torus.X v Ω m*((coeff d (laurentRegrade v Ω δ κ B F.val hF)).coeff w) := by
    intro m
    have H:=congrArg (fun f : PowerSeries (HahnSeries ℤ (Torus v Ω))=>
      (coeff d f).coeff (w+z m)) (hcentral m)
    rw [coeff_mul_C,coeff_C_mul] at H
    rw [HahnSeries.coeff_mul_single_add,HahnSeries.coeff_single_mul_add] at H
    exact H
  apply PowerSeries.ext
  intro n
  by_cases hn : n=0
  · subst n
    simpa only [coeff_zero_eq_constantCoeff,map_one] using F.property.1
  · rw [coeff_one,ite_eq_right hn]
    ext r
    by_cases hr : r=0
    · subst r
      exact F.property.2 n 0 (positive_root_ne_zero C hC (Nat.pos_of_ne_zero hn))
    · by_contra hh
      have hd:=(hF n r hh).1
      have H:=central_support_zero v Ω hv hΩ hnd
        ((coeff (δ r).toNat (laurentRegrade v Ω δ κ B F.val hF)).coeff (κ r))
        (hcoeff (δ r).toNat (κ r)) r hr
      rw [laurentRegrade_read v Ω δ κ η B hF hhom n _ (κ r) r (hhom n r hh)
        (Int.toNat_of_nonneg hd).symm rfl] at H
      exact hh H
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.WallUnits.LaurentRay
lemma vUnit_zpow_injective : Function.Injective (fun z : ℤ=>(↑(vUnit^z):LaurentSeries ℚ)) := by
  intro a b hab
  change (↑(vUnit^a):LaurentSeries ℚ)=↑(vUnit^b) at hab
  rw [vUnit_zpow,vUnit_zpow] at hab
  have H:=congrArg (fun f : LaurentSeries ℚ=>f.coeff (-a)) hab
  by_contra hh
  simp [hh] at H
end ElementaryPositivity.WallUnits.LaurentRay

end
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

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_8
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_8_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_8_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_2_r361ae7_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorusLaurentSeriesRatVUnit_2
lemma mutatedPathCompleted_loop_row_commute {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (d : ℕ) (z : ℤ) (m : M) :
    ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit
      (mutatedPathCompletedPositive Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p))).coeff z)*
      Torus.X LaurentRay.vUnit Ω m=
    Torus.X LaurentRay.vUnit Ω m*
      ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit
      (mutatedPathCompletedPositive Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p))).coeff z) := by
  let D:=(z+(mutationSize Ω C pc+1:ℤ)*(d:ℤ)).toNat
  let N:=max 1 ((mutationSize Ω C pc+1)*max d D)
  have hN : 1≤N:=le_max_left _ _
  have hdN : (mutationSize Ω C pc+1)*d≤N:=
    (Nat.mul_le_mul_left _ (le_max_left d D)).trans (le_max_right _ _)
  have hDN : (mutationSize Ω C pc+1)*D≤N:=
    (Nat.mul_le_mul_left _ (le_max_right d D)).trans (le_max_right _ _)
  let F:=mutatedPathCompletedPositive Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p
  let G:=mutatedPathProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N
  have hc:=mutatedLaurent_coeff_congr Ω C coord hcoord pc LaurentRay.vUnit F G d z
    (mutatedPathCompletion_coeff Ω hΩ C coord pc e he L hdeg p D N hN hDN)
  have HH:=actualInfinityPath_loop_row_commute Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p d N hN hdN z m
  calc
    _ = ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit G)).coeff z)*
        Torus.X LaurentRay.vUnit Ω m := congrArg (fun t=>t*Torus.X LaurentRay.vUnit Ω m) hc
    _ = Torus.X LaurentRay.vUnit Ω m*
        ((coeff d (mutatedLaurent Ω C coord hcoord pc LaurentRay.vUnit G)).coeff z) := HH
    _ = _ := congrArg (fun t=>Torus.X LaurentRay.vUnit Ω m*t) hc.symm

include hcoord hS hcomp in
lemma mutatedPathCompletion_loop (hnd : ∀r≠0,∃m,Ω r m≠0)
    {a : Module.Dual ℝ E} (p : GenericLinePath C e a a) :
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p=1 := by
  let F:=mutatedPathCompletedPositive Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p
  have hC : Function.Injective (mutatedRoots Ω C pc) :=
    Function.LeftInverse.injective (mutatedCoordinates_retraction Ω C coord hcoord pc)
  refine laurentRegrade_central_faithful LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
    (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (-pureDegree coord pc)
    (rootOrder (mutatedCoordinates Ω C coord pc)) (mutationSize Ω C pc)
    LaurentRay.vUnit_zpow_injective hΩ hnd hC F
    (mutated_series_laurentBounded Ω C coord hcoord pc LaurentRay.vUnit F.property.2)
    (completed_full_homogeneous LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedCoordinates Ω C coord pc) (mutatedCoordinates_retraction Ω C coord hcoord pc) F)
    (fun m=> -pureDegree coord pc m) ?_
  intro m
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ext
  funext z
  rw [coeff_mul_C,coeff_C_mul,HahnSeries.coeff_mul_single,HahnSeries.coeff_single_mul]
  exact mutatedPathCompleted_loop_row_commute Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p d _ m
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
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutatedPathIndependentRing
local instance mutatedPathIndependentAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPathIndependentAddGroup_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hcoord hS hcomp hnd in
lemma mutatedPathCompletion_independent {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (p q : GenericLinePath C e a b) :
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p=
      mutatedPathCompletion Ω hΩ C coord pc e he L hdeg q := by
  obtain ⟨r⟩:=generic_path_exists C e b a HB HA
  have H1:=mutatedPathCompletion_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd (p.trans C e r)
  have H2:=mutatedPathCompletion_loop Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd (r.trans C e q)
  rw [mutatedPathCompletion_trans] at H1 H2
  calc
    _ = 1*mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p := (one_mul _).symm
    _ = (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg q*
        mutatedPathCompletion Ω hΩ C coord pc e he L hdeg r)*
        mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p := by rw [H2]
    _ = mutatedPathCompletion Ω hΩ C coord pc e he L hdeg q*1 := by rw [mul_assoc,H1]
    _ = _ := mul_one _

include hnd in
lemma mutatedTransport_eq_path {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (p : GenericLinePath C e a b) :
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val=
      mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p :=
  mutatedPathCompletion_independent Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB _ p

end
end ElementaryPositivity.QuantumTorus

end
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
lemma mutated_degree_covector (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) :
    ∃J:Module.Dual ℝ E,∀i,J (e (simpleRoot (mutatedRoots Ω C pc) i))=1 := by
  classical
  obtain ⟨D,hD⟩:=realRootCoordinates_exists C e hC
  let w:I → ℝ:=fun i=>if i=pc then -1 else 1+(max 0 (-mutationPairing Ω C pc i):ℤ)
  let J:Module.Dual ℝ E:=∑i,w i • (LinearMap.proj i).comp D
  have hj (i:I):J (e (simpleRoot C i))=w i:=by
    simp only [J,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      real_coordinate_simple C e D hD,LinearMap.proj_apply,smul_eq_mul,Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji; simp [hji]
    · simp
  refine ⟨J,fun i=>?_⟩
  by_cases hi:i=pc
  · subst i
    rw [mutatedRoot_p,map_neg,map_neg,hj]
    simp [w]
  · rw [mutatedRoot_off Ω C pc i hi,map_add,map_zsmul,map_add,map_zsmul,hj,hj]
    simp [w,hi,zsmul_eq_mul]

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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationIncomingProbes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))

omit [FiniteDimensional ℝ E] [Fintype I] in
include hS in
lemma realShearVector_ne_zero {v:E} (hv:v≠0) : realShearVector e S (simpleRoot C pc) v≠0 := by
  intro H
  have HH:=congrArg (S (e (simpleRoot C pc))) H
  simp only [realShearVector,map_add,map_smul,hS,smul_zero,add_zero,map_zero] at HH
  exact hv (by simpa only [realShearVector,HH,zero_smul,add_zero] using H)

omit [FiniteDimensional ℝ E] [Fintype I] in
include hS hcomp in
lemma incoming_side_eval (pos:Bool) (r m:M) :
    incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m=
      (S.flip (e r)) (if pos then e m else realShearVector e S (simpleRoot C pc) (e m)) := by
  cases pos
  · change (Ω m (mutationShear Ω (simpleRoot C pc) r):ℝ)=_
    rw [←hcomp]
    change S.flip (e (mutationShear Ω (simpleRoot C pc) r)) (e m)=_
    rw [←realShearCovector_incoming Ω e S (simpleRoot C pc) hS hcomp,
      realShearCovector_eval]
    rfl
  · exact (hcomp m r).symm

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_LatticeHahn
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
local instance latticeHahnAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_r361ae7_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance polynomialAdjointCoefficientsAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualCoefficientsAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualScalarCoefficientsAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_r361ae7_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring_r361ae7_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring_r361ae7_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
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

include hΩ hcoord in
lemma polynomialSection_rebase (a b:M →+ ℝ) (F G:Torus LaurentRay.vUnit Ω)
    (ha:∀m,polynomialSectionCoefficient Ω C coord a F m=G m) (m:M) :
    polynomialSectionCoefficient Ω C coord b F m=
      actualPolynomialAdjointCoefficient Ω (rootOrder coord) (rootChartRatio Ω C a b).val G m := by
  have HA: hahnAction (rootSectionChart Ω C a).val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) F)=
      latticeHahn LaurentRay.vUnit Ω (rootOrder coord) G:=
    (hahnAction_finite_iff Ω hΩ C coord hcoord (rootSectionChart Ω C a) F G).mpr ha
  have HB: hahnAction (rootChartRatio Ω C a b).val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) G)=
      hahnAction (rootSectionChart Ω C b).val (latticeHahn LaurentRay.vUnit Ω (rootOrder coord) F):=by
    rw [rootChartRatio_section,hahnAction_mul _ _ _ (rootSectionChart Ω C b).property.1 (by simp),←HA,
      hahnAction_inverse_cancel _ _ (rootSectionChart Ω C a).property.1]
  have H:=congrArg (fun x:HahnSeries ℤ (Torus LaurentRay.vUnit Ω)=>x.coeff (rootOrder coord m) m) HB
  simpa only [hahnAction_actual_coeff Ω hΩ,polynomialSectionCoefficient] using H.symm

include hΩ in
lemma actualPolynomialAdjointCoefficient_one (τ:M →+ ℤ) (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ 1 F m=F m := by
  rw [←hahnAction_actual_coeff Ω hΩ,hahnAction_one,latticeHahn_coeff,ite_eq_left rfl]

include hΩ in
lemma polynomialSection_negative (h:M →+ ℝ)
    (hh:∀n,0<n → ∀m,HasRootDegree C n m → h m<0)
    (F:Torus LaurentRay.vUnit Ω) (m:M) : polynomialSectionCoefficient Ω C coord h F m=F m := by
  unfold polynomialSectionCoefficient
  rw [rootSectionChart_negative Ω C h hh,actualPolynomialAdjointCoefficient_one Ω hΩ]
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

omit [FiniteDimensional ℝ E] in
lemma nearCut_new_negative {h:Module.Dual ℝ E} (hh:NearCut Ω C pc e h)
    (hp:0<h (e (simpleRoot C pc))) :
    ∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m → h (e m)<0 := by
  have H:∀i,0<(-h) (e (simpleRoot (mutatedRoots Ω C pc) i)):=by
    intro i
    simp only [LinearMap.neg_apply,neg_pos]
    by_cases hi:i=pc
    · subst i
      rw [mutatedRoot_p,map_neg,map_neg]
      linarith
    · rw [mutatedRoot_off Ω C pc i hi,map_add,map_zsmul,map_add,map_zsmul,zsmul_eq_mul]
      have hc:0≤(max 0 (-mutationPairing Ω C pc i):ℝ):=by positivity
      have hb:(max 0 (-mutationPairing Ω C pc i):ℝ)≤(mutationSize Ω C pc:ℝ):=by
        have H:=mutationSize_bound Ω C pc i hi
        have HH:max 0 (-mutationPairing Ω C pc i)≤(mutationSize Ω C pc:ℤ):=
          max_le (by positivity) ((neg_le_abs _).trans H)
        exact_mod_cast HH
      have heps:= (abs_lt.mp hh.1).2
      have hB:0≤(mutationSize Ω C pc:ℝ):=by positivity
      have hm:(mutationSize Ω C pc:ℝ)*h (e (simpleRoot C pc))<1:=by
        have Hmul:((mutationSize Ω C pc:ℝ)+1)*h (e (simpleRoot C pc))<1:=by
          have Hmul: h (e (simpleRoot C pc))*((mutationSize Ω C pc:ℝ)+1)<1:=
            (lt_div_iff₀ (by positivity)).mp heps
          nlinarith
        nlinarith
      simp only [Int.cast_max,Int.cast_zero,Int.cast_neg]
      nlinarith [hh.2 i hi,mul_le_mul_of_nonneg_right hb hp.le]
  intro n hn m hm
  simpa only [LinearMap.neg_apply,neg_pos] using
    covector_root_pos (mutatedRoots Ω C pc) e (-h) H hn hm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NearCutMutation
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
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

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.nearCutMutationRing
local instance nearCutMutationAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutMutationAddGroup_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
omit [FiniteDimensional ℝ E] in
include hcoord hS hcomp in
lemma nearCut_mutated_factor (a:ℝ) (hh:NearCut Ω C pc e (k+a • v)) :
    mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a=
    if (k+a • v) (e (simpleRoot C pc))=0 then
      orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0)))
        (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc)) else 1 := by
  classical
  by_cases hp:(k+a • v) (e (simpleRoot C pc))=0
  · have ha:∃N,a∈lineEvents (realRootsThrough e C N) v k:=
      ⟨1,RationalFiber.line_cut_event C pc e L hdeg v k H a hp⟩
    simp only [mutatedLineFactor,dite_eq_left ha,ite_eq_left hp]
  · rw [ite_eq_right hp]
    unfold mutatedLineFactor
    split
    · next ha=>
      let data:=lineRayData C e he L hdeg v k H a ha
      have HC:=nearCut_noncut_wall Ω C coord hcoord pc e he S hS hcomp L hdeg (k+a • v) hh
        data.root data.degree data.degree_pos data.root_degree data.generic
        (decide (0<(k+a • v) (e (simpleRoot C pc))))
        (cutSide_decide ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc) hp)
      rw [HC]
      have HO:∀b,orientPowerSeries b (1:PowerSeries (Torus LaurentRay.vUnit Ω))=1:=by
        intro b
        apply PowerSeries.ext
        intro n
        exact orientPowerSeries_trivial b 1 n (fun _ _=>rfl) n le_rfl
      simp only [HO,mutationCompletion_one]
    · rfl

omit [FiniteDimensional ℝ E] in
include hcoord hS hcomp in
lemma nearCut_mutated_product (lo hi:ℝ) (hlohi:lo<hi)
    (hlo:lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi:hi∉lineEvents (realRootsThrough e C 1) v k)
    (hh:∀t,lo≤t → t≤hi → NearCut Ω C pc e (k+t • v)) (N:ℕ) (hN:1≤N) :
    mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N *
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+lo • v) (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+hi • v) (e (simpleRoot C pc)))) := by
  classical
  rw [mutatedLineProduct]
  have HE:(intervalEventList C e v k lo hi N).map
      (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H)=
      (intervalEventList C e v k lo hi N).map (fun a=>if k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))=0 then
        orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0)))
          (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc)) else 1):=by
    apply List.map_congr_left
    intro a ha
    simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using
      nearCut_mutated_factor Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a
        (hh a (Finset.mem_filter.mp ((Finset.mem_sort _).mp ha)).2.1.le
          (Finset.mem_filter.mp ((Finset.mem_sort _).mp ha)).2.2.le)
  rw [HE]
  apply pureCut_telescope _ (normalizedSimple_constant Ω _)
    (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) lo hi hlohi
    (Or.inl (RationalFiber.line_cut_offset_ne C pc e L hdeg v k H))
  · exact fun hz=>hlo (RationalFiber.line_cut_event C pc e L hdeg v k H lo hz)
  · exact fun hz=>hhi (RationalFiber.line_cut_event C pc e L hdeg v k H hi hz)
  · exact fun a ha=>(Finset.mem_filter.mp ha).2
  · intro a hla hah hz
    exact Finset.mem_filter.mpr ⟨lineEvents_mono (realRootsThrough_mono C e hN) v k
      (RationalFiber.line_cut_event C pc e L hdeg v k H a hz),hla,hah⟩

omit [FiniteDimensional ℝ E] in
include hcoord hS hcomp in
lemma nearCut_mutated_completion (lo hi:ℝ) (hlohi:lo<hi)
    (hlo:lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi:hi∉lineEvents (realRootsThrough e C 1) v k)
    (hh:∀t,lo≤t → t≤hi → NearCut Ω C pc e (k+t • v)) :
    mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi *
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+lo • v) (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+hi • v) (e (simpleRoot C pc)))) := by
  apply PowerSeries.ext
  intro d
  let N:=max 1 ((mutationSize Ω C pc+1)*d)
  have HH:=nearCut_mutated_product Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H
    lo hi hlohi hlo hhi hh N (le_max_left _ _)
  rw [←HH]
  apply FormalLog.mul_coeff_congr
  · intro j hj
    exact mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg v k H lo hi j N
        (le_max_left _ _) ((Nat.mul_le_mul_left _ hj).trans (le_max_right _ _))
  · exact fun _ _=>rfl

omit [FiniteDimensional ℝ E] in
include hcoord hS hcomp in
lemma nearCut_mutated_path {a b:Module.Dual ℝ E} (p:GenericLinePath C e a b)
    (hh:p.InRegion C e {h | NearCut Ω C pc e h}) :
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p *
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<a (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<b (e (simpleRoot C pc)))) := by
  induction p with
  | nil=>rw [mutatedPathCompletion,one_mul]
  | append s p ih=>
    rw [mutatedPathCompletion,mul_assoc,ih hh.2]
    exact nearCut_mutated_completion Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi s.ordered (s.start_regular 1) (s.finish_regular 1) hh.1

variable (hnd:∀r≠0,∃m,Ω r m≠0)
include hnd in
lemma nearCut_mutated_transport (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc))) :
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val=
      normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc) := by
  obtain ⟨p,hp⟩:=nearCut_path Ω C pc e hC HA HB ha hb
  rw [mutatedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB p]
  have HH:=nearCut_mutated_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p hp
  simpa only [pureCutGauge,decide_eq_false (not_lt.mpr hap.le),Bool.false_eq_true,ite_false, if_false,
    decide_eq_true hbp,ite_true, if_true,mul_one] using HH
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
include hS in
lemma nearCut_double_regular (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) (pos:Bool) :
    ∃h:Module.Dual ℝ E,RegularCovector C e h ∧ NearCut Ω C pc e h ∧
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) ∧
      (∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        realMutationCovector e S (simpleRoot C pc) h (e m)≠0) := by
  classical
  let ε:ℝ:=1/((mutationSize Ω C pc:ℝ)+1)
  have hep:0<ε:=by dsimp [ε] <;> positivity
  obtain ⟨J,hJ⟩:=real_covector_prescribe C e hC (fun _=>1)
  obtain ⟨k,hk⟩:=real_covector_prescribe C e hC (fun i=>if i=pc then if pos then ε/2 else -ε/2 else -2)
  have hkn:NearCut Ω C pc e k:=by
    constructor
    · rw [hk]; simp only [ite_true, if_true]
      cases pos <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,abs_div,abs_of_pos hep,
        abs_neg,abs_of_pos (show (0:ℝ)<2 by norm_num)]
      all_goals change _<ε; linarith
    · intro i hi; rw [hk,ite_eq_right hi]; norm_num
  let P:=insert ((0:ℝ),e (simpleRoot C pc)) (nearCutProbes Ω C pc e)
  let T:ℕ → Finset E:=fun N=>realRootsThrough e C N ∪
    (realRootsThrough e (mutatedRoots Ω C pc) N).image
      (fun x=>if pos then x else realShearVector e S (simpleRoot C pc) x)
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions_with_probes T 0 0 k P J
  have Hreg:RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s (Finset.mem_union_left _ hs)
      (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  have Hcut:=HP ((0:ℝ),e (simpleRoot C pc)) (Finset.mem_insert_self _ _)
  simp only [zero_smul,add_zero] at Hcut
  have Hside:cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc):=by
    cases pos
    · change h (e (simpleRoot C pc))<0
      apply Hcut.2
      rw [hk]; simp only [ite_true, if_true,Bool.false_eq_true,ite_false, if_false]
      linarith
    · change 0<h (e (simpleRoot C pc))
      apply Hcut.1
      rw [hk]; simp only [ite_true, if_true]
      linarith
  refine ⟨h,Hreg,nearCut_of_probes Ω C pc e J k h hJ hkn
    (fun x hx=>HP x (Finset.mem_insert_of_mem hx)),Hside,?_⟩
  intro n hn m hm
  obtain ⟨J',hJ'⟩:=mutated_degree_covector Ω C pc e hC
  have hm0:e m≠0:=by
    have H:=covector_root_pos (mutatedRoots Ω C pc) e J' (fun i=>by rw [hJ']; norm_num) hn hm
    intro h0
    rw [h0,map_zero] at H
    exact lt_irrefl _ H
  have hv:(if pos then e m else realShearVector e S (simpleRoot C pc) (e m))≠0:=by
    cases pos
    · exact realShearVector_ne_zero C pc e S hS hm0
    · exact hm0
  have HT:(if pos then e m else realShearVector e S (simpleRoot C pc) (e m))∈T n:=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e m,realRoot_mem e _ n n le_rfl m hm,rfl⟩)
  have HH:=(Ha n).avoid _ HT (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hv)
  rw [realMutationCovector_eq_side e S _ pos h (by cases pos <;> exact le_of_lt Hside)]
  cases pos
  · simpa only [realSideCovector,Bool.false_eq_true,ite_false, if_false,realShearCovector_eval] using HH
  · exact HH
end
end ElementaryPositivity.QuantumTorus

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
local instance nearCutSectionChartsAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutSectionChartsAddGroup_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
omit [FiniteDimensional ℝ E] in
lemma nearCut_new_section_one {b:Module.Dual ℝ E} (hb:NearCut Ω C pc e b)
    (hbp:0<b (e (simpleRoot C pc))) :
    (rootSectionChart Ω (mutatedRoots Ω C pc)
      ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e)).val=1 := by
  rw [realMutationCovector,ite_eq_left hbp.le]
  exact rootSectionChart_negative Ω _ _ (nearCut_new_negative Ω C pc e hb hbp)

variable (hnd:∀r≠0,∃m,Ω r m≠0)
include hΩ hcoord he hdeg hS hcomp hnd in
lemma nearCut_new_section_chart (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc)))
    (ha':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) a (e m)≠0)
    (hb':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)≠0) :
    (rootSectionChart Ω (mutatedRoots Ω C pc)
      ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e)).val=
      invOfUnit (normalizedSimple Ω (-simpleRoot C pc)) 1 := by
  have H:=nearCut_mutated_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB ha hb hap hbp
  rw [mutatedTransport_canonical Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB ha' hb'] at H
  change (rootChartRatio Ω (mutatedRoots Ω C pc)
    ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e)
    ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e)).val=_ at H
  rw [rootChartRatio_section,nearCut_new_section_one Ω C pc e S hb hbp,one_mul,mutatedRoot_p] at H
  have HH:=congrArg (fun f:PowerSeries (Torus LaurentRay.vUnit Ω)=>invOfUnit f 1) H
  rwa [inverse_inverse _ (rootSectionChart Ω _ _).property.1] at HH
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

variable (hnd:∀r≠0,∃m,Ω r m≠0)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.nearCutPolynomialSeedsRing
local instance nearCutPolynomialSeedsAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutPolynomialSeedsAddGroup_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include he hdeg hS hcomp hnd in
lemma nearCut_new_positive_seed (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc)))
    (ha':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) a (e m)≠0)
    (hb':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)≠0)
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (m:M) :
    polynomialSectionCoefficient Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e) F' m=
      mutationTorusPush Ω hΩ C pc false LaurentRay.vUnit F m := by
  unfold polynomialSectionCoefficient
  rw [nearCut_new_section_chart Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB ha hb hap hbp ha' hb']
  exact pure_mutated_inverse_finite Ω hΩ C coord hcoord pc F F' hF m
end
end ElementaryPositivity.QuantumTorus

end
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
variable (hnd:∀r≠0,∃m,Ω r m≠0)

local instance nearCutPolynomialMutationRing_r361ae7_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance nearCutPolynomialMutationAddCommMonoid_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutPolynomialMutationAddGroup_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include he hdeg hS hcomp hnd in
lemma polynomialSection_mutation (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F')
    (pos:Bool) (h:Module.Dual ℝ E) (HH:RegularCovector C e h)
    (hs:cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc))
    (HH':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) h (e m)≠0) (m:M) :
    polynomialSectionCoefficient Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      ((realMutationCovector e S (simpleRoot C pc) h).toAddMonoidHom.comp e) F'
        (mutationLinearPiece Ω C pc pos m)=
      polynomialSectionCoefficient Ω C coord (h.toAddMonoidHom.comp e) F m := by
  obtain ⟨a,HA,ha,hap,ha'⟩:=nearCut_double_regular Ω C pc e S hS hC false
  obtain ⟨b,HB,hb,hbp,hb'⟩:=nearCut_double_regular Ω C pc e S hS hC true
  have hc:∀d,mutatedCoordinates Ω C coord pc (mutatedRoots Ω C pc d)=d:=
    mutatedCoordinates_retraction Ω C coord hcoord pc
  have haF:∀x,polynomialSectionCoefficient Ω C coord (a.toAddMonoidHom.comp e) F x=F x:=
    polynomialSection_negative Ω hΩ C coord _ (nearCut_old_negative Ω C pc e ha hap) F
  have hbF:∀x,polynomialSectionCoefficient Ω C coord (b.toAddMonoidHom.comp e) F x=F' x:=
    nearCut_old_positive_seed Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hC HA HB ha hb hap hbp F F' hF
  have haG:∀x,polynomialSectionCoefficient Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e) F' x=
      mutationTorusPush Ω hΩ C pc false LaurentRay.vUnit F x:=
    nearCut_new_positive_seed Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB ha hb hap hbp ha' hb' F F' hF
  have hbG:∀x,polynomialSectionCoefficient Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e) F' x=F' x:=by
    intro x
    unfold polynomialSectionCoefficient
    rw [nearCut_new_section_one Ω C pc e S hb hbp,actualPolynomialAdjointCoefficient_one Ω hΩ]
  cases pos
  · rw [polynomialSection_rebase Ω hΩ C coord hcoord (a.toAddMonoidHom.comp e) _ F F haF,
      polynomialSection_rebase Ω hΩ (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc) hc
        ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e) _ F' _ haG]
    exact halfspace_canonical_polynomial_coefficients Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC
      false HA HH hap hs ha' HH' F m
  · rw [polynomialSection_rebase Ω hΩ C coord hcoord (b.toAddMonoidHom.comp e) _ F F' hbF,
      polynomialSection_rebase Ω hΩ (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc) hc
        ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e) _ F' F' hbG]
    have H:=halfspace_canonical_polynomial_coefficients Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC
      true HB HH hbp hs hb' HH' F' m
    have hid:mutationTorusPush Ω hΩ C pc true LaurentRay.vUnit F'=F':=by
      apply Finsupp.ext
      intro x
      have HB:=mutationTorusPush_read Ω hΩ C pc true LaurentRay.vUnit F' x
      exact HB
    rwa [hid] at H
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialIncomingPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits PowerSeriesSplit
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_15
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_18_r361ae7_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_18_r361ae7_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma rootSectionChart_action (h:M →+ ℝ) (X:PowerSeries (Torus LaurentRay.vUnit Ω)) :
    adjoint (rootSectionChart Ω C h).val X=
      sectionValue LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) h
        (adjoint (invOfUnit (simpleTotalTransport Ω C).val 1) X) := by
  exact adjoint_mul _ _ _ (chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1 (by simp)

include hΩ in
lemma monomialSection_incoming_perturbation (b r:M) (H:M →+ ℝ)
    (hs:∀n≤(rootOrder coord (r-b)).toNat,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<H m) ∧ (incomingCovector Ω r m<0 → H m<0)) :
    actualMonomialAdjointCoefficient Ω (rootOrder coord) (rootSectionChart Ω C H).val b r=
      actualMonomialAdjointCoefficient Ω (rootOrder coord)
        (rootSectionChart Ω C (incomingCovector Ω r)).val b r := by
  unfold actualMonomialAdjointCoefficient actualRootCoefficient
  by_cases ht:0 ≤ rootOrder coord (r-b)
  · simp only [ite_eq_left ht]
    have hread (h:M →+ ℝ) :
        coeff (rootOrder coord (r-b)).toNat (adjoint (rootSectionChart Ω C h).val
          (PowerSeries.C (Torus.X LaurentRay.vUnit Ω b))) r=
        coeff (rootOrder coord (r-b)).toNat (normalizedMonomialAction LaurentRay.vUnit Ω
          (rootSectionChart Ω C h).val b) (r-b)*
          (↑(LaurentRay.vUnit^(Ω (r-b) b)):LaurentSeries ℚ):=by
      simpa only [sub_add_cancel] using adjoint_monomial_coeff LaurentRay.vUnit Ω hΩ
        (rootSectionChart Ω C h).val b (r-b) (rootOrder coord (r-b)).toNat
    rw [←hread,←hread,rootSectionChart_action,rootSectionChart_action]
    apply section_incoming_perturbation LaurentRay.vUnit Ω C hΩ r H H
    intro n hn m hm
    exact ⟨(hs n hn m hm).1,(hs n hn m hm).2,fun _=>⟨id,id,id⟩⟩
  · simp only [ite_eq_right ht,zero_mul]

lemma actualPolynomialAdjointCoefficient_congr (τ:M →+ ℤ)
    (f g:PowerSeries (Torus LaurentRay.vUnit Ω)) (F:Torus LaurentRay.vUnit Ω) (r:M)
    (hh:∀b∈F.support,actualMonomialAdjointCoefficient Ω τ f b r=
      actualMonomialAdjointCoefficient Ω τ g b r) :
    actualPolynomialAdjointCoefficient Ω τ f F r=actualPolynomialAdjointCoefficient Ω τ g F r := by
  apply Finset.sum_congr rfl
  intro b hb
  exact congrArg (fun x=>F b*x) (hh b hb)

include hΩ in
lemma polynomialSection_incoming_perturbation (F:Torus LaurentRay.vUnit Ω) (r:M) (H:M →+ ℝ)
    (hs:∀n≤polynomialSectionOrderBound Ω coord F r,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<H m) ∧ (incomingCovector Ω r m<0 → H m<0)) :
    polynomialSectionCoefficient Ω C coord H F r=polynomialSectionIncoming Ω C coord F r := by
  apply actualPolynomialAdjointCoefficient_congr
  intro b hb
  apply monomialSection_incoming_perturbation Ω hΩ C coord b r H
  intro n hn m hm
  have hbnd:(rootOrder coord (r-b)).toNat≤polynomialSectionOrderBound Ω coord F r:=
    Finset.le_sup (f:=fun b=>(rootOrder coord (r-b)).toNat) hb
  exact hs n (hn.trans hbnd) m hm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialIncomingProbes
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
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
include hS hcomp in
lemma polynomial_incoming_probes (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (r:M) (K N:ℕ) :
    ∃pos:Bool,∃h:Module.Dual ℝ E,RegularCovector C e h ∧
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) ∧
      mutationLinearPiece Ω C pc pos r=mutationIncomingLabel Ω (simpleRoot C pc) r ∧
      (∀n≤K,∀m,HasRootDegree C n m →
        (0 < incomingCovector Ω r m → 0<h (e m)) ∧
        (incomingCovector Ω r m<0 → h (e m)<0)) ∧
      (∀n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        (0 < incomingCovector Ω (mutationIncomingLabel Ω (simpleRoot C pc) r) m →
          0 < realMutationCovector e S (simpleRoot C pc) h (e m)) ∧
        (incomingCovector Ω (mutationIncomingLabel Ω (simpleRoot C pc) r) m<0 →
          realMutationCovector e S (simpleRoot C pc) h (e m)<0)) ∧
      (∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        realMutationCovector e S (simpleRoot C pc) h (e m)≠0) := by
  classical
  let A:=realRootsThrough e (mutatedRoots Ω C pc) N
  let Q:=A∪A.image (realShearVector e S (simpleRoot C pc))
  let P:=insert (e (simpleRoot C pc)) (realRootsThrough e C K∪Q)
  let T:ℕ → Finset E:=fun d=>realRootsThrough e C d∪
    (realRootsThrough e (mutatedRoots Ω C pc) d∪
      (realRootsThrough e (mutatedRoots Ω C pc) d).image (realShearVector e S (simpleRoot C pc)))
  let k:=S.flip (e r)
  obtain ⟨h,Ha,_,HP⟩:=generic_for_two_directions_with_probes T 0 0 k (P.image (fun x=>(0,x))) 0
  have HS:∀x∈P,(0<k x → 0<h x) ∧ (k x<0 → h x<0):=by
    intro x hx
    simpa only [zero_smul,add_zero] using HP (0,x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  have Hreg:RegularCovector C e h:=by
    intro d s hs hn
    exact (Ha d).avoid s (Finset.mem_union_left _ hs)
      (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  have hp0:e (simpleRoot C pc)≠0:=hC.ne_zero pc
  have hhp:h (e (simpleRoot C pc))≠0:=Hreg 1 _
    (realRoot_mem e C 1 1 le_rfl _ (simpleRoot_degree C pc)) hp0
  obtain ⟨pos,hpos⟩:∃pos:Bool,cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc):=by
    rcases lt_or_gt_of_ne hhp with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have heval(m:M):realMutationCovector e S (simpleRoot C pc) h (e m)=
      h (if pos then e m else realShearVector e S (simpleRoot C pc) (e m)):=by
    rw [realMutationCovector_eq_side e S _ pos h (by cases pos <;> exact le_of_lt hpos)]
    cases pos
    · exact realShearCovector_eval e S _ _ _
    · rfl
  have hsign:(if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0):=by
    have hs:=HS _ (Finset.mem_insert_self _ _)
    have hc:k (e (simpleRoot C pc))=(Ω (simpleRoot C pc) r:ℝ):=hcomp _ _
    cases pos
    · change h (e (simpleRoot C pc))<0 at hpos
      by_contra hn
      have H:=hs.1 (by rw [hc]; exact_mod_cast lt_of_not_ge hn)
      linarith
    · change 0<h (e (simpleRoot C pc)) at hpos
      by_contra hn
      have H:=hs.2 (by rw [hc]; exact_mod_cast lt_of_not_ge hn)
      linarith
  have hlabel:mutationLinearPiece Ω C pc pos r=mutationIncomingLabel Ω (simpleRoot C pc) r:=by
    cases pos
    · exact (mutationIncomingLabel_nonpositive Ω _ r hsign).symm
    · exact (mutationIncomingLabel_nonnegative Ω _ r hsign).symm
  refine ⟨pos,h,Hreg,hpos,hlabel,?_,?_,?_⟩
  · intro n hn m hm
    have H:=HS _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (realRoot_mem e C K n hn m hm)))
    change (0<S (e m) (e r) → _) ∧ (S (e m) (e r)<0 → _) at H
    rw [hcomp] at H
    exact H
  · intro n hn m hm
    have HA:e m∈A:=realRoot_mem e _ N n hn m hm
    have HQ:(if pos then e m else realShearVector e S (simpleRoot C pc) (e m))∈Q:=by
      cases pos
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e m,HA,rfl⟩)
      · exact Finset.mem_union_left _ HA
    have H:=HS _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ HQ))
    rw [←hlabel,incoming_side_eval Ω C pc e S hS hcomp pos r m,heval]
    exact H
  · intro n hn m hm
    obtain ⟨J,hJ⟩:=mutated_degree_covector Ω C pc e hC
    have hm0:e m≠0:=by
      have H:=covector_root_pos (mutatedRoots Ω C pc) e J (fun i=>by rw [hJ]; norm_num) hn hm
      intro hh
      rw [hh,map_zero] at H
      exact lt_irrefl _ H
    have hv:(if pos then e m else realShearVector e S (simpleRoot C pc) (e m))≠0:=by
      cases pos
      · exact realShearVector_ne_zero C pc e S hS hm0
      · exact hm0
    have HT:(if pos then e m else realShearVector e S (simpleRoot C pc) (e m))∈T n:=by
      apply Finset.mem_union_right
      have HH:=realRoot_mem e (mutatedRoots Ω C pc) n n le_rfl m hm
      cases pos
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e m,HH,rfl⟩)
      · exact Finset.mem_union_left _ HH
    rw [heval]
    exact (Ha n).avoid _ HT (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hv)
end
end ElementaryPositivity.QuantumTorus

end
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
variable (hnd:∀r≠0,∃m,Ω r m≠0)
include he hdeg hS hcomp hnd in
lemma polynomialSectionIncoming_mutation_oai (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (r:M) :
    polynomialSectionIncoming Ω C coord F r=
      polynomialSectionIncoming Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc) F'
        (mutationIncomingLabel Ω (simpleRoot C pc) r) := by
  obtain ⟨pos,h,Hreg,hs,hl,ho,hn,Hnew⟩:=polynomial_incoming_probes Ω C pc e S hS hcomp hC r
    (polynomialSectionOrderBound Ω coord F r)
    (polynomialSectionOrderBound Ω (mutatedCoordinates Ω C coord pc) F'
      (mutationIncomingLabel Ω (simpleRoot C pc) r))
  have Hold:=polynomialSection_incoming_perturbation Ω hΩ C coord F r (h.toAddMonoidHom.comp e) ho
  have Hnew':=polynomialSection_incoming_perturbation Ω hΩ (mutatedRoots Ω C pc)
    (mutatedCoordinates Ω C coord pc) F' (mutationIncomingLabel Ω (simpleRoot C pc) r)
    ((realMutationCovector e S (simpleRoot C pc) h).toAddMonoidHom.comp e) hn
  rw [←Hold,←Hnew',←hl]
  exact (polynomialSection_mutation Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC F F' hF
    pos h Hreg hs Hnew r).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation_oai.{u_1, u_2, u_3}
