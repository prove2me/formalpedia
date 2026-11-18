-- Prove2me | solution 1 for OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:58:21.231425+00:00
-- url     : https://prove2.me/submissions/e74a30f3-b38f-4f4c-b0c8-f23be94a4dec

import Mathlib
import Definitions.Def_OAIQ368Chrom054
import Definitions.Def_OAIQ368Chrom058
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_thetaValue_positive
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_genuine_history_cut_deficit
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularLinear_anchorIncoming
import Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularLinear_locality

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPrecision
open Filter
open scoped LaurentSeries

lemma agrees_refl (b : ℤ) (f : Series) : Agrees b f f := fun _ _=>rfl

end ElementaryPositivity.LaurentPrecision

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_TorusContinuity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.globalStringIndexLinearOrder _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_ra40566_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instSubTorusLaurentSeriesRat
lemma torus_mul_finite (S T : Finset M) (f g : Torus v Ω)
    (hf : f.support⊆S) (hg : g.support⊆T) (m : M) :
    (f*g) m=∑x∈S,∑y∈T,
      (Finsupp.single (x+y) (f x*g y*(↑(v^(Ω x y)) : LaurentSeries ℚ)) : Torus v Ω) m := by
  change Torus.multiply v Ω f g m=_
  unfold Torus.multiply
  rw [Finsupp.sum_of_support_subset f hf _ (by intros; simp)]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finsupp.sum_of_support_subset g hg _ (by intros; simp),Finsupp.finsetSum_apply]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInverse
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
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
lemma coeff_mul_vanish_right (F U : PowerSeries A) (n : ℕ) (hU : ∀j<n,coeff j U=0) :
    coeff n (F*U)=constantCoeff F*coeff n U := by
  classical
  rw [coeff_mul,Finset.sum_eq_single (0,n)]
  · simp only [coeff_zero_eq_constantCoeff]
  · intro p hp hpn
    have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hx : p.2<n:=by
      by_contra hh
      have hp0 : p.1=0:=by omega
      have hp2 : p.2=n:=by omega
      exact hpn (Prod.ext hp0 hp2)
    rw [hU p.2 hx,mul_zero]
  · intro hn
    exact (hn (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp))).elim
lemma coeff_mul_vanish_left (U F : PowerSeries A) (n : ℕ) (hU : ∀j<n,coeff j U=0) :
    coeff n (U*F)=coeff n U*constantCoeff F := by
  classical
  rw [coeff_mul,Finset.sum_eq_single (n,0)]
  · simp only [coeff_zero_eq_constantCoeff]
  · intro p hp hpn
    have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hx : p.1<n:=by
      by_contra hh
      have hp0 : p.2=0:=by omega
      have hp1 : p.1=n:=by omega
      exact hpn (Prod.ext hp1 hp0)
    rw [hU p.1 hx,zero_mul]
  · intro hn
    exact (hn (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp))).elim
lemma adjoint_sub (F X Y : PowerSeries A) : adjoint F (X-Y)=adjoint F X-adjoint F Y := by
  simp only [adjoint,mul_sub,sub_mul]
lemma adjoint_leading (F X Y : PowerSeries A) (hF : constantCoeff F=1) (n : ℕ)
    (hXY : ∀j<n,coeff j X=coeff j Y) :
    coeff n (adjoint F X)-coeff n (adjoint F Y)=coeff n X-coeff n Y := by
  have hU : ∀j<n,coeff j (X-Y)=0:=by intro j hj; rw [map_sub,hXY j hj,sub_self]
  have hFU : ∀j<n,coeff j (F*(X-Y))=0:=by
    intro j hj
    rw [coeff_mul_vanish_right F _ j (fun k hk=>hU k (hk.trans hj)),hU j hj,mul_zero]
  rw [←map_sub,←adjoint_sub,adjoint,coeff_mul_vanish_left _ _ n hFU,
    coeff_mul_vanish_right F _ n hU,hF,one_mul,constantCoeff_invOfUnit]
  simp only [inv_one,Units.val_one,mul_one,map_sub]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RootProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open LaurentPrecision
noncomputable section

lemma positive_zero : Positive 0 := fun _=>natCoeff_zero
lemma Positive.add {f g : LaurentSeries ℚ} (hf : Positive f) (hg : Positive g) : Positive (f+g) :=
  fun j=>(hf j).add (hg j)

lemma single (k : ℤ) (r : ℚ) (hr : NatCoeff r) : Positive (HahnSeries.single k r) := by
  intro j
  rw [HahnSeries.coeff_single]
  split <;> first | exact hr | exact natCoeff_zero

end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SeriesApproximation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter
noncomputable section
variable {M ι : Type*} [AddCommGroup M]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)

lemma testAgreement_refl (T : Finset (PrecisionTest (M:=M))) (F : PowerSeries (Torus v Ω)) :
    TestAgreement v Ω T F F := fun _ _=>agrees_refl _ _

lemma inPrecisionClosure_self {A : Set (PowerSeries (Torus v Ω))} {F : PowerSeries (Torus v Ω)}
    (hF : F∈A) : InPrecisionClosure v Ω A F :=
  fun T=>⟨F,hF,testAgreement_refl v Ω T F⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TorusPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open LaurentPositive WallUnits PowerSeries
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instAddCommMonoidTorusLaurentSeriesRatVUnit
local instance instAddGroupTorusLaurentSeriesRatVUnit_ra40566_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma torusPositive_zero : TorusPositive Ω 0 := fun _=>positive_zero
lemma TorusPositive.add {f g : Torus LaurentRay.vUnit Ω}
    (hf : TorusPositive Ω f) (hg : TorusPositive Ω g) : TorusPositive Ω (f+g) :=
  fun m=>(hf m).add (hg m)
lemma TorusPositive.sum {A : Type*} (s : Finset A) (f : A → Torus LaurentRay.vUnit Ω)
    (h : ∀a∈s,TorusPositive Ω (f a)) : TorusPositive Ω (∑a∈s,f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact torusPositive_zero Ω
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add Ω (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))
lemma torusPositive_monomial (m : M) (r : LaurentSeries ℚ) (hr : Positive r) :
    TorusPositive Ω (Torus.monomial LaurentRay.vUnit Ω m r) := by
  classical
  intro x
  change Positive ((Finsupp.single m r) x)
  by_cases h : m=x
  · subst x
    simpa only [Finsupp.single_eq_same] using hr
  · simpa only [Finsupp.single_eq_of_ne (Ne.symm h)] using positive_zero

lemma TorusPositive.mul {f g : Torus LaurentRay.vUnit Ω}
    (hf : TorusPositive Ω f) (hg : TorusPositive Ω g) : TorusPositive Ω (f*g) := by
  change TorusPositive Ω (Torus.multiply LaurentRay.vUnit Ω f g)
  unfold Torus.multiply Finsupp.sum
  apply TorusPositive.sum
  intro x hx
  apply TorusPositive.sum
  intro y hy
  apply torusPositive_monomial
  rw [LaurentRay.vUnit_zpow]
  exact ((hf x).mul (hg y)).mul (LaurentPositive.single _ _ natCoeff_one)

lemma completedPositive_C_X (m : M) : IntegralPositive Ω (C (Torus.X LaurentRay.vUnit Ω m)) := by
  intro n
  rw [coeff_C]
  split
  · exact torusPositive_monomial Ω _ _ positive_one
  · exact torusPositive_zero Ω

lemma IntegralPositive.mul {F G : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : IntegralPositive Ω F) (hG : IntegralPositive Ω G) : IntegralPositive Ω (F*G) := by
  intro n
  rw [coeff_mul]
  exact TorusPositive.sum Ω _ _ (fun p hp=>(hF p.1).mul Ω (hG p.2))

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I→ℤ) →+ M) (l : Filter ι)
attribute [local instance] Classical.propDecidable

local instance instAddGroupTorusLaurentSeriesRat_3_ra40566_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instSubTorusLaurentSeriesRat_3_ra40566_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma torus_mul_support (S T : Finset M) (f g : Torus v Ω)
    (hf : f.support⊆S) (hg : g.support⊆T) : (f*g).support⊆sumSupport S T := by
  intro m hm
  by_contra H
  apply Finsupp.mem_support_iff.mp hm
  rw [torus_mul_finite v Ω S T f g hf hg m]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  apply Finsupp.single_eq_of_ne
  intro Hxy
  apply H
  exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,Hxy.symm⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GlobalWallPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
attribute [local instance] Classical.propDecidable
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

lemma literalTotalTransport_prescription (hΩ : ∀m,Ω m m=0)
    (l : List (WallUnitDatum M)) (hl : ∀u∈l,u.Allowed C (fun _=>True)) :
    PositiveIncomingPrescription Ω C (literalTotalTransport Ω C l) := by
  classical
  intro r d hd hr
  let D:=literalIncomingCompleted Ω C l hl r
  refine ⟨D,?_,inPrecisionClosure_self LaurentRay.vUnit Ω (literalIncomingRay_mem Ω C l hl r),?_⟩
  · intro n m hm
    by_contra hh
    exact hm (literalRootProducts_strictSupport Ω C (OnPositiveRay r)
      (fun a b ha hb=>ha.add hb) (literalIncomingRay_mem Ω C l hl r) n m hh)
  · intro n m hm
    cases n with
    | zero => simp only [coeff_zero_eq_constantCoeff,FormalLog.log_constant,Finsupp.zero_apply]
    | succ n =>
      by_cases hroot : HasRootDegree C (n+1) m
      · have H:=congrArg (fun x : Torus LaurentRay.vUnit Ω=>x m)
          (incomingSolution_prescription LaurentRay.vUnit Ω C hΩ _ (literalIncomingLog_graded Ω C l) n)
        rw [incomingCoefficient_apply,ite_eq_left hroot,literalIncomingLog_apply,ite_eq_left hroot] at H
        change coeff (n+1) (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m)
          (literalTotalTransport Ω C l)).val) m=coeff (n+1) (FormalLog.log (literalIncomingRay Ω l r)) m
        rw [literalIncomingRay_eq Ω l hm]
        exact H
      · rw [root_graded_log LaurentRay.vUnit Ω C _ (n+1) m hroot,
          root_graded_log LaurentRay.vUnit Ω C D (n+1) m hroot]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleIncomingData
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d)

lemma simpleTotalTransport_positive_prescription (hΩ : ∀m,Ω m m=0) :
    PositiveIncomingPrescription Ω C (simpleTotalTransport Ω C) :=
  literalTotalTransport_prescription Ω C hΩ _ (simpleIncomingList_allowed C)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TranslatedCompletion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.shiftRootGradeAddCommGroup
local instance shiftRootGradeSub_ra40566_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.shiftRootGradeAddGroup
lemma shiftRootGrade_mul (b c : M) (n k : ℕ) (f g : Torus v Ω)
    (hf : f∈shiftRootGrade v Ω C b n) (hg : g∈shiftRootGrade v Ω C c k) :
    f*g∈shiftRootGrade v Ω C (b+c) (n+k) := by
  classical
  intro m hm
  change (Torus.multiply v Ω f g) m=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hxC : HasRootDegree C n (x-b):=by by_contra hn; exact (Finsupp.mem_support_iff.mp hx) (hf x hn)
  have hyC : HasRootDegree C k (y-c):=by by_contra hn; exact (Finsupp.mem_support_iff.mp hy) (hg y hn)
  apply Finsupp.single_eq_of_ne
  intro he
  apply hm
  rw [he]
  convert rootDegree_add C hxC hyC using 1 <;> first | (with_reducible_and_instances rfl) | (abel)
lemma ShiftGraded.mul {b c : M} {X Y : PowerSeries (Torus v Ω)}
    (hX : ShiftGraded v Ω C b X) (hY : ShiftGraded v Ω C c Y) :
    ShiftGraded v Ω C (b+c) (X*Y) := by
  intro n
  rw [coeff_mul]
  apply (shiftRootGrade v Ω C (b+c) n).sum_mem
  intro p hp
  rw [←Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  exact shiftRootGrade_mul v Ω C b c p.1 p.2 _ _ (hX p.1) (hY p.2)
lemma shiftGraded_zero_iff (F : PowerSeries (Torus v Ω)) :
    ShiftGraded v Ω C 0 F↔SeriesGraded v Ω C F := by
  simp only [ShiftGraded,SeriesGraded,shiftRootGrade,rootGrade,AddSubgroup.mem_mk,sub_zero]
lemma ShiftGraded.adjoint {b : M} {X : PowerSeries (Torus v Ω)}
    (hX : ShiftGraded v Ω C b X) (F : CompletedPositive v Ω C) :
    ShiftGraded v Ω C b (adjoint F.val X) := by
  have hF:=(shiftGraded_zero_iff v Ω C F.val).mpr F.property.2
  have hI:=(shiftGraded_zero_iff v Ω C (completedInverse v Ω C F).val).mpr
    (completedInverse v Ω C F).property.2
  simpa only [zero_add,add_zero,PowerSeriesAdjoint.adjoint,completedInverse] using (hF.mul v Ω C hX).mul v Ω C hI
lemma ShiftGraded.monomial (b : M) :
    ShiftGraded v Ω C b (PowerSeries.C (Torus.X v Ω b)) := by
  intro n
  rw [coeff_C]
  split_ifs with hn
  · subst n
    intro m hm
    change (Finsupp.single b (1:LaurentSeries ℚ)) m=0
    apply Finsupp.single_eq_of_ne
    intro he
    apply hm
    rw [←he,sub_self]
    exact rootDegree_zero C
  · exact (shiftRootGrade v Ω C b n).zero_mem

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RealRootCoordinates
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)

lemma covector_root_eval (h:Module.Dual ℝ E) (hh:∀i,h (e (simpleRoot C i))=1)
    {n:ℕ} {m:M} (hm:HasRootDegree C n m) : h (e m)=(n:ℝ) := by
  obtain ⟨a,ha,rfl⟩:=hm
  rw [coefficient_simple_expansion C,map_sum,map_sum]
  simp only [map_zsmul,hh,zsmul_eq_mul,mul_one]
  exact_mod_cast ha

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HomogeneousElementaryExpressions
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
noncomputable section

variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.homogeneousElementaryExpressionsRing
local instance homogeneousElementaryExpressionsAddCommMonoid_ra40566_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.homogeneousElementaryExpressionsAddGroup
lemma cutSupported_zero (ell:M →+ ℤ) (N:ℤ) : CutSupported v Ω ell N 0 := by
  simp [CutSupported]
lemma cutSupported_one (ell:M →+ ℤ) : CutSupported v Ω ell 0 1 := by
  intro m hm
  change m∈(Finsupp.single 0 (1:LaurentSeries ℚ)).support at hm
  have hh:m=0:=by simpa using hm
  subst m
  simp
lemma cutSupported_add (ell:M →+ ℤ) (N:ℤ) {F G:Torus v Ω}
    (hF:CutSupported v Ω ell N F) (hG:CutSupported v Ω ell N G) : CutSupported v Ω ell N (F+G) := by
  intro m hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with hf|hg
  · exact hF m hf
  · exact hG m hg
lemma cutSupported_neg (ell:M →+ ℤ) (N:ℤ) {F:Torus v Ω}
    (hF:CutSupported v Ω ell N F) : CutSupported v Ω ell N (-F) := by
  intro m hm
  exact hF m (by simpa using hm)
lemma cutSupported_mul (ell:M →+ ℤ) (A B:ℤ) {F G:Torus v Ω}
    (hF:CutSupported v Ω ell A F) (hG:CutSupported v Ω ell B G) : CutSupported v Ω ell (A+B) (F*G) := by
  intro m hm
  have hh:=torus_mul_support v Ω F.support G.support F G (by rfl) (by rfl) hm
  obtain ⟨⟨a,b⟩,hab,rfl⟩:=Finset.mem_image.mp hh
  obtain ⟨ha,hb⟩:=Finset.mem_product.mp hab
  simpa only [map_add] using add_le_add (hF a ha) (hG b hb)

open RationalFiber
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_ElementaryExpressionBounds
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
open WallUnits
noncomputable section
variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ)

local instance elementaryExpressionBoundsRing_ra40566_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance elementaryExpressionBoundsAddCommMonoid_ra40566_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance elementaryExpressionBoundsAddGroup_ra40566_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma independentElement_cutSupported_scaled (ell:M →+ ℤ) (K:ℤ) (w:V → M)
    (hw:∀x,ell (w x) ≤ K) (k:ℕ) : CutSupported v Ω ell ((k:ℤ)*K) (independentElement v Ω w k) := by
  intro m hm
  have hn:independentElement v Ω w k m≠0:=Finsupp.mem_support_iff.mp hm
  simp only [independentElement,Finsupp.finsetSum_apply] at hn
  obtain ⟨s,_,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hn
  unfold independentTerm at hs
  split_ifs at hs with hc
  · have hms:m=∑x∈s,w x:=by
      by_contra h
      exact hs (Finsupp.single_eq_of_ne h)
    rw [hms,map_sum]
    calc
      ∑x∈s,ell (w x) ≤ ∑_x∈s,K := Finset.sum_le_sum fun x _=>hw x
      _ = (k:ℤ)*K := by simp [hc.2]
  · exact (hs rfl).elim

lemma ElementaryExpr.cutSupported_scaled {k:ℕ} (f:ElementaryExpr k) (ell:M →+ ℤ) (K:ℤ)
    (w:V → M) (hw:∀x,ell (w x) ≤ K) : CutSupported v Ω ell ((k:ℤ)*K) (f.eval v Ω w) := by
  induction f with
  | zero k => exact cutSupported_zero v Ω ell _
  | one => simpa [eval] using cutSupported_one v Ω ell
  | atom k => exact independentElement_cutSupported_scaled v Ω ell K w hw k
  | add f g hf hg => exact cutSupported_add v Ω ell _ hf hg
  | neg f hf => exact cutSupported_neg v Ω ell _ hf
  | mul f g hf hg => simpa only [eval,Nat.cast_add,add_mul] using cutSupported_mul v Ω ell _ _ hf hg

lemma ElementaryExpr.weight {k:ℕ} (f:ElementaryExpr k) (ell:M →+ ℤ) (K:ℤ)
    (w:V → M) (hw:∀x,ell (w x)=K) (m:M) (hm:m∈(f.eval v Ω w).support) : ell m=(k:ℤ)*K := by
  have h1:=f.cutSupported_scaled v Ω ell K w (fun x=>(hw x).le) m hm
  have h2:=f.cutSupported_scaled v Ω (-ell) (-K) w (fun x=>by simp [hw x]) m hm
  change -ell m ≤ (k:ℤ)*(-K) at h2
  linarith
end
end ElementaryPositivity.QuantumTorus

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
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus
local instance instAddCommMonoidTorus_1_ra40566_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_ra40566_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_ra40566_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_ra40566_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance monomialConjugationAddCommMonoid_ra40566_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_ra40566_1 : AddGroup (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_2_ra40566_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_ra40566_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_LatticeHahn
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq
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
local instance latticeHahnAddCommMonoid_ra40566_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_ra40566_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance polynomialAdjointCoefficientsAddCommMonoid_ra40566_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_ra40566_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualCoefficientsAddCommMonoid_ra40566_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_ra40566_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualScalarCoefficientsAddCommMonoid_ra40566_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_ra40566_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_ra40566_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_18_ra40566_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_18_ra40566_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma rootSectionChart_action (h:M →+ ℝ) (X:PowerSeries (Torus LaurentRay.vUnit Ω)) :
    adjoint (rootSectionChart Ω C h).val X=
      sectionValue LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) h
        (adjoint (invOfUnit (simpleTotalTransport Ω C).val 1) X) := by
  exact adjoint_mul _ _ _ (chartNegative LaurentRay.vUnit Ω C h (simpleTotalTransport Ω C)).property.1 (by simp)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionIncoming
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
attribute [local instance] Classical.propDecidable
variable (F : CompletedPositive v Ω C) (b : M)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.sectionIncomingAddCommGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.sectionIncomingAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.sectionIncomingSub
lemma sectionIncoming_apply (n : ℕ) (X : PowerSeries (Torus v Ω)) (m : M) :
    sectionIncoming v Ω C F b n X m=if HasRootDegree C n (m-b) then
      (coeff n (sectionValue v Ω C F (incomingCovector Ω m) X)) m else 0 := rfl
lemma sectionIncoming_graded (n : ℕ) (X : PowerSeries (Torus v Ω)) :
    sectionIncoming v Ω C F b n X∈shiftRootGrade v Ω C b n := by
  intro m hm
  rw [sectionIncoming_apply,ite_eq_right hm]
lemma sectionIncoming_leading (n : ℕ) (X Y : PowerSeries (Torus v Ω))
    (h : ∀k<n,coeff k X=coeff k Y)
    (hX : coeff n X∈shiftRootGrade v Ω C b n)
    (hY : coeff n Y∈shiftRootGrade v Ω C b n) :
    sectionIncoming v Ω C F b n X-sectionIncoming v Ω C F b n Y=coeff n X-coeff n Y := by
  apply Finsupp.ext
  intro m
  rw [torus_sub_apply,torus_sub_apply,sectionIncoming_apply,sectionIncoming_apply]
  by_cases hm : HasRootDegree C n (m-b)
  · rw [ite_eq_left hm,ite_eq_left hm]
    have H:=adjoint_leading (chartNegative v Ω C (incomingCovector Ω m) F).val X Y
      (chartNegative v Ω C (incomingCovector Ω m) F).property.1 n h
    simpa only [torus_sub_apply,sectionValue] using congrArg (fun t : Torus v Ω=>t m) H
  · rw [ite_eq_right hm,ite_eq_right hm,hX m hm,hY m hm]
lemma sectionIncoming_zero (X : PowerSeries (Torus v Ω))
    (hX : coeff 0 X∈shiftRootGrade v Ω C b 0) :
    sectionIncoming v Ω C F b 0 X=coeff 0 X := by
  apply Finsupp.ext
  intro m
  rw [sectionIncoming_apply]
  by_cases hm : HasRootDegree C 0 (m-b)
  · rw [ite_eq_left hm]
    unfold sectionValue
    rw [coeff_zero_eq_constantCoeff,constant_adjoint _ _ (chartNegative v Ω C _ F).property.1]
  · rw [ite_eq_right hm,hX m hm]

lemma sectionSolution_graded (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈shiftRootGrade v Ω C b n) :
    ShiftGraded v Ω C b (sectionSolution v Ω C F b l) := by
  intro n
  cases n with
  | zero => simpa only [sectionSolution,coeff_mk,sectionSolutionCoefficients] using hl 0
  | succ n =>
    simp only [sectionSolution,coeff_mk,sectionSolutionCoefficients]
    exact (shiftRootGrade v Ω C b (n+1)).sub_mem (hl _) (sectionIncoming_graded v Ω C F b _ _)
lemma sectionTruncation_lower (l : ℕ → Torus v Ω) (n k : ℕ) (hk : k≤n) :
    coeff k (sectionSolution v Ω C F b l)=coeff k (sectionTruncation v Ω C F b l n) := by
  simp only [sectionSolution,sectionTruncation,coeff_mk,ite_eq_left hk]
lemma sectionTruncation_top (l : ℕ → Torus v Ω) (n : ℕ) :
    coeff (n+1) (sectionTruncation v Ω C F b l n)=0 := by
  simp only [sectionTruncation,coeff_mk,show ¬n+1≤n by omega,ite_false, if_false]
lemma sectionSolution_step (l : ℕ → Torus v Ω) (n : ℕ) :
    coeff (n+1) (sectionSolution v Ω C F b l)=l (n+1)-
      sectionIncoming v Ω C F b (n+1) (sectionTruncation v Ω C F b l n) := by
  simp only [sectionSolution,coeff_mk,sectionSolutionCoefficients,sectionTruncation,dite_eq_ite]
lemma sectionSolution_prescription (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈shiftRootGrade v Ω C b n) (n : ℕ) :
    sectionIncoming v Ω C F b n (sectionSolution v Ω C F b l)=l n := by
  cases n with
  | zero =>
    rw [sectionIncoming_zero v Ω C F b _ (sectionSolution_graded v Ω C F b l hl 0)]
    simp only [sectionSolution,coeff_mk,sectionSolutionCoefficients]
  | succ n =>
    have ht : coeff (n+1) (sectionTruncation v Ω C F b l n)∈shiftRootGrade v Ω C b (n+1):=by
      rw [sectionTruncation_top]; exact (shiftRootGrade v Ω C b (n+1)).zero_mem
    have H:=sectionIncoming_leading v Ω C F b (n+1)
      (sectionSolution v Ω C F b l) (sectionTruncation v Ω C F b l n)
      (fun k hk=>sectionTruncation_lower v Ω C F b l n k (by omega))
      (sectionSolution_graded v Ω C F b l hl _) ht
    rw [sectionTruncation_top,sub_zero,sectionSolution_step] at H
    exact sub_left_inj.mp H

theorem existsUnique_section (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈shiftRootGrade v Ω C b n) :
    ∃! X : {X : PowerSeries (Torus v Ω) // ShiftGraded v Ω C b X},
      ∀n,sectionIncoming v Ω C F b n X.val=l n := by
  refine ⟨⟨sectionSolution v Ω C F b l,sectionSolution_graded v Ω C F b l hl⟩,
    sectionSolution_prescription v Ω C F b l hl,?_⟩
  intro X hX
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have H:=sectionIncoming_leading v Ω C F b n X.val (sectionSolution v Ω C F b l)
      ih (X.property n) (sectionSolution_graded v Ω C F b l hl n)
    rw [hX n,sectionSolution_prescription v Ω C F b l hl n,sub_self] at H
    exact sub_eq_zero.mp H.symm

lemma thetaInitial_graded : ShiftGraded v Ω C b (thetaInitial v Ω C F b) :=
  sectionSolution_graded v Ω C F b _ (ShiftGraded.monomial v Ω C b)
lemma thetaInitial_prescription (n : ℕ) :
    sectionIncoming v Ω C F b n (thetaInitial v Ω C F b)=
      coeff n (PowerSeries.C (Torus.X v Ω b)) :=
  sectionSolution_prescription v Ω C F b _ (ShiftGraded.monomial v Ω C b) n
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HomogenizedPolynomialSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.homogenizedPolynomialSectionRing
local instance homogenizedPolynomialSectionAddCommMonoid_ra40566_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance homogenizedPolynomialSectionAddGroup_ra40566_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance homogenizedPolynomialSectionNonUnitalSemiring_ra40566_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.homogenizedPolynomialSectionNonUnitalNonAssocSemiring
lemma homogenize_hahn (τ:M →+ ℤ) (F:Torus LaurentRay.vUnit Ω)
    (hF:∀m,F m≠0 → 0 ≤ τ m) :
    HahnSeries.ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) (homogenize LaurentRay.vUnit Ω τ F)=
      latticeHahn LaurentRay.vUnit Ω τ F := by
  apply HahnSeries.ext
  funext j
  apply Finsupp.ext
  intro m
  rw [ofPowerSeries_coeff_int,latticeHahn_coeff]
  by_cases hf:F m=0
  · split_ifs <;> simp [homogenize_coeff,hf]
  · have hh:=hF m hf
    by_cases hj:0 ≤ j
    · rw [ite_eq_left hj,homogenize_coeff]
      have he:j.toNat=(τ m).toNat ↔ j=τ m:=by omega
      simp only [he]
    · rw [ite_eq_right hj]
      have he:j≠τ m:=by omega
      simp only [he,ite_false, if_false,Finsupp.zero_apply]

lemma ofPowerSeries_adjoint (f X:PowerSeries (Torus LaurentRay.vUnit Ω)) :
    HahnSeries.ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) (adjoint f X)=
      hahnAction f (HahnSeries.ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) X) := by
  simp only [adjoint,hahnAction,map_mul]

include hΩ in
lemma homogenize_adjoint_actual (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → 0 ≤ τ m) (m:M) (hm:0 ≤ τ m) :
    coeff (τ m).toNat (adjoint f (homogenize LaurentRay.vUnit Ω τ F)) m=
      actualPolynomialAdjointCoefficient Ω τ f F m := by
  rw [←hahnAction_actual_coeff Ω hΩ,←homogenize_hahn Ω τ F hF,←ofPowerSeries_adjoint,
    ofPowerSeries_coeff_int,ite_eq_left hm]

include hcoord in
omit [DecidableEq I] in
lemma homogenize_shiftGraded (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base)) :
    ShiftGraded LaurentRay.vUnit Ω C base (homogenize LaurentRay.vUnit Ω (rootOrder coord) F) := by
  intro d m hm
  rw [homogenize_coeff]
  split_ifs with hd
  · by_contra hn
    obtain ⟨k,hk⟩:=hF m hn
    have H:=rootOrder_eq C coord hcoord hk
    rw [map_sub,hb,sub_zero] at H
    have he:d=k:=by rw [hd,H,Int.toNat_natCast]
    exact hm (by rw [he]; exact hk)
  · rfl

include hcoord in
omit [DecidableEq I] in
lemma conePolynomial_nonnegativeOrder (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base)) :
    ∀m,F m≠0 → 0 ≤ rootOrder coord m := by
  intro m hm
  obtain ⟨d,hd⟩:=hF m hm
  have H:=rootOrder_eq C coord hcoord hd
  rw [map_sub,hb,sub_zero] at H
  rw [H]
  exact Int.natCast_nonneg _

include hcoord in
lemma polynomialInitial_graded (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base)) :
    ShiftGraded LaurentRay.vUnit Ω C base (polynomialInitial Ω C coord F) :=
  (homogenize_shiftGraded Ω C coord hcoord base hb F hF).adjoint LaurentRay.vUnit Ω C
    (completedInverse LaurentRay.vUnit Ω C (simpleTotalTransport Ω C))

include hΩ hcoord in
lemma polynomialInitial_incoming (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base))
    (d:ℕ) (m:M) (hm:HasRootDegree C d (m-base)) :
    sectionIncoming LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base d (polynomialInitial Ω C coord F) m=
      polynomialSectionIncoming Ω C coord F m := by
  rw [sectionIncoming_apply,ite_eq_left hm]
  change coeff d (sectionValue LaurentRay.vUnit Ω C (simpleTotalTransport Ω C)
    (incomingCovector Ω m) (polynomialInitial Ω C coord F)) m=_
  unfold polynomialInitial
  rw [←rootSectionChart_action]
  have H:=rootOrder_eq C coord hcoord hm
  rw [map_sub,hb,sub_zero] at H
  have he:d=(rootOrder coord m).toNat:=by rw [H,Int.toNat_natCast]
  rw [he]
  exact homogenize_adjoint_actual Ω hΩ (rootOrder coord) _ F
    (conePolynomial_nonnegativeOrder Ω C coord hcoord base hb F hF) m (by rw [H]; omega)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_CovectorPrescriptions
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
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
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_IndependentElement
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.centersFintype _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M V:Type*} [Field K] [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)

include hΩ in
omit [Fintype V] in
lemma independentTerm_singleton (w:V → M) (x:V) :
    independentTerm v Ω w 1 {x}=Torus.X v Ω (w x) := by
  have hi:IsIndependent Ω w {x}:=by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b
    exact hΩ _
  simp only [independentTerm,hi,Finset.card_singleton,and_self,ite_true, if_true,setMonomial,Finset.sum_singleton]

include hΩ in
lemma independentElement_one (w:V → M) :
    independentElement v Ω w 1=∑x,Torus.X v Ω (w x) := by
  symm
  unfold independentElement
  apply Finset.sum_bij_ne_zero (fun x _ _=>({x}:Finset V))
  · intros; exact Finset.mem_univ _
  · intro x _ _ y _ _ h
    exact Finset.singleton_injective h
  · intro s _ hs
    unfold independentTerm at hs
    split_ifs at hs with H
    · obtain ⟨x,rfl⟩:=Finset.card_eq_one.mp H.2
      refine ⟨x,Finset.mem_univ _,?_,rfl⟩
      intro hh
      have Hx:=congrArg (fun F:Torus v Ω=>F (w x)) hh
      simp [Torus.X,Torus.monomial] at Hx
    · exact (hs rfl).elim
  · intro x _ _
    exact (independentTerm_singleton v Ω hΩ w x).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_PolynomialThetaIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_16
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_19_ra40566_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_19_ra40566_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hΩ hcoord in
lemma polynomialInitial_delta_prescription (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base))
    (hdelta:∀m,polynomialSectionIncoming Ω C coord F m=if m=base then 1 else 0) :
    ∀d,sectionIncoming LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base d
      (polynomialInitial Ω C coord F)=coeff d (PowerSeries.C (Torus.X LaurentRay.vUnit Ω base)) := by
    intro d
    apply Finsupp.ext
    intro m
    by_cases hm:HasRootDegree C d (m-base)
    · rw [polynomialInitial_incoming Ω hΩ C coord hcoord base hb F hF d m hm,hdelta]
      by_cases he:m=base
      · subst m
        have H:=rootOrder_eq C coord hcoord hm
        rw [sub_self,map_zero] at H
        have hd:d=0:=by omega
        rw [hd]
        simp [Torus.X,Torus.monomial]
      · rw [ite_eq_right he,coeff_C]
        split_ifs <;> simp [Torus.X,Torus.monomial,Ne.symm he]
    · rw [sectionIncoming_apply,ite_eq_right hm]
      exact (ShiftGraded.monomial LaurentRay.vUnit Ω C base d m hm).symm

include hΩ hcoord in
lemma polynomialInitial_eq_theta (base:M) (hb:rootOrder coord base=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-base))
    (hdelta:∀m,polynomialSectionIncoming Ω C coord F m=if m=base then 1 else 0) :
    polynomialInitial Ω C coord F=thetaInitial LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base := by
  have hp:=polynomialInitial_delta_prescription Ω hΩ C coord hcoord base hb F hF hdelta
  let X:{X:PowerSeries (Torus LaurentRay.vUnit Ω) // ShiftGraded LaurentRay.vUnit Ω C base X}:=
    ⟨polynomialInitial Ω C coord F,polynomialInitial_graded Ω C coord hcoord base hb F hF⟩
  have U:=(existsUnique_section LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base
    (fun d=>coeff d (PowerSeries.C (Torus.X LaurentRay.vUnit Ω base)))
    (ShiftGraded.monomial LaurentRay.vUnit Ω C base))
  let Y:{X:PowerSeries (Torus LaurentRay.vUnit Ω) // ShiftGraded LaurentRay.vUnit Ω C base X}:=
    ⟨thetaInitial LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base,
      thetaInitial_graded LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) base⟩
  have he:X=Y:=U.unique hp (thetaInitial_prescription LaurentRay.vUnit Ω C
    (simpleTotalTransport Ω C) base)
  exact congrArg Subtype.val he

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StationaryIntegerSequences
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.extendedTotal_last _root_.OAI.ElementaryPositivity.TriangularDynamics.extendedTotal_succ _root_.OAI.ElementaryPositivity.TriangularDynamics.extendedTotal_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.forwardCoord_roots _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchor_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchors _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_anchor _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil _root_.OAI.ElementaryPositivity.TriangularDynamics.scheduledBridge_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics

lemma period_total_nonpos (B K : ℕ → ℤ) (hB : ∀ n, 0 ≤ B n)
    (hK : Monotone K) (step : ∀ n, B (n+1) = B n - K (n+1)) (n : ℕ) :
    K n ≤ 0 := by
  by_contra hn
  have hk : 1 ≤ K n := by omega
  have hb : ∀ t : ℕ, B (n+t) ≤ B n - (t:ℤ) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hm := hK (show n ≤ n+t+1 by omega)
      have hs := step (n+t)
      simp only [Nat.add_succ, Nat.add_zero, Nat.cast_succ] at *
      omega
  have H := hb ((B n).toNat+1)
  have H0 := hB (n+((B n).toNat+1))
  have Hn := Int.toNat_of_nonneg (hB n)
  omega

lemma monotone_int_stabilizes (a : ℕ → ℤ) (ha : Monotone a)
    (hb : ∃ b, ∀ n, a n ≤ b) : ∃ N, ∀ n, N ≤ n → a n = a N := by
  obtain ⟨v,⟨N,hN⟩,hv⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ n, a n = z)
    (by obtain ⟨b,hb⟩ := hb; exact ⟨b,fun z ⟨n,hn⟩ => hn ▸ hb n⟩)
    ⟨a 0,0,rfl⟩
  refine ⟨N,fun n hn => le_antisymm ?_ (ha hn)⟩
  rw [hN]
  exact hv (a n) ⟨n,rfl⟩

lemma finite_coordinates_stabilize {ι : Type*} [Fintype ι]
    (a : ℕ → ι → ℤ) (ha : ∀ i, Monotone (fun n => a n i))
    (hs : ∀ n, ∑ i, a n i ≤ 0) :
    ∃ N, ∀ n, N ≤ n → ∀ i, a n i = a N i := by
  classical
  have hb : ∀ i, ∃ b, ∀ n, a n i ≤ b := by
    intro i
    refine ⟨-∑ j ∈ Finset.univ.erase i, a 0 j,fun n => ?_⟩
    have H := Finset.sum_le_sum (s := Finset.univ.erase i)
      (fun j _ => ha j (show 0 ≤ n by omega))
    have he := Finset.sum_erase_add (Finset.univ : Finset ι) (a n) (Finset.mem_univ i)
    have Hn := hs n
    dsimp only at H he
    omega
  choose N hN using fun i => monotone_int_stabilizes (fun n => a n i) (ha i) (hb i)
  refine ⟨Finset.univ.sup N,fun n hn i => ?_⟩
  have hi : N i ≤ Finset.univ.sup N := Finset.le_sup (f := N) (Finset.mem_univ i)
  rw [hN i n (hi.trans hn),hN i _ hi]

lemma nonnegative_affine_slope (a b : ℤ) (h : ∃ N : ℕ, ∀ L, N ≤ L →
    0 ≤ a + (L:ℤ)*b) : 0 ≤ b := by
  obtain ⟨N,hN⟩ := h
  by_contra hb
  have hb' : b ≤ -1 := by omega
  let L := max N (a.toNat+1)
  have hL := hN L (le_max_left _ _)
  have hLa : a < (L:ℤ) := by
    have hh : a.toNat+1 ≤ L := le_max_right _ _
    have ha : a ≤ (a.toNat:ℤ) := by omega
    omega
  have hL0 : (0:ℤ) ≤ L := Int.natCast_nonneg L
  nlinarith

lemma concave_nonpositive_zero (D : ℕ) (K : ℕ → ℤ)
    (h0 : K 0 = 0) (hD : K D = 0)
    (hn : ∀ i, i ≤ D → K i ≤ 0)
    (hc : ∀ i, 0 < i → i < D → 0 ≤ 2*K i-K (i-1)-K (i+1)) :
    ∀ i, i ≤ D → K i = 0 := by
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (Finset.range (D+1)) K
    (by exact ⟨0,by simp⟩)
  have hjD : j ≤ D := by
    have h := Finset.mem_range.mp hj
    omega
  have hm : ∀ i, i ≤ D → K j ≤ K i := by
    intro i hi
    exact hmin i (Finset.mem_range.mpr (by omega))
  have propagate : ∀ i, i ≤ D → K i = K j → K j = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi he
      by_cases hz : i = 0
      · simpa [hz,h0] using he.symm
      by_cases hd : i = D
      · simpa [hd,hD] using he.symm
      have H := hc i (by omega) (by omega)
      have Hl := hm (i-1) (by omega)
      have Hr := hm (i+1) (by omega)
      have he' : K (i-1) = K j := by omega
      exact ih (i-1) (by omega) (by omega) he'
  have hj0 := propagate j hjD rfl
  intro i hi
  have hh := hm i hi
  have hh' := hn i hi
  omega
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

omit [DecidableEq B] in
lemma total_levels (level : B → Fin n) (m : Lattice n B) :
    ∑ i, levelTotal level i m = ∑ b, m (Sum.inr b) := by
  simp only [levelTotal,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  rw [Finset.sum_comm]
  simp

variable (Ω : Lattice n B →+ Lattice n B →+ ℤ)

omit [Fintype B] in
lemma rotate_bridge_mono (level : B → Fin n) (L : ℕ) (m : Lattice n B) (b c : B) :
    m (Sum.inr c) ≤ rotate Ω level L m b (Sum.inr c) := by
  simp only [rotate,mutationIncomingLabel,Pi.add_apply,Pi.smul_apply,eventRoot_bridge,
    smul_eq_mul]
  split_ifs <;> simp

omit [Fintype B] in
lemma period_bridge_mono (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B) (c : B) :
    m (Sum.inr c) ≤ period Ω level cycle L m (Sum.inr c) := by
  induction cycle generalizing m with
  | nil => exact le_rfl
  | cons b bs ih =>
    exact (rotate_bridge_mono Ω level L m b c).trans (ih (rotate Ω level L m b))

lemma periodFunctional_rotate (level : B → Fin n) (i : Fin n) (L : ℕ) (m : Lattice n B) (b : B) :
    periodFunctional level i L (rotate Ω level L m b) = periodFunctional level i L m := by
  simp only [rotate,mutationIncomingLabel,map_add,map_zsmul,periodFunctional_eventRoot,
    smul_zero,add_zero]

lemma periodFunctional_period (level : B → Fin n) (i : Fin n) (cycle : List B)
    (L : ℕ) (m : Lattice n B) :
    periodFunctional level i L (period Ω level cycle L m) = periodFunctional level i L m := by
  induction cycle generalizing m with
  | nil => rfl
  | cons b bs ih =>
    change periodFunctional level i L (period Ω level bs L (rotate Ω level L m b)) = _
    rw [ih,periodFunctional_rotate]

omit [Fintype B] in
lemma history_bridge_mono (level : B → Fin n) (cycle : List B) (m : Lattice n B) (b : B) :
    Monotone (fun L => history Ω level cycle m L (Sum.inr b)) := by
  apply monotone_nat_of_le_succ
  intro L
  exact period_bridge_mono Ω level cycle L _ b

lemma history_total_mono (level : B → Fin n) (cycle : List B) (m : Lattice n B) (i : Fin n) :
    Monotone (fun L => levelTotal level i (history Ω level cycle m L)) := by
  intro L L' h
  apply Finset.sum_le_sum
  intro b _
  split_ifs
  · exact history_bridge_mono Ω level cycle m b h
  · rfl

lemma history_deficit_step (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (i : Fin n) (N L : ℕ) :
    cutDeficit level i N (L+1) (history Ω level cycle m (L+1)) =
      cutDeficit level i N L (history Ω level cycle m L) -
        levelTotal level i (history Ω level cycle m (L+1)) := by
  have h := periodFunctional_period Ω level i cycle L (history Ω level cycle m L)
  change periodFunctional level i L (history Ω level cycle m (L+1)) = _ at h
  simp only [cutDeficit,periodFunctional,AddMonoidHom.add_apply,AddMonoidHom.zsmul_apply,
    smul_eq_mul,Nat.cast_add,Nat.cast_one] at *
  linear_combination -h

lemma history_total_nonpos (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (N : ℕ) (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L))
    (L : ℕ) (i : Fin n) : levelTotal level i (history Ω level cycle m L) ≤ 0 :=
  period_total_nonpos (fun L => cutDeficit level i N L (history Ω level cycle m L))
    (fun L => levelTotal level i (history Ω level cycle m L)) (fun L => hs L i)
    (history_total_mono Ω level cycle m i) (history_deficit_step Ω level cycle m i N) L

lemma history_bridge_stabilizes (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (N : ℕ) (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L)) :
    ∃ T, ∀ L, T ≤ L → ∀ b, history Ω level cycle m L (Sum.inr b) =
      history Ω level cycle m T (Sum.inr b) := by
  apply finite_coordinates_stabilize (fun L b => history Ω level cycle m L (Sum.inr b))
    (history_bridge_mono Ω level cycle m)
  intro L
  rw [←total_levels level]
  exact Finset.sum_nonpos (fun i _ => history_total_nonpos Ω level cycle m N hs L i)
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLateStationarity
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.forwardCoord_roots _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchor_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchors _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_anchor _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil _root_.OAI.ElementaryPositivity.TriangularDynamics.scheduledBridge_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
variable (Ω : Lattice n B →+ Lattice n B →+ ℤ)

omit [Fintype B] in
lemma period_of_bridge_eq (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B)
    (h : ∀ b, period Ω level cycle L m (Sum.inr b) = m (Sum.inr b)) :
    period Ω level cycle L m = m ∧ ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) m := by
  induction cycle generalizing m with
  | nil => exact ⟨rfl,by simp⟩
  | cons b bs ih =>
    have hle := period_bridge_mono Ω level bs L (rotate Ω level L m b) b
    change rotate Ω level L m b (Sum.inr b) ≤ period Ω level (b::bs) L m (Sum.inr b) at hle
    rw [h b] at hle
    have ht : max 0 (-Ω (eventRoot level L b) m) = 0 := by
      simp only [rotate,mutationIncomingLabel,Pi.add_apply,Pi.smul_apply,eventRoot_bridge,
        ite_true, if_true,smul_eq_mul,mul_one] at hle
      omega
    have hfix : rotate Ω level L m b = m := by
      simp only [rotate,mutationIncomingLabel,ht,zero_zsmul,add_zero]
    have hp : period Ω level (b::bs) L m = period Ω level bs L m := by
      change period Ω level bs L (rotate Ω level L m b) = _
      rw [hfix]
    have H := ih m (by intro c; simpa only [hp] using h c)
    refine ⟨hp.trans H.1,fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · omega
    · exact H.2 c hc

lemma history_late_fixed (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (N : ℕ) (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L)) :
    ∃ T, (∀ L, T ≤ L → history Ω level cycle m L = history Ω level cycle m T) ∧
      ∀ L, T ≤ L → ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) (history Ω level cycle m T) := by
  obtain ⟨T,hT⟩ := history_bridge_stabilizes Ω level cycle m N hs
  have he : ∀ L, T ≤ L → period Ω level cycle L (history Ω level cycle m L) =
      history Ω level cycle m L ∧
      ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) (history Ω level cycle m L) := by
    intro L hL
    apply period_of_bridge_eq
    intro b
    change history Ω level cycle m (L+1) (Sum.inr b) = history Ω level cycle m L (Sum.inr b)
    rw [hT (L+1) (by omega) b,hT L hL b]
  have hconst : ∀ k, history Ω level cycle m (T+k) = history Ω level cycle m T := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ,history]
      exact ((he (T+k) (by omega)).1).trans ih
  refine ⟨T,?_,?_⟩
  · intro L hL
    simpa only [Nat.add_sub_of_le hL] using hconst (L-T)
  · intro L hL b hb
    have HH := (he L hL).2 b hb
    have H := hconst (L-T)
    rw [Nat.add_sub_of_le hL] at H
    simpa only [H] using HH

omit [Fintype B] in
lemma eventRoot_pairing (level : B → Fin n) (L : ℕ) (b : B) (m : Lattice n B) :
    Ω (eventRoot level L b) m = Ω (eventRoot level 0 b) m + (L:ℤ)*Ω (delta level b) m := by
  simp only [eventRoot,Nat.cast_zero,zero_zsmul,add_zero,map_add,map_zsmul,
    AddMonoidHom.add_apply,AddMonoidHom.zsmul_apply,smul_eq_mul]

omit [Fintype B] in
lemma period_fixed (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B)
    (hp : ∀ b ∈ cycle, 0 ≤ Ω (eventRoot level L b) m) : period Ω level cycle L m = m := by
  induction cycle with
  | nil => rfl
  | cons b bs ih =>
    change period Ω level bs L (mutationIncomingLabel Ω (eventRoot level L b) m) = m
    rw [mutationIncomingLabel_nonnegative Ω _ m (hp b (by simp))]
    exact ih (by intro c hc; exact hp c (by simp [hc]))

omit [Fintype B] in
lemma period_injective (hΩ : ∀ m, Ω m m = 0) (level : B → Fin n) (cycle : List B) (L : ℕ) :
    Function.Injective (period Ω level cycle L) := by
  induction cycle with
  | nil => exact Function.injective_id
  | cons b bs ih =>
    intro m m' h
    apply (mutationIncomingLabelEquiv Ω (eventRoot level L b) (hΩ _)).injective
    apply ih
    exact h

omit [Fintype B] in
lemma history_injective (hΩ : ∀ m, Ω m m = 0) (level : B → Fin n) (cycle : List B) (L : ℕ) :
    Function.Injective (fun m => history Ω level cycle m L) := by
  induction L with
  | zero => exact Function.injective_id
  | succ L ih =>
    intro m m' h
    apply ih
    exact period_injective Ω hΩ level cycle L h

omit [Fintype B] in
lemma history_fixed (level : B → Fin n) (cycle : List B) (m : Lattice n B)
    (hp : ∀ L b, b ∈ cycle → 0 ≤ Ω (eventRoot level L b) m) (L : ℕ) :
    history Ω level cycle m L = m := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [history,ih]
    exact period_fixed Ω level cycle L m (hp L)
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

omit [DecidableEq B] in
lemma extendedTotal_nonpos (level : B → Fin n) (m : Lattice n B)
    (h : ∀ i, levelTotal level i m ≤ 0) (k : ℕ) : extendedTotal level m k ≤ 0 := by
  unfold extendedTotal
  split_ifs with hk
  · exact h _
  · rfl

omit [DecidableEq B] in
lemma extendedTotal_all_zero (level : B → Fin n) (m : Lattice n B)
    (h : ∀ k, k ≤ n+1 → extendedTotal level m k = 0) (k : ℕ) :
    extendedTotal level m k = 0 := by
  by_cases hk : k ≤ n+1
  · exact h k hk
  · simp [extendedTotal,show ¬(0<k ∧ k≤n) by omega]

variable (Ω : Lattice n B →+ Lattice n B →+ ℤ)

lemma tropical_history_stationary (hΩ : ∀ m, Ω m m = 0)
    (level : B → Fin n) (hl : Function.Surjective level)
    (cycle : List B) (hcycle : ∀ b, b ∈ cycle)
    (hdelta : ∀ b m, Ω (delta level b) m =
      2*extendedTotal level m ((level b).val+1) - extendedTotal level m (level b).val -
        extendedTotal level m ((level b).val+2))
    (m : Lattice n B) (N : ℕ)
    (hs : ∀ L i, 0 ≤ cutDeficit level i N L (history Ω level cycle m L)) :
    (∀ i, levelTotal level i m = 0) ∧
      (∀ b, 0 ≤ Ω (eventRoot level 0 b) m) ∧
      (∀ L, history Ω level cycle m L = m) := by
  obtain ⟨T,hT,hp⟩ := history_late_fixed Ω level cycle m N hs
  let star := history Ω level cycle m T
  have hslope : ∀ b, 0 ≤ Ω (delta level b) star := by
    intro b
    apply nonnegative_affine_slope (Ω (eventRoot level 0 b) star)
    refine ⟨T,fun L hL => ?_⟩
    rw [←eventRoot_pairing]
    exact hp L hL b (hcycle b)
  have ht : ∀ k, k ≤ n+1 → extendedTotal level star k = 0 := by
    apply concave_nonpositive_zero (n+1) (extendedTotal level star)
      (extendedTotal_zero _ _) (extendedTotal_last _ _)
    · intro k _
      exact extendedTotal_nonpos level star (fun i => history_total_nonpos Ω level cycle m N hs T i) k
    · intro k hk hkn
      let i : Fin n := ⟨k-1,by omega⟩
      obtain ⟨b,hb⟩ := hl i
      have HH := hslope b
      rw [hdelta,hb] at HH
      have hi : i.val+1=k := by dsimp [i]; omega
      have hi' : i.val+2=k+1 := by omega
      rw [hi,hi'] at HH
      exact HH
  have hall := extendedTotal_all_zero level star ht
  have hd0 : ∀ b, Ω (delta level b) star = 0 := by
    intro b
    rw [hdelta,hall,hall,hall]
    ring
  have hp0 : ∀ b, 0 ≤ Ω (eventRoot level 0 b) star := by
    intro b
    have HH := hp T le_rfl b (hcycle b)
    change 0 ≤ Ω (eventRoot level T b) star at HH
    rw [eventRoot_pairing,hd0,mul_zero,add_zero] at HH
    exact HH
  have hpl : ∀ L b, b ∈ cycle → 0 ≤ Ω (eventRoot level L b) star := by
    intro L b _
    rw [eventRoot_pairing,hd0,mul_zero,add_zero]
    exact hp0 b
  have hm : m = star := by
    apply history_injective Ω hΩ level cycle T
    change history Ω level cycle m T = history Ω level cycle star T
    rw [history_fixed Ω level cycle star hpl T]
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [hm,←extendedTotal_succ]
    exact hall _
  · simpa only [hm] using hp0
  · intro L
    rw [hm]
    exact history_fixed Ω level cycle star hpl L
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteLatticePairing
attribute [-instance] _root_.OAI.ElementaryPositivity.TriangularDynamics.instAntisymmCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instDecidableRelCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instIsTransCellPhaseLE _root_.OAI.ElementaryPositivity.TriangularDynamics.instTotalCellPhaseLE
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.forwardCoord_roots _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchor_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_anchors _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_anchor _root_.OAI.ElementaryPositivity.TriangularDynamics.omega_delta_delta _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil _root_.OAI.ElementaryPositivity.TriangularDynamics.scheduledBridge_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma matrixPairing_apply (K : Matrix V V ℤ) (x y : V → ℤ) :
    matrixPairing K x y = ∑ a, ∑ b, x a * K a b * y b :=
  Matrix.toBilin'_apply _ _ _

lemma matrixPairing_single_left (K : Matrix V V ℤ) (a : V) (m : V → ℤ) :
    matrixPairing K (Pi.single a 1) m = ∑ b, K a b * m b := by
  rw [matrixPairing_apply,Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

lemma matrixPairing_skew (K : Matrix V V ℤ) (hK : ∀ a b, K a b = -K b a)
    (x y : V → ℤ) : matrixPairing K x y = -matrixPairing K y x := by
  rw [matrixPairing_apply,matrixPairing_apply,Finset.sum_comm]
  simp only [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hK b a]
  ring

lemma matrixPairing_self (K : Matrix V V ℤ) (hK : ∀ a b, K a b = -K b a)
    (m : V → ℤ) : matrixPairing K m m = 0 := by
  have := matrixPairing_skew K hK m m
  omega

variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
lemma chartMatrix_skew (level : B → Fin n) (bb : B → B → ℤ)
    (hbb : ∀ b c, bb b c = -bb c b) (a c : Vertex n B) :
    chartMatrix level bb a c = -chartMatrix level bb c a := by
  cases a <;> cases c <;> simp only [chartMatrix]
  · rfl
  · ring
  · ring
  · apply hbb

lemma chartPairing_self (level : B → Fin n) (bb : B → B → ℤ)
    (hbb : ∀ b c, bb b c = -bb c b) (m : Lattice n B) :
    chartPairing level bb m m = 0 :=
  matrixPairing_self _ (chartMatrix_skew level bb hbb) m

omit [DecidableEq B] in
lemma total_as_sum (level : B → Fin n) (m : Lattice n B) (k : ℕ) :
    extendedTotal level m k = ∑ b, if (level b).val+1=k then m (.inr b) else 0 := by
  unfold extendedTotal
  split_ifs with hk
  · change (∑ b, if level b = ⟨k-1,by omega⟩ then m (.inr b) else 0) = _
    apply Finset.sum_congr rfl
    intro b _
    have hh : level b = (⟨k-1,by omega⟩ : Fin n) ↔ (level b).val+1=k := by
      constructor
      · intro h; have := congrArg Fin.val h; dsimp at this; omega
      · intro h; apply Fin.ext; dsimp; omega
    simp only [hh]
  · symm
    apply Finset.sum_eq_zero
    intro b _
    have hne : ¬(level b).val+1=k := by have := (level b).isLt; omega
    simp [hne]

lemma chartPairing_anchor (level : B → Fin n) (bb : B → B → ℤ)
    (a : Fin (n+1)) (m : Lattice n B) :
    chartPairing level bb (anchor a) m =
      extendedTotal level m a.val - extendedTotal level m (a.val+1) := by
  change matrixPairing (chartMatrix level bb) (Pi.single (.inl a) 1) m = _
  rw [matrixPairing_single_left,Fintype.sum_sum_type]
  simp only [chartMatrix,zero_mul,Finset.sum_const_zero,zero_add]
  rw [total_as_sum,total_as_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have h1 : a = (level b).succ ↔ (level b).val+1=a.val := by
    rw [Fin.ext_iff]; simp only [Fin.val_succ]; omega
  have h2 : a = (level b).castSucc ↔ (level b).val+1=a.val+1 := by
    rw [Fin.ext_iff]; simp only [Fin.val_castSucc]; omega
  simp only [h1,h2]
  split_ifs <;> ring

lemma chartPairing_delta (level : B → Fin n) (bb : B → B → ℤ)
    (b : B) (m : Lattice n B) :
    chartPairing level bb (delta level b) m =
      2*extendedTotal level m ((level b).val+1) - extendedTotal level m (level b).val -
        extendedTotal level m ((level b).val+2) := by
  simp only [delta,map_sub,AddMonoidHom.sub_apply,chartPairing_anchor,
    Fin.val_succ,Fin.val_castSucc]
  ring

lemma chart_tropical_stationary (level : B → Fin n) (hl : Function.Surjective level)
    (bb : B → B → ℤ) (hbb : ∀ b c, bb b c = -bb c b)
    (cycle : List B) (hcycle : ∀ b, b ∈ cycle) (m : Lattice n B) (N : ℕ)
    (hs : ∀ L i, 0 ≤ cutDeficit level i N L
      (history (chartPairing level bb) level cycle m L)) :
    (∀ i, levelTotal level i m = 0) ∧
      (∀ b, 0 ≤ chartPairing level bb (eventRoot level 0 b) m) ∧
      (∀ L, history (chartPairing level bb) level cycle m L = m) :=
  tropical_history_stationary _ (chartPairing_self level bb hbb) level hl cycle hcycle
    (chartPairing_delta level bb) m N hs

end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

lemma triangularBB_skew {n : ℕ} (b c : Cell n) : triangularBB b c= -triangularBB c b := by
  unfold triangularBB
  ring

lemma triangularOmega_self {n : ℕ} (m : Lattice n (Cell n)) : triangularOmega n m m=0 :=
  chartPairing_self _ _ triangularBB_skew m

end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularGapOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ}

lemma phaseCycle_nodup : (phaseCycle n).Nodup := Finset.sort_nodup _ _
lemma phaseCycle_pairwise : (phaseCycle n).Pairwise phaseLE := by
  exact Finset.pairwise_sort _ _

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLevelQueues
attribute [-simp] _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_last _root_.OAI.ElementaryPositivity.TriangularDynamics.levelNode_zero _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_cycle _root_.OAI.ElementaryPositivity.TriangularDynamics.partialBridge_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ}

lemma initialLevelQueue_mem (i : Fin n) (b : Cell n) :
    b∈initialLevelQueue i ↔ b.1=i := by
  rw [initialLevelQueue,List.mem_ofFn]
  constructor
  · rintro ⟨j,rfl⟩; rfl
  · intro hb
    cases b with | mk l r =>
      dsimp only at hb
      subst l
      exact ⟨r.rev,by simp⟩

lemma initialLevelQueue_nodup (i : Fin n) : (initialLevelQueue i).Nodup := by
  rw [initialLevelQueue,List.nodup_ofFn]
  intro j k h
  have hh:=congrArg cellRow h
  apply Fin.rev_injective
  exact Fin.ext hh

lemma initialLevelQueue_pairwise (i : Fin n) : (initialLevelQueue i).Pairwise phaseLE := by
  rw [initialLevelQueue,List.pairwise_ofFn]
  intro j k hjk
  apply Or.inl
  apply Or.inl
  change k.rev.val < j.rev.val
  simp only [Fin.val_rev]
  have := k.isLt
  omega

lemma phaseCycle_levelQueue (i : Fin n) : levelQueue (phaseCycle n) i=initialLevelQueue i := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba=>Std.Antisymm.antisymm (r:=phaseLE) a b hab hba)
  · exact List.Pairwise.filter _ phaseCycle_pairwise
  · exact initialLevelQueue_pairwise i
  · apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ phaseCycle_nodup)
      (initialLevelQueue_nodup i)).mpr
    intro b
    simp only [List.mem_filter,decide_eq_true_eq,mem_phaseCycle,true_and,initialLevelQueue_mem]

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ForwardChartMutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.ForwardChain
variable {M : Type*} [AddCommGroup M]
lemma gaps_ofFn_nodes {k:ℕ} (x:Fin (k+2) → M) :
    gaps (x 0) (List.ofFn (fun j:Fin k=>x j.succ.castSucc)) (x (Fin.last (k+1)))=
      List.ofFn (fun j:Fin (k+1)=>x j.succ-x j.castSucc) := by
  induction k with
  | zero => simp [gaps,List.ofFn_succ]
  | succ k ih =>
    rw [List.ofFn_succ,gaps,List.ofFn_succ]
    congr 1
    exact ih (fun j=>x j.succ)
end ElementaryPositivity.ForwardChain

end
section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ} {R : Type*} [CommRing R]

lemma levelNode_middle (i:Fin n) (j:Fin (i.val+1)) :
    levelNode i j.succ.castSucc=.inr ⟨i,j.rev⟩ := by
  simp only [levelNode,Fin.val_castSucc,Fin.val_succ]
  rw [dite_eq_right (by omega),dite_eq_right (by have := j.isLt; omega)]
  congr 2

lemma mem_gapIndices (g:GapIndex n) : g∈gapIndices n := by
  rcases g with ⟨i,j⟩
  exact List.mem_flatMap.mpr ⟨i,List.mem_finRange _,List.mem_map.mpr ⟨j,List.mem_finRange _,rfl⟩⟩
lemma gapIndices_nodup : (gapIndices n).Nodup := by
  rw [gapIndices,List.nodup_flatMap]
  constructor
  · intro i _
    exact (List.nodup_finRange _).map (fun a b h=>by cases h; rfl)
  · apply (List.nodup_finRange n).pairwise_of_forall_ne
    intro i j _ _ hij g hg hg'
    obtain ⟨a,_,ha⟩:=List.mem_map.mp hg
    obtain ⟨b,_,hb⟩:=List.mem_map.mp hg'
    exact hij (by simpa using congrArg Sigma.fst (ha.trans hb.symm))

lemma initial_levelGaps (i:Fin n) :
    levelGaps (anchor (n:=n)) bridge (phaseCycle n) i=
      (List.finRange (i.val+2)).map (fun j=>forwardGap (R:=ℤ) ⟨i,j⟩) := by
  rw [levelGaps,phaseCycle_levelQueue,initialLevelQueue,List.map_ofFn]
  have H:=ForwardChain.gaps_ofFn_nodes (fun j:Fin (i.val+3)=>
    (Pi.single (levelNode i j) 1:Vertex n (Cell n) → ℤ))
  simpa only [levelNode_zero,levelNode_last,levelNode_middle,anchor,bridge,
    forwardGap,List.ofFn_eq_map,Function.comp_def] using H

lemma initial_forwardInventory :
    forwardInventory anchor bridge (phaseCycle n)=
      (gapIndices n).map (forwardGap (R:=ℤ)) := by
  rw [forwardInventory,gapIndices,List.map_flatMap]
  congr 1
  funext i
  rw [initial_levelGaps,List.map_map]
  rfl

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.LatticeExtension
open scoped BigOperators
variable {V : Type*} [Fintype V]

variable (Ω : (V → ℤ) →+ (V → ℤ) →+ ℤ)

lemma form_self (hΩ : ∀m,Ω m m=0) (x : Extended V) : form Ω x x=0 := by
  rw [form_apply,hΩ,zero_add]
  have H : dot x.2 x.1=dot x.1 x.2 := by
    simp only [dot_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [H,sub_self]

lemma form_nondegenerate [DecidableEq V] : ∀r≠0,∃m,form Ω r m≠0 := by
  intro r hr
  by_contra hh
  push Not at hh
  have hfirst : r.1=0 := by
    ext i
    have H:=hh (0,Pi.single i 1)
    simp only [form_apply,map_zero,dot_single,zero_add,zero_sub,neg_eq_zero] at H
    exact H
  have hsecond : r.2=0 := by
    ext i
    have H:=hh (Pi.single i 1,0)
    simp only [form_apply,hfirst,map_zero,AddMonoidHom.zero_apply,zero_add,
      dot_single,sub_zero] at H
    exact H
  exact hr (Prod.ext hfirst hsecond)
end ElementaryPositivity.LatticeExtension

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialSection
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
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))

local instance polynomialSectionRing_ra40566_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance polynomialSectionAddCommMonoid_ra40566_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialSectionAddGroup_ra40566_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
omit [DecidableEq I] in
include hΩ in
lemma actualMonomialAdjoint_support (τ:M →+ ℤ) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (b m:M) (hm:actualMonomialAdjointCoefficient Ω τ f.val b m≠0) :
    ∃d,HasRootDegree C d (m-b) := by
  have H:=normalizedMonomialAction_graded LaurentRay.vUnit Ω hΩ C f b
  unfold actualMonomialAdjointCoefficient actualRootCoefficient at hm
  split_ifs at hm with ht
  · refine ⟨(τ (m-b)).toNat,?_⟩
    by_contra hn
    exact hm (by rw [H _ _ hn,zero_mul])
  · exact (hm (zero_mul _)).elim

omit [DecidableEq I] in
include hΩ in
lemma actualPolynomialAdjoint_support (τ:M →+ ℤ) (f:CompletedPositive LaurentRay.vUnit Ω C)
    (F:Torus LaurentRay.vUnit Ω) (m:M)
    (hm:actualPolynomialAdjointCoefficient Ω τ f.val F m≠0) :
    ∃b∈F.support,∃d,HasRootDegree C d (m-b) := by
  classical
  unfold actualPolynomialAdjointCoefficient Finsupp.sum at hm
  obtain ⟨b,hb,hb'⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨b,hb,actualMonomialAdjoint_support Ω hΩ C τ f b m ?_⟩
  intro hh
  exact hb' (show F b * actualMonomialAdjointCoefficient Ω τ f.val b m = 0 from by simp only [hh,mul_zero])

include hΩ in
lemma polynomialSection_support (h:M →+ ℝ) (F:Torus LaurentRay.vUnit Ω) (m:M)
    (hm:polynomialSectionCoefficient Ω C coord h F m≠0) :
    ∃b∈F.support,∃d,HasRootDegree C d (m-b) :=
  actualPolynomialAdjoint_support Ω hΩ C (rootOrder coord) (rootSectionChart Ω C h) F m hm

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RealLatticeRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LatticeRealization
open scoped BigOperators
open TriangularDynamics
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma cast_injective : Function.Injective (cast (V:=V)) := by
  intro a b h
  ext i
  have H := congrFun h i
  change (a i : ℝ)=(b i : ℝ) at H
  exact_mod_cast H

variable (A : Matrix V V ℤ)

lemma realPairing_apply (x y : V → ℝ) :
    realPairing A x y=∑i,∑j,x i*(A i j:ℝ)*y j := Matrix.toBilin'_apply _ _ _

lemma realPairing_cast (x y : V → ℤ) :
    realPairing A (cast x) (cast y)=(matrixPairing A x y:ℝ) := by
  simp only [realPairing_apply,matrixPairing_apply,cast_apply,Int.cast_sum,Int.cast_mul]

lemma realPairing_skew (hA : ∀i j,A i j= -A j i) (x y : V → ℝ) :
    realPairing A x y= -realPairing A y x := by
  rw [realPairing_apply,realPairing_apply,Finset.sum_comm]
  simp only [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA j i,Int.cast_neg]
  ring

lemma realPairing_self (hA : ∀i j,A i j= -A j i) (x : V → ℝ) :
    realPairing A x x=0 := by
  have H:=realPairing_skew A hA x x
  linarith

lemma realDot_apply (x y : V → ℝ) : realDot x y=∑i,x i*y i := by
  simp [realDot,Matrix.toBilin'_apply,Matrix.one_apply]
lemma realDot_comm (x y : V → ℝ) : realDot x y=realDot y x := by
  simp only [realDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring
lemma realDot_cast (x y : V → ℤ) :
    realDot (cast x) (cast y)=(LatticeExtension.dot x y:ℝ) := by
  simp only [realDot_apply,LatticeExtension.dot_apply,cast_apply,Int.cast_sum,Int.cast_mul]

omit [Fintype V] [DecidableEq V] in
lemma extendedCast_apply (x : LatticeExtension.Extended V) :
    extendedCast x=(cast x.1,cast x.2) := rfl
omit [Fintype V] [DecidableEq V] in
lemma extendedCast_injective : Function.Injective (extendedCast (V:=V)) := by
  intro a b h
  apply Prod.ext
  · exact cast_injective (congrArg Prod.fst h)
  · exact cast_injective (congrArg Prod.snd h)

lemma extendedRealForm_apply (x y : (V → ℝ) × (V → ℝ)) :
    extendedRealForm A x y=realPairing A x.1 y.1+realDot x.2 y.1-realDot x.1 y.2 := rfl

lemma extendedRealForm_self (hA : ∀i j,A i j= -A j i) (x : (V → ℝ) × (V → ℝ)) :
    extendedRealForm A x x=0 := by
  rw [extendedRealForm_apply,realPairing_self A hA,zero_add,realDot_comm x.2 x.1,sub_self]

lemma extendedRealForm_cast (x y : LatticeExtension.Extended V) :
    extendedRealForm A (extendedCast x) (extendedCast y)=
      (LatticeExtension.form (matrixPairing A) x y:ℝ) := by
  simp only [extendedRealForm_apply,extendedCast_apply,realPairing_cast,realDot_cast,
    LatticeExtension.form_apply,Int.cast_sub,Int.cast_add]

end ElementaryPositivity.LatticeRealization

end
section
namespace ElementaryPositivity.ForwardChain
variable {M M':Type*} [AddCommGroup M] [AddCommGroup M']
lemma gaps_map (a:M →+ M') (x y:M) (bs:List M) :
    gaps (a x) (bs.map a) (a y)=(gaps x bs y).map a := by
  induction bs generalizing x with
  | nil => simp [gaps,map_sub]
  | cons b bs ih => simp only [gaps,List.map_cons,map_sub,ih]
end ElementaryPositivity.ForwardChain

namespace ElementaryPositivity.TriangularDynamics
variable {n:ℕ} {M M':Type*} [AddCommGroup M] [AddCommGroup M']
lemma forwardInventory_map (a:M →+ M') (d:Fin (n+1) → M) (w:Cell n → M) (q:List (Cell n)) :
    forwardInventory (a ∘ d) (a ∘ w) q=(forwardInventory d w q).map a := by
  unfold forwardInventory
  rw [List.map_flatMap]
  congr 1
  funext i
  simp only [levelGaps,Function.comp_apply,←List.map_map,ForwardChain.gaps_map]
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus LatticeExtension LatticeRealization
open Classical
noncomputable section
variable {n:ℕ}

lemma initialFreeChart_inventory :
    ((gapIndices n).map (simpleRoot (initialFreeChart n).roots)).Perm
      (forwardInventory (includeVertices ∘ anchor) (includeVertices ∘ bridge) (phaseCycle n)) := by
  apply List.Perm.of_eq
  rw [forwardInventory_map,initial_forwardInventory,List.map_map]
  apply List.map_congr_left
  intro g _
  exact extendedRoot_eq g

lemma extendedOmega_self : ∀m,extendedOmega n m m=0 := form_self _ triangularOmega_self
lemma extendedOmega_nondegenerate : ∀r≠0,∃m,extendedOmega n r m≠0 := form_nondegenerate _
lemma triangularRealForm_self : ∀m, triangularRealForm n m m=0 :=
  extendedRealForm_self _ (chartMatrix_skew cellLevel triangularBB triangularBB_skew)
lemma triangularRealForm_compatible (m m':Extended (Vertex n (Cell n))) :
    triangularRealForm n (extendedCast m) (extendedCast m')=(extendedOmega n m m':ℝ) :=
  extendedRealForm_cast _ _ _
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularPolynomialStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization
open Classical
noncomputable section
variable {n:ℕ}

lemma cellLevel_surjective : Function.Surjective (@cellLevel n) := by
  intro i
  exact ⟨⟨i,⟨0,by omega⟩⟩,rfl⟩

lemma triangularExpression_stationary {N:ℕ} (f:ElementaryExpr N) (m:Lattice n (Cell n))
    (hm:triangularIncoming f m≠0) :
    (∀i,levelTotal cellLevel i m=0) ∧
      (∀b,0≤triangularOmega n (eventRoot cellLevel 0 b) m) ∧
      (∀L,history (triangularOmega n) cellLevel (phaseCycle n) m L=m) := by
  apply chart_tropical_stationary cellLevel cellLevel_surjective triangularBB triangularBB_skew
    (phaseCycle n) (mem_phaseCycle (n:=n)) m N
  intro L i
  have hzero : periodBridge (n:=n) 0 = bridge := by
    funext c
    simp [periodBridge]
  have hinv : ((gapIndices n).map (simpleRoot (initialFreeChart n).roots)).Perm
      (forwardInventory (includeVertices ∘ anchor) (includeVertices ∘ periodBridge 0) (phaseCycle n)) := by
    simpa only [hzero] using initialFreeChart_inventory (n:=n)
  have hm' : polynomialSectionIncoming (extendedOmega n) (initialFreeChart n).roots (initialFreeChart n).coord
      (f.eval LaurentRay.vUnit (extendedOmega n)
        (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ periodBridge 0)))
      (includeVertices m)≠0 := by
    simpa only [triangularIncoming,triangularExpression,initialFreeChart,hzero] using hm
  exact genuine_history_cut_deficit (extendedOmega n) extendedOmega_self extendedCast extendedCast_injective
    (triangularRealForm n) triangularRealForm_self triangularRealForm_compatible extendedOmega_nondegenerate
    includeVertices extendedOmega_original (AddMonoidHom.fst _ _) (fun _=>rfl)
    (gapIndices n) (gapIndices_nodup (n:=n)) (mem_gapIndices (n:=n)) (initialFreeChart n) hinv f m hm' L i
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open QuantumTorus
open Classical
noncomputable section
variable {n:ℕ} {R:Type*} [CommRing R]

lemma forwardRoots_single (g:GapIndex n) (r:R) :
    forwardRoots (Pi.single g r)=r • forwardGap g := by
  rw [forwardRoots_apply,Finset.sum_eq_single g]
  · simp
  · intro h _ hh
    simp [Ne.symm hh]
  · simp

lemma forwardRoots_coord_gap (g:GapIndex n) :
    forwardRoots (forwardCoord (forwardGap (R:=R) g))=forwardGap g := by
  rw [forwardCoord_gap,forwardRoots_single,one_smul]

lemma forwardRoots_coord_level (i:Fin n)
    (h:forwardRoots (forwardCoord (Pi.single (.inl i.castSucc) (1:R)))=
      Pi.single (.inl i.castSucc) 1-Pi.single (.inl (0:Fin (n+1))) 1)
    (j:Fin (i.val+3)) :
    forwardRoots (forwardCoord (Pi.single (levelNode i j) (1:R)))=
      Pi.single (levelNode i j) 1-Pi.single (.inl (0:Fin (n+1))) 1 := by
  induction j using Fin.induction with
  | zero => simpa only [levelNode_zero] using h
  | succ j ih =>
    have H:=forwardRoots_coord_gap (R:=R) (⟨i,j⟩:GapIndex n)
    simp only [forwardGap,map_sub] at H
    rw [ih] at H
    exact sub_eq_iff_eq_add.mp H |>.trans (by abel)

lemma forwardRoots_coord_anchor (a:Fin (n+1)) :
    forwardRoots (forwardCoord (Pi.single (.inl a) (1:R)))=
      Pi.single (.inl a) 1-Pi.single (.inl (0:Fin (n+1))) 1 := by
  induction a using Fin.induction with
  | zero =>
    have hz:forwardCoord (Pi.single (.inl (0:Fin (n+1))) (1:R))=0 := by
      ext g
      simp [forwardCoord_single,afterGap]
    rw [hz,map_zero,sub_self]
  | succ i ih =>
    simpa only [levelNode_last] using forwardRoots_coord_level i ih (Fin.last (i.val+2))

lemma forwardRoots_coord_vertex (a:Vertex n (Cell n)) :
    forwardRoots (forwardCoord (Pi.single a (1:R)))=Pi.single a 1-Pi.single (.inl (0:Fin (n+1))) 1 := by
  cases a with
  | inl a => exact forwardRoots_coord_anchor a
  | inr b =>
    let j:Fin (b.1.val+3):=⟨b.1.val+1-b.2.val,by have := b.2.isLt; omega⟩
    have hj:levelNode b.1 j=.inr b:=by
      have haq:=b.2.isLt
      simp only [levelNode,j]
      rw [dite_eq_right (by omega),dite_eq_right (by omega)]
      congr 1
      apply cell_ext
      · rfl
      change b.1.val+1-(b.1.val+1-b.2.val)=b.2.val
      omega
    simpa only [hj] using forwardRoots_coord_level b.1 (forwardRoots_coord_anchor b.1.castSucc) j

lemma vertexWeight_apply (m:Vertex n (Cell n) → R) : vertexWeight m=∑a,m a := by
  simp [vertexWeight,LinearMap.sum_apply]

lemma forwardRoots_coord (m:Vertex n (Cell n) → R) :
    forwardRoots (forwardCoord m)=m-vertexWeight m • Pi.single (.inl (0:Fin (n+1))) 1 := by
  have hm:m=∑a,m a • Pi.single a (1:R) := by
    ext a
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  calc
    _ = ∑a,m a • forwardRoots (forwardCoord (Pi.single a (1:R))) := by
      conv_lhs => rw [hm]
      simp only [map_sum,map_smul]
    _ = ∑a,m a • (Pi.single a (1:R)-Pi.single (.inl (0:Fin (n+1))) 1) := by
      simp_rw [forwardRoots_coord_vertex]
    _ = (∑a,m a • Pi.single a (1:R))-(∑a,m a • Pi.single (.inl (0:Fin (n+1))) 1) := by
      simp only [smul_sub,Finset.sum_sub_distrib]
    _ = _ := by rw [←hm,←Finset.sum_smul,vertexWeight_apply]

lemma forwardCoord_nonneg (m:Lattice n (Cell n)) (hm:∀a,0 ≤ m a) (g:GapIndex n) :
    0 ≤ forwardCoord m g := by
  rw [forwardCoord_apply]
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> first | exact hm a | omega

lemma triangularVertex_rootDegree (m:Lattice n (Cell n)) (hm:∀a,0 ≤ m a) :
    ∃k,HasRootDegree (forwardRoots (R:=ℤ) (n:=n)).toAddMonoidHom k (m-vertexWeight m • anchor 0) := by
  let c:GapIndex n → ℕ:=fun g=>(forwardCoord m g).toNat
  have hc:(fun g=>(c g:ℤ))=forwardCoord m := by
    ext g
    exact Int.toNat_of_nonneg (forwardCoord_nonneg m hm g)
  refine ⟨∑g,c g,c,rfl,?_⟩
  change forwardRoots (fun g=>(c g:ℤ))=m-vertexWeight m • anchor 0
  rw [hc,forwardRoots_coord]
  rfl
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularIncoming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma initial_vertexDisplay (a:Vertex n (Cell n)) :
    vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge) a=
      includeVertices (Pi.single a (1:ℤ)) := by cases a <;> rfl

lemma triangularSeed_nonneg {N:ℕ} (f:ElementaryExpr N)
    (m:Extended (Vertex n (Cell n))) (hm:m∈(triangularExpression f).support)
    (a:Vertex n (Cell n)) : 0 ≤ m.1 a := by
  let ell : Extended (Vertex n (Cell n)) →+ ℤ :=
    -((Pi.evalAddMonoidHom (fun _=>ℤ) a).comp (AddMonoidHom.fst _ _))
  have H:=f.cutSupported_scaled LaurentRay.vUnit (extendedOmega n) ell 0
    (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) (fun x=>by
      rw [initial_vertexDisplay]
      change -((Pi.single x (1:ℤ) : Lattice n (Cell n)) a) ≤ 0
      simp only [Pi.single_apply]
      split_ifs <;> omega) m hm
  change -(m.1 a) ≤ (N:ℤ)*0 at H
  omega

lemma triangularSeed_dual_zero {N:ℕ} (f:ElementaryExpr N)
    (m:Extended (Vertex n (Cell n))) (hm:m∈(triangularExpression f).support) : m.2=0 := by
  ext a
  let ell : Extended (Vertex n (Cell n)) →+ ℤ :=
    (Pi.evalAddMonoidHom (fun _=>ℤ) a).comp (AddMonoidHom.snd _ _)
  have H:=f.weight LaurentRay.vUnit (extendedOmega n) ell 0
    (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) (fun x=>by
      rw [initial_vertexDisplay]; rfl) m hm
  change m.2 a=(N:ℤ)*0 at H
  change m.2 a=0
  simpa only [mul_zero] using H

lemma triangularSeed_weight {N:ℕ} (f:ElementaryExpr N)
    (m:Extended (Vertex n (Cell n))) (hm:m∈(triangularExpression f).support) : vertexWeight m.1=(N:ℤ) := by
  let ell: Extended (Vertex n (Cell n)) →+ ℤ :=
    (vertexWeight (R:=ℤ)).toAddMonoidHom.comp (AddMonoidHom.fst _ _)
  have H:=f.weight LaurentRay.vUnit (extendedOmega n) ell 1
    (vertexDisplay (includeVertices ∘ anchor) (includeVertices ∘ bridge)) (fun x=>by
      rw [initial_vertexDisplay]
      change vertexWeight (Pi.single x (1:ℤ))=1
      simp [vertexWeight_apply,Pi.single_apply]) m hm
  change vertexWeight m.1=(N:ℤ)*1 at H
  simpa only [mul_one] using H

lemma triangularSeed_in_rootCone {N:ℕ} (f:ElementaryExpr N)
    (m:Extended (Vertex n (Cell n))) (hm:m∈(triangularExpression f).support) :
    ∃k,HasRootDegree (extendedRoots n) k (m-includeVertices ((N:ℤ) • anchor 0)) := by
  obtain ⟨k,c,hc,he⟩:=triangularVertex_rootDegree m.1 (triangularSeed_nonneg f m hm)
  refine ⟨k,c,hc,?_⟩
  change includeVertices (forwardRoots (fun i=>(c i:ℤ)))=m-includeVertices ((N:ℤ) • anchor 0)
  rw [triangularSeed_weight f m hm] at he
  change forwardRoots (fun i=>(c i:ℤ))=m.1-(N:ℤ) • anchor 0 at he
  rw [he,map_sub]
  congr 1
  exact Prod.ext rfl (triangularSeed_dual_zero f m hm).symm

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLinearIncoming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma triangularLinear_sum : triangularExpression (n:=n) (.atom 1)=
    ∑a:Vertex n (Cell n),Torus.X LaurentRay.vUnit (extendedOmega n)
      (includeVertices (Pi.single a (1:ℤ))) := by
  unfold triangularExpression ElementaryExpr.eval
  rw [independentElement_one _ _ extendedOmega_self]
  apply Finset.sum_congr rfl
  intro a _
  rw [initial_vertexDisplay]

lemma triangularLinear_support (m:Extended (Vertex n (Cell n)))
    (hm:(triangularExpression (.atom 1)) m≠0) :
    ∃a:Vertex n (Cell n),m=includeVertices (Pi.single a (1:ℤ)) := by
  rw [triangularLinear_sum,Finsupp.finsetSum_apply] at hm
  obtain ⟨a,_,ha⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨a,?_⟩
  by_contra hh
  exact ha (Finsupp.single_eq_of_ne hh)

lemma stationary_vertex_initial (a:Vertex n (Cell n))
    (hK:∀i,levelTotal cellLevel i (Pi.single a (1:ℤ))=0)
    (hxi:∀b,0 ≤ triangularOmega n (eventRoot cellLevel 0 b) (Pi.single a (1:ℤ))) :
    a=Sum.inl (0:Fin (n+1)) := by
  cases a with
  | inr b =>
    have H:=hK b.1
    change levelTotal cellLevel b.1 (bridge b)=0 at H
    simp only [levelTotal_bridge,cellLevel,ite_true, if_true] at H
    contradiction
  | inl a =>
    congr 1
    by_contra ha
    have ha0:0 < a.val:=by
      have hh:a.val≠0:=by intro H; exact ha (Fin.ext H)
      omega
    let i:Fin n:=⟨a.val-1,by have := a.isLt; omega⟩
    let b:Cell n:=⟨i,⟨0,by omega⟩⟩
    have H:=hxi b
    change 0 ≤ triangularOmega n (eventRoot cellLevel 0 b) (anchor a) at H
    rw [eventRoot_anchor] at H
    have he:a=b.1.succ:=by apply Fin.ext; dsimp [b,i]; omega
    have hn:a≠b.1.castSucc:=by intro hh; have := congrArg Fin.val hh; dsimp [b,i] at this; omega
    rw [ite_eq_left he,ite_eq_right hn] at H
    omega

lemma triangularLinear_onlyIncoming (m:Lattice n (Cell n)) (hm:triangularIncoming (.atom 1) m≠0) :
    m=anchor 0 := by
  have H:=triangularLinear_locality m hm
  rw [H] at hm
  obtain ⟨a,ha⟩:=triangularLinear_support (includeVertices m) hm
  have he:m=Pi.single a (1:ℤ):=congrArg Prod.fst ha
  obtain ⟨hK,hxi,_⟩:=triangularExpression_stationary (.atom 1) m (by rw [H]; exact hm)
  rw [he] at hK hxi
  rw [he,stationary_vertex_initial a hK hxi]
  rfl

lemma triangularLinear_incoming (m:Lattice n (Cell n)) :
    triangularIncoming (.atom 1) m=if m=anchor 0 then 1 else 0 := by
  by_cases hm:m=anchor 0
  · rw [hm,ite_eq_left rfl,triangularLinear_anchorIncoming]
  · rw [ite_eq_right hm]
    by_contra hn
    exact hm (triangularLinear_onlyIncoming m hn)

lemma triangularIncoming_dual_zero {N:ℕ} (f:ElementaryExpr N) (m:Extended (Vertex n (Cell n)))
    (hm:polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
      (triangularExpression f) m≠0) : m.2=0 := by
  obtain ⟨b,hb,d,c,_,he⟩:=polynomialSection_support (extendedOmega n) extendedOmega_self
    (extendedRoots n) (extendedCoord n) (incomingCovector (extendedOmega n) m)
    (triangularExpression f) m hm
  have H:=congrArg Prod.snd he
  change 0=m.2-b.2 at H
  rw [triangularSeed_dual_zero f b hb,sub_zero] at H
  exact H.symm

lemma triangularLinear_fullIncoming (m:Extended (Vertex n (Cell n))) :
    polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
      (triangularExpression (.atom 1)) m=if m=includeVertices (anchor 0) then 1 else 0 := by
  by_cases hd:m.2=0
  · have he:m=includeVertices m.1:=Prod.ext rfl hd
    rw [he]
    change triangularIncoming (.atom 1) m.1=_
    rw [triangularLinear_incoming]
    congr 1
    apply propext
    constructor
    · intro hh; rw [hh]
    · exact fun hh=>congrArg Prod.fst hh
  · have hn:m≠includeVertices (anchor 0):=by intro hh; exact hd (congrArg Prod.snd hh)
    rw [ite_eq_right hn]
    by_contra hz
    exact hd (triangularIncoming_dual_zero (.atom 1) m hz)

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLinearSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension PowerSeries PowerSeriesAdjoint
open Classical
noncomputable section
variable {n:ℕ}

lemma extendedCoord_anchor_zero : extendedCoord n (includeVertices (anchor 0))=0 := by
  ext g
  change forwardCoord (Pi.single (Sum.inl (0:Fin (n+1))) (1:ℤ)) g=0
  rw [forwardCoord_single]
  simp [afterGap]
lemma rootOrder_anchor_zero : rootOrder (extendedCoord n) (includeVertices (anchor 0))=0 := by
  change (∑g,extendedCoord n (includeVertices (anchor 0)) g)=0
  rw [extendedCoord_anchor_zero]
  simp
lemma triangularLinear_initial :
    polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression (.atom 1))=
      thetaInitial LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (includeVertices (anchor 0)) := by
  apply polynomialInitial_eq_theta (extendedOmega n) extendedOmega_self (extendedRoots n)
    (extendedCoord n) extendedCoord_roots (includeVertices (anchor 0)) (rootOrder_anchor_zero (n:=n))
  · intro m hm
    simpa only [Nat.cast_one,one_smul] using triangularSeed_in_rootCone (.atom 1) m (Finsupp.mem_support_iff.mpr hm)
  · intro m
    by_cases he:m=includeVertices (anchor 0)
    · simpa only [ite_eq_left he] using triangularLinear_fullIncoming m
    · simpa only [ite_eq_right he] using triangularLinear_fullIncoming m

lemma triangularLinear_theta (h:Extended (Vertex n (Cell n)) →+ ℝ) :
    adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) h).val
      (homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression (.atom 1)))=
      thetaValue LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (includeVertices (anchor 0)) h := by
  rw [rootSectionChart_action]
  change sectionValue _ _ _ _ _ (polynomialInitial _ _ _ _)=_
  rw [triangularLinear_initial]
  rfl

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

local instance triangularLinearSectionRing_ra40566_1 : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularLinearSectionAddCommGroup_ra40566_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularLinearSectionAddGroup_ra40566_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance triangularLinearSectionSub_ra40566_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
local instance triangularLinearSectionNonUnitalSemiring_ra40566_1 : NonUnitalSemiring (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toNonUnitalSemiring
local instance triangularLinearSectionNonUnitalNonAssocSemiring_ra40566_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toNonUnitalNonAssocSemiring
lemma triangularSeed_order_nonnegative {N:ℕ} (f:ElementaryExpr N) :
    ∀m,triangularExpression (n:=n) f m≠0 → 0 ≤ rootOrder (extendedCoord n) m := by
  apply conePolynomial_nonnegativeOrder (extendedOmega n) (extendedRoots n) (extendedCoord n)
    extendedCoord_roots (includeVertices ((N:ℤ) • anchor 0))
  · rw [map_zsmul,map_zsmul,rootOrder_anchor_zero,zsmul_zero]
  · intro m hm
    exact triangularSeed_in_rootCone f m (Finsupp.mem_support_iff.mpr hm)

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularPositivePowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A:Type*} [Ring A]
lemma adjoint_product (F X Y:PowerSeries A) (hF:constantCoeff F=1) :
    adjoint F (X*Y)=adjoint F X*adjoint F Y := by
  unfold adjoint
  calc
    _ = F*X*(invOfUnit F 1*F)*Y*invOfUnit F 1 := by rw [invOfUnit_mul F 1 hF]; simp only [mul_one,mul_assoc]
    _ = _ := by simp only [mul_assoc]
end
end ElementaryPositivity.PowerSeriesAdjoint

namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularPositivePowersRing
local instance triangularPositivePowersAddCommMonoid_ra40566_1 : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance triangularPositivePowersAddCommGroup_ra40566_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularPositivePowersAddGroup_ra40566_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
lemma homogenize_one_triangular :
    homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) 1=1 := by
  change homogenize _ _ _ (Torus.monomial LaurentRay.vUnit (extendedOmega n) 0 1)=_
  rw [homogenize_monomial,map_zero,Int.toNat_zero,monomial_zero_eq_C_apply]
  exact map_one PowerSeries.C

lemma triangularLinear_positive (h:Module.Dual ℝ ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ))) :
    IntegralPositive (extendedOmega n)
      (adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) (h.toAddMonoidHom.comp extendedCast)).val
        (homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression (.atom 1)))) := by
  obtain ⟨L,hL⟩:=real_covector_prescribe (extendedRoots n) extendedCast extendedRoots_realIndependent (fun _=>1)
  rw [triangularLinear_theta]
  exact thetaValue_positive (extendedOmega n) (extendedRoots n) extendedCast extendedCast_injective
    (triangularRealForm n) triangularRealForm_self triangularRealForm_compatible L
    (fun _ _ hm=>covector_root_eval (extendedRoots n) extendedCast L hL hm)
    (simpleTotalTransport (extendedOmega n) (extendedRoots n))
    (simpleTotalTransport_positive_prescription _ _ extendedOmega_self) _ h

lemma triangularPower_positive_oai (N:ℕ)
    (h:Module.Dual ℝ ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ))) :
    IntegralPositive (extendedOmega n)
      (adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) (h.toAddMonoidHom.comp extendedCast)).val
        (homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression (linearPower N)))) := by
  induction N with
  | zero=>
    change IntegralPositive _ (adjoint _ (homogenize _ _ _ 1))
    rw [homogenize_one_triangular]
    have H:adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) (h.toAddMonoidHom.comp extendedCast)).val 1=1:=by
      simp only [adjoint,mul_one]
      exact mul_invOfUnit _ 1 (rootSectionChart _ _ _).property.1
    rw [H]
    simpa only [Torus.X_zero,map_one] using completedPositive_C_X (extendedOmega n) 0
  | succ N ih=>
    change IntegralPositive _ (adjoint _ (homogenize _ _ _
      (triangularExpression (linearPower N)*triangularExpression (.atom 1))))
    rw [homogenize_mul _ _ _ _ _ (triangularSeed_order_nonnegative _) (triangularSeed_order_nonnegative _),
      adjoint_product _ _ _ (rootSectionChart _ _ _).property.1]
    exact ih.mul _ (triangularLinear_positive h)

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

theorem solution : type_of% @OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive_oai := @OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive_oai
