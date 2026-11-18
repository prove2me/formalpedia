-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:55:57.697481+00:00
-- url     : https://prove2.me/submissions/160450a6-e929-4975-9830-1af58377aac9

import Mathlib
import Definitions.Def_OAIQ368Chrom006
import Definitions.Def_OAIQ368Chrom016
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_positive_sections

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInverse
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
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

end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TranslatedCompletion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
local instance shiftRootGradeSub_rdc343f_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.shiftRootGradeAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionIncoming
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TorusPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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

local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_rdc343f_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_rdc343f_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma torusPositive_zero : TorusPositive Ω 0 := fun _=>positive_zero
lemma torusPositive_monomial (m : M) (r : LaurentSeries ℚ) (hr : Positive r) :
    TorusPositive Ω (Torus.monomial LaurentRay.vUnit Ω m r) := by
  classical
  intro x
  change Positive ((Finsupp.single m r) x)
  by_cases h : m=x
  · subst x
    simpa only [Finsupp.single_eq_same] using hr
  · simpa only [Finsupp.single_eq_of_ne (Ne.symm h)] using positive_zero

lemma completedPositive_C_X (m : M) : IntegralPositive Ω (C (Torus.X LaurentRay.vUnit Ω m)) := by
  intro n
  rw [coeff_C]
  split
  · exact torusPositive_monomial Ω _ _ positive_one
  · exact torusPositive_zero Ω

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularCommutativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry FiniteEventTraversal LaurentPositive WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

theorem thetaValue_positive_oai (F : CompletedPositive LaurentRay.vUnit Ω C)
    (incoming : PositiveIncomingPrescription Ω C F) (b : M) (h : Module.Dual ℝ E) :
    IntegralPositive Ω (thetaValue LaurentRay.vUnit Ω C F b (h.toAddMonoidHom.comp e)) := by
  intro N
  exact positive_sections Ω C e he B hB hcomp L hdeg F incoming b
    (thetaInitial LaurentRay.vUnit Ω C F b) (thetaInitial_graded LaurentRay.vUnit Ω C F b)
    (fun n=>by rw [thetaInitial_prescription]; exact completedPositive_C_X Ω b n) N h
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive_oai.{u_1, u_2, u_3}
