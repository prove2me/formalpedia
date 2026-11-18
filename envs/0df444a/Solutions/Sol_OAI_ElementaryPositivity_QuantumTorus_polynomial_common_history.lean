-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T19:02:01.55321+00:00
-- url     : https://prove2.me/submissions/be04b3f7-a7d9-4fed-b3ad-dcea752d8304

import Mathlib
import Definitions.Def_OAIQ368Chrom058
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_section_line_program
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_wall_joint_induction

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
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootTruncation
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
namespace RootTruncation
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma cut_congr {N : ℕ} {F G : PowerSeries A} (h : ∀n≤N,coeff n F=coeff n G) :
    cut N F=cut N G := by
  ext n
  simp only [coeff_cut]
  split_ifs with hn
  · exact h n hn
  · rfl
@[simp] lemma cut_cut (N : ℕ) (F : PowerSeries A) : cut N (cut N F)=cut N F :=
  cut_congr (fun _ hn=>coeff_cut_of_le F hn)
end
end RootTruncation
end ElementaryPositivity

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
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_TruncatedPrecisionClosure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation LaurentPrecision Filter WallUnits
noncomputable section
variable {M I J : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M→+M→+ℤ)
lemma RootClosedThrough.congr {N : ℕ} {A : Set (PowerSeries (Torus v Ω))}
    {F G : PowerSeries (Torus v Ω)} (hF : RootClosedThrough v Ω N A F)
    (he : ∀n≤N,coeff n F=coeff n G) : RootClosedThrough v Ω N A G := by
  change InPrecisionClosure v Ω _ _ at hF ⊢
  rw [←cut_congr he]
  exact hF
lemma InPrecisionClosure.cut {A : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (hF : InPrecisionClosure v Ω A F) (N : ℕ) :
    RootClosedThrough v Ω N A F := by
  intro T
  obtain ⟨G,hG,H⟩:=hF T
  refine ⟨RootTruncation.cut N G,⟨G,hG,rfl⟩,?_⟩
  intro t ht
  simp only [coeff_cut]
  by_cases hn : t.1≤N
  · simp only [hn,ite_true, if_true]; exact H t ht
  · simp only [hn,ite_false, if_false]; exact agrees_refl _ _
lemma rootClosedThrough_self {N : ℕ} {A : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (hF : F∈A) : RootClosedThrough v Ω N A F :=
  inPrecisionClosure_self v Ω ⟨F,hF,rfl⟩
end

end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallLineInitial
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
theorem incoming_positive_at_far (N d : ℕ) (r : M) (hd : 0 < d) (hr : HasRootDegree C d r)
    (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) (B.flip (e r)) k)
    (F D : CompletedPositive LaurentRay.vUnit Ω C)
    (hD : ∀n m,coeff (n+1) D.val m≠0 → OnPositiveRay r m)
    (hpos : RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay r)) D.val)
    (hprescribed : ∀n ≤ N,∀m,OnPositiveRay r m →
      coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω m) F).val) m=
        coeff n (FormalLog.log D.val) m) :
    ∃b,0 < b ∧ (∀a∈lineEvents (realRootsThrough e C N) (B.flip (e r)) k,a < b) ∧
      RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C ((k+b • B.flip (e r)).toAddMonoidHom.comp e) F).val := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  obtain ⟨b,hb,hbound⟩:=finite_upper_bound (lineEvents (realRootsThrough e C N) (B.flip (e r)) k)
  refine ⟨b,hb,hbound,?_⟩
  have Hgen:=offset_ray_generic C e he L hdeg N d r hd hr (B.flip (e r)) k H
  have Hinc:=incoming_ray_element_through LaurentRay.vUnit Ω C hΩ r (k.toAddMonoidHom.comp e)
    H.on_ray F D N (fun n hn hnN m hm hΩm hkm => Hgen.2 n hn hnN m hm hkm) hD hprescribed
  have Href:=chart_zero_refinement LaurentRay.vUnit Ω C (incomingCovector Ω r)
    (k.toAddMonoidHom.comp e) ((k+b • B.flip (e r)).toAddMonoidHom.comp e) F N (by
      intro n hn m hm
      have HH:=far_line_lex (realRootsThrough e C N) (B.flip (e r)) k b hbound
        (e m) (realRoot_mem e C N n hn m hm)
      simp only [LinearMap.flip_apply,hcomp] at HH
      exact HH)
  apply hpos.congr LaurentRay.vUnit Ω
  intro n hn
  exact (Href n hn |>.trans (Hinc n hn)).symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GlobalWallPositive
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry FiniteEventTraversal WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

lemma literalRootProducts_one (P : M → Prop) :
    (1 : PowerSeries (Torus LaurentRay.vUnit Ω))∈literalRootProducts Ω C P :=
  ⟨[],by simp,by simp⟩
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

theorem positive_walls_through (F : CompletedPositive LaurentRay.vUnit Ω C)
    (incoming : PositiveIncomingPrescription Ω C F) : ∀N,WallsPositiveThrough Ω C e N F := by
  intro N
  induction N with
  | zero =>
    intro r d hd hr h hg
    have H:=rootClosedThrough_self LaurentRay.vUnit Ω (N:=0) (literalRootProducts_one Ω C (OnPositiveRay r))
    apply H.congr LaurentRay.vUnit Ω
    intro i hi
    have hi0 : i=0:=by omega
    subst i
    rw [coeff_zero_eq_constantCoeff,map_one,(chartZero LaurentRay.vUnit Ω C _ F).property.1]
  | succ n ih =>
    intro r d hd hr h hg
    let S:=realRootsThrough e C (n+1)
    let vR:=B.flip (e r)
    obtain ⟨k,Hk,Hsign⟩:=exists_generic_offset S (e r) vR h hg.1
    let events:=lineEvents S vR k
    let P (a : ℝ):=RootClosedThrough LaurentRay.vUnit Ω (n+1)
      (literalRootProducts Ω C (OnPositiveRay r))
      (chartZero LaurentRay.vUnit Ω C ((k+a • vR).toAddMonoidHom.comp e) F).val
    have h0 : (0:ℝ)∉events:=by
      intro hevent
      obtain ⟨s,hs,hv,hs0⟩:=(mem_lineEvents_iff S vR k 0).mp hevent
      have hn : s∉Submodule.span ℝ {e r}:=by
        intro hmem
        obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp hmem
        apply hv
        rw [←hc,map_smul]
        change c*B (e r) (e r)=0
        rw [hB,mul_zero]
      apply Hk.avoid s hs hn
      simpa only [zero_smul,add_zero] using hs0
    have hstart : ∃b,0 ≤ b ∧ (∀a∈events,a < b) ∧ P b:=by
      obtain ⟨D,hD,hpos,hpres⟩:=incoming r d hd hr
      obtain ⟨b,hb,hbound,hwall⟩:=incoming_positive_at_far Ω C e he B hB hcomp L hdeg
        (n+1) d r hd hr k Hk F D hD (hpos.cut LaurentRay.vUnit Ω (n+1))
        (fun j hj m hm => hpres j m hm)
      exact ⟨b,hb.le,hbound,hwall⟩
    have hcell : ∀a b,0 ≤ a → 0 ≤ b → a∉events → b∉events →
        (∀z∈events,a < z ↔ b < z) → P a → P b:=by
      intro a b ha hb haS hbS Hside hpa
      apply hpa.congr LaurentRay.vUnit Ω
      apply chart_sign_congr_through LaurentRay.vUnit Ω C _ _ F (n+1)
      intro j hj hjN m hm
      exact line_cell_signs S vR k a b haS hbS Hside (e m) (realRoot_mem e C (n+1) j hjN m hm)
    have hstep : ∀a∈events,0 < a → ∃ε > 0,∀δ : ℝ,0 < δ → δ < ε → P (a+δ) → P (a-δ):=by
      intro a ha ha0
      exact wall_joint_induction Ω C e he B hB hcomp L hdeg n d r hd hr F ih k Hk a ha
    have HK : RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
        (chartZero LaurentRay.vUnit Ω C (k.toAddMonoidHom.comp e) F).val:=by
      have HH:=descend events P hstart hcell hstep 0 (le_refl 0) h0
      simpa only [P,zero_smul,add_zero] using HH
    have Hchart:=chart_sign_congr_through LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (k.toAddMonoidHom.comp e) F (n+1) (by
        intro j hj hjN m hm
        have HS:=Hsign (e m) (realRoot_mem e C (n+1) j hjN m hm)
        refine ⟨HS.1,?_,HS.2⟩
        intro hh
        exact ((hg.2 j hj hjN m hm hh).eval (k.toAddMonoidHom.comp e)).2.1.mpr Hk.on_ray)
    exact HK.congr LaurentRay.vUnit Ω (fun j hj => (Hchart j hj).symm)
end
end ElementaryPositivity.QuantumTorus

end
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
local instance instAddCommMonoidTorus_1_r7c9703_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_r7c9703_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_r7c9703_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_r7c9703_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance monomialConjugationAddCommMonoid_r7c9703_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance monomialConjugationAddGroup_r7c9703_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
lemma X_mul_X_neg (b:M) : Torus.X v Ω b*Torus.X v Ω (-b)=1 := by
  rw [Torus.X_mul_X_of_pairing_zero v Ω b (-b) (by simp only [map_neg,hΩ,neg_zero])]
  simp only [add_neg_cancel]
  rfl

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
local instance instAddCommMonoidTorus_2_r7c9703_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_r7c9703_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance shiftRootGradeSub_r7c9703_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
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
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SectionCharts
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.SplitTree.degreesDecidableEq _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
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
local instance latticeHahnAddCommMonoid_r7c9703_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance latticeHahnAddGroup_r7c9703_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance polynomialAdjointCoefficientsAddCommMonoid_r7c9703_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance polynomialAdjointCoefficientsAddGroup_r7c9703_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualCoefficientsAddCommMonoid_r7c9703_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualCoefficientsAddGroup_r7c9703_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance pureActualScalarCoefficientsAddCommMonoid_r7c9703_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance pureActualScalarCoefficientsAddGroup_r7c9703_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance pureActualScalarCoefficientsNonUnitalSemiring_r7c9703_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance halfspacePolynomialCoefficientsCoeffAddCommMonoid_r7c9703_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsCoeffAddGroup_r7c9703_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance halfspacePolynomialCoefficientsCoeffNonUnitalSemiring_r7c9703_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance halfspacePolynomialCoefficientsCoeffNonUnitalNonAssocSemiring_r7c9703_1 : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_18_r7c9703_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_18_r7c9703_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance homogenizedPolynomialSectionAddCommMonoid_r7c9703_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance homogenizedPolynomialSectionAddGroup_r7c9703_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance homogenizedPolynomialSectionNonUnitalSemiring_r7c9703_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SectionMonomialExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
lemma mem_gradePoints (b m:M) (j:ℕ) : m∈gradePoints C b j ↔ HasRootDegree C j (m-b) := by
  simp only [gradePoints,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_LocalHistoryFormula
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.LocalHistoryFormula.leafFintype _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

namespace LocalHistoryFormula
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)

lemma eval_sumList (A:ℕ → M → LaurentSeries ℚ) (ps:List (LocalHistoryFormula M E)) :
    eval Ω C e F A (sumList ps)=(ps.map (eval Ω C e F A)).sum := by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>simp only [sumList,eval,List.map_cons,List.sum_cons,ih]
lemma positive_sumList (ps:List (LocalHistoryFormula M E))
    (hp:∀p∈ps,Positive Ω C e F p) : Positive Ω C e F (sumList ps) := by
  induction ps with
  | nil=>trivial
  | cons p ps ih=>exact ⟨hp p (by simp),ih (fun q hq=>hp q (by simp [hq]))⟩
lemma bounded_sumList (b:M) (N:ℕ) (ps:List (LocalHistoryFormula M E))
    (hp:∀p∈ps,Bounded C b N p) : Bounded C b N (sumList ps) := by
  induction ps with
  | nil=>trivial
  | cons p ps ih=>exact ⟨hp p (by simp),ih (fun q hq=>hp q (by simp [hq]))⟩
end LocalHistoryFormula
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
namespace LocalHistoryFormula
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)
lemma eval_finSum {J:Type*} (s:Finset J) (f:J → LocalHistoryFormula M E)
    (A:ℕ → M → LaurentSeries ℚ) :
    eval Ω C e F A (finSum s f)=∑j∈s,eval Ω C e F A (f j) := by
  rw [finSum,eval_sumList,List.map_map]
  simp
lemma positive_finSum {J:Type*} (s:Finset J) (f:J → LocalHistoryFormula M E)
    (hp:∀j∈s,Positive Ω C e F (f j)) : Positive Ω C e F (finSum s f) := by
  apply positive_sumList
  intro p hp'
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hp'
  exact hp j (Finset.mem_toList.mp hj)
lemma bounded_finSum {J:Type*} (s:Finset J) (f:J → LocalHistoryFormula M E)
    (b:M) (N:ℕ) (hp:∀j∈s,Bounded C b N (f j)) : Bounded C b N (finSum s f) := by
  apply bounded_sumList
  intro p hp'
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hp'
  exact hp j (Finset.mem_toList.mp hj)
end LocalHistoryFormula

variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (e:M →+ E) (he:Function.Injective e)
variable (B:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB:∀x,B x x=0)
variable (hcomp:∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

lemma common_history_producer (F:CompletedPositive LaurentRay.vUnit Ω C)
    (incoming:PositiveIncomingPrescription Ω C F) (b:M) :
    ∀N (h:Module.Dual ℝ E) (r:M),HasRootDegree C N (r-b) →
      ∃p:LocalHistoryFormula M E,
        p.Positive Ω C e F ∧ p.Bounded C b N ∧
        ∀X:PowerSeries (Torus LaurentRay.vUnit Ω),ShiftGraded LaurentRay.vUnit Ω C b X →
          p.eval Ω C e F (fun j m=>coeff j (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω m) X) m)=
            coeff N (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X) r := by
  have walls:=positive_walls_through Ω C e he B hB hcomp L hdeg F incoming
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih=>
    intro h r hr
    obtain ⟨ts,hpos,hid⟩:=section_line_program Ω C e he B hB hcomp L hdeg F N (walls N) h r
    have HT:∀(t:LineTransfer E) (j:Fin N) (m:{m:M // m∈gradePoints C b j}),
        ∃p:LocalHistoryFormula M E,p.Positive Ω C e F ∧ p.Bounded C b j ∧
          ∀X:PowerSeries (Torus LaurentRay.vUnit Ω),ShiftGraded LaurentRay.vUnit Ω C b X →
            p.eval Ω C e F (fun k a=>coeff k (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω a) X) a)=
              coeff j (sectionValue LaurentRay.vUnit Ω C F (t.source.toAddMonoidHom.comp e) X) m := by
      intro t j m
      exact ih j j.isLt t.source m ((mem_gradePoints C b m j).mp m.property)
    choose p hp hb heval using HT
    let q (t:LineTransfer E):LocalHistoryFormula M E:=
      .finSum Finset.univ (fun j:Fin N=>.finSum (gradePoints C b j).attach (fun m=>
        .jump (N-j.val) m.val r t (p t j m)))
    have qp:∀t∈ts,(q t).Positive Ω C e F:=by
      intro t ht
      apply LocalHistoryFormula.positive_finSum
      intro j hj
      apply LocalHistoryFormula.positive_finSum
      intro m hm
      exact ⟨hpos t ht (N-j.val) (Nat.sub_le _ _) m.val,hp t j m⟩
    have qb:∀t∈ts,(q t).Bounded C b N:=by
      intro t ht
      apply LocalHistoryFormula.bounded_finSum
      intro j hj
      apply LocalHistoryFormula.bounded_finSum
      intro m hm
      exact ⟨by omega,j.val,by omega,hb t j m⟩
    have qe:∀t (X:PowerSeries (Torus LaurentRay.vUnit Ω)),ShiftGraded LaurentRay.vUnit Ω C b X →
        (q t).eval Ω C e F (fun k a=>coeff k (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω a) X) a)=
          t.delta Ω C e F b X N r := by
      intro t X hX
      unfold q
      rw [LocalHistoryFormula.eval_finSum]
      unfold LineTransfer.delta
      rw [←Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      rw [LocalHistoryFormula.eval_finSum]
      calc
        _=∑m∈(gradePoints C b j).attach,
          coeff j (sectionValue LaurentRay.vUnit Ω C F (t.source.toAddMonoidHom.comp e) X) m.val*
            monomialJump Ω (t.operator Ω C e F) (N-j.val) m.val r:=by
          apply Finset.sum_congr rfl
          intro m hm
          change monomialJump Ω (t.operator Ω C e F) (N-j.val) m.val r*_= _
          rw [heval t j m X hX,mul_comm]
        _= _:=Finset.sum_attach (gradePoints C b j) (fun m=>
          coeff j (sectionValue LaurentRay.vUnit Ω C F (t.source.toAddMonoidHom.comp e) X) m*
            monomialJump Ω (t.operator Ω C e F) (N-j.val) m r)
    let out:LocalHistoryFormula M E:=.add (.stop N r) (.sumList (ts.map q))
    refine ⟨out,⟨trivial,?_⟩,⟨⟨le_rfl,hr⟩,?_⟩,?_⟩
    · apply LocalHistoryFormula.positive_sumList
      intro a ha
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp ha
      exact qp t ht
    · apply LocalHistoryFormula.bounded_sumList
      intro a ha
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp ha
      exact qb t ht
    · intro X hX
      change coeff N (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω r) X) r+
        LocalHistoryFormula.eval Ω C e F _ (.sumList (ts.map q))=_
      rw [LocalHistoryFormula.eval_sumList,List.map_map]
      apply Eq.trans _ (hid b X hX).symm
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      exact qe t X hX
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_CommonHistoryLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus.LocalHistoryFormula
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)

lemma leafBound (b:M) (N:ℕ) (p:LocalHistoryFormula M E) (hp:p.Bounded C b N) (l:p.Leaf) :
    p.leafDegree l≤N ∧ HasRootDegree C (p.leafDegree l) (p.leafExponent l-b) := by
  induction p generalizing N with
  | zero=>exact l.elim
  | stop j m=>exact hp
  | add p q ihp ihq=>cases l with
    | inl l=>exact ihp N hp.1 l
    | inr l=>exact ihq N hp.2 l
  | jump d m r t p ih=>
    obtain ⟨hd,j,hj,hp⟩:=hp
    obtain ⟨hl,hr⟩:=ih j hp l
    exact ⟨by dsimp [leafDegree]; omega,hr⟩

lemma eval_eq_sum_leaves (p:LocalHistoryFormula M E) (A:ℕ → M → LaurentSeries ℚ) :
    p.eval Ω C e F A=∑l:p.Leaf,leafWeight Ω C e F p l*A (p.leafDegree l) (p.leafExponent l) := by
  induction p with
  | zero=>
    change 0=∑l:Empty,_
    exact (Finset.sum_eq_zero (fun l _=>l.elim)).symm
  | stop j m=>
    change A j m=∑l:Unit,_
    rw [Fintype.sum_unique]
    simp [leafWeight,leafDegree,leafExponent]
  | add p q ihp ihq=>
    change p.eval Ω C e F A+q.eval Ω C e F A=∑l:Sum p.Leaf q.Leaf,_
    rw [Fintype.sum_sum_type,ihp,ihq]
    rfl
  | jump d m r t p ih=>
    change monomialJump Ω (t.operator Ω C e F) d m r*p.eval Ω C e F A=∑l:p.Leaf,_
    rw [ih,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    exact (mul_assoc _ _ _).symm
end
end ElementaryPositivity.QuantumTorus.LocalHistoryFormula

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits HahnSeries
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.commonHistoryLeavesRing
local instance commonHistoryLeavesAddCommMonoid_r7c9703_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance commonHistoryLeavesAddGroup_r7c9703_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hΩ hcoord in
lemma polynomialInitial_value (b:M) (hb:rootOrder coord b=0)
    (F:Torus LaurentRay.vUnit Ω) (hF:∀m,F m≠0 → ∃d,HasRootDegree C d (m-b))
    (d:ℕ) (m:M) (hm:HasRootDegree C d (m-b)) (h:M →+ ℝ) :
    coeff d (sectionValue LaurentRay.vUnit Ω C (simpleTotalTransport Ω C) h
      (polynomialInitial Ω C coord F)) m=polynomialSectionCoefficient Ω C coord h F m := by
  unfold polynomialInitial
  rw [←rootSectionChart_action]
  have H:=rootOrder_eq C coord hcoord hm
  rw [map_sub,hb,sub_zero] at H
  have he:d=(rootOrder coord m).toNat:=by rw [H,Int.toNat_natCast]
  rw [he]
  exact homogenize_adjoint_actual Ω hΩ (rootOrder coord) _ F
    (conePolynomial_nonnegativeOrder Ω C coord hcoord b hb F hF) m (by rw [H]; omega)

variable (e:M →+ E) (he:Function.Injective e)
variable (B:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB:∀x,B x x=0)
variable (hcomp:∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hΩ hcoord he hB hcomp hdeg in
lemma polynomial_common_history_oai (b:M) (hb:rootOrder coord b=0)
    (N:ℕ) (r:M) (hr:HasRootDegree C N (r-b)) :
    ∃p:LocalHistoryFormula M E,
      p.Positive Ω C e (simpleTotalTransport Ω C) ∧ p.Bounded C b N ∧
      ∀F:Torus LaurentRay.vUnit Ω,
        (∀m,F m≠0 → ∃d,HasRootDegree C d (m-b)) →
        F r=∑l:p.Leaf,p.leafWeight Ω C e (simpleTotalTransport Ω C) l *
          polynomialSectionIncoming Ω C coord F (p.leafExponent l) := by
  obtain ⟨p,hp,hbnd,hid⟩:=common_history_producer Ω C e he B hB hcomp L hdeg
    (simpleTotalTransport Ω C) (simpleTotalTransport_positive_prescription Ω C hΩ) b N (-L) r hr
  refine ⟨p,hp,hbnd,?_⟩
  intro F hF
  have H:=hid (polynomialInitial Ω C coord F) (polynomialInitial_graded Ω C coord hcoord b hb F hF)
  rw [polynomialInitial_value Ω hΩ C coord hcoord b hb F hF N r hr,
    polynomialSection_negative Ω hΩ C coord] at H
  · rw [LocalHistoryFormula.eval_eq_sum_leaves] at H
    rw [←H]
    apply Finset.sum_congr rfl
    intro l hl
    congr 1
    exact polynomialInitial_value Ω hΩ C coord hcoord b hb F hF _ _
      (p.leafBound C b N hbnd l).2 (incomingCovector Ω (p.leafExponent l))
  · intro k hk m hm
    change -(L (e m)) < 0
    rw [hdeg k m hm]
    exact neg_neg_of_pos (Nat.cast_pos.mpr hk)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.QuantumTorus.polynomial_common_history_oai.{u_1, u_2, u_3}
