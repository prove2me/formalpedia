-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:04.089475+00:00
-- url     : https://prove2.me/submissions/1c00837f-0f21-47bf-b0d8-872c2a249f42

import Mathlib
import Definitions.Def_OAIQ368Chrom008
import Definitions.Def_OAIQ368Chrom009
import Definitions.Def_OAIQ368Chrom010
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_mutatedIncoming_probe
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_mutatedTransport_negative_ratio
import Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_actualInfinityPath_product_square
import Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_finite_refinement_import

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingSystem
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.PowerSeriesSplit
noncomputable section

variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instAddGroupTorus_1
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instSubTorus_1
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instModuleRatTorus
theorem existsUnique_incoming (hΩ : ∀m,Ω m m=0) (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈rootGrade v Ω C n) :
    ∃! g : CompletedPositive v Ω C,
      ∀n,incomingCoefficient v Ω C (n+1) g.val=l (n+1) := by
  let g : CompletedPositive v Ω C := ⟨incomingSolution v Ω C l,
    incomingSolution_constant v Ω C l,incomingSolution_graded v Ω C l hl⟩
  refine ⟨g,fun n => incomingSolution_prescription v Ω C hΩ l hl n,?_⟩
  intro f hf
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,f.property.1,g.property.1]
    | succ n =>
      have H := incomingCoefficient_leading v Ω C hΩ f.val g.val n
        (fun k hk => ih k (by omega)) (f.property.2 _) (g.property.2 _)
      rw [hf n,incomingSolution_prescription v Ω C hΩ l hl n] at H
      ext m
      have he := congrArg (fun x : Torus v Ω => x m) H
      simp only [torus_sub_apply,sub_self] at he
      exact sub_eq_zero.mp he.symm

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_OrderedRootReordering
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries Filter WallUnits
noncomputable section
variable {M J A ι : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M)

lemma SeriesGraded.list_prod (s : List A)
    (F : A→PowerSeries (Torus LaurentRay.vUnit Ω))
    (hF : ∀a∈s,SeriesGraded LaurentRay.vUnit Ω C (F a)) :
    SeriesGraded LaurentRay.vUnit Ω C (s.map F).prod := by
  induction s with
  | nil=>simpa using SeriesGraded.one LaurentRay.vUnit Ω C
  | cons a s ih=>
    simpa only [List.map_cons,List.prod_cons] using
      (hF a (by simp)).mul LaurentRay.vUnit Ω C (ih (fun x hx=>hF x (by simp [hx])))

end
end ElementaryPositivity.QuantumTorus

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
local instance instAddCommMonoidTorus_1_r8ac191_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_r8ac191_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_r8ac191_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance rationalLaurentFaithfulRing_r8ac191_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rationalLaurentFaithfulNonUnitalSemiring_r8ac191_1 : NonUnitalSemiring (Torus v Ω) :=
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
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.rationalThroughRing
local instance rationalThroughAddCommMonoid_r8ac191_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rationalThroughAddGroup_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance rationalThroughNonUnitalSemiring_r8ac191_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance rationalThroughNonUnitalNonAssocSemiring_r8ac191_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_4_r8ac191_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_7_r8ac191_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_7_r8ac191_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_5_r8ac191_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_5_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_8_r8ac191_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_8_r8ac191_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationSimpleIncoming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutationSimpleIncomingRing
local instance mutationSimpleIncomingAddCommMonoid_r8ac191_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance mutationSimpleIncomingAddGroup_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma regrade_homogeneous_identity (δ : M →+ ℤ) (B : ℕ) (f : PowerSeries (Torus v Ω))
    (hf : FullHomogeneous v Ω δ f) : regrade v Ω δ (B+1) f=f := by
  classical
  apply PowerSeries.ext
  intro d
  ext m
  rw [regrade_coeff_eval]
  by_cases hd : d=(δ m).toNat
  · rw [ite_eq_left hd]
    apply Finset.sum_eq_single d
    · intro n hn hnd
      by_contra hnz
      have H:=hf n m hnz
      rw [H,Int.toNat_natCast] at hd
      exact hnd hd.symm
    · intro hn
      have hb : d<(B+1)*d+1:=by nlinarith
      exact (hn (Finset.mem_range.mpr hb)).elim
  · rw [ite_eq_right hd]
    by_contra HH
    have H:=hf d m (Ne.symm HH)
    rw [H,Int.toNat_natCast] at hd
    exact hd rfl

lemma normalizedSimple_homogeneous (δ : M →+ ℤ) (r : M) (hr : δ r=1) :
    FullHomogeneous LaurentRay.vUnit Ω δ (normalizedSimple Ω r) := by
  intro n m hm
  have he : m=n • r:=by
    by_contra hh
    apply hm
    rw [normalizedSimple,coeff_raySeries]
    exact Finsupp.single_eq_of_ne hh
  subst m
  rw [map_nsmul,hr,nsmul_eq_mul,mul_one]

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (hΩ : ∀m,Ω m m=0) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

omit [Fintype I] in
lemma mutation_push_normalizedSimple (pos : Bool) (r : M) :
    PowerSeries.map (mutationTorusPush Ω hΩ C pc pos LaurentRay.vUnit) (normalizedSimple Ω r)=
      normalizedSimple Ω (mutationLinearPiece Ω C pc pos r) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_map,normalizedSimple,coeff_raySeries,normalizedSimple,coeff_raySeries]
  change Torus.push LaurentRay.vUnit Ω Ω (mutationLinearPiece Ω C pc pos) _ (Torus.monomial _ _ _ _)=_
  rw [Torus.push_monomial,map_nsmul]

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)
lemma mutation_side_simple_image (i : I) (hi : i≠pc)
    (hside : if pos then 0≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0) :
    mutationLinearPiece Ω C pc pos (simpleRoot C i)=simpleRoot (mutatedRoots Ω C pc) i := by
  rw [mutatedRoot_off Ω C pc i hi]
  cases pos
  · change mutationPairing Ω C pc i≤0 at hside
    rw [max_eq_right (by omega : 0≤ -mutationPairing Ω C pc i)]
    change simpleRoot C i-Ω (simpleRoot C pc) (simpleRoot C i) • simpleRoot C pc=
      simpleRoot C i+(-Ω (simpleRoot C pc) (simpleRoot C i)) • simpleRoot C pc
    rw [neg_zsmul,sub_eq_add_neg]
  · change 0≤ mutationPairing Ω C pc i at hside
    rw [max_eq_left (by omega : -mutationPairing Ω C pc i≤0),zero_zsmul,add_zero]
    rfl

include hcoord in
lemma mutation_side_simple_order (i : I) (hi : i≠pc)
    (hside : if pos then 0≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0) :
    mutationNewOrder Ω C coord pc pos (simpleRoot C i)=1 := by
  apply mutationNewOrder_of_root Ω C coord hcoord
  rw [mutation_side_simple_image Ω C pc pos i hi hside]
  exact simpleRoot_degree (mutatedRoots Ω C pc) i

include hcoord in
lemma mutation_normalized_simple_side (i : I) (hi : i≠pc)
    (hside : if pos then 0≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0) :
    mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (normalizedSimple Ω (simpleRoot C i))=
      normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) i) := by
  rw [mutationCompletion,regrade_homogeneous_identity]
  · rw [mutation_push_normalizedSimple,mutation_side_simple_image Ω C pc pos i hi hside]
  · exact normalizedSimple_homogeneous Ω _ _ (mutation_side_simple_order Ω C coord hcoord pc pos i hi hside)

end
end ElementaryPositivity.QuantumTorus

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

local instance mutationRegradeCompatibilityRing_r8ac191_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutationRegradeCompatibilityAddCommMonoid_r8ac191_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance mutationRegradeCompatibilityAddGroup_r8ac191_1 : AddGroup (Torus v Ω) :=
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationOrientedCompatibility
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] (v : Rˣ) (Ω : M →+ M →+ ℤ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus_3
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instAddCommMonoidTorus_4
local instance instAddGroupTorus_6_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma inverse_support_addSubmonoid (P : AddSubmonoid M) (f : PowerSeries (Torus v Ω))
    (hf : ∀n m,coeff n f m≠0 → m∈P) :
    ∀n m,coeff n (invOfUnit f 1) m≠0 → m∈P := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    intro m hm
    by_cases hn : n=0
    · subst n
      rw [coeff_invOfUnit,ite_eq_left rfl] at hm
      have hm0 : m=0:=by
        by_contra hh
        apply hm
        change Finsupp.single 0 (1:R) m=0
        exact Finsupp.single_eq_of_ne hh
      exact hm0 ▸ P.zero_mem
    · rw [coeff_invOfUnit,ite_eq_right hn] at hm
      simp only [inv_one,Units.val_one] at hm
      rw [torus_neg_one_mul] at hm
      change -(∑ab∈Finset.HasAntidiagonal.antidiagonal n,
        if ab.2<n then coeff ab.1 f*coeff ab.2 (invOfUnit f 1) else 0) m≠0 at hm
      have HH:=neg_ne_zero.mp hm
      rw [nonp_torus_eval_sum] at HH
      obtain ⟨ab,hab,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero HH
      have hb : ab.2<n:=by by_contra hh; simp [hh] at hz
      rw [ite_eq_left hb] at hz
      obtain ⟨a,b,ha,hb',he⟩:=torus_product_nonzero v Ω _ _ m hz
      exact he ▸ P.add_mem (hf ab.1 a ha) (ih ab.2 hb b hb')
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
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_GeometricMutation
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

include hS in
lemma realShearCovector_at_p (h : Module.Dual ℝ E) :
    realShearCovector e S p h (e p)=h (e p) := by
  simp [realShearCovector,hS]
include hS in
lemma realShearCovectorInverse_at_p (h : Module.Dual ℝ E) :
    realShearCovectorInverse e S p h (e p)=h (e p) := by
  simp [realShearCovectorInverse,hS]
include hS in
lemma realShearCovector_right_inverse (h : Module.Dual ℝ E) :
    realShearCovector e S p (realShearCovectorInverse e S p h)=h := by
  rw [realShearCovector,realShearCovectorInverse_at_p e S p hS]
  exact sub_add_cancel h _

include hS in
lemma realMutationCovector_at_p (h : Module.Dual ℝ E) :
    realMutationCovector e S p h (e p)=h (e p) := by
  unfold realMutationCovector
  split_ifs <;> first | rfl | exact realShearCovector_at_p e S p hS h

include hcomp in
lemma realShearCovector_lattice (h : Module.Dual ℝ E) :
    (realShearCovector e S p h).toAddMonoidHom.comp e=shearCovector Ω p (h.toAddMonoidHom.comp e) := by
  ext m
  change h (e m)+h (e p)*S (e p) (e m)=h (e (m+Ω p m • p))
  rw [hcomp,map_add,map_zsmul,map_add,map_zsmul]
  simp only [zsmul_eq_mul]
  ring
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
include hS hcomp in
lemma realShearCovector_incidence (h : Module.Dual ℝ E) (m : M) :
    realShearCovector e S p h (e (mutationShear Ω p m))=h (e m) := by
  have hp : Ω p p=0:=by
    have H:=hS (e p)
    rw [hcomp] at H
    exact_mod_cast H
  change ((realShearCovector e S p h).toAddMonoidHom.comp e) (mutationShear Ω p m)=_
  rw [realShearCovector_lattice Ω e S p hcomp]
  change h (e (mutationShearInverse Ω p (mutationShear Ω p m)))=_
  rw [mutationShear_left_inverse Ω p hp]

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
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I) (pos : Bool)

variable {R : Type*} [CommRing R] (v : Rˣ)

variable (hcoord : ∀d,coord (C d)=d)
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))

omit [Fintype I] in
include hS hcomp in
lemma realSideCovector_mutated_incidence (h : Module.Dual ℝ E) (r : M) :
    realSideCovector e S (simpleRoot C pc) pos h (e (mutationLinearPiece Ω C pc pos r))=h (e r) := by
  cases pos
  · exact realShearCovector_incidence Ω e S (simpleRoot C pc) hS hcomp h r
  · rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedWallKernel
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (u : Rˣ) (Ω : M →+ M →+ ℤ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus_4
local instance instAddCommMonoidTorus_5_r8ac191_2 : AddCommMonoid (Torus u Ω) := (Torus.instRing u Ω).toAddCommMonoid
local instance instAddGroupTorus_7_r8ac191_1 : AddGroup (Torus u Ω) := (Torus.instRing u Ω).toAddGroup
lemma orientPowerSeries_submonoid (P : AddSubmonoid M) (b : Bool)
    (f : PowerSeries (Torus u Ω)) (hf : ∀n m,coeff n f m≠0 → m∈P) :
    ∀n m,coeff n (orientPowerSeries b f) m≠0 → m∈P := by
  cases b
  · exact inverse_support_addSubmonoid u Ω P f hf
  · exact hf
lemma one_kernel_support (h : M →+ ℝ) (n : ℕ) (m : M)
    (hm : coeff n (1 : PowerSeries (Torus u Ω)) m≠0) : h m=0 := by
  by_cases hn : n=0
  · subst n
    rw [coeff_zero_eq_constantCoeff_apply,constantCoeff_one] at hm
    have hm0 : m=0:=by
      by_contra hh
      exact hm (Finsupp.single_eq_of_ne hh)
    simp [hm0]
  · rw [coeff_one,ite_eq_right hn] at hm
    exact (hm rfl).elim

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M)
omit [DecidableEq I] in
lemma chartZero_kernel_support (h : M →+ ℝ) (T : CompletedPositive u Ω C) :
    ∀n m,coeff n (chartZero u Ω C h T).val m≠0 → h m=0 := by
  intro n m hm
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff_apply,(chartZero u Ω C h T).property.1] at hm
    have hm0 : m=0:=by
      by_contra hh
      exact hm (Finsupp.single_eq_of_ne hh)
    simp [hm0]
  | succ n => exact (chart_three_support u Ω C h T).2.1 n m hm
end

noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_6
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_9_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_9_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma normalizedSimple_kernel_support (h : M →+ ℝ) (r : M) (hr : h r=0) :
    ∀n m,coeff n (normalizedSimple Ω r) m≠0 → h m=0 := by
  intro n m hm
  rw [normalizedSimple,coeff_raySeries] at hm
  have heq : m=n • r:=by
    by_contra hh
    exact hm (Finsupp.single_eq_of_ne hh)
  rw [heq,map_nsmul,hr,nsmul_zero]

include hS hcomp in
lemma mutationCompletion_kernel_support (pos : Bool) (h : Module.Dual ℝ E)
    (f : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf : ∀n m,coeff n f m≠0 → h (e m)=0) :
    ∀n m,coeff n (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f) m≠0 →
      realSideCovector e S (simpleRoot C pc) pos h (e m)=0 := by
  intro n m hm
  obtain ⟨a,rfl⟩:=mutationLinearPiece_surjective Ω hΩ C pc pos m
  rw [mutationCompletion_coeff_read] at hm
  split_ifs at hm with hd
  · obtain ⟨j,hj,hja⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [realSideCovector_mutated_incidence Ω C pc pos e S hS hcomp]
    exact hf j a hja
  · exact (hm rfl).elim

variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
include hS hcomp in
lemma mutatedLineFactor_kernel (a : ℝ) :
    ∀n m,coeff n (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a) m≠0 →
      realMutationCovector e S (simpleRoot C pc) (k+a • v) (e m)=0 := by
  classical
  unfold mutatedLineFactor
  split
  · next ha=>
    split
    · next hp=>
      have hcut : realMutationCovector e S (simpleRoot C pc) (k+a • v)=k+a • v:=by
        unfold realMutationCovector
        rw [ite_eq_left (le_of_eq hp.symm)]
      rw [hcut]
      apply orientPowerSeries_submonoid LaurentRay.vUnit Ω
        (((k+a • v).toAddMonoidHom.comp e).ker.toAddSubmonoid)
      apply normalizedSimple_kernel_support
      rw [mutatedRoot_p,map_neg]
      change -((k+a • v) (e (simpleRoot C pc)))=0
      rw [hp,neg_zero]
    · next hp=>
      let pos:=decide (0<(k+a • v) (e (simpleRoot C pc)))
      have hs : if pos then 0≤(k+a • v) (e (simpleRoot C pc)) else
          (k+a • v) (e (simpleRoot C pc))≤0:=by
        dsimp [pos]
        split_ifs with hh
        · exact le_of_lt (of_decide_eq_true hh)
        · exact le_of_not_gt (by simpa only [decide_eq_true_eq] using hh)
      rw [realMutationCovector_eq_side e S (simpleRoot C pc) pos _ hs]
      apply mutationCompletion_kernel_support Ω hΩ C coord pc e S hS hcomp pos
      apply orientPowerSeries_submonoid LaurentRay.vUnit Ω
        (((k+a • v).toAddMonoidHom.comp e).ker.toAddSubmonoid)
      exact chartZero_kernel_support LaurentRay.vUnit Ω C _ _
  · exact one_kernel_support LaurentRay.vUnit Ω
      ((realMutationCovector e S (simpleRoot C pc) (k+a • v)).toAddMonoidHom.comp e)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutatedPureFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_7
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_10_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_10_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma pureFaceSeries_of_pure (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf:∀n m,coeff n f m≠0 → nonpDegree coord pc m=0) : pureFaceSeries Ω coord pc f=f := by
  apply PowerSeries.ext
  intro n
  apply Finsupp.ext
  intro m
  rw [pureFaceSeries_apply]
  split_ifs with h
  · rfl
  · exact (not_ne_iff.mp (fun H=>h (hf n m H))).symm

include hcoord in
lemma pureFaceSeries_kernel_one (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf:SeriesGraded LaurentRay.vUnit Ω C f) (hc:constantCoeff f=1)
    (h:M →+ ℝ) (hp:h (simpleRoot C pc)≠0)
    (hk:∀n m,coeff n f m≠0 → h m=0) : pureFaceSeries Ω coord pc f=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    rw [coeff_pureFaceSeries,coeff_zero_eq_constantCoeff_apply,hc,coeff_zero_eq_constantCoeff_apply,
      constantCoeff_one,zeroProject_one]
  | succ n =>
    apply Finsupp.ext
    intro m
    rw [pureFaceSeries_apply,coeff_one,ite_eq_right (show n+1≠0 by omega)]
    change (if nonpDegree coord pc m=0 then coeff (n+1) f m else 0)=0
    split_ifs with hm
    · by_contra hn
      have hr:HasRootDegree C (n+1) m:=by
        by_contra hh
        exact hn (hf (n+1) m hh)
      have HH:=hk (n+1) m hn
      rw [nonp_zero_root C coord hcoord pc hr hm,map_nsmul,nsmul_eq_mul] at HH
      exact hp ((mul_eq_zero.mp HH).resolve_left (by positivity))
    · rfl

include hcoord in
lemma pureFaceSeries_orient_simple (b:Bool) :
    pureFaceSeries Ω coord pc (orientPowerSeries b (normalizedSimple Ω (simpleRoot C pc)))=
      orientPowerSeries b (normalizedSimple Ω (simpleRoot C pc)) := by
  apply pureFaceSeries_of_pure
  have HH:=orientPowerSeries_submonoid LaurentRay.vUnit Ω
    ((nonpDegree coord pc).ker.toAddSubmonoid) b (normalizedSimple Ω (simpleRoot C pc))
  apply HH
  intro n m hm
  rw [normalizedSimple,coeff_raySeries] at hm
  have heq:m=n • simpleRoot C pc:=by
    by_contra hh
    exact hm (Finsupp.single_eq_of_ne hh)
  change nonpDegree coord pc m=0
  rw [heq,map_nsmul,nonpDegree_simple_self C coord hcoord,nsmul_zero]

variable {E:Type*} [AddCommGroup E] [Module ℝ E]
variable (hΩ:∀m,Ω m m=0) (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k:Module.Dual ℝ E) (H:∀N,GenericOffset (realRootsThrough e C N) 0 v k)

include hcoord hS hcomp in
lemma mutatedLineFactor_pure (a:ℝ) :
    pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a)=
    if (k+a • v) (e (simpleRoot C pc))=0 then
      orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0)))
        (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc)) else 1 := by
  classical
  by_cases hp:(k+a • v) (e (simpleRoot C pc))=0
  · have hevent:∃N,a∈lineEvents (realRootsThrough e C N) v k:=
      ⟨1,RationalFiber.line_cut_event C pc e L hdeg v k H a hp⟩
    rw [ite_eq_left hp,mutatedLineFactor,dite_eq_left hevent,ite_eq_left hp]
    exact pureFaceSeries_orient_simple Ω (mutatedRoots Ω C pc)
      (mutatedCoordinates Ω C coord pc) (mutatedCoordinates_retraction Ω C coord hcoord pc) pc _
  · rw [ite_eq_right hp]
    apply pureFaceSeries_kernel_one Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
      (mutatedCoordinates_retraction Ω C coord hcoord pc) pc _
      (mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a)
      (mutatedLineFactor_constant Ω hΩ C coord pc e he L hdeg v k H a)
      ((realMutationCovector e S (simpleRoot C pc) (k+a • v)).toAddMonoidHom.comp e)
    · change realMutationCovector e S (simpleRoot C pc) (k+a • v)
        (e (simpleRoot (mutatedRoots Ω C pc) pc))≠0
      rw [mutatedRoot_p,map_neg,map_neg,realMutationCovector_at_p e S _ hS]
      exact neg_ne_zero.mpr hp
    · exact mutatedLineFactor_kernel Ω hΩ C coord pc e he S hS hcomp L hdeg v k H a
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
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RegradeLog
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.FormalLog.log_one _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A] [Algebra ℚ A]
lemma logPolynomial_coeff (F : PowerSeries A) (hf : constantCoeff F=1) (N n : ℕ) (hn : n≤N) :
    coeff n (logPolynomial F N)=coeff n (FormalLog.log F) := by
  simp only [logPolynomial,FormalLog.log,coeff_mk,map_sum,coeff_smul]
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro k hk hkn
  rw [coeff_power_vanish (F-1) (by simp [hf]) (k+1) n (by
    simp only [Finset.mem_range,not_lt] at hkn; omega),smul_zero]
end
end ElementaryPositivity.FormalLog
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeLogRing
local instance regradeLogNonUnitalSemiring_r8ac191_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance regradeLogNonUnitalNonAssocSemiring_r8ac191_1 : NonUnitalNonAssocSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeLogAddCommMonoid
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeLogAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeLogAddCommGroup
local instance regradeLogSub_r8ac191_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
omit [Algebra ℚ R] in
lemma RegradeBound.pow {f : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B f) (k : ℕ) :
    RegradeBound v Ω δ B (f^k) := by
  induction k with
  | zero=>simpa using RegradeBound.one v Ω δ B
  | succ k ih=>exact ih.mul v Ω δ B hf

omit [Algebra ℚ R] in
lemma regrade_pow {F : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B F) (k : ℕ) :
    regrade v Ω δ B (F^k)=(regrade v Ω δ B F)^k := by
  induction k with
  | zero=>simpa using regrade_one v Ω δ B
  | succ k ih=>rw [pow_succ,regrade_mul v Ω δ B (hf.pow v Ω δ B k) hf,ih,pow_succ]
lemma regrade_logPolynomial (F : PowerSeries (Torus v Ω)) (hf : RegradeBound v Ω δ B F) (N : ℕ) :
    regrade v Ω δ B (FormalLog.logPolynomial F N)=
      FormalLog.logPolynomial (regrade v Ω δ B F) N := by
  change regradeLinear v Ω δ B (FormalLog.logPolynomial F N)=_
  rw [FormalLog.logPolynomial,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]
  congr 1
  change regrade v Ω δ B ((F-1)^(k+1))=_
  rw [regrade_pow v Ω δ B (by
    intro j m hm
    by_cases hF : coeff j F m=0
    · apply RegradeBound.one v Ω δ B j m
      intro h1
      apply hm
      rw [map_sub,sub_eq_add_neg]
      change coeff j F m+ -(coeff j (1 : PowerSeries (Torus v Ω)) m)=0
      rw [hF,h1,neg_zero,add_zero]
    · exact hf j m hF)]
  congr 1
  change regradeLinear v Ω δ B (F-1)=_
  rw [map_sub]
  change regrade v Ω δ B F-regrade v Ω δ B 1=_
  rw [regrade_one]
omit [Algebra ℚ R] in
lemma regrade_constant (F : PowerSeries (Torus v Ω)) (hf : constantCoeff F=1) :
    constantCoeff (regrade v Ω δ B F)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply,regrade_coeff]
  simp only [mul_zero,zero_add,Finset.sum_range_one,coeff_zero_eq_constantCoeff,hf,
    homogenize_one,constantCoeff_one]
omit [Algebra ℚ R] in
lemma regrade_coeff_congr (F G : PowerSeries (Torus v Ω)) (d : ℕ)
    (H : ∀n≤B*d,coeff n F=coeff n G) :
    coeff d (regrade v Ω δ B F)=coeff d (regrade v Ω δ B G) := by
  rw [regrade_coeff,regrade_coeff]
  apply Finset.sum_congr rfl
  intro n hn
  rw [H n (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn)]
lemma regrade_log (F : PowerSeries (Torus v Ω))
    (hf : RegradeBound v Ω δ B F) (hc : constantCoeff F=1) :
    regrade v Ω δ B (FormalLog.log F)=FormalLog.log (regrade v Ω δ B F) := by
  apply PowerSeries.ext
  intro d
  let N:=max d (B*d)
  calc
    coeff d (regrade v Ω δ B (FormalLog.log F))=
        coeff d (regrade v Ω δ B (FormalLog.logPolynomial F N)) := by
      apply regrade_coeff_congr
      intro n hn
      exact (FormalLog.logPolynomial_coeff F hc N n (hn.trans (le_max_right _ _))).symm
    _ = coeff d (FormalLog.logPolynomial (regrade v Ω δ B F) N) := by
      rw [regrade_logPolynomial v Ω δ B F hf N]
    _ = coeff d (FormalLog.log (regrade v Ω δ B F)) :=
      FormalLog.logPolynomial_coeff _ (regrade_constant v Ω δ B F hc) N d (le_max_left _ _)
end
end ElementaryPositivity.QuantumTorus

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
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_PureCutTelescoping
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
local instance instNonUnitalSemiringTorus_11_r8ac191_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_11_r8ac191_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance infinityLaurentFiniteAddCommMonoid_r8ac191_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance infinityLaurentFiniteAddGroup_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance infinityLaurentFiniteNonUnitalSemiring_r8ac191_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance infinityLaurentFiniteNonUnitalNonAssocSemiring_r8ac191_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance rootLaurentCompletionAddCommMonoid_r8ac191_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rootLaurentCompletionAddGroup_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorusLaurentSeriesRat_r8ac191_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRat_4_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedPureLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k:Module.Dual ℝ E) (H:∀N,GenericOffset (realRootsThrough e C N) 0 v k)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutatedPureLineRing
local instance mutatedPureLineAddCommMonoid_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPureLineAddGroup_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hcoord in
lemma pureFaceSeries_product {J:Type*} (l:List J) (f:J → PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf:∀a∈l,SeriesGraded LaurentRay.vUnit Ω C (f a)) :
    pureFaceSeries Ω coord pc (l.map f).prod=(l.map (fun a=>pureFaceSeries Ω coord pc (f a))).prod := by
  induction l with
  | nil=>exact pureFaceSeries_one Ω coord pc
  | cons a l ih=>
    simp only [List.map_cons,List.prod_cons]
    rw [pureFaceSeries_mul Ω C coord hcoord pc _ _ (hf a (by simp))
      (SeriesGraded.list_prod Ω C l f (fun a ha=>hf a (by simp [ha]))),
      ih (fun a ha=>hf a (by simp [ha]))]

include hcoord hS hcomp in
lemma mutatedLineProduct_pure (lo hi:ℝ) (hlohi:lo<hi)
    (hlo:lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi:hi∉lineEvents (realRootsThrough e C 1) v k) (N:ℕ) (hN:1≤N) :
    pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N)*
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+lo • v) (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+hi • v) (e (simpleRoot C pc)))) := by
  classical
  rw [mutatedLineProduct,pureFaceSeries_product Ω (mutatedRoots Ω C pc)
    (mutatedCoordinates Ω C coord pc) (mutatedCoordinates_retraction Ω C coord hcoord pc) pc _ _
    (fun a _=>mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a)]
  have heq:(fun a=>pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a))=
    (fun a=>if k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))=0 then
      orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0)))
        (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc)) else 1):=by
    funext a
    simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using
      mutatedLineFactor_pure Ω C coord hcoord pc hΩ e he S hS hcomp L hdeg v k H a
  rw [heq]
  apply pureCut_telescope _ (normalizedSimple_constant Ω _)
    (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) lo hi hlohi
    (Or.inl (RationalFiber.line_cut_offset_ne C pc e L hdeg v k H))
  · exact fun hz=>hlo (RationalFiber.line_cut_event C pc e L hdeg v k H lo hz)
  · exact fun hz=>hhi (RationalFiber.line_cut_event C pc e L hdeg v k H hi hz)
  · exact fun a ha=>(Finset.mem_filter.mp ha).2
  · intro a hla hah hz
    exact Finset.mem_filter.mpr ⟨lineEvents_mono (realRootsThrough_mono C e hN) v k
      (RationalFiber.line_cut_event C pc e L hdeg v k H a hz),hla,hah⟩

include hcoord hS hcomp in
lemma mutatedLineCompletion_pure (lo hi:ℝ) (hlohi:lo<hi)
    (hlo:lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi:hi∉lineEvents (realRootsThrough e C 1) v k) :
    pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi)*
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+lo • v) (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+hi • v) (e (simpleRoot C pc)))) := by
  apply PowerSeries.ext
  intro d
  let N:=max 1 ((mutationSize Ω C pc+1)*d)
  have HH:=mutatedLineProduct_pure Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H
    lo hi hlohi hlo hhi N (le_max_left _ _)
  rw [←HH]
  apply FormalLog.mul_coeff_congr
  · intro j hj
    rw [coeff_pureFaceSeries,coeff_pureFaceSeries,
      mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg v k H lo hi j N
        (le_max_left _ _) ((Nat.mul_le_mul_left _ hj).trans (le_max_right _ _))]
  · exact fun _ _=>rfl
end
end ElementaryPositivity.QuantumTorus

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
local instance instAddCommMonoidTorus_7_r8ac191_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_7_r8ac191_2 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_r8ac191_2 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_r8ac191_2 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_1_r8ac191_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance laurentCompletionFaithfulAddCommMonoid_r8ac191_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentCompletionFaithfulAddGroup_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentCompletionFaithfulNonUnitalSemiring_r8ac191_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_8_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_8_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_2_r8ac191_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance mutatedPathIndependentAddCommMonoid_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPathIndependentAddGroup_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
variable (hnd:∀r≠0,∃m,Ω r m≠0)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutatedPathIndependentPureRing
local instance mutatedPathIndependentPureAddCommMonoid_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPathIndependentPureAddGroup_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hcoord hS hcomp in
omit [FiniteDimensional ℝ E] in
lemma mutatedPathCompletion_pure {a b:Module.Dual ℝ E} (p:GenericLinePath C e a b) :
    pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p)*
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<a (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<b (e (simpleRoot C pc)))) := by
  induction p with
  | nil=>rw [mutatedPathCompletion,pureFaceSeries_one,one_mul]
  | append s p ih=>
    rw [mutatedPathCompletion,pureFaceSeries_mul Ω (mutatedRoots Ω C pc)
      (mutatedCoordinates Ω C coord pc) (mutatedCoordinates_retraction Ω C coord hcoord pc) pc _ _
      (mutatedLineCompletion_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
        s.direction s.offset s.generic s.lo s.hi)
      (mutatedPathCompletion_graded Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p),
      mul_assoc,ih]
    exact mutatedLineCompletion_pure Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi s.ordered (s.start_regular 1) (s.finish_regular 1)

include hnd in
lemma mutatedTransport_pure {a b:Module.Dual ℝ E}
    (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:a (e (simpleRoot C pc))<0) (hb:0<b (e (simpleRoot C pc))) :
    pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val=
      normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc) := by
  obtain ⟨p⟩:=generic_path_exists C e a b HA HB
  rw [mutatedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB p]
  have HH:=mutatedPathCompletion_pure Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p
  simpa only [pureCutGauge,decide_eq_false (not_lt.mpr (le_of_lt ha)),Bool.false_eq_true,ite_false, if_false,
    decide_eq_true hb,ite_true, if_true,mul_one] using HH
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationLogCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I) (pos : Bool) (v : Rˣ)
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorus_6
local instance instAddCommMonoidTorus_7_r8ac191_2 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_9_r8ac191_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma mutationCompletion_log (F : PowerSeries (Torus v Ω))
    (hf : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) F)
    (hc : constantCoeff F=1) :
    mutationCompletion Ω hΩ C coord pc pos v (FormalLog.log F)=
      FormalLog.log (mutationCompletion Ω hΩ C coord pc pos v F) := by
  unfold mutationCompletion
  rw [regrade_log v Ω _ _ F hf hc]
  exact (FormalLog.log_map (mutationTorusPush Ω hΩ C pc pos v).toRatAlgHom _).symm
lemma mutationCompletion_log_read (F : PowerSeries (Torus v Ω))
    (hf : RegradeBound v Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) F)
    (hc : constantCoeff F=1) (d : ℕ) (m : M) :
    coeff d (FormalLog.log (mutationCompletion Ω hΩ C coord pc pos v F))
        (mutationLinearPiece Ω C pc pos m)=
      if d=(mutationNewOrder Ω C coord pc pos m).toNat then
        ∑n∈Finset.range ((mutationSize Ω C pc+1)*d+1), coeff n (FormalLog.log F) m else 0 := by
  rw [←mutationCompletion_log Ω hΩ C coord pc pos v F hf hc,mutationCompletion_coeff_read]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
attribute [local instance] Classical.decEq
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
lemma regular_covector_with_signs (Q P : Finset E) (k : Module.Dual ℝ E) :
    ∃h : Module.Dual ℝ E,RegularCovector C e h ∧ (∀q∈Q,q≠0 → h q≠0) ∧
      ∀s∈P,(0<k s → 0<h s) ∧ (k s<0 → h s<0) := by
  classical
  let W : Set E:=((⋃N,(realRootsThrough e C N : Set E))∪(Q : Set E))\{0}
  have hW : W.Countable:=
    ((Set.countable_iUnion (fun N=>(realRootsThrough e C N).countable_toSet)).union Q.countable_toSet).mono
      Set.sdiff_subset
  have hp : ∀w∈W,w∉Submodule.span ℝ ({0}:Set E):=by
    intro w hw
    simpa only [W,Set.mem_sdiff,Set.mem_singleton_iff,Submodule.span_zero_singleton,Submodule.mem_bot]
      using hw.2
  obtain ⟨h,_,hh,HS⟩:=countable_avoid_with_probes W hW 0 hp
    (P.image (fun s=>(0,s))) 0 k (map_zero k)
  refine ⟨h,?_,?_,?_⟩
  · intro N s hs hn
    exact hh s ⟨Or.inl (Set.mem_iUnion.mpr ⟨N,hs⟩),hn⟩
  · intro q hq hn
    exact hh q ⟨Or.inr hq,hn⟩
  · intro s hs
    simpa only [zero_smul,add_zero] using HS (0,s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)

lemma regular_straddle (Q P : Finset E) (k : Module.Dual ℝ E) (r : E)
    (hr : r≠0) (hk : k r=0) :
    ∃x y : Module.Dual ℝ E,RegularCovector C e x ∧ RegularCovector C e y ∧
      (∀q∈Q,q≠0 → x q≠0) ∧ (∀q∈Q,q≠0 → y q≠0) ∧
      0<x r ∧ y r<0 ∧
      ∀s∈P,(0<k s → 0<x s ∧ 0<y s) ∧ (k s<0 → x s<0 ∧ y s<0) := by
  classical
  obtain ⟨g,hg⟩:=Module.Projective.exists_dual_eq_one ℝ hr
  obtain ⟨ε,hε,HE⟩:=preserve_finite_signs P k g
  obtain ⟨η,hη,HH⟩:=preserve_finite_signs P k (-g)
  let kx:=k+(ε/2) • g
  let ky:=k+(η/2) • (-g)
  obtain ⟨x,HX,Hx,Sx⟩:=regular_covector_with_signs C e Q (insert r P) kx
  obtain ⟨y,HY,Hy,Sy⟩:=regular_covector_with_signs C e Q (insert r P) ky
  have hxr : 0<kx r:=by simp only [kx,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hk,hg] <;> linarith
  have hyr : ky r<0:=by simp only [ky,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.neg_apply,smul_eq_mul,hk,hg] <;> linarith
  refine ⟨x,y,HX,HY,Hx,Hy,(Sx r (Finset.mem_insert_self _ _)).1 hxr,
    (Sy r (Finset.mem_insert_self _ _)).2 hyr,?_⟩
  intro s hs
  have He:=HE (ε/2) (by linarith) (by linarith) s hs
  have Hh:=HH (η/2) (by linarith) (by linarith) s hs
  exact ⟨fun h=>⟨(Sx s (Finset.mem_insert_of_mem hs)).1 (He.1 h),
      (Sy s (Finset.mem_insert_of_mem hs)).1 (Hh.1 h)⟩,
    fun h=>⟨(Sx s (Finset.mem_insert_of_mem hs)).2 (He.2.1 h),
      (Sy s (Finset.mem_insert_of_mem hs)).2 (Hh.2.1 h)⟩⟩

lemma regular_straddle_offcut (Q P : Finset E) (k : Module.Dual ℝ E) (r p : E)
    (hr : r≠0) (hk : k r=0) (hp : p∉Submodule.span ℝ {r}) :
    ∃x y : Module.Dual ℝ E,RegularCovector C e x ∧ RegularCovector C e y ∧
      (∀q∈Q,q≠0 → x q≠0) ∧ (∀q∈Q,q≠0 → y q≠0) ∧
      0<x r ∧ y r<0 ∧ ((0<x p ∧ 0<y p) ∨ (x p<0 ∧ y p<0)) ∧
      ∀s∈insert p P,(0<k s → 0<x s ∧ 0<y s) ∧ (k s<0 → x s<0 ∧ y s<0) := by
  classical
  obtain ⟨h,hhr,hhp,Hh⟩:=generic_offset r {p} (insert p P) k hk (by simpa using hp)
  obtain ⟨x,y,HX,HY,Hx,Hy,hxr,hyr,HS⟩:=regular_straddle C e Q (insert p P) h r hr hhr
  refine ⟨x,y,HX,HY,Hx,Hy,hxr,hyr,?_,?_⟩
  · rcases lt_or_gt_of_ne (hhp p (Finset.mem_singleton_self p)) with hn|hn
    · exact Or.inr ((HS p (Finset.mem_insert_self _ _)).2 hn)
    · exact Or.inl ((HS p (Finset.mem_insert_self _ _)).1 hn)
  · intro s hs
    exact ⟨fun h=>(HS s hs).1 ((Hh s hs).1 h),fun h=>(HS s hs).2 ((Hh s hs).2 h)⟩
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

include hS in
lemma mutated_regular_anchors (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) :
    ∃a b:Module.Dual ℝ E,RegularCovector C e a ∧ RegularCovector C e b ∧
      (∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        0 < realMutationCovector e S (simpleRoot C pc) a (e m)) ∧
      (∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        realMutationCovector e S (simpleRoot C pc) b (e m)<0) := by
  classical
  obtain ⟨J,hJ⟩:=mutated_degree_covector Ω C pc e hC
  have hJp:J (e (simpleRoot C pc))= -1:=by
    have H:=hJ pc
    rw [mutatedRoot_p,map_neg,map_neg] at H
    linarith
  let K:=realShearCovectorInverse e S (simpleRoot C pc) J
  have hK:realShearCovector e S (simpleRoot C pc) K=J:=
    realShearCovector_right_inverse e S _ hS J
  let P:=Finset.univ.image (fun i=>realShearVector e S (simpleRoot C pc)
    (e (simpleRoot (mutatedRoots Ω C pc) i)))
  let Q:=Finset.univ.image (fun i=>e (simpleRoot (mutatedRoots Ω C pc) i))
  obtain ⟨a,HA,_,Sa⟩:=regular_covector_with_signs C e ∅ (insert (e (simpleRoot C pc)) P) K
  obtain ⟨b,HB,_,Sb⟩:=regular_covector_with_signs C e ∅ (insert (e (simpleRoot C pc)) Q) (-J)
  have hap:a (e (simpleRoot C pc))<0:=by
    apply (Sa _ (Finset.mem_insert_self _ _)).2
    rw [realShearCovectorInverse_at_p e S _ hS J,hJp]
    norm_num
  have hbp:0<b (e (simpleRoot C pc)):=by
    apply (Sb _ (Finset.mem_insert_self _ _)).1
    simp [hJp]
  have ha:∀i,0 < realMutationCovector e S (simpleRoot C pc) a
      (e (simpleRoot (mutatedRoots Ω C pc) i)):=by
    intro i
    rw [realMutationCovector,ite_eq_right (not_le_of_gt hap),realShearCovector_eval]
    apply (Sa _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))).1
    rw [←realShearCovector_eval,hK,hJ]
    norm_num
  have hb:∀i,0<(-realMutationCovector e S (simpleRoot C pc) b)
      (e (simpleRoot (mutatedRoots Ω C pc) i)):=by
    intro i
    rw [realMutationCovector,ite_eq_left hbp.le,LinearMap.neg_apply]
    apply neg_pos.mpr
    apply (Sb _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))).2
    simp [hJ]
  refine ⟨a,b,HA,HB,fun n hn m hm=>covector_root_pos _ e _ ha hn hm,?_⟩
  intro n hn m hm
  have H:=covector_root_pos _ e _ hb hn hm
  simpa only [LinearMap.neg_apply,neg_pos] using H
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))

lemma onPositiveRay_real_span {r p:M} (H:OnPositiveRay r p) :
    e p∈Submodule.span ℝ {e r} := by
  obtain ⟨a,b,ha,hb,H⟩:=H
  have HH:(a:ℝ) • e p=(b:ℝ) • e r:=by
    simpa only [map_nsmul,Nat.cast_smul_eq_nsmul] using congrArg e H
  refine Submodule.mem_span_singleton.mpr ⟨(a:ℝ)⁻¹*(b:ℝ),?_⟩
  rw [mul_smul,←HH,inv_smul_smul₀ (by exact_mod_cast (Nat.ne_of_gt ha))]

include he hS hcomp in
lemma nonpure_preimage_off_line (J:Module.Dual ℝ E)
    (hJ:∀i,J (e (simpleRoot (mutatedRoots Ω C pc) i))=1)
    (r:M) (d:ℕ) (hd:0<d)
    (hr:HasRootDegree (mutatedRoots Ω C pc) d (mutationIncomingLabel Ω (simpleRoot C pc) r))
    (hn:¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
      (simpleRoot (mutatedRoots Ω C pc) pc)) :
    e (simpleRoot C pc)∉Submodule.span ℝ {e r} := by
  intro H
  obtain ⟨a,ha⟩:=Submodule.mem_span_singleton.mp H
  have hp:Ω (simpleRoot C pc) r=0:=by
    have HH:(Ω (simpleRoot C pc) r:ℝ)=0:=by
      rw [←hcomp,←ha,map_smul,LinearMap.smul_apply,hS,smul_zero]
    exact_mod_cast HH
  have hh:mutationIncomingLabel Ω (simpleRoot C pc) r=r:=
    mutationIncomingLabel_nonnegative Ω _ r (by omega)
  apply hn
  apply positive_ray_of_mem_span e he (mutatedRoots Ω C pc) J
    (fun n m hm=>covector_root_eval _ e J hJ hm) _ _ d 1 hd (by omega) hr
    (simpleRoot_degree _ pc)
  rw [hh,mutatedRoot_p,map_neg]
  exact Submodule.neg_mem _ H

include he hS hcomp in
lemma nonpure_preimage_geometry (J:Module.Dual ℝ E)
    (hJ:∀i,J (e (simpleRoot (mutatedRoots Ω C pc) i))=1)
    (r:M) (d:ℕ) (hd:0<d)
    (hr:HasRootDegree (mutatedRoots Ω C pc) d (mutationIncomingLabel Ω (simpleRoot C pc) r))
    (hn:¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
      (simpleRoot (mutatedRoots Ω C pc) pc)) :
    e r≠0 ∧ e (simpleRoot C pc)∉Submodule.span ℝ {e r} ∧
      ¬OnPositiveRay r (simpleRoot C pc) := by
  have HP:=nonpure_preimage_off_line Ω C pc e he S hS hcomp J hJ r d hd hr hn
  refine ⟨?_,HP,fun H=>HP (onPositiveRay_real_span e H)⟩
  intro H
  have hr0:r=0:=he (H.trans (map_zero e).symm)
  have hh:mutationIncomingLabel Ω (simpleRoot C pc) r=0:=by simp [hr0,mutationIncomingLabel]
  have HJ:=covector_root_eval _ e J hJ hr
  rw [hh,map_zero,map_zero] at HJ
  have : (d:ℝ)>0:=by exact_mod_cast hd
  linarith
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationIncomingFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma literalIncomingRay_eq_one_of_none (l : List (WallUnitDatum M)) (r : M)
    (hn : ∀u∈l,¬OnPositiveRay r u.root) : literalIncomingRay Ω l r=1 := by
  classical
  unfold literalIncomingRay
  have hf : l.filter (fun u=>OnPositiveRay r u.root)=[]:=by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro u hu
    have H:=List.mem_filter.mp hu
    exact hn u H.1 (of_decide_eq_true H.2)
  rw [hf,List.map_nil,List.prod_nil]
lemma literalIncoming_simple_nonsimple (r : M)
    (hn : ∀i,¬OnPositiveRay r (simpleRoot C i)) : literalIncomingRay Ω (simpleIncomingList C) r=1 := by
  apply literalIncomingRay_eq_one_of_none
  intro u hu
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hu
  exact hn i

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (p : M) (hp : Ω p p=0)
lemma mutationIncomingLabel_nsmul (a : ℕ) (m : M) :
    mutationIncomingLabel Ω p (a • m)=a • mutationIncomingLabel Ω p m := by
  by_cases hm : 0≤Ω p m
  · rw [mutationIncomingLabel_nonnegative Ω p m hm,
      mutationIncomingLabel_nonnegative Ω p (a • m)]
    rw [map_nsmul,nsmul_eq_mul]
    exact mul_nonneg (Int.natCast_nonneg _) hm
  · have hm' : Ω p m≤0:=le_of_lt (lt_of_not_ge hm)
    rw [mutationIncomingLabel_nonpositive Ω p m hm',
      mutationIncomingLabel_nonpositive Ω p (a • m),map_nsmul]
    rw [map_nsmul,nsmul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hm'
include hp in
lemma mutationIncomingLabel_positive_ray_iff (r m : M) :
    OnPositiveRay (mutationIncomingLabel Ω p r) (mutationIncomingLabel Ω p m)↔OnPositiveRay r m := by
  constructor
  · rintro ⟨a,b,ha,hb,he⟩
    refine ⟨a,b,ha,hb,?_⟩
    apply (mutationIncomingLabelEquiv Ω p hp).injective
    change mutationIncomingLabel Ω p (a • m)=mutationIncomingLabel Ω p (b • r)
    simpa only [mutationIncomingLabel_nsmul] using he
  · rintro ⟨a,b,ha,hb,he⟩
    exact ⟨a,b,ha,hb,by simpa only [mutationIncomingLabel_nsmul] using congrArg (mutationIncomingLabel Ω p) he⟩

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (pc : I)
lemma mutationIncomingLabel_simple (i : I) (hi : i≠pc) :
    mutationIncomingLabel Ω (simpleRoot C pc) (simpleRoot C i)=simpleRoot (mutatedRoots Ω C pc) i := by
  rw [mutatedRoot_off Ω C pc i hi]
  rfl
lemma mutationIncomingLabel_simple_ray_iff (hΩ : ∀m,Ω m m=0)
    (i : I) (hi : i≠pc) (r : M) :
    OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r) (simpleRoot (mutatedRoots Ω C pc) i)↔
      OnPositiveRay r (simpleRoot C i) := by
  rw [←mutationIncomingLabel_simple Ω C pc i hi]
  exact mutationIncomingLabel_positive_ray_iff Ω (simpleRoot C pc) (hΩ _) r (simpleRoot C i)
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

include he hcoord hS hcomp in
lemma mutation_incoming_probes (K N:ℕ) (r:M) (hr:e r≠0)
    (hp:e (simpleRoot C pc)∉Submodule.span ℝ {e r}) :
    ∃(pos:Bool) (x y:Module.Dual ℝ E),RegularCovector C e x ∧ RegularCovector C e y ∧
      cutSide pos (x.toAddMonoidHom.comp e) (simpleRoot C pc) ∧
      cutSide pos (y.toAddMonoidHom.comp e) (simpleRoot C pc) ∧
      (if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0) ∧
      mutationLinearPiece Ω C pc pos r=mutationIncomingLabel Ω (simpleRoot C pc) r ∧
      0<x (e r) ∧ y (e r)<0 ∧
      (∀ n≤K,∀m,HasRootDegree C n m →
        (0 < incomingCovector Ω r m → 0<x (e m) ∧ 0<y (e m)) ∧
        (incomingCovector Ω r m<0 → x (e m)<0 ∧ y (e m)<0)) ∧
      (∀ n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
        (0 < incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m →
          0 < realMutationCovector e S (simpleRoot C pc) x (e m) ∧
          0 < realMutationCovector e S (simpleRoot C pc) y (e m)) ∧
        (incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m<0 →
          realMutationCovector e S (simpleRoot C pc) x (e m)<0 ∧
          realMutationCovector e S (simpleRoot C pc) y (e m)<0)) ∧
      (∀ n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
        realMutationCovector e S (simpleRoot C pc) x (e m)≠0 ∧
        realMutationCovector e S (simpleRoot C pc) y (e m)≠0) := by
  classical
  let A:=realRootsThrough e (mutatedRoots Ω C pc) N
  let Q:=A∪A.image (realShearVector e S (simpleRoot C pc))
  let P:=realRootsThrough e C K∪Q
  let k:=S.flip (e r)
  obtain ⟨x,y,HX,HY,Hx,Hy,hxr,hyr,hside,HS⟩:=regular_straddle_offcut C e Q P k
    (e r) (e (simpleRoot C pc)) hr (hS _) hp
  have existSide : ∃pos:Bool,(if pos then 0<x (e (simpleRoot C pc)) ∧ 0<y (e (simpleRoot C pc))
        else x (e (simpleRoot C pc))<0 ∧ y (e (simpleRoot C pc))<0):=by
    rcases hside with hh|hh
    · exact ⟨true,hh⟩
    · exact ⟨false,hh⟩
  obtain ⟨pos,hpos⟩:=existSide
  have sx : cutSide pos (x.toAddMonoidHom.comp e) (simpleRoot C pc):=by cases pos <;> exact hpos.1
  have sy : cutSide pos (y.toAddMonoidHom.comp e) (simpleRoot C pc):=by cases pos <;> exact hpos.2
  have hxside:=realMutationCovector_eq_side e S (simpleRoot C pc) pos x (by cases pos <;> exact le_of_lt hpos.1)
  have hyside:=realMutationCovector_eq_side e S (simpleRoot C pc) pos y (by cases pos <;> exact le_of_lt hpos.2)
  have evalX (m:M) : realMutationCovector e S (simpleRoot C pc) x (e m)=
      x (if pos then e m else realShearVector e S (simpleRoot C pc) (e m)):=by
    rw [hxside]; cases pos
    · exact realShearCovector_eval e S _ _ _
    · rfl
  have evalY (m:M) : realMutationCovector e S (simpleRoot C pc) y (e m)=
      y (if pos then e m else realShearVector e S (simpleRoot C pc) (e m)):=by
    rw [hyside]; cases pos
    · exact realShearCovector_eval e S _ _ _
    · rfl
  have memQ (n:ℕ) (hn:n≤N) (m:M) (hm:HasRootDegree (mutatedRoots Ω C pc) n m) :
      (if pos then e m else realShearVector e S (simpleRoot C pc) (e m))∈Q:=by
    have ha : e m∈A:=realRoot_mem e _ N n hn m hm
    cases pos
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e m,ha,rfl⟩)
    · exact Finset.mem_union_left _ ha
  have hsign : (if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0):=by
    have hs:=HS (e (simpleRoot C pc)) (Finset.mem_insert_self _ _)
    have hc : k (e (simpleRoot C pc))=(Ω (simpleRoot C pc) r:ℝ):=hcomp _ _
    cases pos
    · have hh : Ω (simpleRoot C pc) r≤0:=by
        by_contra hn
        have H:=hs.1 (by rw [hc]; exact_mod_cast lt_of_not_ge hn)
        exact (not_lt_of_ge hpos.1.le H.1)
      exact hh
    · have hh : 0≤Ω (simpleRoot C pc) r:=by
        by_contra hn
        have H:=hs.2 (by rw [hc]; exact_mod_cast lt_of_not_ge hn)
        exact (not_lt_of_ge (le_of_lt hpos.1) H.1)
      exact hh
  refine ⟨pos,x,y,HX,HY,sx,sy,hsign,?_,hxr,hyr,?_,?_,?_⟩
  · cases pos
    · exact (mutationIncomingLabel_nonpositive Ω (simpleRoot C pc) r hsign).symm
    · exact (mutationIncomingLabel_nonnegative Ω (simpleRoot C pc) r hsign).symm
  · intro n hn m hm
    have H:=HS (e m) (Finset.mem_insert_of_mem (Finset.mem_union_left _ (realRoot_mem e C K n hn m hm)))
    change ((0 < S (e m) (e r) → _) ∧ (S (e m) (e r)<0 → _)) at H
    rw [hcomp] at H
    exact H
  · intro n hn m hm
    have H:=HS _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (memQ n hn m hm)))
    rw [evalX,evalY,incoming_side_eval Ω C pc e S hS hcomp pos r m]
    exact H
  · intro n hn m hm
    have hnz : e m≠0:=by
      intro H
      have hm0 : m=0:=he (H.trans (map_zero e).symm)
      exact positive_root_ne_zero (mutatedRoots Ω C pc)
        (Function.LeftInverse.injective (mutatedCoordinates_retraction Ω C coord hcoord pc))
        (Nat.succ_pos n) (hm0 ▸ hm)
    have hv : (if pos then e m else realShearVector e S (simpleRoot C pc) (e m))≠0:=by
      cases pos
      · exact realShearVector_ne_zero C pc e S hS hnz
      · exact hnz
    rw [evalX,evalY]
    exact ⟨Hx _ (memQ (n+1) hn m hm) hv,Hy _ (memQ (n+1) hn m hm) hv⟩
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutationIncomingProbesRing
local instance mutationIncomingProbesAddCommMonoid_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutationIncomingProbesAddGroup_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma normalizedSimple_regradeBound (δ:M →+ ℤ) (B:ℕ) (r:M) (hr:δ r=1) :
    RegradeBound LaurentRay.vUnit Ω δ (B+1) (normalizedSimple Ω r) := by
  intro n m hm
  have H:=normalizedSimple_homogeneous Ω δ r hr n m hm
  rw [H,Int.toNat_natCast]
  exact ⟨Int.natCast_nonneg _,by nlinarith⟩

omit [Fintype I] in
lemma ray_pairing_side (pos:Bool) (r:M) (i:I) (hr:OnPositiveRay r (simpleRoot C i))
    (hs:if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0) :
    if pos then 0 ≤ mutationPairing Ω C pc i else mutationPairing Ω C pc i≤0 := by
  obtain ⟨a,b,ha,hb,HH⟩:=hr
  have H:=congrArg (Ω (simpleRoot C pc)) HH
  simp only [map_nsmul,nsmul_eq_mul] at H
  have ha' : (0:ℤ)<a:=by exact_mod_cast ha
  have hb' : (0:ℤ)<b:=by exact_mod_cast hb
  cases pos
  · change Ω (simpleRoot C pc) r≤0 at hs
    change Ω (simpleRoot C pc) (simpleRoot C i)≤0
    nlinarith
  · change 0≤Ω (simpleRoot C pc) r at hs
    change 0≤Ω (simpleRoot C pc) (simpleRoot C i)
    nlinarith

include hcoord in
lemma mutation_literal_incoming (pos:Bool) (r:M)
    (hs:if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0)
    (ho:¬OnPositiveRay r (simpleRoot C pc))
    (hn:¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
      (simpleRoot (mutatedRoots Ω C pc) pc)) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (literalIncomingRay Ω (simpleIncomingList C) r) ∧
    mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (literalIncomingRay Ω (simpleIncomingList C) r)=
      literalIncomingRay Ω (simpleIncomingList (mutatedRoots Ω C pc)) (mutationIncomingLabel Ω (simpleRoot C pc) r) := by
  classical
  by_cases H:∃i,OnPositiveRay r (simpleRoot C i)
  · obtain ⟨i,hi⟩:=H
    have hip : i≠pc:=by rintro rfl; exact ho hi
    have hs':=ray_pairing_side Ω C pc pos r i hi hs
    have hi':= (mutationIncomingLabel_simple_ray_iff Ω C pc hΩ i hip r).mpr hi
    rw [literalIncomingRay_eq Ω _ hi,literalIncoming_simple Ω C coord hcoord i,
      literalIncomingRay_eq Ω _ hi',literalIncoming_simple Ω (mutatedRoots Ω C pc)
        (mutatedCoordinates Ω C coord pc) (mutatedCoordinates_retraction Ω C coord hcoord pc) i]
    exact ⟨normalizedSimple_regradeBound Ω _ _ _ (mutation_side_simple_order Ω C coord hcoord pc pos i hip hs'),
      mutation_normalized_simple_side Ω hΩ C coord hcoord pc pos i hip hs'⟩
  · have H':∀i,¬OnPositiveRay r (simpleRoot C i):=by simpa only [not_exists] using H
    have HH:∀i,¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
        (simpleRoot (mutatedRoots Ω C pc) i):=by
      intro i hi
      by_cases hip:i=pc
      · subst i; exact hn hi
      · exact H' i ((mutationIncomingLabel_simple_ray_iff Ω C pc hΩ i hip r).mp hi)
    rw [literalIncoming_simple_nonsimple Ω C r H',literalIncoming_simple_nonsimple Ω _ _ HH,
      mutationCompletion_one]
    exact ⟨RegradeBound.one _ _ _ _,rfl⟩

include hcoord hΩ in
lemma mutation_incoming_log_read (pos:Bool) (r:M) (d:ℕ)
    (hs:if pos then 0≤Ω (simpleRoot C pc) r else Ω (simpleRoot C pc) r≤0)
    (ho:¬OnPositiveRay r (simpleRoot C pc))
    (hn:¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
      (simpleRoot (mutatedRoots Ω C pc) pc)) :
    coeff d (FormalLog.log (literalIncomingRay Ω (simpleIncomingList (mutatedRoots Ω C pc))
      (mutationIncomingLabel Ω (simpleRoot C pc) r))) (mutationLinearPiece Ω C pc pos r)=
      if d=(mutationNewOrder Ω C coord pc pos r).toNat then
        ∑n∈Finset.range ((mutationSize Ω C pc+1)*d+1),
          coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω r)
            (simpleTotalTransport Ω C)).val) r else 0 := by
  obtain ⟨hb,he⟩:=mutation_literal_incoming Ω hΩ C coord hcoord pc pos r hs ho hn
  rw [←he,mutationCompletion_log_read Ω hΩ C coord pc pos LaurentRay.vUnit _ hb]
  · split_ifs
    · apply Finset.sum_congr rfl
      intro n hn
      exact (literalTotalTransport_ray_prescription Ω C hΩ _ (simpleIncomingList_allowed C)
        r n r ⟨1,1,by omega,by omega,rfl⟩).symm
    · rfl
  · exact (literalIncomingCompleted Ω C (simpleIncomingList C) (simpleIncomingList_allowed C) r).property.1
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedIncomingNonpure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
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
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_11
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_14_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_14_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedIncoming_nonpure (r:M) (hr:e r≠0)
    (hp:e (simpleRoot C pc)∉Submodule.span ℝ {e r})
    (ho:¬OnPositiveRay r (simpleRoot C pc))
    (hn:¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
      (simpleRoot (mutatedRoots Ω C pc) pc))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (hA:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      0 < realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0) (d:ℕ) :
    coeff d (FormalLog.log (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (incomingCovector Ω (mutationIncomingLabel Ω (simpleRoot C pc) r))
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val)
      (mutationIncomingLabel Ω (simpleRoot C pc) r)=
    coeff d (FormalLog.log (literalIncomingRay Ω (simpleIncomingList (mutatedRoots Ω C pc))
      (mutationIncomingLabel Ω (simpleRoot C pc) r)))
      (mutationIncomingLabel Ω (simpleRoot C pc) r) := by
  obtain ⟨pos,x,y,HX,HY,sx,sy,hs,hlabel,hxr,hyr,Ho,Hn,Hreg⟩:=
    mutation_incoming_probes Ω C coord hcoord pc e he S hS hcomp
      ((mutationSize Ω C pc+1)*d) d r hr hp
  have H:=mutatedIncoming_probe Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    pos d d le_rfl r HA HB HX HY
    (fun n _ m hm=>hA _ (Nat.succ_pos n) m hm)
    (fun n _ m hm=>hB _ (Nat.succ_pos n) m hm)
    (fun n nh m hm=>(Hreg n nh m hm).1)
    (fun n nh m hm=>(Hreg n nh m hm).2) sx sy
    (fun n nh m hm=>⟨fun h=>((Ho n nh m hm).1 h).1,fun h=>((Ho n nh m hm).2 h).1⟩)
    (fun n nh m hm=>⟨fun h=>((Ho n nh m hm).1 h).2,fun h=>((Ho n nh m hm).2 h).2⟩)
    (fun n nh m hm=>⟨fun h=>((Hn n nh m hm).1 h).1,fun h=>((Hn n nh m hm).2 h).1⟩)
    (fun n nh m hm=>⟨fun h=>((Hn n nh m hm).1 h).2,fun h=>((Hn n nh m hm).2 h).2⟩)
    hxr.le hyr
  have HH:=mutation_incoming_log_read Ω hΩ C coord hcoord pc pos r d hs ho hn
  rw [hlabel] at H HH
  exact H.trans HH.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedIncomingNonpureRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
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
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_12
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_15_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_15_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedIncoming_nonpure_root
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (s:M) (d:ℕ) (hd:0<d) (hs:HasRootDegree (mutatedRoots Ω C pc) d s)
    (hn:¬OnPositiveRay s (simpleRoot (mutatedRoots Ω C pc) pc))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (hA:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      0 < realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0) :
    coeff d (FormalLog.log (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (incomingCovector Ω s)
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val) s=
    coeff d (FormalLog.log (literalIncomingRay Ω (simpleIncomingList (mutatedRoots Ω C pc)) s)) s := by
  let r:=(mutationIncomingLabelEquiv Ω (simpleRoot C pc) (hΩ _)).symm s
  have hr:mutationIncomingLabel Ω (simpleRoot C pc) r=s:=
    (mutationIncomingLabelEquiv Ω (simpleRoot C pc) (hΩ _)).apply_symm_apply s
  obtain ⟨J,hJ⟩:=mutated_degree_covector Ω C pc e hC
  obtain ⟨hr0,hp,ho⟩:=nonpure_preimage_geometry Ω C pc e he S hS hcomp J hJ r d hd
    (hr.symm ▸ hs) (by rwa [hr])
  have HH:=mutatedIncoming_nonpure Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    r hr0 hp ho (by rwa [hr]) HA HB hA hB d
  simpa only [hr] using HH
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
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
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_13
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_16_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_16_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedIncoming_pure_root
    (s:M) (d:ℕ) (hs:OnPositiveRay s (simpleRoot (mutatedRoots Ω C pc) pc))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:a (e (simpleRoot C pc))<0) (hb:0<b (e (simpleRoot C pc))) :
    coeff d (FormalLog.log (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (incomingCovector Ω s)
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val) s=
    coeff d (FormalLog.log (literalIncomingRay Ω (simpleIncomingList (mutatedRoots Ω C pc)) s)) s := by
  let C':=mutatedRoots Ω C pc
  let coord':=mutatedCoordinates Ω C coord pc
  have hc:∀a,coord' (C' a)=a:=mutatedCoordinates_retraction Ω C coord hcoord pc
  have hz:nonpDegree coord' pc s=0:=by
    obtain ⟨a,b,ha,hb,heq⟩:=hs
    have H:=congrArg (nonpDegree coord' pc) heq
    rw [map_nsmul,map_nsmul,nonpDegree_simple_self C' coord' hc pc,nsmul_zero,nsmul_eq_mul] at H
    exact (mul_eq_zero.mp H.symm).resolve_left (by exact_mod_cast (Nat.ne_of_gt hb))
  have hp:incomingCovector Ω s (simpleRoot C' pc)=0:=by
    obtain ⟨a,b,ha,hb,heq⟩:=hs
    have H:=congrArg (Ω (simpleRoot C' pc)) heq
    rw [map_nsmul,map_nsmul,hΩ,nsmul_zero,nsmul_eq_mul] at H
    have HH:(Ω (simpleRoot C' pc)) s=0:=
      (mul_eq_zero.mp H.symm).resolve_left (by exact_mod_cast (Nat.ne_of_gt hb))
    change ((Ω (simpleRoot C' pc)) s:ℝ)=0
    exact_mod_cast HH
  let T:=mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
  rw [pureFace_log_chart_apply Ω C' coord' hc pc (incomingCovector Ω s) hp T d s hz]
  have HH:=congrArg (fun f:PowerSeries (Torus LaurentRay.vUnit Ω)=>coeff d (FormalLog.log f) s)
    (mutatedTransport_pure Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB ha hb)
  change coeff d (FormalLog.log (pureFace Ω C' coord' pc T).val) s=_ at HH
  rw [←pureFaceSeries_log Ω C' coord' hc pc,pureFaceSeries_apply,hz,ite_eq_left rfl] at HH
  rw [literalIncomingRay_eq Ω _ hs,literalIncoming_simple Ω C' coord' hc pc]
  exact HH
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutatedSystemIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
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
include hnd in
lemma mutatedTransport_eq_simple
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (hA:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      0 < realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0) :
    mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB=
      simpleTotalTransport Ω (mutatedRoots Ω C pc) := by
  let C':=mutatedRoots Ω C pc
  have ha:a (e (simpleRoot C pc))<0:=by
    have H:=hA 1 (by omega) _ (simpleRoot_degree C' pc)
    rw [mutatedRoot_p,map_neg,map_neg,realMutationCovector_at_p e S _ hS a] at H
    exact neg_pos.mp H
  have hb:0<b (e (simpleRoot C pc)):=by
    have H:=hB 1 (by omega) _ (simpleRoot_degree C' pc)
    rw [mutatedRoot_p,map_neg,map_neg,realMutationCovector_at_p e S _ hS b] at H
    exact neg_neg_iff_pos.mp H
  let T:=mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
  have hT:∀n,incomingCoefficient LaurentRay.vUnit Ω C' (n+1) T.val=
      literalIncomingLog Ω C' (simpleIncomingList C') (n+1):=by
    intro n
    apply Finsupp.ext
    intro m
    rw [incomingCoefficient_apply,literalIncomingLog_apply]
    by_cases hm:HasRootDegree C' (n+1) m
    · rw [ite_eq_left hm,ite_eq_left hm]
      change coeff (n+1) (FormalLog.log (chartZero LaurentRay.vUnit Ω C'
        (incomingCovector Ω m) T).val) m=_
      by_cases hp:OnPositiveRay m (simpleRoot C' pc)
      · exact mutatedIncoming_pure_root Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
          m (n+1) hp HA HB ha hb
      · exact mutatedIncoming_nonpure_root Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
          hC m (n+1) (by omega) hm hp HA HB hA hB
    · rw [ite_eq_right hm,ite_eq_right hm]
  exact (existsUnique_incoming LaurentRay.vUnit Ω C' hΩ
    (literalIncomingLog Ω C' (simpleIncomingList C'))
    (literalIncomingLog_graded Ω C' (simpleIncomingList C'))).unique hT
    (incomingSolution_prescription LaurentRay.vUnit Ω C' hΩ _
      (literalIncomingLog_graded Ω C' (simpleIncomingList C')))
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
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
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_14
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_17_r8ac191_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_17_r8ac191_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedTransport_canonical_finite
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) (N:ℕ)
    {x y:Module.Dual ℝ E} (HX:RegularCovector C e x) (HY:RegularCovector C e y)
    (hx:∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
    (hy:∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) y (e m)≠0) :
    ∀n≤N,coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HX HY).val=
      coeff n ((chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) y).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val *
        invOfUnit (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val 1) := by
  obtain ⟨a,b,HA,HB,hA,hB⟩:=mutated_regular_anchors Ω C pc e S hS hC
  have H:=mutatedTransport_negative_ratio Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    N HA HB HX HY (fun n _ m hm=>hA _ (by omega) m hm)
    (fun n _ m hm=>hB _ (by omega) m hm) hx hy
  rw [mutatedTransport_eq_simple Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd hC HA HB hA hB] at H
  exact H
include hnd in
lemma mutatedTransport_canonical_oai
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {x y:Module.Dual ℝ E} (HX:RegularCovector C e x) (HY:RegularCovector C e y)
    (hx:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
    (hy:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) y (e m)≠0) :
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HX HY).val=
      (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) y).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val *
        invOfUnit (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val 1 := by
  apply PowerSeries.ext
  intro n
  exact mutatedTransport_canonical_finite Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    hC n HX HY (fun j _ m hm=>hx _ (by omega) m hm)
    (fun j _ m hm=>hy _ (by omega) m hm) n le_rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical_oai.{u_1, u_2, u_3}
