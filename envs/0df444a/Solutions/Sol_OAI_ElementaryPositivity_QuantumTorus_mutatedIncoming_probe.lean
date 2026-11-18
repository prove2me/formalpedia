-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:02.884271+00:00
-- url     : https://prove2.me/submissions/1baaa76f-e039-419b-92ac-db1e8d8d3477

import Mathlib
import Definitions.Def_OAIQ368Chrom008
import Definitions.Def_OAIQ368Chrom009
import Definitions.Def_OAIQ368Chrom010
import Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_mutatedTransport_negative_ratio
import Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_actualInfinityPath_product_square
import Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_finite_refinement_import

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
local instance instAddCommMonoidTorus_1_r719cec_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_r719cec_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_r719cec_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance rationalLaurentFaithfulRing_r719cec_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rationalLaurentFaithfulNonUnitalSemiring_r719cec_1 : NonUnitalSemiring (Torus v Ω) :=
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
local instance rationalThroughAddCommMonoid_r719cec_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rationalThroughAddGroup_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance rationalThroughNonUnitalSemiring_r719cec_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance rationalThroughNonUnitalNonAssocSemiring_r719cec_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_4_r719cec_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_7_r719cec_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_7_r719cec_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance instAddCommMonoidTorus_5_r719cec_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_5_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_8_r719cec_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_8_r719cec_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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

local instance mutationRegradeCompatibilityRing_r719cec_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutationRegradeCompatibilityAddCommMonoid_r719cec_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance mutationRegradeCompatibilityAddGroup_r719cec_1 : AddGroup (Torus v Ω) :=
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_r719cec_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_r719cec_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

lemma cutSide_decision (pos : Bool) (h : M →+ ℝ) (p : M) (hs : cutSide pos h p) :
    h p≠0 ∧ decide (0<h p)=pos := by
  cases pos
  · change h p<0 at hs
    exact ⟨ne_of_lt hs,decide_eq_false (not_lt_of_ge (le_of_lt hs))⟩
  · change 0<h p at hs
    exact ⟨ne_of_gt hs,decide_eq_true hs⟩

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_5
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_8_r719cec_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_8_r719cec_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma mutatedLineFactor_nocut (pos : Bool) (a : ℝ)
    (hs : cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (noncutOldLineFactor Ω C e he L hdeg v k H a) := by
  classical
  obtain ⟨hp,hpos⟩:=cutSide_decision pos _ _ hs
  change (k+a • v) (e (simpleRoot C pc))≠0 at hp
  change decide (0<(k+a • v) (e (simpleRoot C pc)))=pos at hpos
  unfold mutatedLineFactor noncutOldLineFactor
  split
  · next ha=>simp only; rw [hpos]
  · next ha=>exact (mutationCompletion_one Ω hΩ C coord pc pos LaurentRay.vUnit).symm

include hΩ hcoord hS hcomp in
lemma noncutOldLineFactor_bound (pos : Bool) (a : ℝ)
    (hs : cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (noncutOldLineFactor Ω C e he L hdeg v k H a) := by
  classical
  unfold noncutOldLineFactor
  split
  · next ha=>
    let data:=lineRayData C e he L hdeg v k H a ha
    have hf:=simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg
      data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic pos hs
    have hb:=mutationCompletion_bound Ω hΩ C coord hcoord pc pos LaurentRay.vUnit _ hf
    change RegradeBound _ _ _ _ (orientPowerSeries (decide (v (e data.root)<0)) _)
    cases hb' : decide (v (e data.root)<0)
    · exact hb.invOfUnit LaurentRay.vUnit Ω _ _
    · exact hb
  · exact RegradeBound.one _ _ _ _

include hcoord hS hcomp in
lemma noncutOldLineFactor_comparison (pos : Bool) (a : ℝ)
    (hs : cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    noncutOldLineFactor Ω C e he L hdeg v k H a=
      (comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)).val.val := by
  classical
  have hp:=(cutSide_decision pos _ _ hs).1
  change (k+a • v) (e (simpleRoot C pc))≠0 at hp
  unfold noncutOldLineFactor actualLineLetter
  split
  · next ha=>
    simp only
    let data:=lineRayData C e he L hdeg v k H a ha
    cases hh : decide (v (e data.root)<0) <;>
      simp only [orientPowerSeries,orientedBounded,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
        comparisonOld,completedBiUnit_val]
    all_goals rfl
  · next ha=>simp only [comparisonOld]; rfl
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
local instance instAddGroupTorus_6_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance regradeLogNonUnitalSemiring_r719cec_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance regradeLogNonUnitalNonAssocSemiring_r719cec_1 : NonUnitalNonAssocSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeLogAddCommMonoid
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeLogAddGroup
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeLogAddCommGroup
local instance regradeLogSub_r719cec_1 : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
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
local instance instNonUnitalSemiringTorus_11_r719cec_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_11_r719cec_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance infinityLaurentFiniteAddCommMonoid_r719cec_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance infinityLaurentFiniteAddGroup_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance infinityLaurentFiniteNonUnitalSemiring_r719cec_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance infinityLaurentFiniteNonUnitalNonAssocSemiring_r719cec_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
local instance rootLaurentCompletionAddCommMonoid_r719cec_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rootLaurentCompletionAddGroup_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorusLaurentSeriesRat_r719cec_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRat_4_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorus_7_r719cec_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_7_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_r719cec_2 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_r719cec_2 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_1_r719cec_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance laurentCompletionFaithfulAddCommMonoid_r719cec_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentCompletionFaithfulAddGroup_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentCompletionFaithfulNonUnitalSemiring_r719cec_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_8_r719cec_2 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_8_r719cec_2 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_2_r719cec_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance mutatedPathIndependentAddCommMonoid_r719cec_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPathIndependentAddGroup_r719cec_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingTransportTrace
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma inverse_coeff_congr (F G : PowerSeries A) (hF : constantCoeff F=1)
    (hG : constantCoeff G=1) (N : ℕ) (H : ∀n≤N,coeff n F=coeff n G) :
    ∀n≤N,coeff n (invOfUnit F 1)=coeff n (invOfUnit G 1) := by
  intro n hn
  have HH:=mul_coeff_congr (invOfUnit F 1) (F*invOfUnit G 1)
    (invOfUnit F 1) (G*invOfUnit G 1) n (fun _ _=>rfl) (by
      intro j hj
      exact mul_coeff_congr _ _ _ _ j (fun k hk=>H k (hk.trans (hj.trans hn))) (fun _ _=>rfl))
  rw [←mul_assoc,invOfUnit_mul F 1 hF,one_mul,mul_invOfUnit G 1 hG,mul_one] at HH
  exact HH.symm
end
end ElementaryPositivity.FormalLog
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.incomingTransportTraceRing
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.incomingTransportTraceAddCommMonoid
local instance incomingTransportTraceAddGroup_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma chartNegative_log_positive (h : M →+ ℝ) (F : CompletedPositive v Ω C)
    (r : M) (hr : 0≤h r) (n : ℕ) :
    coeff n (FormalLog.log (chartNegative v Ω C h F).val) r=0 := by
  exact strict_log_support v Ω (V:=fun m=>h m<0)
    (fun a b ha hb=>by simpa only [map_add] using add_neg ha hb) _
    (chartNegative v Ω C h F).property.1
    (fun j m hm=>by by_contra hh; exact hm ((chart_three_support v Ω C h F).2.2 j m hh))
    n r (not_lt.mpr hr)

lemma chartNegative_log_negative_kernel (hΩ : ∀m,Ω m m=0) (r : M)
    (F : CompletedPositive v Ω C)
    (hf : ∀n,coeff n F.val∈supportedSubalgebra v Ω (kernelSupport Ω r))
    (h : M →+ ℝ) (hr : h r<0) (n : ℕ) :
    coeff n (FormalLog.log (chartNegative v Ω C h F).val) r=
      coeff n (FormalLog.log F.val) r := by
  let A:=chartPositive v Ω C h F
  let B:=chartZero v Ω C h F
  let D:=chartNegative v Ω C h F
  have hs:=chartThree_supported v Ω C h (kernelSupport Ω r) F hf
  have H1:=kernel_trace_log_product v Ω hΩ r A.val B.val A.property.1 B.property.1 hs.1 hs.2.1 n
  have H2:=kernel_trace_log_product v Ω hΩ r (A.val*B.val) D.val
    (by simp [A.property.1,B.property.1]) D.property.1
    (PowerSeriesSplit.mul_mem (supportedSubring v Ω (kernelSupport Ω r)) _ _ hs.1 hs.2.1) hs.2.2 n
  have hp : coeff n (FormalLog.log A.val) r=0:=by
    exact strict_log_support v Ω (V:=fun m=>0<h m)
      (fun a b ha hb=>by simpa only [map_add] using add_pos ha hb) A.val A.property.1
      (fun j m hm=>by by_contra hh; exact hm ((chart_three_support v Ω C h F).1 j m hh))
      n r (not_lt.mpr hr.le)
  have hz : coeff n (FormalLog.log B.val) r=0:=by
    exact strict_log_support v Ω (V:=fun m=>h m=0)
      (fun a b ha hb=>by rw [map_add,ha,hb,add_zero]) B.val B.property.1
      (fun j m hm=>by by_contra hh; exact hm ((chart_three_support v Ω C h F).2.1 j m hh))
      n r (ne_of_lt hr)
  rw [H1,hp,hz,zero_add,zero_add] at H2
  rw [show A.val*B.val*D.val=F.val from chart_three_factorization v Ω C h F] at H2
  exact H2.symm

lemma kernel_trace_log_inverse (hΩ : ∀m,Ω m m=0) (r : M)
    (F : PowerSeries (Torus v Ω)) (hf : constantCoeff F=1)
    (hs : ∀n,coeff n F∈supportedSubalgebra v Ω (kernelSupport Ω r)) (n : ℕ) :
    coeff n (FormalLog.log (invOfUnit F 1)) r= -coeff n (FormalLog.log F) r := by
  have hi : ∀j,coeff j (invOfUnit F 1)∈supportedSubalgebra v Ω (kernelSupport Ω r):=by
    intro j m hm
    by_contra hh
    exact hm (inverse_support_addSubmonoid v Ω (kernelSupport Ω r) F
      (fun k a ha=>by by_contra hn; exact ha (hs k a hn)) j m hh)
  have H:=kernel_trace_log_product v Ω hΩ r F (invOfUnit F 1) hf (by simp) hs hi n
  rw [mul_invOfUnit F 1 hf,FormalLog.log_one,map_zero,Finsupp.zero_apply] at H
  exact eq_neg_of_add_eq_zero_right H.symm

lemma incoming_negative_ratio_log (hΩ : ∀m,Ω m m=0) (r : M)
    (F : CompletedPositive v Ω C) (x y : M →+ ℝ) (N : ℕ)
    (hx : ∀n≤N,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<x m) ∧ (incomingCovector Ω r m<0 → x m<0))
    (hy : ∀n≤N,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<y m) ∧ (incomingCovector Ω r m<0 → y m<0))
    (hxr : 0≤x r) (hyr : y r<0) :
    ∀n≤N,coeff n (FormalLog.log ((chartNegative v Ω C y F).val*
        invOfUnit (chartNegative v Ω C x F).val 1)) r=
      coeff n (FormalLog.log (chartZero v Ω C (incomingCovector Ω r) F).val) r := by
  let B:=chartZero v Ω C (incomingCovector Ω r) F
  let D:=chartNegative v Ω C (incomingCovector Ω r) F
  let X:=chartNegative v Ω C x B
  let Y:=chartNegative v Ω C y B
  have Hx:=chart_negative_refinement v Ω C (incomingCovector Ω r) x x F N (by
    intro n hn m hm
    exact ⟨(hx n hn m hm).1,(hx n hn m hm).2,fun _=>⟨id,id,id⟩⟩)
  have Hy:=chart_negative_refinement v Ω C (incomingCovector Ω r) y y F N (by
    intro n hn m hm
    exact ⟨(hy n hn m hm).1,(hy n hn m hm).2,fun _=>⟨id,id,id⟩⟩)
  have hi:=FormalLog.inverse_coeff_congr _ _ (chartNegative v Ω C x F).property.1
    (by change constantCoeff (X.val*D.val)=1; simp [X.property.1,D.property.1]) N Hx
  have hinv : invOfUnit (X.val*D.val) 1=invOfUnit D.val 1*invOfUnit X.val 1:=by
    apply left_inv_eq_right_inv (PowerSeries.invOfUnit_mul _ 1 (by simp [X.property.1,D.property.1]))
    simp only [mul_assoc,←mul_assoc D.val,PowerSeries.mul_invOfUnit D.val 1 D.property.1,
      one_mul,PowerSeries.mul_invOfUnit X.val 1 X.property.1]
  have he : ∀n≤N,coeff n ((chartNegative v Ω C y F).val*invOfUnit (chartNegative v Ω C x F).val 1)=
      coeff n (Y.val*invOfUnit X.val 1):=by
    intro n hn
    have H:=FormalLog.mul_coeff_congr _ _ _ _ n
      (fun j hj=>Hy j (hj.trans hn)) (fun j hj=>hi j (hj.trans hn))
    rw [hinv,mul_assoc,←mul_assoc D.val,PowerSeries.mul_invOfUnit D.val 1 D.property.1,one_mul] at H
    exact H
  have hB:=incoming_chart_supported v Ω C r F
  have hsX:=(chartThree_supported v Ω C x (kernelSupport Ω r) B hB).2.2
  have hsY:=(chartThree_supported v Ω C y (kernelSupport Ω r) B hB).2.2
  have hsI : ∀j,coeff j (invOfUnit X.val 1)∈supportedSubalgebra v Ω (kernelSupport Ω r):=by
    intro j m hm
    by_contra hh
    exact hm (inverse_support_addSubmonoid v Ω _ X.val
      (fun k a ha=>by by_contra hn; exact ha (hsX k a hn)) j m hh)
  intro n hn
  rw [FormalLog.log_coeff_congr _ _ n (fun j hj=>he j (hj.trans hn)),
    kernel_trace_log_product v Ω hΩ r Y.val (invOfUnit X.val 1) Y.property.1 (by simp) hsY hsI n,
    kernel_trace_log_inverse v Ω hΩ r X.val X.property.1 hsX n,
    chartNegative_log_positive v Ω C x B r hxr n,neg_zero,add_zero]
  exact chartNegative_log_negative_kernel v Ω C hΩ r B hB y hyr n
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedNoCutTransport
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutatedNoCutTransportRing
local instance mutatedNoCutTransportAddCommMonoid_r719cec_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedNoCutTransportAddGroup_r719cec_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma mutatedLineProduct_nocut_eq (pos : Bool) (lo hi : ℝ) (N : ℕ)
    (hs : ∀a∈intervalEventList C e v k lo hi N,
      cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
          (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
          (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
          (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N)).val.val := by
  classical
  let U:=fun a=>comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
    (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
    (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
    (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)
  have HH : ∀l : List ℝ, (∀a∈l,cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) →
      RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
        (l.map U).prod.val.val ∧
      (l.map (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H)).prod=
        mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (l.map U).prod.val.val := by
    intro l
    induction l with
    | nil=>
      intro _
      exact ⟨RegradeBound.one _ _ _ _,(mutationCompletion_one Ω hΩ C coord pc pos LaurentRay.vUnit).symm⟩
    | cons a l ih=>
      intro hl
      obtain ⟨ht,ih⟩:=ih (fun b hb=>hl b (List.mem_cons_of_mem a hb))
      have ha:=hl a (by simp)
      have heq : noncutOldLineFactor Ω C e he L hdeg v k H a=(U a).val.val:=
        noncutOldLineFactor_comparison Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos a ha
      have hb : RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos)
          (mutationSize Ω C pc+1) (U a).val.val:=by
        rw [←heq]
        exact noncutOldLineFactor_bound Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos a ha
      have hf:=mutatedLineFactor_nocut Ω hΩ C coord pc e he L hdeg v k H pos a ha
      rw [heq] at hf
      change RegradeBound _ _ _ _ ((U a).val.val*(l.map U).prod.val.val) ∧
        mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a*
          (l.map (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H)).prod=_
      refine ⟨hb.mul _ _ _ _ ht,?_⟩
      rw [hf,ih,←mutationCompletion_mul Ω hΩ C coord pc pos LaurentRay.vUnit hb ht]
      rfl
  simpa only [mutatedLineProduct,comparisonWordOld,actualLineWord,List.map_map,Function.comp_def]
    using (HH (intervalEventList C e v k lo hi N) hs).2

include hS hcomp in
lemma mutatedLineCompletion_nocut (pos : Bool) (lo hi : ℝ) (horder : lo<hi)
    (hlo : ∀N,lo∉lineEvents (realRootsThrough e C N) v k)
    (hhi : ∀N,hi∉lineEvents (realRootsThrough e C N) v k)
    (hs : ∀a,lo<a → a<hi → cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (lineNegativeUnit Ω C coord hcoord pc e v k hi*
          (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹).val.val := by
  classical
  apply PowerSeries.ext
  intro d
  let N:=max 1 ((mutationSize Ω C pc+1)*d)
  have hN : 1≤N:=le_max_left _ _
  have hdN : (mutationSize Ω C pc+1)*d≤N:=le_max_right _ _
  rw [mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg v k H lo hi d N hN hdN]
  have hsN : ∀a∈intervalEventList C e v k lo hi N,
      cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc):=by
    intro a ha
    have haF:=Finset.mem_sort (· ≥ ·) |>.mp ha
    have hab:=(Finset.mem_filter.mp haF).2
    exact hs a hab.1 hab.2
  rw [mutatedLineProduct_nocut_eq Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos lo hi N hsN]
  apply mutationCompletion_congr_through Ω hΩ C coord pc pos LaurentRay.vUnit _ _ d N hdN
  have ht:=actualLine_old_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N
    (hlo N) (hhi N) horder
  have HH:=oldCoefficientsEqual_mul Ω coord pc N _ _
    (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹
    (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹ ht (fun _ _=>rfl)
  simpa only [mul_assoc,mul_inv_cancel,mul_one,oldCoefficientsEqual] using HH
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutatedNoCutTransportPathRing
local instance mutatedNoCutTransportPathAddCommMonoid_r719cec_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedNoCutTransportPathAddGroup_r719cec_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma noncutComparisonWord_bound (pos : Bool) (lo hi : ℝ) (N : ℕ)
    (hs : ∀a∈intervalEventList C e v k lo hi N,
      cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N)).val.val := by
  let U:=fun a=>comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
    (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
    (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
    (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)
  have HH : ∀l : List ℝ, (∀a∈l,cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) →
      RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
        (l.map U).prod.val.val := by
    intro l
    induction l with
    | nil=>intro _; exact RegradeBound.one _ _ _ _
    | cons a l ih=>
      intro hl
      have ha:=hl a (by simp)
      have hb:=noncutOldLineFactor_bound Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos a ha
      rw [noncutOldLineFactor_comparison Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos a ha] at hb
      exact hb.mul _ _ _ _ (ih (fun b hh=>hl b (List.mem_cons_of_mem a hh)))
  simpa only [comparisonWordOld,actualLineWord,List.map_map,Function.comp_def] using
    HH (intervalEventList C e v k lo hi N) hs

include hΩ he hS hcomp hdeg H in
lemma noncutEndpointRatio_bound (pos : Bool) (lo hi : ℝ) (ho : lo<hi)
    (ha : ∀N,lo∉lineEvents (realRootsThrough e C N) v k)
    (hb : ∀N,hi∉lineEvents (realRootsThrough e C N) v k)
    (hs : ∀a,lo<a → a<hi → cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (lineNegativeUnit Ω C coord hcoord pc e v k hi*
        (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹).val.val := by
  intro n m hm
  have hsN : ∀a∈intervalEventList C e v k lo hi n,
      cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc):=by
    intro a hh
    have hhF:=Finset.mem_sort (· ≥ ·) |>.mp hh
    have hab:=(Finset.mem_filter.mp hhF).2
    exact hs a hab.1 hab.2
  have hbnd:=noncutComparisonWord_bound Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H pos lo hi n hsN
  have ht:=actualLine_old_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi n
    (ha n) (hb n) ho
  have HH:=oldCoefficientsEqual_mul Ω coord pc n _ _
    (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹
    (lineNegativeUnit Ω C coord hcoord pc e v k lo)⁻¹ ht (fun _ _=>rfl)
  simp only [mul_assoc,mul_inv_cancel,mul_one] at HH
  apply hbnd n m
  rw [HH n le_rfl]
  exact hm

include hS hcomp in
lemma mutatedPathCompletion_nocut {a b : Module.Dual ℝ E} (pos : Bool) (p : GenericLinePath C e a b)
    (hs : p.OnCutSide C pc e pos) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (negativeCovectorUnit Ω C coord hcoord pc e b*(negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹).val.val ∧
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (negativeCovectorUnit Ω C coord hcoord pc e b*(negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹).val.val := by
  induction p with
  | nil=>
    simp only [mul_inv_cancel]
    exact ⟨RegradeBound.one _ _ _ _,(mutationCompletion_one Ω hΩ C coord pc pos LaurentRay.vUnit).symm⟩
  | append s p ih=>
    obtain ⟨hs,ht⟩:=hs
    obtain ⟨hp,ih⟩:=ih ht
    have hb:=noncutEndpointRatio_bound Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic pos s.lo s.hi s.ordered s.start_regular s.finish_regular hs
    have heq:=mutatedLineCompletion_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic pos s.lo s.hi s.ordered s.start_regular s.finish_regular hs
    change RegradeBound _ _ _ _
      (negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e))⁻¹).val.val at hb
    change mutatedLineCompletion Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
          (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e))⁻¹).val.val at heq
    have htel : (negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e))⁻¹)*
      (negativeCovectorUnit Ω C coord hcoord pc e (s.start C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹)=
      negativeCovectorUnit Ω C coord hcoord pc e (s.finish C e)*
        (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹ := by simp only [mul_assoc,inv_mul_cancel_left]
    refine ⟨?_,?_⟩
    · simpa only [←Units.val_mul,←Subring.coe_mul,htel] using hb.mul _ _ _ _ hp
    · change mutatedLineCompletion Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi*
        mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p=_
      rw [heq,ih,←mutationCompletion_mul Ω hΩ C coord pc pos LaurentRay.vUnit hb hp]
      exact congrArg (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit)
        (congrArg (fun u=>u.val.val) htel)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedHalfspaceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
section Algebra
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (pc : I) (e : M →+ E)
omit [Fintype I] in
lemma cutSide_affineSegment (pos : Bool) (a b : Module.Dual ℝ E)
    (ha : cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb : cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc))
    (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    cutSide pos ((a+t • (b-a)).toAddMonoidHom.comp e) (simpleRoot C pc) := by
  cases pos
  · change a (e (simpleRoot C pc))<0 at ha
    change b (e (simpleRoot C pc))<0 at hb
    change (a+t • (b-a)) (e (simpleRoot C pc))<0
    simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul]
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht1) ha,mul_neg_of_pos_of_neg ht hb]
  · change 0<a (e (simpleRoot C pc)) at ha
    change 0<b (e (simpleRoot C pc)) at hb
    change 0<(a+t • (b-a)) (e (simpleRoot C pc))
    simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,smul_eq_mul]
    nlinarith [mul_pos (sub_pos.mpr ht1) ha,mul_pos ht hb]

lemma GenericLinePath.OnCutSide.trans {a b c : Module.Dual ℝ E} (pos : Bool)
    (p : GenericLinePath C e a b) (q : GenericLinePath C e b c)
    (hp : p.OnCutSide C pc e pos) (hq : q.OnCutSide C pc e pos) :
    (p.trans C e q).OnCutSide C pc e pos := by
  induction q with
  | nil=>exact hp
  | append s q ih=>exact ⟨hq.1,ih hq.2⟩

lemma GenericLinePath.OnCutSide.reindex {a b a' b' : Module.Dual ℝ E} (pos : Bool)
    (p : GenericLinePath C e a b) (hp : p.OnCutSide C pc e pos) (ha : a=a') (hb : b=b') :
    ∃q : GenericLinePath C e a' b',q.OnCutSide C pc e pos := by
  cases ha
  cases hb
  exact ⟨p,hp⟩

lemma segmentBetween_onCutSide (pos : Bool) (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 (b-a) a)
    (ha : cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb : cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    (GenericLinePath.single C e (segmentBetween C e a b HA HB H)).OnCutSide C pc e pos := by
  refine ⟨?_,trivial⟩
  intro t ht ht1
  exact cutSide_affineSegment C pc e pos a b ha hb t ht ht1
end Algebra
section Existence
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (pc : I) (e : M →+ E)
theorem generic_path_exists_onCutSide (pos : Bool) (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (ha : cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb : cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∃p : GenericLinePath C e a b,p.OnCutSide C pc e pos := by
  classical
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions (realRootsThrough e C) a b a {e (simpleRoot C pc)}
  have HH : RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  have hs : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc):=by
    have ht:=HP (e (simpleRoot C pc)) (Finset.mem_singleton_self _)
    cases pos
    · exact ht.2 ha
    · exact ht.1 ha
  have hx : ∃p : GenericLinePath C e a h,p.OnCutSide C pc e pos := by
    let s:=segmentBetween C e a h HA HH (fun N=>(Ha N).join (HA N))
    have hh:=segmentBetween_onCutSide C pc e pos a h HA HH (fun N=>(Ha N).join (HA N)) ha hs
    have hp : ∃p : GenericLinePath C e (s.start C e) (s.finish C e),p.OnCutSide C pc e pos:=
      ⟨GenericLinePath.single C e s,hh⟩
    obtain ⟨p,hp⟩:=hp
    exact GenericLinePath.OnCutSide.reindex C pc e pos p hp
      (segmentBetween_start C e _ _ _ _ _) (segmentBetween_finish C e _ _ _ _ _)
  have hy : ∃p : GenericLinePath C e h b,p.OnCutSide C pc e pos := by
    let s:=segmentBetween C e h b HH HB (fun N=>(Hb N).join_reverse (HB N))
    have hh:=segmentBetween_onCutSide C pc e pos h b HH HB (fun N=>(Hb N).join_reverse (HB N)) hs hb
    have hp : ∃p : GenericLinePath C e (s.start C e) (s.finish C e),p.OnCutSide C pc e pos:=
      ⟨GenericLinePath.single C e s,hh⟩
    obtain ⟨p,hp⟩:=hp
    exact GenericLinePath.OnCutSide.reindex C pc e pos p hp
      (segmentBetween_start C e _ _ _ _ _) (segmentBetween_finish C e _ _ _ _ _)
  obtain ⟨p,hp⟩:=hx
  obtain ⟨q,hq⟩:=hy
  exact ⟨p.trans C e q,GenericLinePath.OnCutSide.trans C pc e pos p q hp hq⟩
end Existence
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutatedNegativeCharts
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
include hnd in
lemma mutatedTransport_nocut (pos : Bool) {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (ha : cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb : cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (negativeCovectorUnit Ω C coord hcoord pc e b*
        (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹).val.val ∧
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (negativeCovectorUnit Ω C coord hcoord pc e b*
          (negativeCovectorUnit Ω C coord hcoord pc e a)⁻¹).val.val := by
  obtain ⟨p,hp⟩:=generic_path_exists_onCutSide C pc e pos a b HA HB ha hb
  obtain ⟨hbound,heq⟩:=mutatedPathCompletion_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg pos p hp
  exact ⟨hbound,(mutatedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB p).trans heq⟩
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
local instance instAddCommMonoidTorus_7_r719cec_2 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_9_r719cec_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_10
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_13_r719cec_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_13_r719cec_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedIncoming_probe_oai (pos : Bool) (d N : ℕ) (hdN : d≤N) (r : M)
    {a b x y : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (HX : RegularCovector C e x) (HY : RegularCovector C e y)
    (hA : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      0 < realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0)
    (hx : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
    (hy : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) y (e m)≠0)
    (hsx : cutSide pos (x.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hsy : cutSide pos (y.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hxo : ∀n≤(mutationSize Ω C pc+1)*d,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<x (e m)) ∧ (incomingCovector Ω r m<0 → x (e m)<0))
    (hyo : ∀n≤(mutationSize Ω C pc+1)*d,∀m,HasRootDegree C n m →
      (0 < incomingCovector Ω r m → 0<y (e m)) ∧ (incomingCovector Ω r m<0 → y (e m)<0))
    (hxn : ∀n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      (0 < incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m →
        0 < realMutationCovector e S (simpleRoot C pc) x (e m)) ∧
      (incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m<0 →
        realMutationCovector e S (simpleRoot C pc) x (e m)<0))
    (hyn : ∀n≤N,∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      (0 < incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m →
        0 < realMutationCovector e S (simpleRoot C pc) y (e m)) ∧
      (incomingCovector Ω (mutationLinearPiece Ω C pc pos r) m<0 →
        realMutationCovector e S (simpleRoot C pc) y (e m)<0))
    (hxr : 0≤x (e r)) (hyr : y (e r)<0) :
    coeff d (FormalLog.log (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (incomingCovector Ω (mutationLinearPiece Ω C pc pos r))
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val)
        (mutationLinearPiece Ω C pc pos r)=
      if d=(mutationNewOrder Ω C coord pc pos r).toNat then
        ∑n∈Finset.range ((mutationSize Ω C pc+1)*d+1),
          coeff n (FormalLog.log (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω r)
            (simpleTotalTransport Ω C)).val) r else 0 := by
  let xp:=(realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e
  let yp:=(realMutationCovector e S (simpleRoot C pc) y).toAddMonoidHom.comp e
  let T:=mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
  let F:=(negativeCovectorUnit Ω C coord hcoord pc e y*
    (negativeCovectorUnit Ω C coord hcoord pc e x)⁻¹).val.val
  have hxp : xp (mutationLinearPiece Ω C pc pos r)=x (e r):=by
    change realMutationCovector e S (simpleRoot C pc) x (e (mutationLinearPiece Ω C pc pos r))=_
    rw [realMutationCovector_eq_side e S _ pos x (by cases pos <;> exact le_of_lt hsx)]
    cases pos
    · exact realShearCovector_incidence Ω e S (simpleRoot C pc) hS hcomp x r
    · rfl
  have hyp : yp (mutationLinearPiece Ω C pc pos r)=y (e r):=by
    change realMutationCovector e S (simpleRoot C pc) y (e (mutationLinearPiece Ω C pc pos r))=_
    rw [realMutationCovector_eq_side e S _ pos y (by cases pos <;> exact le_of_lt hsy)]
    cases pos
    · exact realShearCovector_incidence Ω e S (simpleRoot C pc) hS hcomp y r
    · rfl
  have Hn:=incoming_negative_ratio_log LaurentRay.vUnit Ω (mutatedRoots Ω C pc) hΩ
    (mutationLinearPiece Ω C pc pos r) T xp yp N hxn hyn (hxp ▸ hxr) (hyp ▸ hyr) d hdN
  have Hratio:=mutatedTransport_negative_ratio Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    N HA HB HX HY hA hB hx hy
  have Hlog:=congrArg (fun f:Torus LaurentRay.vUnit Ω=>f (mutationLinearPiece Ω C pc pos r))
    (FormalLog.log_coeff_congr _ _ d (fun j hj=>Hratio j (hj.trans hdN)))
  have Hcut:=mutatedTransport_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd pos HX HY hsx hsy
  have hc : constantCoeff F=1:=by
    change constantCoeff ((chartNegative LaurentRay.vUnit Ω C (y.toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val * invOfUnit (chartNegative LaurentRay.vUnit Ω C
          (x.toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val 1)=1
    simp only [map_mul,(chartNegative LaurentRay.vUnit Ω C _ (simpleTotalTransport Ω C)).property.1,
      constantCoeff_invOfUnit,inv_one,Units.val_one,one_mul]
  have Ho:=incoming_negative_ratio_log LaurentRay.vUnit Ω C hΩ r (simpleTotalTransport Ω C)
    (x.toAddMonoidHom.comp e) (y.toAddMonoidHom.comp e) ((mutationSize Ω C pc+1)*d) hxo hyo hxr hyr
  rw [←Hn,←Hlog,Hcut.2,mutationCompletion_log_read Ω hΩ C coord pc pos LaurentRay.vUnit F Hcut.1 hc]
  split_ifs
  · apply Finset.sum_congr rfl
    intro j hj
    exact Ho j (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj)
  · rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe_oai.{u_1, u_2, u_3}
