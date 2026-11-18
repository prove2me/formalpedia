-- Prove2me | solution 1 for OAI.ElementaryPositivity.RationalFiber.actualPath_rational_loop_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:57:16.990789+00:00
-- url     : https://prove2.me/submissions/fd9ff28e-7148-4e98-bcef-58fe344ee194

import Mathlib
import Definitions.Def_OAIQ368Chrom008
import Definitions.Def_OAIQ368Chrom009
import Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_finite_refinement_import

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
local instance rationalThroughAddCommMonoid_rb82075_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rationalThroughAddGroup_rb82075_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance rationalThroughNonUnitalSemiring_rb82075_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance rationalThroughNonUnitalNonAssocSemiring_rb82075_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
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
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (δ k : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorus_8
local instance instAddCommMonoidTorus_5_rb82075_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_5_rb82075_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_8_rb82075_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_8_rb82075_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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
theorem actualPath_rational_loop_coefficient_oai {a : Module.Dual ℝ E}
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

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.RationalFiber.actualPath_rational_loop_coefficient_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.RationalFiber.actualPath_rational_loop_coefficient_oai.{u_1, u_2, u_3}
