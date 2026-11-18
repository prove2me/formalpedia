-- Prove2me | solution 1 for OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_negative_ratio
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T18:57:14.955804+00:00
-- url     : https://prove2.me/submissions/7d9a750f-2a60-4a08-ac2c-1485fc6b737f

import Mathlib
import Definitions.Def_OAIQ368Chrom008
import Definitions.Def_OAIQ368Chrom011
import Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_actualInfinityPath_loop_commute

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

lemma mutated_pos_of_nonneg (h : Module.Dual ℝ E) (x : E) (hc : 0≤S (e p) x) :
    0 < realMutationCovector e S p h x ↔ 0<h x ∧ 0<h (realShearVector e S p x) := by
  have heq:=realShearCovector_eval e S p h x
  have hw : h (realShearVector e S p x)=h x+h (e p)*S (e p) x := by
    rw [←heq]; rfl
  rw [realMutationCovector]
  split_ifs with hp
  · rw [hw]
    exact ⟨fun hh=>⟨hh,lt_of_lt_of_le hh (le_add_of_nonneg_right (mul_nonneg hp hc))⟩,And.left⟩
  · rw [heq,hw]
    have hm : h (e p)*S (e p) x≤0:=mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hp)) hc
    exact ⟨fun hh=>⟨by linarith,hh⟩,And.right⟩

lemma mutated_pos_of_nonpos (h : Module.Dual ℝ E) (x : E) (hc : S (e p) x≤0) :
    0 < realMutationCovector e S p h x ↔ 0<h x ∨ 0<h (realShearVector e S p x) := by
  have heq:=realShearCovector_eval e S p h x
  have hw : h (realShearVector e S p x)=h x+h (e p)*S (e p) x := by
    rw [←heq]; rfl
  rw [realMutationCovector]
  split_ifs with hp
  · rw [hw]
    have hm : h (e p)*S (e p) x≤0:=mul_nonpos_of_nonneg_of_nonpos hp hc
    constructor
    · exact Or.inl
    · rintro (hh|hh) <;> linarith
  · rw [heq,hw]
    have hm : 0≤h (e p)*S (e p) x:=mul_nonneg_of_nonpos_of_nonpos (le_of_lt (lt_of_not_ge hp)) hc
    constructor
    · exact Or.inr
    · rintro (hh|hh) <;> linarith

lemma real_convex_pos (a b t : ℝ) (ha : 0<a) (hb : 0<b) (ht : 0≤t) (ht1 : t≤1) :
    0<(1-t)*a+t*b := by
  have h0:=mul_nonneg (sub_nonneg.mpr ht1) ha.le
  have h1:=mul_nonneg ht hb.le
  by_cases hz : t=0
  · subst t; simpa using ha
  · have hh:=mul_pos (lt_of_le_of_ne ht (Ne.symm hz)) hb
    linarith

lemma mutation_segment_with_both (a h : Module.Dual ℝ E) (x : E)
    (ha : 0 < realMutationCovector e S p a x)
    (hh : 0<h x ∧ 0<h (realShearVector e S p x))
    (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    0 < realMutationCovector e S p ((1-t) • a+t • h) x := by
  have hp (y : E) (hay : 0<a y) (hhy : 0<h y) :
      0<((1-t) • a+t • h) y := by
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
    exact real_convex_pos _ _ _ hay hhy ht ht1
  by_cases hc : 0≤S (e p) x
  · have HA:=(mutated_pos_of_nonneg e S p a x hc).mp ha
    exact (mutated_pos_of_nonneg e S p _ x hc).mpr ⟨hp x HA.1 hh.1,hp _ HA.2 hh.2⟩
  · have hc':=le_of_lt (lt_of_not_ge hc)
    apply (mutated_pos_of_nonpos e S p _ x hc').mpr
    rcases (mutated_pos_of_nonpos e S p a x hc').mp ha with HA|HA
    · exact Or.inl (hp x HA hh.1)
    · exact Or.inr (hp _ HA hh.2)

lemma mutation_segment_same_side (a b : Module.Dual ℝ E) (x : E)
    (ha : 0 < realMutationCovector e S p a x) (hb : 0 < realMutationCovector e S p b x)
    (hs : (0≤a (e p) ∧ 0≤b (e p)) ∨ (a (e p)≤0 ∧ b (e p)≤0))
    (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    0 < realMutationCovector e S p ((1-t) • a+t • b) x := by
  have heval (y : E) : ((1-t) • a+t • b) y=(1-t)*a y+t*b y := rfl
  have hpos (h : Module.Dual ℝ E) (hh : 0≤h (e p)) : realMutationCovector e S p h=h := ite_eq_left hh
  have hneg (h : Module.Dual ℝ E) (hh : h (e p)≤0) :
      realMutationCovector e S p h=realShearCovector e S p h := by
    by_cases hz : h (e p)=0
    · rw [realMutationCovector,ite_eq_left (by rw [hz]),realShearCovector,hz,zero_smul,add_zero]
    · exact ite_eq_right (by intro hh'; exact hz (le_antisymm hh hh'))
  rcases hs with hs|hs
  · have hv : 0≤((1-t) • a+t • b) (e p):=by
      rw [heval]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hs.1) (mul_nonneg ht hs.2)
    rw [hpos _ hv,heval]
    rw [hpos _ hs.1] at ha
    rw [hpos _ hs.2] at hb
    exact real_convex_pos _ _ _ ha hb ht ht1
  · have hv : ((1-t) • a+t • b) (e p)≤0:=by
      rw [heval]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hs.1)
        (mul_nonpos_of_nonneg_of_nonpos ht hs.2)
    rw [hneg _ hv,realShearCovector_eval,heval]
    rw [hneg _ hs.1,realShearCovector_eval] at ha
    rw [hneg _ hs.2,realShearCovector_eval] at hb
    exact real_convex_pos _ _ _ ha hb ht ht1
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
local instance instAddCommMonoidTorus_1_rf09d92_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_rf09d92_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_rf09d92_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_rf09d92_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
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

local instance mutationRegradeCompatibilityRing_rf09d92_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutationRegradeCompatibilityAddCommMonoid_rf09d92_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance mutationRegradeCompatibilityAddGroup_rf09d92_1 : AddGroup (Torus v Ω) :=
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_rf09d92_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_rf09d92_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance instAddGroupTorus_6_rf09d92_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorus_5_rf09d92_1 : AddCommMonoid (Torus u Ω) := (Torus.instRing u Ω).toAddCommMonoid
local instance instAddGroupTorus_7_rf09d92_1 : AddGroup (Torus u Ω) := (Torus.instRing u Ω).toAddGroup
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_9_rf09d92_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_9_rf09d92_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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
local instance rootLaurentCompletionAddCommMonoid_rf09d92_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rootLaurentCompletionAddGroup_rf09d92_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorusLaurentSeriesRat_rf09d92_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRat_4_rf09d92_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_rf09d92_2 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_rf09d92_2 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_1_rf09d92_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorusLaurentSeriesRatVUnit_1
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
local instance laurentCompletionFaithfulAddCommMonoid_rf09d92_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentCompletionFaithfulAddGroup_rf09d92_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentCompletionFaithfulNonUnitalSemiring_rf09d92_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
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
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_8_rf09d92_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_8_rf09d92_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_2_rf09d92_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
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
local instance mutatedPathIndependentAddCommMonoid_rf09d92_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPathIndependentAddGroup_rf09d92_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
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

include hnd in
lemma mutatedTransport_trans {a b c : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) (HC : RegularCovector C e c) :
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HC).val=
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HB HC).val*
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val := by
  let p:=Classical.choice (generic_path_exists C e a b HA HB)
  let q:=Classical.choice (generic_path_exists C e b c HB HC)
  rw [mutatedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HC (p.trans C e q)]
  exact mutatedPathCompletion_trans Ω hΩ C coord pc e he L hdeg p q
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

noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
lemma generic_region_path_via (a b k : Module.Dual ℝ E) (P : Finset E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (U : Set (Module.Dual ℝ E))
    (hU : ∀h : Module.Dual ℝ E,
      (∀x∈P,(0<k x → 0<h x) ∧ (k x<0 → h x<0)) →
      (∀t:ℝ,0≤t → t≤1 → (1-t) • a+t • h∈U) ∧
      (∀t:ℝ,0≤t → t≤1 → (1-t) • h+t • b∈U)) :
    ∃p : GenericLinePath C e a b,p.InRegion C e U := by
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions (realRootsThrough e C) a b k P
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
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationChamberPaths
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
  [FiniteDimensional ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M) (hS : ∀x,S x x=0)

include hS in
omit [FiniteDimensional ℝ E] in
lemma cut_positive_intermediate (P : Finset E) (a b : Module.Dual ℝ E)
    (ha : a∈mutationSignRegion e S p P) (hb : b∈mutationSignRegion e S p P)
    (hap : a (e p)<0) (hbp : 0<b (e p)) :
    ∃k : Module.Dual ℝ E,k (e p)=0 ∧
      ∀x∈P,0<k x ∧ 0<k (realShearVector e S p x) := by
  let t:=-a (e p)/(b (e p)-a (e p))
  have hden : 0<b (e p)-a (e p):=by linarith
  have ht : 0<t:=div_pos (neg_pos.mpr hap) hden
  have ht1 : t<1:=by change -a (e p)/(b (e p)-a (e p))<1; rw [div_lt_one hden]; linarith
  let k:=(1-t) • realMutationCovector e S p a+t • realMutationCovector e S p b
  have hk : k (e p)=0:=by
    simp only [k,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
      realMutationCovector_at_p e S p hS]
    dsimp [t]
    field_simp
    ring
  refine ⟨k,hk,?_⟩
  intro x hx
  have hkp : 0<k x:=by
    change 0<(1-t)*realMutationCovector e S p a x+t*realMutationCovector e S p b x
    exact real_convex_pos _ _ _ (ha x hx) (hb x hx) ht.le ht1.le
  refine ⟨hkp,?_⟩
  simpa only [realShearVector,map_add,map_smul,hk,smul_zero,add_zero] using hkp

include hS in
lemma generic_mutation_region_path (P : Finset E) (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (ha : a∈mutationSignRegion e S p P) (hb : b∈mutationSignRegion e S p P)
    (hap : a (e p)≠0) (hbp : b (e p)≠0) :
    ∃q : GenericLinePath C e a b,q.InRegion C e (mutationSignRegion e S p P) := by
  classical
  have hpositive (g : Module.Dual ℝ E) (hg : 0<g (e p)) :
      realMutationCovector e S p g=g:=ite_eq_left hg.le
  have hnegative (g : Module.Dual ℝ E) (hg : g (e p)<0) :
      realMutationCovector e S p g=realShearCovector e S p g:=ite_eq_right (not_le.mpr hg)
  by_cases hpa : 0<a (e p)
  · by_cases hpb : 0<b (e p)
    · apply generic_region_path_via C e a b a (insert (e p) P) HA HB
      intro h Hh
      have hhp : 0<h (e p):=(Hh _ (Finset.mem_insert_self _ _)).1 hpa
      have hhr : h∈mutationSignRegion e S p P:=by
        intro x hx
        rw [hpositive h hhp]
        apply (Hh x (Finset.mem_insert_of_mem hx)).1
        simpa only [hpositive a hpa] using ha x hx
      constructor
      · intro t ht ht1 x hx
        exact mutation_segment_same_side e S p a h x (ha x hx) (hhr x hx)
          (Or.inl ⟨hpa.le,hhp.le⟩) t ht ht1
      · intro t ht ht1 x hx
        exact mutation_segment_same_side e S p h b x (hhr x hx) (hb x hx)
          (Or.inl ⟨hhp.le,hpb.le⟩) t ht ht1
    · have hpb' : b (e p)<0:=lt_of_le_of_ne (le_of_not_gt hpb) hbp
      obtain ⟨k,_,Hk⟩:=cut_positive_intermediate e S p hS P b a hb ha hpb' hpa
      apply generic_region_path_via C e a b k (P∪P.image (realShearVector e S p)) HA HB
      intro h Hh
      have hh (x : E) (hx : x∈P) : 0<h x ∧ 0<h (realShearVector e S p x):=
        ⟨(Hh x (Finset.mem_union_left _ hx)).1 (Hk x hx).1,
          (Hh _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))).1 (Hk x hx).2⟩
      constructor
      · intro t ht ht1 x hx
        exact mutation_segment_with_both e S p a h x (ha x hx) (hh x hx) t ht ht1
      · intro t ht ht1 x hx
        have H:=mutation_segment_with_both e S p b h x (hb x hx) (hh x hx) (1-t)
          (sub_nonneg.mpr ht1) (by linarith)
        have heq : (1-(1-t)) • b+(1-t) • h=(1-t) • h+t • b:=by module
        rwa [heq] at H
  · have hpa' : a (e p)<0:=lt_of_le_of_ne (le_of_not_gt hpa) hap
    by_cases hpb : 0<b (e p)
    · obtain ⟨k,_,Hk⟩:=cut_positive_intermediate e S p hS P a b ha hb hpa' hpb
      apply generic_region_path_via C e a b k (P∪P.image (realShearVector e S p)) HA HB
      intro h Hh
      have hh (x : E) (hx : x∈P) : 0<h x ∧ 0<h (realShearVector e S p x):=
        ⟨(Hh x (Finset.mem_union_left _ hx)).1 (Hk x hx).1,
          (Hh _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))).1 (Hk x hx).2⟩
      constructor
      · intro t ht ht1 x hx
        exact mutation_segment_with_both e S p a h x (ha x hx) (hh x hx) t ht ht1
      · intro t ht ht1 x hx
        have H:=mutation_segment_with_both e S p b h x (hb x hx) (hh x hx) (1-t)
          (sub_nonneg.mpr ht1) (by linarith)
        have heq : (1-(1-t)) • b+(1-t) • h=(1-t) • h+t • b:=by module
        rwa [heq] at H
    · have hpb' : b (e p)<0:=lt_of_le_of_ne (le_of_not_gt hpb) hbp
      apply generic_region_path_via C e a b a (insert (e p) (P.image (realShearVector e S p))) HA HB
      intro h Hh
      have hhp : h (e p)<0:=(Hh _ (Finset.mem_insert_self _ _)).2 hpa'
      have hhr : h∈mutationSignRegion e S p P:=by
        intro x hx
        rw [hnegative h hhp,realShearCovector_eval]
        apply (Hh _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x,hx,rfl⟩))).1
        simpa only [hnegative a hpa',realShearCovector_eval] using ha x hx
      constructor
      · intro t ht ht1 x hx
        exact mutation_segment_same_side e S p a h x (ha x hx) (hhr x hx)
          (Or.inr ⟨hpa'.le,hhp.le⟩) t ht ht1
      · intro t ht ht1 x hx
        exact mutation_segment_same_side e S p h b x (hhr x hx) (hb x hx)
          (Or.inr ⟨hhp.le,hpb'.le⟩) t ht ht1
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.mutationChamberPathsRing
local instance mutationChamberPathsAddCommMonoid_rf09d92_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutationChamberPathsAddGroup_rf09d92_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hcoord hS hcomp in
omit [FiniteDimensional ℝ E] in
lemma mutatedLineFactor_protected (P : Finset E) (V : M → Prop) (D : ℕ)
    (hP : ∀n,n+1≤D → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      ¬V m → e m∈P ∨ -(e m)∈P)
    (v k : Module.Dual ℝ E) (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : k+a • v∈mutationSignRegion e S (simpleRoot C pc) P) :
    ∀n,n+1≤D → SupportedOn LaurentRay.vUnit Ω V
      (coeff (n+1) (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a)) := by
  intro n hn m hm
  by_contra hh
  have hd : HasRootDegree (mutatedRoots Ω C pc) (n+1) m:=by
    by_contra hr
    exact hh (mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a
      (n+1) m hr)
  have hk:=mutatedLineFactor_kernel Ω hΩ C coord pc e he S hS hcomp L hdeg v k H a (n+1) m hh
  rcases hP n hn m hd hm with hp|hp
  · have Hpos:=ha (e m) hp
    linarith
  · have Hpos:=ha (-e m) hp
    rw [map_neg,hk,neg_zero] at Hpos
    exact (lt_irrefl 0) Hpos

include hcoord hS hcomp in
omit [FiniteDimensional ℝ E] in
lemma mutatedLineProduct_protected (P : Finset E) (V : M → Prop)
    (hV : ∀a b,V a → V b → V (a+b)) (D : ℕ)
    (hP : ∀n,n+1≤D → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      ¬V m → e m∈P ∨ -(e m)∈P)
    (v k : Module.Dual ℝ E) (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
    (lo hi : ℝ) (N : ℕ)
    (hregion : ∀a,lo≤a → a≤hi → k+a • v∈mutationSignRegion e S (simpleRoot C pc) P) :
    ∀n,n+1≤D → SupportedOn LaurentRay.vUnit Ω V
      (coeff (n+1) (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N)) := by
  let F (a : ℝ) : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc):=
    ⟨mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a,
      mutatedLineFactor_constant Ω hΩ C coord pc e he L hdeg v k H a,
      mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a⟩
  apply strict_list_product_through LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
    (intervalEventList C e v k lo hi N) F V hV D
  intro a ha
  have haF : a∈intervalLineEvents C e v k lo hi N:=Finset.mem_sort _ |>.mp ha
  have hab:=(Finset.mem_filter.mp haF).2
  exact mutatedLineFactor_protected Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
    P V D hP v k H a (hregion a hab.1.le hab.2.le)

include hcoord hS hcomp in
omit [FiniteDimensional ℝ E] in
lemma mutatedPathCompletion_protected (P : Finset E) (V : M → Prop)
    (hV : ∀a b,V a → V b → V (a+b)) (D : ℕ)
    (hP : ∀n,n+1≤D → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      ¬V m → e m∈P ∨ -(e m)∈P)
    {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (hp : p.InRegion C e (mutationSignRegion e S (simpleRoot C pc) P)) :
    ∀n,n+1≤D → SupportedOn LaurentRay.vUnit Ω V
      (coeff (n+1) (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p)) := by
  induction p with
  | nil=>
    intro n hn
    simp only [mutatedPathCompletion,coeff_one,show n+1≠0 by omega,ite_false, if_false]
    exact SupportedOn.zero LaurentRay.vUnit Ω V
  | append s p ih=>
    apply strict_mul_through LaurentRay.vUnit Ω V hV _ _ D
      (mutatedLineCompletion_constant Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi)
      (mutatedPathCompletion_constant Ω hΩ C coord pc e he L hdeg p) _ (ih hp.2)
    intro n hn
    rw [mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi
      (n+1) (max 1 ((mutationSize Ω C pc+1)*D)) (le_max_left _ _)
      ((Nat.mul_le_mul_left _ hn).trans (le_max_right _ _))]
    exact mutatedLineProduct_protected Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      P V hV D hP s.direction s.offset s.generic s.lo s.hi _ hp.1 n hn
end

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
lemma mutatedTransport_protected (P : Finset E) (V : M → Prop)
    (hV : ∀a b,V a → V b → V (a+b)) (D : ℕ)
    (hP : ∀n,n+1≤D → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      ¬V m → e m∈P ∨ -(e m)∈P)
    {a b : Module.Dual ℝ E} (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (ha : a∈mutationSignRegion e S (simpleRoot C pc) P)
    (hb : b∈mutationSignRegion e S (simpleRoot C pc) P)
    (hap : a (e (simpleRoot C pc))≠0) (hbp : b (e (simpleRoot C pc))≠0) :
    ∀n,n+1≤D → SupportedOn LaurentRay.vUnit Ω V
      (coeff (n+1) (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val) := by
  obtain ⟨q,hq⟩:=generic_mutation_region_path C e S (simpleRoot C pc) hS P a b HA HB ha hb hap hbp
  rw [mutatedTransport_eq_path Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HB q]
  exact mutatedPathCompletion_protected Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg P V hV D hP q hq
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutatedEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
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

omit [DecidableEq I] in
lemma mem_strictRootsThrough (D : ℕ) (m : M) :
    m∈strictRootsThrough C D ↔ ∃n,n+1≤D ∧ HasRootDegree C (n+1) m := by
  classical
  simp only [strictRootsThrough,Finset.mem_biUnion,Finset.mem_range,Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq,Nat.lt_iff_add_one_le]

omit [FiniteDimensional ℝ E] in
include hdeg in
lemma RegularCovector.simple_ne {a : Module.Dual ℝ E} (HA : RegularCovector C e a) :
    a (e (simpleRoot C pc))≠0 :=
  HA 1 _ (realRoot_mem e C 1 1 le_rfl _ (simpleRoot_degree C pc))
    (realRoot_ne_zero C e L hdeg 1 (by omega) _ (simpleRoot_degree C pc))

include hnd in
lemma mutatedTransport_endpoint_support (V : M → Prop)
    (hV : ∀a b,V a → V b → V (a+b)) (D : ℕ)
    {a b : Module.Dual ℝ E} (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (hmatch : ∀n,n+1≤D → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m → ¬V m →
      (0 < realMutationCovector e S (simpleRoot C pc) a (e m) ∧
       0 < realMutationCovector e S (simpleRoot C pc) b (e m)) ∨
      (realMutationCovector e S (simpleRoot C pc) a (e m)<0 ∧
       realMutationCovector e S (simpleRoot C pc) b (e m)<0)) :
    ∀n,n+1≤D → SupportedOn LaurentRay.vUnit Ω V
      (coeff (n+1) (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB).val) := by
  classical
  let f (m : M) : E:=if 0 < realMutationCovector e S (simpleRoot C pc) a (e m) then e m else -e m
  let R:=(strictRootsThrough (mutatedRoots Ω C pc) D).filter (fun m=>¬V m)
  let P:=R.image f
  have hp (n : ℕ) (hn : n+1≤D) (m : M)
      (hm : HasRootDegree (mutatedRoots Ω C pc) (n+1) m) (hv : ¬V m) : f m∈P:=
    Finset.mem_image.mpr ⟨m,Finset.mem_filter.mpr
      ⟨(mem_strictRootsThrough _ _ _).mpr ⟨n,hn,hm⟩,hv⟩,rfl⟩
  have hab : a∈mutationSignRegion e S (simpleRoot C pc) P ∧
      b∈mutationSignRegion e S (simpleRoot C pc) P:=by
    have aux (x : E) (hx : x∈P) :
        0 < realMutationCovector e S (simpleRoot C pc) a x ∧
        0 < realMutationCovector e S (simpleRoot C pc) b x:=by
      obtain ⟨m,hm,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨hm,hv⟩:=Finset.mem_filter.mp hm
      obtain ⟨n,hn,hm⟩:=(mem_strictRootsThrough _ _ _).mp hm
      rcases hmatch n hn m hm hv with hh|hh
      · dsimp only [f]
        rw [ite_eq_left hh.1]
        exact hh
      · dsimp only [f]
        rw [ite_eq_right (not_lt.mpr hh.1.le),map_neg,map_neg]
        exact ⟨neg_pos.mpr hh.1,neg_pos.mpr hh.2⟩
    exact ⟨fun x hx=>(aux x hx).1,fun x hx=>(aux x hx).2⟩
  apply mutatedTransport_protected Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    P V hV D _ HA HB hab.1 hab.2 (HA.simple_ne C pc e L hdeg) (HB.simple_ne C pc e L hdeg)
  intro n hn m hm hv
  have hh:=hp n hn m hm hv
  dsimp [f] at hh
  split_ifs at hh
  · exact Or.inl hh
  · exact Or.inr hh
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutatedCanonicalCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
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

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_8
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_11_rf09d92_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_11_rf09d92_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedTransport_chart_three (N : ℕ) (h : M →+ ℝ)
    {a b x y : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (HX : RegularCovector C e x) (HY : RegularCovector C e y)
    (hA : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      0 < realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0)
    (hX : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      (h m<0 → realMutationCovector e S (simpleRoot C pc) x (e m)<0) ∧
      (0≤h m → 0 < realMutationCovector e S (simpleRoot C pc) x (e m)))
    (hY : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      (0<h m → 0 < realMutationCovector e S (simpleRoot C pc) y (e m)) ∧
      (h m≤0 → realMutationCovector e S (simpleRoot C pc) y (e m)<0)) :
    ∀n≤N,
      coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HY HB).val=
        coeff n (chartPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) h
          (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val ∧
      coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HX HY).val=
        coeff n (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc) h
          (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val ∧
      coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HX).val=
        coeff n (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc) h
          (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val := by
  let T (u w : Module.Dual ℝ E) (HU : RegularCovector C e u) (HW : RegularCovector C e w):=
    mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HU HW
  have hc:=mutatedTransport_endpoint_support Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    (fun m=>h m<0) (fun u w hu hw=>by simpa only [map_add] using add_neg hu hw) N HA HX
    (by intro n hn m hm hh; exact Or.inl ⟨hA n hn m hm,(hX n hn m hm).2 (le_of_not_gt hh)⟩)
  have ha:=mutatedTransport_endpoint_support Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    (fun m=>0<h m) (fun u w hu hw=>by simpa only [map_add] using add_pos hu hw) N HY HB
    (by intro n hn m hm hh; exact Or.inr ⟨(hY n hn m hm).2 (le_of_not_gt hh),hB n hn m hm⟩)
  have hb:=mutatedTransport_endpoint_support Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    (fun m=>h m=0) (fun u w hu hw=>by rw [map_add,hu,hw,add_zero]) N HX HY
    (by
      intro n hn m hm hh
      rcases lt_or_gt_of_ne hh with hp|hp
      · exact Or.inr ⟨(hX n hn m hm).1 hp,(hY n hn m hm).2 hp.le⟩
      · exact Or.inl ⟨(hX n hn m hm).2 hp.le,(hY n hn m hm).1 hp⟩)
  apply chart_three_truncated_unique LaurentRay.vUnit Ω (mutatedRoots Ω C pc) h
    (T a b HA HB) (T y b HY HB).val (T x y HX HY).val (T a x HA HX).val N
    (T y b HY HB).property.1 (T x y HX HY).property.1 (T a x HA HX).property.1
  · have h1:=mutatedTransport_trans Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HX HY
    have h2:=mutatedTransport_trans Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HY HB
    dsimp [T]
    rw [mul_assoc,←h1,←h2]
  · intro n hn m hm
    by_contra hh
    exact hm (ha n hn m hh)
  · intro n hn m hm
    by_contra hh
    exact hm (hb n hn m hh)
  · intro n hn m hm
    by_contra hh
    exact hm (hc n hn m hh)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingTransportTrace
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
open PowerSeries WallUnits FiniteRayGeometry
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

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_9
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_12_rf09d92_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_12_rf09d92_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedTransport_chartNegative (N : ℕ) {a b x : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) (HX : RegularCovector C e x)
    (hA : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      0 < realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0)
    (hx : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0) :
    ∀n≤N, coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HX).val=
      coeff n (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
        (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val := by
  intro n hn
  exact (mutatedTransport_chart_three Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd N
    ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
    HA HB HX HX hA hB
    (by intro j hj m hm; exact ⟨id,fun hh=>lt_of_le_of_ne hh (Ne.symm (hx j hj m hm))⟩)
    (by intro j hj m hm; exact ⟨id,fun hh=>lt_of_le_of_ne hh (hx j hj m hm)⟩)
    n hn).2.2

include hnd in
lemma mutatedTransport_negative_ratio_oai (N : ℕ) {a b x y : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (HX : RegularCovector C e x) (HY : RegularCovector C e y)
    (hA : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      0 < realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0)
    (hx : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
    (hy : ∀n,n+1≤N → ∀m,HasRootDegree (mutatedRoots Ω C pc) (n+1) m →
      realMutationCovector e S (simpleRoot C pc) y (e m)≠0) :
    ∀n≤N, coeff n (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HX HY).val=
      coeff n ((chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) y).toAddMonoidHom.comp e)
        (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val *
        invOfUnit (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
        (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val 1) := by
  let T (u w : Module.Dual ℝ E) (HU : RegularCovector C e u) (HW : RegularCovector C e w):=
    mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HU HW
  have Hx:=mutatedTransport_chartNegative Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd N HA HB HX hA hB hx
  have Hy:=mutatedTransport_chartNegative Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd N HA HB HY hA hB hy
  have Hi:=FormalLog.inverse_coeff_congr _ _ (T a x HA HX).property.1
    (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc) _ (T a b HA HB)).property.1 N Hx
  have He : (T x y HX HY).val=(T a y HA HY).val*invOfUnit (T a x HA HX).val 1:=by
    have H:=mutatedTransport_trans Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd HA HX HY
    change (T a y HA HY).val=(T x y HX HY).val*(T a x HA HX).val at H
    rw [H,mul_assoc,mul_invOfUnit _ _ (T a x HA HX).property.1,mul_one]
  intro n hn
  change coeff n (T x y HX HY).val=_
  rw [He]
  exact FormalLog.mul_coeff_congr _ _ _ _ n
    (fun j hj=>Hy j (hj.trans hn)) (fun j hj=>Hi j (hj.trans hn))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_negative_ratio_oai.{u_1, u_2, u_3} := @OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_negative_ratio_oai.{u_1, u_2, u_3}
