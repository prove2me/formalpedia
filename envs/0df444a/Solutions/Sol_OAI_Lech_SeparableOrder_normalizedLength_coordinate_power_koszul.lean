-- Prove2me | solution 1 for OAI.Lech.SeparableOrder.normalizedLength_coordinate_power_koszul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:32:44.920773+00:00
-- url     : https://prove2.me/submissions/c5c9a4de-af90-4eec-ab05-6d008cf9ca7b

import Mathlib
import Definitions.Def_OAIQ032L023
import Theorems.Thm_OAI_Lech_RootTower_normalizedLength_eq_zero_of_root_annihilated

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NormalizedLengthTrivialRelation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
namespace Lech.NormalizedLength
lemma trivialRelation_of_injective_flat_lift {R M N : Type*}
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Flat R N] (g : N →ₗ[R] M) (hg : Function.Injective g)
    {l : ℕ} {f : Fin l → R} {x : Fin l → M}
    (hx : ∑ i, f i • x i = 0) (y : Fin l → N) (hy : ∀ i, g (y i) = x i) :
    Module.IsTrivialRelation f x := by
  have hz : ∑ i, f i • y i = 0 := by
    apply hg
    simpa only [map_sum, map_smul, hy, map_zero] using hx
  obtain ⟨k, a, z, hz, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hz
  refine ⟨k, a, fun j => g (z j), ?_, ha⟩
  intro i
  rw [← hy i, hz i, map_sum]
  simp only [map_smul]
end Lech.NormalizedLength


namespace Lech.NormalizedLength.Tower
variable {L : Type*} [CommRing L] (T : Lech.NormalizedLength.Tower L)

lemma finite_collection_stage {ι : Type*} [Fintype ι] (x : ι → L) (n : ℕ) :
    ∃ m, n ≤ m ∧ ∀ i, x i ∈ T.ring m := by
  classical
  choose k hk using fun i => T.exhaustive (x i)
  refine ⟨max n (Finset.univ.sup k), le_max_left _ _, fun i => ?_⟩
  exact T.mono ((Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)) (hk i)

lemma flat_limit (n : ℕ) : Module.Flat (T.ring n) L := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hx
  obtain ⟨m, hnm, hm⟩ := T.finite_collection_stage x n
  let : Algebra (T.ring n) (T.ring m) := (Subring.inclusion (T.mono hnm)).toAlgebra
  let := T.flat n m hnm
  let φ : T.ring m →ₗ[T.ring n] L :=
    { toFun := fun z => (z : L)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact trivialRelation_of_injective_flat_lift φ Subtype.val_injective hx
    (fun i => ⟨x i, hm i⟩) (fun _ => rfl)

end Lech.NormalizedLength.Tower

open TensorProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerLengthEq
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct


namespace Lech.TraceConductor
open Algebra Module

variable {A E : Type*} [CommRing A] [CommRing E] [Algebra A E]

 
lemma finite_denominators (B : Subalgebra A E)
    (hden : ∀ x : E, ∃ a : A, a ≠ 0 ∧ a • x ∈ B)
    [IsDomain A] {ι : Type*} [Finite ι] (v : ι → E) :
    ∃ a : A, a ≠ 0 ∧ ∀ i, a • v i ∈ B := by
  classical
  have hfin (s : Finset ι) : ∃ a : A, a ≠ 0 ∧ ∀ i ∈ s, a • v i ∈ B := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨a, ha, hva⟩ := hden (v i)
        obtain ⟨b, hb, hvb⟩ := ih
        refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [mul_comm a b, mul_smul]
          exact B.smul_mem hva b
        · rw [mul_smul]
          exact B.smul_mem (hvb j hj) a
  let := Fintype.ofFinite ι
  simpa only [Finset.mem_univ, forall_true_left] using hfin Finset.univ

variable (A K E : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]

include K in
 

theorem exists_conductor (B : Subalgebra A E)
    (hden : ∀ x : E, ∃ a : A, a ≠ 0 ∧ a • x ∈ B) :
    ∃ g : A, g ≠ 0 ∧ ∀ c : E, IsIntegral A c → g • c ∈ B := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K E
  obtain ⟨g, hg, hgb⟩ := finite_denominators B hden b.traceDual
  refine ⟨g, hg, fun c hc => ?_⟩
  have hspan : c ∈ Submodule.span A (Set.range b.traceDual) := by
    apply integralClosure_le_span_dualBasis b hb
    exact hc
  clear hc
  induction hspan using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hgb i
  | zero => simp
  | add x y hx hy ihx ihy => simpa [smul_add] using B.add_mem ihx ihy
  | smul a x hx ih =>
      rw [smul_comm g a]
      exact B.smul_mem ih a

end Lech.TraceConductor


namespace Lech.TraceConductor
open Module
variable {A K E : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field E] [Algebra A E] [Algebra K E] [IsScalarTower A K E]

lemma denominator_of_span (B : Subalgebra A E) {s : Set E}
    (hden : ∀ x ∈ s, ∃ a : A, a ≠ 0 ∧ a • x ∈ B)
    {x : E} (hx : x ∈ Submodule.span K s) : ∃ a : A, a ≠ 0 ∧ a • x ∈ B := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hden x hx
  | zero => exact ⟨1,one_ne_zero,by simp⟩
  | add x y hx hy ix iy =>
      obtain ⟨a,ha,hax⟩ := ix
      obtain ⟨b,hb,hby⟩ := iy
      refine ⟨a*b,mul_ne_zero ha hb,?_⟩
      rw [smul_add]
      apply B.add_mem
      · rw [mul_comm a b,mul_smul]
        exact B.smul_mem hax b
      · rw [mul_smul]
        exact B.smul_mem hby a
  | smul t x hx ih =>
      obtain ⟨a,ha,hax⟩ := ih
      obtain ⟨u,v,hv,rfl⟩ := IsFractionRing.div_surjective A t
      have hv : v ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hv
      refine ⟨v*a,mul_ne_zero hv ha,?_⟩
      have hv' : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hv
      have heq : (v*a) • ((algebraMap A K u / algebraMap A K v) • x) = u • (a • x) := by
        rw [← IsScalarTower.algebraMap_smul K (v*a), ← IsScalarTower.algebraMap_smul K u,
          ← IsScalarTower.algebraMap_smul K a, map_mul, smul_smul, smul_smul]
        congr 1
        field_simp
      rw [heq]
      exact B.smul_mem hax u

variable {D : Type*} [CommRing D] [IsDomain D] [Algebra A D] [Algebra D E]
  [IsFractionRing D E] [IsScalarTower A D E] [Algebra.IsAlgebraic A D]

omit [IsDomain A] in
lemma denominator_fraction (x : E) :
    ∃ a : A, a ≠ 0 ∧ ∃ d : D, a • x = algebraMap D E d := by
  obtain ⟨u,v,hv,rfl⟩ := IsFractionRing.div_surjective D x
  have hv : v ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hv
  obtain ⟨y,a,ha,h⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul A u hv
  refine ⟨a,ha,y,?_⟩
  have hv' : algebraMap D E v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective D E)).mpr hv
  rw [Algebra.smul_def, ← mul_div_assoc, div_eq_iff hv', ← map_mul]
  have hh := congrArg (algebraMap D E) h
  simpa only [Algebra.smul_def,map_mul,← IsScalarTower.algebraMap_apply,mul_comm] using hh

end Lech.TraceConductor


namespace Lech.RootTower
variable {A B C : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
  [CommRing C] [IsReduced C] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [CharP C p]

omit [IsReduced A] [IsReduced B] in
lemma perfectMap_of (f : A →+* B) (a : A) :
    perfectMap p f (PerfectClosure.of A p a) = PerfectClosure.of B p (f a) :=
  PerfectRing.lift_comp_apply _ _ _ _

end Lech.RootTower


namespace Lech.TraceConductor
open Lech.RootTower
variable (A D K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing D] [IsDomain D] [Field K] [Field L]
  [Algebra A D] [Algebra A K] [IsFractionRing A K]
  [Algebra A L] [Algebra D L] [IsFractionRing D L] [IsScalarTower A D L]
  [Algebra K L] [IsScalarTower A K L] [Algebra.IsIntegral A D]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p] [CharP K p] [CharP L p]


include K in
omit [CharP D p] in
 
theorem exists_perfect_conductor :
    ∃ g : A, g ≠ 0 ∧ ∀ c : PerfectClosure L p, IsIntegral (PerfectClosure A p) c →
      (PerfectClosure.of A p g) • c ∈ perfectOrder A D L p := by
  let P := PerfectClosure A p
  let Q := PerfectClosure K p
  let E := PerfectClosure L p
  let B := perfectOrder A D L p
  have hden0 : ∀ x ∈ Set.range (PerfectClosure.of L p), ∃ a : P, a ≠ 0 ∧ a • x ∈ B := by
    rintro x ⟨l,rfl⟩
    obtain ⟨a,ha,d,hd⟩ := denominator_fraction (A := A) (D := D) l
    refine ⟨PerfectClosure.of A p a,?_,?_⟩
    · change rootMap A p 0 a ≠ 0
      exact (map_ne_zero_iff _ (rootMap_injective A p 0)).mpr ha
    · change perfectMap p (algebraMap A L) (PerfectClosure.of A p a) * PerfectClosure.of L p l ∈ B
      rw [perfectMap_of, ← map_mul]
      rw [show algebraMap A L a * l = algebraMap D L d from by simpa only [Algebra.smul_def] using hd]
      exact Algebra.subset_adjoin ⟨d,rfl⟩
  have hden : ∀ x : E, ∃ a : P, a ≠ 0 ∧ a • x ∈ B := by
    intro x
    apply denominator_of_span (K := Q) B hden0
    rw [perfect_span K L p]
    trivial
  obtain ⟨g,hg,hgc⟩ := exists_conductor P Q E B hden
  obtain ⟨⟨n,a⟩,rfl⟩ := PerfectClosure.mk_surjective A p g
  have hn : 0 < p^n := pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n
  refine ⟨a,?_,fun c hc => ?_⟩
  · intro ha
    apply hg
    change rootMap A p n a = 0
    rw [ha,map_zero]
  · have hh : PerfectClosure.of A p a = (rootMap A p n a)^(p^n-1) * rootMap A p n a := by
      rw [← rootMap_pow p n a, ← pow_succ, Nat.sub_add_cancel hn]
    rw [hh,mul_smul]
    exact B.smul_mem (hgc c hc) _

end Lech.TraceConductor
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TraceConductorPerfectOrder
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
namespace Lech.TraceConductor
open Lech.RootTower
variable (A D L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Field L] [Algebra A L] [Algebra D L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP L p]


omit [IsDomain A] [IsDomain D] in
lemma perfectOrder_roots (n : ℕ) {x : PerfectClosure L p} (hx : x ∈ perfectOrder A D L p) :
    ∃ y ∈ perfectOrderAt A D L p n, y^(p^n) = x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨d,rfl⟩ := hx
      exact ⟨rootMap L p n (algebraMap D L d),Algebra.subset_adjoin ⟨d,rfl⟩,rootMap_pow p n _⟩
  | algebraMap a =>
      obtain ⟨b,hb⟩ := (surjective_frobenius (PerfectClosure A p) p).iterate n a
      refine ⟨algebraMap (PerfectClosure A p) (PerfectClosure L p) b,
        (perfectOrderAt A D L p n).algebraMap_mem b,?_⟩
      rw [← map_pow,show b^(p^n) = a from by simpa only [iterate_frobenius] using hb]
  | add x y hx hy ix iy =>
      obtain ⟨a,ha,hax⟩ := ix
      obtain ⟨b,hb,hby⟩ := iy
      exact ⟨a+b,(perfectOrderAt A D L p n).add_mem ha hb,by rw [add_pow_char_pow,hax,hby]⟩
  | mul x y hx hy ix iy =>
      obtain ⟨a,ha,hax⟩ := ix
      obtain ⟨b,hb,hby⟩ := iy
      exact ⟨a*b,(perfectOrderAt A D L p n).mul_mem ha hb,by rw [mul_pow,hax,hby]⟩

omit [IsDomain D] in
lemma root_conductor (g : A)
    (hg : ∀ c : PerfectClosure L p, IsIntegral (PerfectClosure A p) c →
      PerfectClosure.of A p g • c ∈ perfectOrder A D L p)
    (n : ℕ) (c : PerfectClosure L p) (hc : IsIntegral (PerfectClosure A p) c) :
    rootMap A p n g • c ∈ perfectOrderAt A D L p n := by
  obtain ⟨y,hy,heq⟩ := perfectOrder_roots A D L p n (hg (c^(p^n)) (hc.pow _))
  have hh : y = rootMap A p n g • c := by
    apply (injective_frobenius (PerfectClosure L p) p).iterate n
    rw [iterate_frobenius,iterate_frobenius,heq,smul_pow,rootMap_pow]
  rwa [hh] at hy

end Lech.TraceConductor

open scoped TensorProduct nonZeroDivisors
namespace Lech.TensorInjection

lemma injective_of_basis {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (b : Module.Basis ι R M) (f : M →ₗ[R] N)
    (h : LinearIndependent R (fun i => f (b i))) : Function.Injective f := by
  have he : f = b.constr R (fun i => f (b i)) := by
    apply b.ext
    intro i
    simp
  rw [he]
  exact b.injective_constr_of_linearIndependent h

section Field
variable {K L Q E : Type*} [Field K] [Field L] [Field Q] [CommRing E]
  [Algebra K L] [Algebra K Q] [Algebra K E] [Algebra Q E]
  [IsScalarTower K Q E]

lemma field_product_injective {ι : Type*} (b : Module.Basis ι K L) (f : L →ₐ[K] E)
    (h : LinearIndependent Q (fun i => f (b i))) :
    Function.Injective (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q E) f) := by
  apply injective_of_basis (b.baseChange Q)
    (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q E) f).toLinearMap
  simpa only [AlgHom.toLinearMap_apply, Module.Basis.baseChange_apply,Algebra.TensorProduct.productLeftAlgHom, Algebra.TensorProduct.lift_tmul,
    map_one,one_mul] using h
end Field

section IntegralBase
variable {A K P Q : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CommRing P] [Field Q] [Algebra A P] [Algebra A Q]
  [Algebra K Q] [IsScalarTower A K Q]

omit [IsDomain A] in
 
lemma localized_product_injective (f : P →ₐ[A] Q) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Q) f) := by
  let : Algebra P (K ⊗[A] P) := Algebra.TensorProduct.rightAlgebra
  let S := Algebra.algebraMapSubmonoid P A⁰
  let F := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Q) f
  apply IsLocalization.injective_of_map_algebraMap_zero (M := S) (K ⊗[A] P) F.toRingHom
  intro x hx
  change F (1 ⊗ₜ[A] x) = 0 at hx
  have hx' : f x = 0 := by
    simpa [F,Algebra.TensorProduct.productLeftAlgHom,Algebra.TensorProduct.lift_tmul] using hx
  have he : x = 0 := (map_eq_zero_iff _ hf).mp hx'
  simp [he]
end IntegralBase

variable {A K D L P Q E : Type*}
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing D] [Algebra A D] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L]
  [CommRing P] [Algebra A P] [Module.Flat A P]
  [Field Q] [Algebra A Q] [Algebra K Q] [IsScalarTower A K Q]
  [CommRing E] [Algebra A E] [Algebra K E] [IsScalarTower A K E]
  [Algebra Q E] [IsScalarTower K Q E] [IsScalarTower A Q E]

omit [IsDomain A] in
 

theorem stage_product_injective {ι : Type*} (b : Module.Basis ι K L)
    (fD : D →ₐ[A] L) (hfD : Function.Injective fD)
    (fP : P →ₐ[A] Q) (hfP : Function.Injective fP)
    (fL : L →ₐ[K] E) (hind : LinearIndependent Q (fun i => fL (b i))) :
    Function.Injective (Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom A Q E).comp fP) ((fL.restrictScalars A).comp fD)) := by
  let U := K ⊗[A] P
  let j : U →ₐ[K] Q := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Q) fP
  have hj : Function.Injective j := localized_product_injective fP hfP
  let k : L ⊗[K] U →ₐ[K] L ⊗[K] Q :=
    Algebra.TensorProduct.map (AlgHom.id K L) j
  have hk : Function.Injective k := by
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := L) j.toLinearMap hj
  let e := Algebra.TensorProduct.cancelBaseChange A K K L P
  let v : D ⊗[A] P →ₐ[A] L ⊗[A] P :=
    Algebra.TensorProduct.map fD (AlgHom.id A P)
  have hv : Function.Injective v :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := P) fD.toLinearMap hfD
  let t := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q E) fL
  have ht : Function.Injective t := field_product_injective b fL hind
  let F : P ⊗[A] D →ₐ[A] E := (t.restrictScalars A).comp
    (((Algebra.TensorProduct.comm K L Q).toAlgHom.restrictScalars A).comp
      ((k.restrictScalars A).comp ((e.symm.toAlgHom.restrictScalars A).comp
        (v.comp (Algebra.TensorProduct.comm A P D).toAlgHom))))
  have hF : Function.Injective F := ht.comp
    ((Algebra.TensorProduct.comm K L Q).injective.comp
      (hk.comp (e.symm.injective.comp (hv.comp (Algebra.TensorProduct.comm A P D).injective))))
  have heq : F = Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom A Q E).comp fP) ((fL.restrictScalars A).comp fD) := by
    apply Algebra.TensorProduct.ext'
    intro a d
    simp [F,v,k,j,t,e,Algebra.TensorProduct.productMap,
      Algebra.TensorProduct.productLeftAlgHom, Algebra.TensorProduct.lift_tmul, mul_comm]
    change fL (fD d) * (algebraMap Q E) ((algebraMap K Q) 1 * fP a) = _
    simp
  rwa [heq] at hF
end Lech.TensorInjection


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]

lemma rootMap_eq_frobeniusEquiv (n : ℕ) : rootMap A p n =
    (iterateFrobeniusEquiv (PerfectClosure A p) p n).symm.toRingHom.comp
      (PerfectClosure.of A p) := by
  ext a
  apply (iterateFrobeniusEquiv (PerfectClosure A p) p n).injective
  change (rootMap A p n a)^(p^n) = _
  rw [rootMap_pow]
  exact ((iterateFrobeniusEquiv (PerfectClosure A p) p n).apply_symm_apply _).symm

lemma rootMap_flat (hflat : (PerfectClosure.of A p).Flat) (n : ℕ) :
    (rootMap A p n).Flat := by
  rw [rootMap_eq_frobeniusEquiv]
  exact RingHom.Flat.comp hflat (RingHom.Flat.of_bijective
    (iterateFrobeniusEquiv (PerfectClosure A p) p n).symm.bijective)

end Lech.RootTower


namespace Lech.RootTower
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]

 
lemma root_basis_independent [Algebra.IsSeparable K L] {ι : Type*}
    (b : Module.Basis ι K L) (n : ℕ) :
    LinearIndependent (PerfectClosure K p) (fun i => rootMap L p n (b i)) := by
  let : Algebra K (PerfectClosure K p) := (rootMap K p n).toAlgebra
  let : Algebra K (PerfectClosure L p) := ((rootMap L p n).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K (PerfectClosure K p) (PerfectClosure L p) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (perfectMap_root p (algebraMap K L) n a).symm)
  let f : L →ₐ[K] PerfectClosure L p :=
    { __ := rootMap L p n, commutes' _ := rfl }
  let : IsPurelyInseparable K (PerfectClosure K p) :=
    (isPurelyInseparable_iff_pow_mem K p).mpr (by
      intro x
      obtain ⟨j,a,ha⟩ := IsPRadical.pow_mem (PerfectClosure.of K p) p x
      refine ⟨j, a^(p^n), ?_⟩
      change rootMap K p n (a^(p^n)) = x^(p^j)
      rw [map_pow,rootMap_pow]
      exact ha)
  apply LinearIndependent.map_of_isPurelyInseparable_of_isSeparable (F := K)
  · intro i
    exact (Algebra.IsSeparable.isSeparable K (b i)).map f (rootMap_injective L p n)
  · exact b.linearIndependent.map' f.toLinearMap
      (LinearMap.ker_eq_bot.mpr (rootMap_injective L p n))

end Lech.RootTower


namespace Lech.PerfectStages
open Lech.RootTower Lech.TraceConductor
variable (A D L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Field L] [Algebra A D] [Algebra A L] [Algebra D L] [IsScalarTower A D L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p] [CharP L p]

omit [IsDomain A] in
 
lemma embedded_perfection_integral [Algebra.IsIntegral A D] (c : PerfectClosure D p) :
    IsIntegral (PerfectClosure A p) (perfectMap p (algebraMap D L) c) := by
  let : Algebra A (PerfectClosure L p) :=
    ((PerfectClosure.of L p).comp (algebraMap A L)).toAlgebra
  let : IsScalarTower A (PerfectClosure A p) (PerfectClosure L p) :=
    IsScalarTower.of_algebraMap_eq' (PerfectRing.lift_comp _ _ _).symm
  let f : D →ₐ[A] PerfectClosure L p :=
    { __ := (PerfectClosure.of L p).comp (algebraMap D L)
      commutes' a := congrArg (PerfectClosure.of L p) (IsScalarTower.algebraMap_apply A D L a).symm }
  obtain ⟨⟨n,d⟩,rfl⟩ := PerfectClosure.mk_surjective D p c
  change IsIntegral (PerfectClosure A p)
    (perfectMap p (algebraMap D L) (rootMap D p n d))
  rw [perfectMap_root]
  apply IsIntegral.of_pow (pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n)
  rw [rootMap_pow]
  exact (IsIntegral.map f (Algebra.IsIntegral.isIntegral (R := A) d)).tower_top

end Lech.PerfectStages


namespace Lech.PerfectStages
open Lech.RootTower Lech.TraceConductor
open scoped TensorProduct
variable (A D K L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Field K] [Field L] [Algebra A D] [Algebra A K] [IsFractionRing A K]
  [Algebra A L] [Algebra D L] [IsFractionRing D L] [IsScalarTower A D L]
  [Algebra K L] [IsScalarTower A K L] [Algebra.IsSeparable K L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP K p] [CharP L p]

include K in
omit [IsDomain D] in
 
theorem tensorStageMap_injective (hflat : (PerfectClosure.of A p).Flat) (n : ℕ) :
    Function.Injective (tensorStageMap A D L p n) := by
  let P := PerfectClosure A p
  let Q := PerfectClosure K p
  let E := PerfectClosure L p
  let : Algebra A P := (rootMap A p n).toAlgebra
  let : Module.Flat A P := rootMap_flat A p hflat n
  let : Algebra K Q := (rootMap K p n).toAlgebra
  let : Algebra A Q := ((rootMap K p n).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K Q := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra K E := ((rootMap L p n).comp (algebraMap K L)).toAlgebra
  let : Algebra A E := ((rootMap L p n).comp (algebraMap A L)).toAlgebra
  let : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact congrArg (rootMap L p n) (IsScalarTower.algebraMap_apply A K L a))
  let : IsScalarTower K Q E := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (perfectMap_root p (algebraMap K L) n a).symm)
  let : IsScalarTower A Q E := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change rootMap L p n (algebraMap A L a) =
      perfectMap p (algebraMap K L) (rootMap K p n (algebraMap A K a))
    rw [perfectMap_root,IsScalarTower.algebraMap_apply A K L])
  let fP : P →ₐ[A] Q :=
    { __ := perfectMap p (algebraMap A K)
      commutes' a := perfectMap_root p (algebraMap A K) n a }
  let fL : L →ₐ[K] E := { __ := rootMap L p n, commutes' _ := rfl }
  have hh := Lech.TensorInjection.stage_product_injective (Module.Free.chooseBasis K L)
    (IsScalarTower.toAlgHom A D L) (IsFractionRing.injective D L)
    fP (perfectMap_injective p _ (IsFractionRing.injective A K)) fL
    (root_basis_independent K L p (Module.Free.chooseBasis K L) n)
  have he : (tensorStageMap A D L p n).toRingHom =
      (Algebra.TensorProduct.productMap ((IsScalarTower.toAlgHom A Q E).comp fP)
        ((fL.restrictScalars A).comp (IsScalarTower.toAlgHom A D L))).toRingHom := by
    apply RingHom.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul a d =>
        change perfectMap p (algebraMap A L) a * rootMap L p n (algebraMap D L d) =
          perfectMap p (algebraMap K L) (perfectMap p (algebraMap A K) a) *
            rootMap L p n (algebraMap D L d)
        congr 1
        have hp := congrArg (fun f : PerfectClosure A p →+* PerfectClosure L p => f a)
          (perfectMap_comp p (algebraMap A K) (algebraMap K L))
        simpa only [RingHom.comp_apply,← IsScalarTower.algebraMap_eq] using hp.symm
    | add x y hx hy => simp only [map_add,hx,hy]
  change Function.Injective (tensorStageMap A D L p n).toRingHom
  rw [he]
  exact hh

end Lech.PerfectStages


namespace Lech.PerfectStages
open Lech.RootTower Lech.TraceConductor
open scoped TensorProduct
variable (A D L : Type*) [CommRing A] [IsDomain A] [CommRing D] [Field L]
  [Algebra A D] [Algebra A L] [Algebra D L] [IsScalarTower A D L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP L p]

 
lemma tensorStageMap_range (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (tensorStageMap A D L p n).range = perfectOrderAt A D L p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    induction x using OAI.tensorInductionOn with
    | tmul a d =>
        change perfectMap p (algebraMap A L) a * rootMap L p n (algebraMap D L d) ∈ _
        exact (perfectOrderAt A D L p n).mul_mem
          ((perfectOrderAt A D L p n).algebraMap_mem a) (Algebra.subset_adjoin ⟨d,rfl⟩)
    | add x y hx hy => simpa only [map_add] using (perfectOrderAt A D L p n).add_mem hx hy
  · apply Algebra.adjoin_le
    rintro _ ⟨d,rfl⟩
    refine ⟨1 ⊗ₜ[A] d,?_⟩
    change perfectMap p (algebraMap A L) 1 * rootMap L p n (algebraMap D L d) = _
    simp

end Lech.PerfectStages


namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

variable (L : Type*) [Field L] [Algebra A L] [Algebra D L] [IsScalarTower A D L]
  [CharP L p]

lemma fieldMap_tensor (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (fieldMap A D p L).comp (tensorMap A D p n) =
      Lech.PerfectStages.tensorStageMap A D L p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply AlgHom.ext
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul a d =>
    change perfectMap p (algebraMap D L)
      (perfectMap p (algebraMap A D) a * rootMap D p n d) = _
    rw [map_mul,perfectMap_root]
    change _ = perfectMap p (algebraMap A L) a * rootMap L p n (algebraMap D L d)
    congr 1
    rw [← RingHom.comp_apply,perfectMap_comp,← IsScalarTower.algebraMap_eq]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (·+·) hx hy

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [IsScalarTower A K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p]

include L K in
omit [FiniteDimensional K L] in
lemma tensorMap_injective (hflat : (PerfectClosure.of A p).Flat) (n : ℕ) :
    Function.Injective (tensorMap A D p n) := by
  have h := Lech.PerfectStages.tensorStageMap_injective A D K L p hflat n
  have hh := fieldMap_tensor A D p L n
  intro x y hxy
  apply h
  rw [← hh]
  exact congrArg (fieldMap A D p L) hxy

include L K in
 

theorem exists_conductor [IsIntegrallyClosed A] [Algebra.IsIntegral A D] :
    ∃ g : A, g ≠ 0 ∧ ∀ (n : ℕ) (c : PerfectClosure D p),
      rootMap A p n g • c ∈ stage A D p n := by
  obtain ⟨g,hg,hgc⟩ := Lech.TraceConductor.exists_perfect_conductor A D K L p
  refine ⟨g,hg,fun n c => ?_⟩
  have hi := Lech.PerfectStages.embedded_perfection_integral A D L p c
  have hc := Lech.TraceConductor.root_conductor A D L p g hgc n _ hi
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  rw [← Lech.PerfectStages.tensorStageMap_range A D L p n] at hc
  obtain ⟨x,hx⟩ := hc
  rw [← tensorMap_range A D p n]
  refine ⟨x,?_⟩
  apply perfectMap_injective p (algebraMap D L) (IsFractionRing.injective D L)
  change (fieldMap A D p L) (tensorMap A D p n x) =
    (fieldMap A D p L) (rootMap A p n g • c)
  rw [map_smul,← AlgHom.comp_apply, fieldMap_tensor]
  exact hx

end Lech.PerfectDomainStages
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFiniteFree
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
namespace Lech

 

theorem finite_free_factorization (A M : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (n : ℕ) (g : A), g ≠ 0 ∧
      ∃ (u : (Fin n → A) →ₗ[A] M) (v : M →ₗ[A] (Fin n → A)),
        u.comp v = g • LinearMap.id ∧ v.comp u = g • LinearMap.id := by
  let := Module.finitePresentation_of_finite A M
  let K := FractionRing A
  let MK := LocalizedModule A⁰ M
  let f : M →ₗ[A] MK := LocalizedModule.mkLinearMap A⁰ M
  let n := Module.finrank K MK
  let e : MK ≃ₗ[A] (Fin n → K) := (Module.finBasis K MK).equivFun.restrictScalars A
  let j : (Fin n → A) →ₗ[A] (Fin n → K) :=
    LinearMap.pi fun i => (Algebra.linearMap A K).comp (LinearMap.proj i)
  have : IsLocalizedModule A⁰ j := by dsimp [j]; infer_instance
  obtain ⟨v,s,hv⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule A⁰ j
    (e.toLinearMap.comp f)
  obtain ⟨u,t,hu⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule A⁰ f
    (e.symm.toLinearMap.comp j)
  have huv : f.comp (u.comp v) = f.comp (((t:A)*(s:A)) • LinearMap.id) := by
    apply LinearMap.ext
    intro x
    have ht := LinearMap.congr_fun hu (v x)
    have hs := LinearMap.congr_fun hv x
    change f (u (v x)) = (t:A) • e.symm (j (v x)) at ht
    change j (v x) = (s:A) • e (f x) at hs
    change f (u (v x)) = f (((t:A)*(s:A)) • x)
    rw [ht,hs,map_smul,e.symm_apply_apply,map_smul,mul_smul]
  have hvu : j.comp (v.comp u) = j.comp (((t:A)*(s:A)) • LinearMap.id) := by
    apply LinearMap.ext
    intro x
    have ht := LinearMap.congr_fun hu x
    have hs := LinearMap.congr_fun hv (u x)
    change f (u x) = (t:A) • e.symm (j x) at ht
    change j (v (u x)) = (s:A) • e (f (u x)) at hs
    change j (v (u x)) = j (((t:A)*(s:A)) • x)
    rw [hs,ht,map_smul,e.apply_symm_apply,map_smul,mul_smul,smul_comm]
  obtain ⟨a,ha⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule A⁰ f
    (u.comp v) (((t:A)*(s:A)) • LinearMap.id) huv
  obtain ⟨b,hb⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule A⁰ j
    (v.comp u) (((t:A)*(s:A)) • LinearMap.id) hvu
  refine ⟨n,(a:A)*(b:A)*((t:A)*(s:A)),?_, ((a:A)*(b:A)) • u,v,?_,?_⟩
  · exact mul_ne_zero (mul_ne_zero (nonZeroDivisors.coe_ne_zero a)
      (nonZeroDivisors.coe_ne_zero b))
      (mul_ne_zero (nonZeroDivisors.coe_ne_zero t) (nonZeroDivisors.coe_ne_zero s))
  · rw [LinearMap.smul_comp, mul_comm (a:A) (b:A),mul_smul]
    change (b:A) • ((a:A) • u.comp v) = _
    rw [show (a:A) • u.comp v = (a:A) • (((t:A)*(s:A)) • LinearMap.id) from ha]
    simp only [smul_smul]
    congr 1
    ring
  · rw [LinearMap.comp_smul,mul_smul]
    change (a:A) • ((b:A) • v.comp u) = _
    rw [show (b:A) • v.comp u = (b:A) • (((t:A)*(s:A)) • LinearMap.id) from hb]
    simp only [smul_smul]
    congr 1
    ring

end Lech


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors

open scoped nonZeroDivisors
namespace Lech.RootTower

lemma flat_colon_membership {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (a b : R) (c d : S)
    (h : f a * c = f b * d) :
    c ∈ ((Ideal.span ({b} : Set R)).colon {a}).map f := by
  classical
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hf
  have hh : ∑ i : Fin 2, (![a,-b] i) • (![c,d] i) = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_neg, neg_mul]
    simpa only [sub_eq_add_neg] using sub_eq_zero.mpr h
  obtain ⟨k,u,v,hu,hr⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := S) hh
  rw [show c = ∑ j, u 0 j • v j from hu 0]
  apply Ideal.sum_mem
  intro j _
  have hj : u 0 j ∈ (Ideal.span ({b} : Set R)).colon {a} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton]
    have hj := hr j
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul] at hj
    refine ⟨u 1 j, ?_⟩
    have he : a * u 0 j = b * u 1 j := sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hj)
    simpa only [mul_comm] using he
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem f hj)

lemma Frobenius_map_le_pow {R : Type*} [CommRing R] (p n : ℕ) [Fact p.Prime]
    [CharP R p] (I : Ideal R) :
    I.map (iterateFrobenius R p n) ≤ I ^ (p^n) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change iterateFrobenius R p n x ∈ I ^ (p^n)
  rw [iterateFrobenius_def]
  exact Ideal.pow_mem_pow hx _

lemma integral_uniform_denominator {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] {x : K} (hx : IsIntegral R x) :
    ∃ c : R, c ≠ 0 ∧ ∀ n : ℕ, IsLocalization.IsInteger R (c • x^n) := by
  obtain ⟨s,hs⟩ := hx.fg_adjoin_singleton
  obtain ⟨c,hc⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors R) s
  refine ⟨c, nonZeroDivisors.coe_ne_zero c, fun n => ?_⟩
  have hn : x^n ∈ Submodule.span R (s : Set K) := by
    rw [hs]
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin rfl) n
  have hall : ∀ y ∈ Submodule.span R (s : Set K),
      IsLocalization.IsInteger R ((c : R) • y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simpa using (IsLocalization.isInteger_zero (R := R) (S := K))
    | add y z _ _ hy hz => simpa [smul_add] using IsLocalization.isInteger_add hy hz
    | smul a y _ hy =>
        rw [smul_comm]
        exact IsLocalization.isInteger_smul hy
  exact hall _ hn

 

theorem isIntegrallyClosed_of_flat_frobenius (R : Type*) [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hf : ∀ n, (iterateFrobenius R p n).Flat) : IsIntegrallyClosed R := by
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  intro x hx
  obtain ⟨c,hc,hcx⟩ := integral_uniform_denominator hx
  obtain ⟨b,a,ha⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) x
  by_contra hn
  let J := (Ideal.span ({(b : R)} : Set R)).colon {a}
  have hJ : J ≠ ⊤ := by
    intro hJ
    have haJ : a ∈ Ideal.span ({(b : R)} : Set R) := by
      have h1 : (1 : R) ∈ J := hJ ▸ (show (1 : R) ∈ (⊤ : Ideal R) from trivial)
      simpa [J, Submodule.mem_colon_singleton] using h1
    obtain ⟨y,hy⟩ := Ideal.mem_span_singleton.mp haJ
    apply hn
    refine ⟨y, ?_⟩
    apply mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property)
    rw [← map_mul, ← hy]
    simpa only [Algebra.smul_def] using ha
  have hcpow (n : ℕ) : c ∈ J ^ (p^n) := by
    obtain ⟨d,hd⟩ := hcx (p^n)
    simp only [Algebra.smul_def] at hd
    have he : (iterateFrobenius R p n) a * c =
        (iterateFrobenius R p n) (b : R) * d := by
      apply IsFractionRing.injective R (FractionRing R)
      simp only [map_mul, iterateFrobenius_def, map_pow]
      change (algebraMap R (FractionRing R) a)^(p^n) * algebraMap R (FractionRing R) c = _
      rw [ha]
      simp only [Algebra.smul_def, mul_pow]
      rw [mul_assoc, mul_comm (x^(p^n)), ← hd]
    exact Frobenius_map_le_pow p n J
      (flat_colon_membership (iterateFrobenius R p n) (hf n) a b c d he)
  apply hc
  apply (Ideal.mem_bot.mp : c ∈ (⊥ : Ideal R) → c = 0)
  rw [← J.iInf_pow_eq_bot_of_isDomain hJ]
  apply Ideal.mem_iInf.mpr
  intro n
  exact Ideal.pow_le_pow_right (by
    exact Nat.le_of_lt (Nat.lt_pow_self (Nat.Prime.one_lt Fact.out))) (hcpow n)

end Lech.RootTower


namespace Lech.PowerSeries
open MvPowerSeries
variable {σ R : Type*} [Fintype σ] [CommRing R]

lemma pick_zero : pick (0 : σ →₀ ℕ) = none := by simp [pick]
lemma pick_positive {d : σ →₀ ℕ} {i : σ} (hi : pick d = some i) : 0 < d i := by
  classical
  by_cases hd : d = 0
  · subst d; simp [pick] at hi
  · have hc : Classical.choose (exists_positive hd) = i := by
      exact Option.some.inj (by simpa only [pick,dite_eq_right hd] using hi)
    rw [← hc]
    exact Classical.choose_spec (exists_positive hd)

lemma exists_pick {d : σ →₀ ℕ} (hd : d ≠ 0) : ∃ i, pick d = some i := by
  simp [pick,hd]

lemma coeff_divide_X (f : MvPowerSeries σ R) (i : σ) (d : σ →₀ ℕ) :
    coeff d (divide f i * X i) = if pick d = some i then coeff d f else 0 := by
  classical
  rw [X,coeff_mul_monomial]
  by_cases hle : Finsupp.single i 1 ≤ d
  · rw [ite_eq_left hle]
    simp only [mul_one]
    change (if pick (d - Finsupp.single i 1 + Finsupp.single i 1) = some i then
      coeff (d - Finsupp.single i 1 + Finsupp.single i 1) f else 0) = _
    rw [tsub_add_cancel_of_le hle]
  · rw [ite_eq_right hle]
    have hp : pick d ≠ some i := by
      intro hc
      apply hle
      intro j
      by_cases hji : j = i
      · subst j; simpa using (Nat.succ_le_iff.mpr (pick_positive hc))
      · simp [hji]
    simp [hp]

 

lemma sum_divide_X (f : MvPowerSeries σ R) :
    ∑ i, divide f i * X i = f - C (constantCoeff f) := by
  classical
  ext d
  simp only [map_sum,coeff_divide_X,map_sub]
  by_cases hd : d = 0
  · subst d
    simp [pick_zero]
  · obtain ⟨i,hi⟩ := exists_pick hd
    rw [Finset.sum_eq_single i]
    · simp [hi,coeff_C,hd]
    · intro j _ hji
      simp [hi,Ne.symm hji]
    · simp

lemma variables_eq_ker_constantCoeff :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) = RingHom.ker constantCoeff := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  · intro f hf
    have hc : constantCoeff f = 0 := hf
    have h := sum_divide_X f
    rw [hc,map_zero,sub_zero] at h
    rw [← h]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))

variable {k : Type*} [Field k]
lemma maximalIdeal_eq_variables :
    IsLocalRing.maximalIdeal (MvPowerSeries σ k) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ k)) := by
  rw [variables_eq_ker_constantCoeff]
  ext f
  simp only [IsLocalRing.mem_maximalIdeal,RingHom.mem_ker,mem_nonunits_iff,isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero,not_not]

end Lech.PowerSeries


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLengthLe
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors

open scoped BigOperators


namespace Lech.RootTower
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

lemma perfectClosure_flat : (PerfectClosure.of (MvPowerSeries σ k) p).Flat := by
  let A := MvPowerSeries σ k
  have hf : (algebraMap (rootRing A p 0) (PerfectClosure A p)).Flat := by
    apply RingHom.flat_algebraMap_iff.mpr
    exact (regularTower σ k p).flat_limit 0
  have h := (RingHom.Flat.of_bijective (rootEquiv A p 0).bijective).comp hf
  have he : (algebraMap (rootRing A p 0) (PerfectClosure A p)).comp
      (rootEquiv A p 0).toRingHom = PerfectClosure.of A p := by
    apply DFunLike.ext
    intro a
    rfl
  change ((algebraMap (rootRing A p 0) (PerfectClosure A p)).comp
    (rootEquiv A p 0).toRingHom).Flat at h
  rwa [he] at h
end Lech.RootTower


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusIntermediatePowerMap
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct


namespace Lech.SeparableOrder
variable (A D K L : Type*) [CommRing A] [CommRing D] [IsDomain D]
  [Field K] [Field L] [Algebra A D] [Algebra A K] [Algebra A L]
  [Algebra K L] [Algebra D L] [IsScalarTower A K L] [IsScalarTower A D L]



omit [IsDomain D] in
lemma toField_injective [IsFractionRing D L] : Function.Injective (toField A D K L) := by
  intro x y h
  apply Subtype.ext
  exact IsFractionRing.injective D L (congrArg Subtype.val h)

instance orderFieldFaithful [IsFractionRing D L] :
    FaithfulSMul (order A D K L) (separableClosure K L) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (toField_injective A D K L)


variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [FiniteDimensional K L]

omit [IsDomain D] in
 

lemma uniform_power : ∃ n : ℕ, ∀ x : D, x^(p^n) ∈ order A D K L := by
  let E := separableClosure K L
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  let : IsPurelyInseparable E L := separableClosure.isPurelyInseparable K L
  let : CharP E p := (Algebra.charP_iff K E p).mp inferInstance
  refine ⟨IsPurelyInseparable.exponent E L,fun x => ?_⟩
  change IsSeparable K (algebraMap D L (x^_))
  rw [map_pow]
  obtain ⟨y,hy⟩ := IsPurelyInseparable.exponent_def' E p (algebraMap D L x)
  rw [← hy]
  exact y.2

 

instance orderFraction [IsFractionRing D L] :
    IsFractionRing (order A D K L) (separableClosure K L) := by
  obtain ⟨n,hn⟩ := uniform_power A D K L p
  have hq : 0 < p^n := pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective D (z : L)
  have hb0 : algebraMap D L b ≠ 0 :=
    (map_ne_zero_iff (algebraMap D L) (IsFractionRing.injective D L)).mpr
      (nonZeroDivisors.coe_ne_zero ⟨b,hb⟩)
  have hid : algebraMap D L (a*b^(p^n-1)) = (z : L) * algebraMap D L (b^(p^n)) := by
    rw [← hab, map_mul, map_pow, map_pow]
    rw [← Nat.sub_add_cancel hq, pow_succ]
    field_simp
    simp only [Nat.sub_add_cancel hq]
  have ha : a*b^(p^n-1) ∈ order A D K L := by
    change IsSeparable K (algebraMap D L (a*b^(p^n-1)))
    rw [hid]
    exact Field.isSeparable_mul z.2 (hn b)
  refine ⟨⟨a*b^(p^n-1),ha⟩, ⟨b^(p^n),hn b⟩, ?_⟩
  apply Subtype.ext
  change (z : L) = algebraMap D L (a*b^(p^n-1)) / algebraMap D L (b^(p^n))
  rw [hid, mul_div_cancel_right₀]
  rw [map_pow]
  exact pow_ne_zero _ hb0

end Lech.SeparableOrder


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerNormalizedLength
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct


namespace Lech
open scoped TensorProduct
variable {A P M N : Type*} [CommRing A] [CommRing P] [Algebra A P]
  [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
lemma baseChange_scalar_factorization (u : M →ₗ[A] N) (v : N →ₗ[A] M)
    (b : A) (hb : u.comp v = b • LinearMap.id) :
    (u.baseChange P).comp (v.baseChange P) = (algebraMap A P b) • LinearMap.id := by
  rw [← LinearMap.baseChange_comp,hb,LinearMap.baseChange_smul,LinearMap.baseChange_id]
  apply LinearMap.ext
  intro x
  change b • x = (algebraMap A P b) • x
  exact (algebraMap_smul P b x).symm
end Lech


namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

 

theorem exists_root_finite_free_factorization
    (hi : ∀ n, Function.Injective (tensorMap A D p n))
    (hg : ∃ g : A, g ≠ 0 ∧ ∀ n c, rootMap A p n g • c ∈ stage A D p n) :
    ∃ (r : ℕ) (a : A), a ≠ 0 ∧ ∀ n : ℕ,
      ∃ (u : (Fin r → PerfectClosure A p) →ₗ[PerfectClosure A p] PerfectClosure D p)
        (v : PerfectClosure D p →ₗ[PerfectClosure A p] (Fin r → PerfectClosure A p)),
        u.comp v = rootMap A p n a • LinearMap.id := by
  classical
  obtain ⟨g,hgn,hgc⟩ := hg
  obtain ⟨r,b,hbn,u,v,huv,_⟩ := Lech.finite_free_factorization A D
  refine ⟨r,b*g,mul_ne_zero hbn hgn,fun n => ?_⟩
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let : Algebra A P := (rootMap A p n).toAlgebra
  let B := stage A D p n
  let e := (tensorEquiv A D p n (hi n)).toLinearEquiv
  let q := ((Pi.basisFun A (Fin r)).baseChange P).equivFun
  let c : C →ₗ[P] B := (Lech.Conductor.linearMap B (rootMap A p n g) (hgc n)).restrictScalars P
  let j : B →ₗ[P] C := B.val.toLinearMap
  let U := j.comp (e.toLinearMap.comp ((u.baseChange P).comp q.symm.toLinearMap))
  let V := q.toLinearMap.comp ((v.baseChange P).comp (e.symm.toLinearMap.comp c))
  refine ⟨U,V,?_⟩
  have hvu := Lech.baseChange_scalar_factorization (P := P) u v b huv
  apply LinearMap.ext
  intro x
  change j (e ((u.baseChange P) (q.symm (q ((v.baseChange P) (e.symm (c x))))))) =
    rootMap A p n (b*g) • x
  rw [q.symm_apply_apply]
  have hh := LinearMap.congr_fun hvu (e.symm (c x))
  change (u.baseChange P) ((v.baseChange P) (e.symm (c x))) =
    rootMap A p n b • e.symm (c x) at hh
  rw [hh,map_smul,e.apply_symm_apply,map_smul]
  change rootMap A p n b • (rootMap A p n g • x) = _
  rw [← mul_smul,← map_mul]
end Lech.PerfectDomainStages

open scoped Classical Pointwise
namespace Lech.PowerSeries
open MvPowerSeries RingTheory.Sequence
variable (k : Type*) [Field k]

lemma killSucc_surjective (h : ℕ) :
    Function.Surjective (killCompl (R := k) (Fin.succEmb h)) := by
  intro f
  exact ⟨rename (Fin.succEmb h) f,killCompl_rename_app _⟩

lemma killSucc_ker (h : ℕ) :
    RingHom.ker (killCompl (R := k) (Fin.succEmb h)).toRingHom =
      Ideal.span {(X (0 : Fin (h+1)) : MvPowerSeries (Fin (h+1)) k)} := by
  apply le_antisymm
  · intro f hf
    apply Ideal.mem_span_singleton.mpr
    apply X_dvd_iff.mpr
    intro d hd
    have he : d ∈ Set.range (Finsupp.embDomain (Fin.succEmb h)) := by
      rw [Finsupp.mem_range_embDomain_iff]
      intro i hi
      have hn : i ≠ 0 := by
        intro hz
        subst i
        exact (Finsupp.mem_support_iff.mp hi) hd
      exact ⟨i.pred hn,Fin.succ_pred i hn⟩
    obtain ⟨a,rfl⟩ := he
    have hx := congrArg (coeff a) hf
    exact hx
  · rw [Ideal.span_singleton_le_iff_mem]
    apply killCompl_X_eq_zero
    rintro ⟨i,hi⟩
    exact Fin.succ_ne_zero i hi

lemma variables_weaklyRegular (h : ℕ) :
    IsWeaklyRegular (MvPowerSeries (Fin h) k)
      (List.ofFn (X : Fin h → MvPowerSeries (Fin h) k)) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [List.ofFn_succ,isWeaklyRegular_cons_iff]
    constructor
    · apply IsSMulRegular.of_ne_zero
      intro hz
      have hx := congrArg (coeff (Finsupp.single 0 1)) hz
      simp at hx
    · let A := MvPowerSeries (Fin (h+1)) k
      let B := MvPowerSeries (Fin h) k
      let f : A →+* B := (killCompl (R := k) (Fin.succEmb h)).toRingHom
      let : Algebra A B := f.toAlgebra
      let q : A →ₗ[A] B := Algebra.linearMap A B
      have hker : q.ker = (X (0 : Fin (h+1)) : A) • (⊤ : Submodule A A) := by
        change RingHom.ker f = _
        rw [killSucc_ker]
        rw [← Submodule.ideal_span_singleton_smul]
        exact (Ideal.mul_top _).symm
      let e : QuotSMulTop (X (0 : Fin (h+1)) : A) A ≃ₗ[A] B :=
        (Submodule.quotEquivOfEq _ _ hker.symm).trans
          (q.quotKerEquivOfSurjective (killSucc_surjective k h))
      apply (e.isWeaklyRegular_congr _).mpr
      apply (isWeaklyRegular_map_algebraMap_iff B B _).mp
      have hm : (List.ofFn (fun i : Fin h => (X i.succ : A))).map (algebraMap A B) =
          List.ofFn (X : Fin h → B) := by
        rw [List.map_ofFn]
        congr 1
        funext i
        exact killCompl_X (e := Fin.succEmb h) i
      rw [hm]
      exact ih
end Lech.PowerSeries
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFlatVariables
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise


namespace Lech
open RingTheory.Sequence
open scoped TensorProduct
lemma weaklyRegular_map_of_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (zs : List R) (h : IsWeaklyRegular R zs) :
    IsWeaklyRegular S (zs.map f) := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hf
  apply (isWeaklyRegular_map_algebraMap_iff S S zs).mpr
  exact ((TensorProduct.lid R S).isWeaklyRegular_congr zs).mp
    (h.isWeaklyRegular_rTensor (M₂ := S))
end Lech


namespace Lech.PowerSeries
open RingTheory.Sequence
variable (h : ℕ) (k : Type*) [Field k]
lemma variables_pow_weaklyRegular (a : ℕ) (ha : a ≠ 0) :
    IsWeaklyRegular (MvPowerSeries (Fin h) k)
      (List.ofFn (fun i : Fin h => (MvPowerSeries.X i : MvPowerSeries (Fin h) k)^a)) := by
  let : NeZero a := ⟨ha⟩
  have hh := Lech.weaklyRegular_map_of_flat
    (MvPowerSeries.expand (σ := Fin h) (R := k) a ha).toRingHom
    (RootTower.expansion_flat a) _ (variables_weaklyRegular k h)
  simpa only [List.map_ofFn,Function.comp_def,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,MvPowerSeries.expand_X] using hh

lemma perfect_free_variables_pow_weaklyRegular (p : ℕ) [Fact p.Prime]
    [CharP k p] [PerfectRing k p] (r a : ℕ) (ha : a ≠ 0) :
    IsWeaklyRegular (Fin r → PerfectClosure (MvPowerSeries (Fin h) k) p)
      ((List.ofFn (fun i : Fin h => (MvPowerSeries.X i : MvPowerSeries (Fin h) k)^a)).map
        (PerfectClosure.of (MvPowerSeries (Fin h) k) p)) := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let : Algebra A P := (PerfectClosure.of A p).toAlgebra
  have : Module.Flat A P := (RingHom.flat_algebraMap_iff).mp (RootTower.perfectClosure_flat (Fin h) k p)
  have : Module.Flat A (Fin r → P) := Module.Flat.trans A P (Fin r → P)
  apply (isWeaklyRegular_map_algebraMap_iff P (Fin r → P) _).mpr
  exact ((TensorProduct.lid A (Fin r → P)).isWeaklyRegular_congr _).mp
    ((variables_pow_weaklyRegular h k a ha).isWeaklyRegular_rTensor (M₂ := Fin r → P))
end Lech.PowerSeries

open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex

open scoped ENNReal ZeroObject

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex











open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian






















namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open RingTheory.Sequence
universe u v
variable {R : Type u} [CommRing R]

lemma cone_homology_zero_of_mono {C : Type*} [Category C] [Abelian C]
    {F G : CochainComplex C ℤ}
    (f : F ⟶ G) (i : ℤ) (hG : IsZero (G.homology i))
    [Mono (homologyMap f (i+1))] : IsZero ((mappingCone f).homology i) := by
  have hfmono : Mono (homologyMap f (i+1)) := inferInstance
  let Q := HomotopyCategory.homologyFunctor C (.up ℤ) i
  let T := mappingCone.triangleh f
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished f
  let e := HomotopyCategory.homologyFunctorFactors C (.up ℤ) i
  let e' := (HomotopyCategory.homologyFunctor C (.up ℤ) 0).shiftIso
    1 i (i+1) (by omega)
  let e'' := HomotopyCategory.homologyFunctorFactors C (.up ℤ) (i+1)
  have hm : Mono (Q.map ((CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).map T.mor₁)) := by
    have hm' : Mono ((HomotopyCategory.homologyFunctor C (.up ℤ)
        (i+1)).map T.mor₁) := by
      have hh := e''.hom.naturality f
      have : Mono ((e''.hom.app F) ≫ homologyMap f (i+1)) :=
        mono_comp' (inferInstance : Mono (e''.hom.app F)) hfmono
      change Mono (e''.hom.app F ≫ (homologyFunctor C (.up ℤ) (i+1)).map f) at this
      rw [← hh] at this
      change Mono ((HomotopyCategory.homologyFunctor C (.up ℤ) (i+1)).map T.mor₁ ≫
        e''.hom.app G) at this
      exact mono_of_mono _ (e''.hom.app G)
    have : Mono (((e'.hom.app T.obj₁) ≫
        (HomotopyCategory.homologyFunctor C (.up ℤ) (i+1)).map T.mor₁)) :=
      mono_comp' (inferInstance : Mono (e'.hom.app T.obj₁)) hm'
    change Mono (e'.hom.app T.obj₁ ≫
      ((HomotopyCategory.homologyFunctor C (.up ℤ) 0).shift (i+1)).map T.mor₁) at this
    rw [← e'.hom.naturality T.mor₁] at this
    change Mono (Q.map ((CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).map T.mor₁) ≫
      e'.hom.app T.obj₂) at this
    exact mono_of_mono (Q.map ((CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).map T.mor₁))
      (e'.hom.app T.obj₂)
  have hex := Q.map_distinguished_exact T.rotate (Pretriangulated.rot_of_distTriang T hT)
  have hmneg : Mono (Q.map (-((CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).map T.mor₁))) := by
    rw [Functor.map_neg]
    infer_instance
  have hz3 : Q.map T.mor₃ = 0 := by
    apply (cancel_mono (Q.map (-((CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).map T.mor₁)))).mp
    rw [zero_comp]
    have hw := ((Pretriangulated.shortComplexOfDistTriangle T.rotate.rotate
      (Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang T hT))).map Q).zero
    exact hw
  have hzG : IsZero (Q.obj T.obj₂) := hG.of_iso (e.app G)
  have hz := hex.isZero_X₂ (hzG.eq_zero_of_src _) hz3
  exact hz.of_iso (e.app (mappingCone f)).symm

lemma tensor_single_homology_zero_of_regular (M : ModuleCat.{v} R) (zs : List R)
    (hreg : IsWeaklyRegular M zs.reverse) (i : ℤ) (hi : i < 0) :
    IsZero ((tensor zs (singleModule M)).homology i) := by
  induction zs generalizing i with
  | nil =>
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact isZero_single_obj_X (.up ℤ) 0 M i (by omega)
  | cons a zs ih =>
    rw [List.reverse_cons,isWeaklyRegular_append_iff,isWeaklyRegular_singleton_iff] at hreg
    have hreg' := hreg.1
    let F := tensor zs (singleModule M)
    have hm : Mono (homologyMap (a • 𝟙 F) (i+1)) := by
      rw [homologyMap_smul,homologyMap_id]
      by_cases hz : i+1 = 0
      · rw [hz]
        apply (ModuleCat.mono_iff_injective _).mpr
        let e := (singleTensorHomologyZeroIso M zs).toLinearEquiv
        have hh : IsSMulRegular (M ⧸ (entryIdeal zs • (⊤ : Submodule R M))) a := by
          have heq : Ideal.ofList zs.reverse = entryIdeal zs := by
            simp [entryIdeal,Ideal.ofList,List.mem_reverse]
          rw [heq] at hreg
          exact hreg.2
        intro x y hxy
        apply e.injective
        apply hh
        change a • x = a • y at hxy
        simpa only [map_smul] using congrArg e hxy
      · have hzero : IsZero (F.homology (i+1)) := ih hreg' (i+1) (by omega)
        exact hzero.mono _
    exact cone_homology_zero_of_mono (a • 𝟙 F) i (ih hreg' i hi)
end Lech.Koszul
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulConeFunctor
attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u v
variable {R : Type u} [CommRing R]

lemma scalar_homology_zero_of_factorization (zs : List R) (M N : ModuleCat.{v} R)
    (u : N ⟶ M) (v : M ⟶ N) (a : R) (ha : v ≫ u = a • 𝟙 M)
    (i : ℤ) (hN : IsZero ((tensor zs (singleModule N)).homology i)) :
    a • 𝟙 ((tensor zs (singleModule M)).homology i) = 0 := by
  let K := single (ModuleCat.{v} R) (.up ℤ) (0 : ℤ) ⋙ tensorFunctor zs
  have hNK : IsZero ((K.obj N).homology i) := hN
  have he : homologyMap (K.map (v ≫ u)) i = 0 := by
    rw [K.map_comp,homologyMap_comp]
    rw [hNK.eq_zero_of_tgt (homologyMap (K.map v) i),zero_comp]
  rw [ha,K.map_smul,K.map_id,homologyMap_smul,homologyMap_id] at he
  exact he

lemma scalar_smul_homology_zero_of_factorization
    (zs : List R) (M : Type u) [AddCommGroup M] [Module R M]
    (r : ℕ) (u : (Fin r → R) →ₗ[R] M) (v : M →ₗ[R] (Fin r → R))
    (a : R) (ha : u.comp v = a • LinearMap.id)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (Fin r → R) zs.reverse)
    (i : ℤ) (hi : i < 0) (x : (tensor zs (singleModule (ModuleCat.of R M))).homology i) :
    a • x = 0 := by
  have he : (ModuleCat.ofHom v) ≫ (ModuleCat.ofHom u) =
      a • 𝟙 (ModuleCat.of R M) := by
    apply ModuleCat.hom_ext
    exact ha
  have hh := scalar_homology_zero_of_factorization zs (ModuleCat.of R M)
    (ModuleCat.of R (Fin r → R)) (ModuleCat.ofHom u) (ModuleCat.ofHom v) a he i
      (tensor_single_homology_zero_of_regular _ zs hreg i hi)
  exact congrArg (fun f => f x) hh
end Lech.Koszul


namespace Lech.PerfectDomainStages
open Lech.RootTower Lech.Koszul
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]

local instance instIsDomainMvPowerSeriesFin_solutions_1 : IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _

include K L in
 

theorem normalizedLength_regular_koszul (ys : List (MvPowerSeries (Fin h) k))
    (hys : (entryIdeal ys).radical = IsLocalRing.maximalIdeal (MvPowerSeries (Fin h) k))
    (hreg : ∀ r : ℕ, RingTheory.Sequence.IsWeaklyRegular
      (Fin r → PerfectClosure (MvPowerSeries (Fin h) k) p)
      (ys.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p)))
    (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((tensor ((ys.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p)).reverse)
        (singleModule (ModuleCat.of (PerfectClosure (MvPowerSeries (Fin h) k) p)
          (PerfectClosure D p)))).homology i) = 0 := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let zs : List P := (ys.map (PerfectClosure.of A p)).reverse
  let F := singleModule (ModuleCat.of P C)
  have hflat := perfectClosure_flat (Fin h) k p
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_flat_frobenius A p
    (fun n => iterateFrobenius_flat (σ := Fin h) (R := k) p n)
  have hinj (n : ℕ) := tensorMap_injective A D p L K hflat n
  obtain ⟨g,hg,hgc⟩ := exists_conductor A D p L K
  obtain ⟨r,a,ha,hfac⟩ := exists_root_finite_free_factorization A D p hinj ⟨g,hg,hgc⟩
  apply normalizedLength_eq_zero_of_root_annihilated h k p
    ((tensor zs F).homology i) (entryIdeal ys) hys ha
  · have hvars : (entryIdeal ys).map (PerfectClosure.of A p) ≤ entryIdeal zs := by
      rw [entryIdeal, Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro _ ⟨y,hy,rfl⟩
      apply Ideal.subset_span
      change PerfectClosure.of A p y ∈ zs
      simp only [zs,List.mem_reverse,List.mem_map]
      exact ⟨y,hy,rfl⟩
    intro b hb x
    exact Module.mem_annihilator.mp
      (tensor_homology_annihilator zs F i (hvars (Ideal.mem_map_of_mem _ hb))) x
  · intro n x
    obtain ⟨u,v,huv⟩ := hfac n
    apply scalar_smul_homology_zero_of_factorization zs C r u v (rootMap A p n a) huv _ i hi x
    simpa only [zs,List.reverse_reverse] using hreg r

include K L in
 

theorem normalizedLength_coordinate_power_koszul (a : ℕ) (ha : a ≠ 0)
    (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((tensor (((List.ofFn (fun j : Fin h =>
          (MvPowerSeries.X j : MvPowerSeries (Fin h) k)^a)).map
          (PerfectClosure.of (MvPowerSeries (Fin h) k) p)).reverse)
        (singleModule (ModuleCat.of (PerfectClosure (MvPowerSeries (Fin h) k) p)
          (PerfectClosure D p)))).homology i) = 0 := by
  apply normalizedLength_regular_koszul h k D p K L _ _
    (fun r => Lech.PowerSeries.perfect_free_variables_pow_weaklyRegular h k p r a ha) i hi
  let A := MvPowerSeries (Fin h) k
  have hm := Lech.PowerSeries.maximalIdeal_eq_variables (σ := Fin h) (k := k)
  apply le_antisymm
  · apply (IsLocalRing.maximalIdeal.isMaximal A).isPrime.isRadical.radical_le_iff.mpr
    apply Ideal.span_le.mpr
    intro x hx
    change x ∈ List.ofFn (fun j : Fin h => (MvPowerSeries.X j : A)^a) at hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    apply (IsLocalRing.maximalIdeal A).pow_mem_of_mem ?_ a (Nat.pos_of_ne_zero ha)
    rw [hm]
    exact Ideal.subset_span ⟨j,rfl⟩
  · rw [hm]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨a, Ideal.subset_span (by simp only [Set.mem_ofPred_eq,List.mem_ofFn]; exact ⟨j,rfl⟩)⟩

end Lech.PerfectDomainStages


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SeparableOrderNormalizedLength
attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul
open CategoryTheory CochainComplex HomologicalComplex
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]

local instance separableOrderCoordinatePowerSeriesIsDomain :
    IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _

include K L in
 

theorem normalizedLength_coordinate_power_koszul_oai (a : ℕ) (ha : a ≠ 0)
    (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((tensor (((List.ofFn (fun j : Fin h =>
          (MvPowerSeries.X j : MvPowerSeries (Fin h) k)^a)).map
          (PerfectClosure.of (MvPowerSeries (Fin h) k) p)).reverse)
        (singleModule (ModuleCat.of (PerfectClosure (MvPowerSeries (Fin h) k) p)
          (PerfectClosure D p)))).homology i) = 0 := by
  let A := MvPowerSeries (Fin h) k
  let B := order A D K L
  let E := separableClosure K L
  let : CharP B p := B.val.toRingHom.charP Subtype.val_injective p
  let : CharP E p := (algebraMap E L).charP (algebraMap E L).injective p
  let P := PerfectClosure A p
  let ys : List P := ((List.ofFn (fun j : Fin h => (MvPowerSeries.X j : A)^a)).map
    (PerfectClosure.of A p)).reverse
  obtain ⟨e,he⟩ := uniform_power A D K L p
  let eqv := perfectAlgEquiv p B.val Subtype.val_injective
    ⟨e,fun d => ⟨⟨d^(p^e),he d⟩,rfl⟩⟩
  let eqh := (homologyFunctor (ModuleCat P) (.up ℤ) i).mapIso
    ((tensorFunctor ys).mapIso ((single (ModuleCat P) (.up ℤ) 0).mapIso
      eqv.toLinearEquiv.toModuleIso))
  have hnorm := (regularTower (Fin h) k p).length_eq_of_equiv eqh.toLinearEquiv
  exact hnorm.symm.trans
    (Lech.PerfectDomainStages.normalizedLength_coordinate_power_koszul h k B p K E a ha i hi)
end Lech.SeparableOrder


end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.SeparableOrder.normalizedLength_coordinate_power_koszul_oai.{u} := @OAI.Lech.SeparableOrder.normalizedLength_coordinate_power_koszul_oai.{u}
