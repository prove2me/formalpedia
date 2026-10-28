-- Prove2me | solution 1 for OAI.Lech.PerfectDomainStages.frobenius_homology_conductor_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:24:14.957865+00:00
-- url     : https://prove2.me/submissions/86259b6b-1299-4298-931e-070f83efef2c

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L023
import Theorems.Thm_OAI_Lech_PerfectDomainStages_normalizedLength_stage_homology
import Theorems.Thm_OAI_Lech_PerfectDomainStages_normalizedLength_stage_scalar_quotient_homology
import Theorems.Thm_OAI_Lech_SeparableOrder_normalizedLength_perfection_shortComplex_homology
import Theorems.Thm_OAI_Lech_frobenius_shortComplex_homology_finiteLength

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
-- module Solutions.OAIQ032_LECH.Multiplicity_PerfectDomainStagesTensorTo
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
namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

lemma rootToStage_scalar (n : ℕ) (g : A) :
    rootToStage A D p n (algebraMap A D g) =
      algebraMap (PerfectClosure A p) (stage A D p n) (rootMap A p n g) := by
  apply Subtype.ext
  exact (perfectMap_root p (algebraMap A D) n g).symm

end Lech.PerfectDomainStages


namespace Lech.NormalizedLength.Tower
variable {L : Type*} [CommRing L] (T : Tower L)
variable {M N P : Type*} [AddCommGroup M] [Module L M]
  [AddCommGroup N] [Module L N] [AddCommGroup P] [Module L P]

 

lemma length_kernel_eq_cokernel (f : M →ₗ[L] M) (hM : T.length M ≠ ⊤) :
    T.length f.ker = T.length (M ⧸ f.range) := by
  have h₁ := T.length_eq_add_of_exact f.rangeRestrict.ker.subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  have hk : f.rangeRestrict.ker = f.ker := by ext x; simp
  rw [hk] at h₁
  have h₂ := T.length_eq_add_of_exact f.range.subtype f.range.mkQ
    (Submodule.subtype_injective _) f.range.mkQ_surjective
    (LinearMap.exact_subtype_mkQ f.range)
  have hr : T.length f.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM (T.length_le_of_injective f.range.subtype
      (Submodule.subtype_injective _))
  exact (ENNReal.add_right_inj hr).mp ((add_comm _ _).trans (h₁.symm.trans h₂))

 

lemma length_torsion_subquotient_le (i : N →ₗ[L] M) (q : N →ₗ[L] P)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (g : L) (hg : ∀ x : P, g • x = 0) (hM : T.length M ≠ ⊤) :
    T.length P ≤ T.length (M ⧸ (LinearMap.lsmul L M g).range) := by
  let fN := LinearMap.lsmul L N g
  let fM := LinearMap.lsmul L M g
  have hqker : fN.range ≤ q.ker := by
    rintro x ⟨y,rfl⟩
    change q (g • y) = 0
    rw [map_smul,hg]
  let q' := fN.range.liftQ q hqker
  have hq' : Function.Surjective q' := by
    intro x
    obtain ⟨y,rfl⟩ := hq x
    exact ⟨fN.range.mkQ y,rfl⟩
  let i' : fN.ker →ₗ[L] fM.ker :=
    (i.comp fN.ker.subtype).codRestrict fM.ker (by
      intro x
      change g • i x = 0
      rw [← map_smul]
      simpa only [fN, LinearMap.lsmul_apply, map_zero] using congrArg i x.property)
  have hi' : Function.Injective i' := by
    intro x y h
    apply Subtype.ext
    apply hi
    exact congrArg Subtype.val h
  have hN : T.length N ≠ ⊤ :=
    ne_top_of_le_ne_top hM (T.length_le_of_injective i hi)
  calc
    T.length P ≤ T.length (N ⧸ fN.range) :=
      T.length_le_of_surjective q' hq'
    _ = T.length fN.ker := (T.length_kernel_eq_cokernel fN hN).symm
    _ ≤ T.length fM.ker := T.length_le_of_injective i' hi'
    _ = _ := T.length_kernel_eq_cokernel fM hM
end Lech.NormalizedLength.Tower


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorConductor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech.TensorConductor

section Conductor
variable {D R C : Type*} [CommRing D] [CommRing R] [CommRing C]
  [Algebra R C] [Algebra D C]
  (B : Subalgebra R C) (hf : ∀ d : D, algebraMap D C d ∈ B)

variable [Algebra D B] [IsScalarTower D B C]

variable (M : Type*) [AddCommGroup M] [Module D M]

lemma conductor_composition (g : R) (hg : ∀ c : C, g • c ∈ B) :
    (conductor (D := D) B M g hg).comp (inclusion (D := D) B M) = g • (LinearMap.id : B ⊗[D] M →ₗ[R] B ⊗[D] M) := by
  apply LinearMap.ext
  intro t
  induction t using OAI.tensorInductionOn with
  | tmul b m => rfl
  | add x y hx hy => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (·+·) hx hy

end Conductor
end Lech.TensorConductor

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
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma free_extendScalars (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Free R M] :
    Module.Free S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change Module.Free S (S ⊗[R] M)
  infer_instance

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarHomologyError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped Pointwise
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma scalarHomologyCokernelEmbedding_injective (g : R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x)) (i : ℤ) :
    Function.Injective (scalarHomologyCokernelEmbedding g F hg i) := by
  let e := (Submodule.quotEquivOfEq _ _ (scalarHomologyKer g F hg i).symm).trans
    (homologyMap (complexQuotientπ (Ideal.span {g}) F) i).hom.quotKerEquivRange
  intro x y hxy
  apply e.injective
  apply Subtype.ext
  exact hxy

lemma homology_kernel_killed_of_scalar_retract
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (u : F ⟶ G) (v : G ⟶ F)
    (g : R) (h : u ≫ v = g • 𝟙 F) (i : ℤ) :
    ∀ x : (homologyMap u i).hom.ker, g • x = 0 := by
  intro x
  apply Subtype.ext
  have heq := congrArg (fun f => homologyMap f i) h
  rw [homologyMap_comp,Koszul.homologyMap_smul,homologyMap_id] at heq
  have hx := congrArg (fun f => f x) heq
  change homologyMap v i (homologyMap u i x) = g • (x : F.homology i) at hx
  rw [x.property,map_zero] at hx
  exact hx.symm

lemma normalized_homology_length_le_of_scalar_retract (T : NormalizedLength.Tower R)
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (u : F ⟶ G) (v : G ⟶ F)
    (g : R) (h : u ≫ v = g • 𝟙 F) (i : ℤ)
    (hg : ∀ j,Function.Injective (fun x : F.X j => g • x))
    (hfin : T.length (F.homology i) ≠ ⊤) :
    T.length (F.homology i) ≤ T.length (G.homology i) +
      T.length ((((complexQuotient (Ideal.span {g}) (.up ℤ)).obj F).homology i)) := by
  let f := (homologyMap u i).hom
  have hk := T.length_torsion_subquotient_le f.ker.subtype (LinearMap.id : f.ker →ₗ[R] f.ker)
    f.ker.subtype_injective Function.surjective_id g
    (homology_kernel_killed_of_scalar_retract u v g h i) hfin
  have he := T.length_eq_add_of_exact f.rangeRestrict.ker.subtype f.rangeRestrict
    f.rangeRestrict.ker.subtype_injective f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  have hk' : f.rangeRestrict.ker = f.ker := by ext; simp
  rw [hk'] at he
  rw [he,add_comm]
  exact add_le_add (T.length_le_of_injective f.range.subtype f.range.subtype_injective)
    (hk.trans (T.length_le_of_injective (scalarHomologyCokernelEmbedding g F hg i)
      (scalarHomologyCokernelEmbedding_injective g F hg i)))
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ComplexConductor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech.TensorConductor
universe u
variable {D R C : Type u} [CommRing D] [CommRing R] [CommRing C]
  [Algebra R C] [Algebra D C]
  (B : Subalgebra R C) [Algebra D B] [IsScalarTower D B C]

lemma complex_conductor_composition (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (g : R) (hg : ∀ c : C,g • c∈B) :
    complexInclusion B F ≫ complexRetreat B F g hg = g • 𝟙 (stageComplex B F) := by
  have hc := IsScalarTower.algebraMap_eq D B C
  let fB := algebraMap D B
  let fC := algebraMap D C
  let : Algebra D B := fB.toAlgebra
  let : Algebra D C := fC.toAlgebra
  let : IsScalarTower D B C := IsScalarTower.of_algebraMap_eq' hc
  ext i : 1
  apply ModuleCat.hom_ext
  ext x
  change B ⊗[D] (F.X i) at x
  have he := LinearMap.congr_fun (conductor_composition (D := D) B (F.X i) g hg) x
  change conductor (D := D) B (F.X i) g hg (inclusion (D := D) B (F.X i) x) =
    (algebraMap R B g) • (x : B ⊗[D] (F.X i))
  simpa only [IsScalarTower.algebraMap_smul,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply] using he

lemma stage_homology_length_le (T : NormalizedLength.Tower R)
    (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (g : R) (hg : ∀ c : C,g • c∈B) (i : ℤ)
    (hinj : ∀ j,Function.Injective (fun x : (stageComplex B F).X j => g • x))
    (hfin : T.length ((stageComplex B F).homology i) ≠ ⊤) :
    T.length ((stageComplex B F).homology i) ≤
      T.length ((ambientComplex (R := R) (C := C) F).homology i) +
      T.length ((((Lech.complexQuotient (Ideal.span {g}) (.up ℤ)).obj
        (stageComplex B F)).homology i)) :=
  normalized_homology_length_le_of_scalar_retract T
    (complexInclusion B F) (complexRetreat B F g hg) g
    (complex_conductor_composition B F g hg) i hinj hfin
end Lech.TensorConductor

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarQuotientTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma free_scalar_injective [IsDomain R] (M : ModuleCat.{u} R) [Module.Free R M]
    (g : R) (hg : g ≠ 0) : Function.Injective (fun x : M => g • x) :=
  smul_right_injective M hg
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootStageQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]

attribute [local instance] OAI.Lech.PerfectDomainStages.rootStageQuotientPowerSeriesIsDomain
omit [IsLocalRing D] [IsNoetherianRing D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D] [PerfectRing k p] in
lemma rootStage_scalar_injective (n : ℕ) (a : MvPowerSeries (Fin h) k)
    (ha : algebraMap (MvPowerSeries (Fin h) k) D a ≠ 0)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hf : ∀ j,Module.Free D (F.X j)) :
    ∀ j,Function.Injective (fun x : ((rootStageFunctor h k D p n).obj F).X j =>
      rootMap (MvPowerSeries (Fin h) k) p n a • x) := by
  intro j
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let B := stage A D p n
  let f := rootToStage A D p n
  let M := (ModuleCat.extendScalars f).obj (F.X j)
  have := hf j
  have : Module.Free B M := free_extendScalars f (F.X j)
  have hn : f (algebraMap A D a) ≠ 0 := by
    intro hz
    apply ha
    apply rootMap_injective D p n
    have hh := congrArg (fun b : B => (b : PerfectClosure D p)) hz
    change rootMap D p n (algebraMap A D a) = 0 at hh
    simpa only [map_zero] using hh
  have hi := free_scalar_injective M (f (algebraMap A D a)) hn
  rw [rootToStage_scalar] at hi
  exact hi

end Lech.PerfectDomainStages

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RobertsSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped TensorProduct ENNReal Topology
namespace Lech.PerfectDomainStages
open Lech.RootTower Lech.Koszul
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]
local instance robertsSeparablePowerSeriesIsDomain : IsDomain (MvPowerSeries (Fin h) k) :=
  NoZeroDivisors.to_isDomain _

include K L in
lemma frobenius_homology_conductor_bound_oai
    (hdim : dimension D = h)
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F) :
    ∃ a : D, a ≠ 0 ∧ ∀ n i, i < 0 →
      Module.length D ((frobeniusComplex D p n F).homology i) ≤
        Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
          (frobeniusComplex D p n F)).homology i) := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let T := regularTower (Fin h) k p
  have hflat := perfectClosure_flat (Fin h) k p
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_flat_frobenius A p
    (fun n => iterateFrobenius_flat (σ := Fin h) (R := k) p n)
  have hAD : Function.Injective (algebraMap A D) := by
    apply Function.Injective.of_comp (f := algebraMap D L)
    rw [← RingHom.coe_comp,← IsScalarTower.algebraMap_eq A D L]
    rw [IsScalarTower.algebraMap_eq A K L,RingHom.coe_comp]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  obtain ⟨a,ha,hac⟩ := exists_conductor A D p L K
  have haD : algebraMap A D a ≠ 0 := (map_ne_zero_iff _ hAD).mpr ha
  refine ⟨algebraMap A D a,haD,fun n i hi => ?_⟩
  have hinj := tensorMap_injective A D p L K hflat n
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  have hq0 : (p : ℝ≥0∞)^(n*h) ≠ 0 := pow_ne_zero _ hp0
  have hqfin : (p : ℝ≥0∞)^(n*h) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  let B := stage A D p n
  let g := rootMap A p n a
  let : Algebra D B := (originalToStage A D p n).toAlgebra
  let : Algebra D C := (PerfectClosure.of D p).toAlgebra
  let : IsScalarTower D B C := IsScalarTower.of_algebraMap_eq' rfl
  have hstage : T.length ((stageComplex h k D p n F).homology i) ≠ ⊤ := by
    rw [show T.length ((stageComplex h k D p n F).homology i) = _ from
      normalizedLength_stage_homology h k D p hres F hF.term_finite n hinj i]
    apply ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hq0)
    exact ENat.toENNReal_ne_top.mpr (Module.length_ne_top_iff.mpr
      (frobenius_shortComplex_homology_finiteLength p F hF n i))
  have hfree (j : ℤ) : Module.Free D ((frobeniusComplex D p n F).X j) := by
    have := hF.term_free j
    exact free_extendScalars (iterateFrobenius D p n) (F.X j)
  have hgi (j : ℤ) : Function.Injective (fun x : (stageComplex h k D p n F).X j => g • x) := by
    let e := ((HomologicalComplex.eval _ _ j).mapIso (stageRootIso h k D p n F)).toLinearEquiv
    intro x y hxy
    apply e.injective
    apply rootStage_scalar_injective h k D p n a haD (frobeniusComplex D p n F) hfree j
    have h := congrArg e hxy
    erw [e.map_smul, e.map_smul] at h
    exact h
  have hb := Lech.TensorConductor.stage_homology_length_le B T F g (hac n) i hgi hstage
  have hz : T.length ((Lech.TensorConductor.ambientComplex (R:=P) (C:=C) F).homology i) = 0 := by
    apply (T.length_eq_of_equiv
      (restrictionHomologyIso (algebraMap P C)
        (((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex _).obj F) i).toLinearEquiv).trans
    exact Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology
      h k D p K L hdim F hF i hi
  rw [hz,zero_add] at hb
  change normalizedLength (Fin h) k p ((stageComplex h k D p n F).homology i) ≤
    normalizedLength (Fin h) k p (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj
      (stageComplex h k D p n F)).homology i) at hb
  rw [normalizedLength_stage_homology h k D p hres F hF.term_finite n hinj i,
    normalizedLength_stage_scalar_quotient_homology h k D p hres F hF.term_free hF.term_finite n hinj a haD i] at hb
  have hc := (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.mpr hqfin)
    (ENNReal.inv_ne_top.mpr hq0)).mp hb
  exact ENat.toENNReal_le.mp hc

end Lech.PerfectDomainStages

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.PerfectDomainStages.frobenius_homology_conductor_bound_oai.{u} := @OAI.Lech.PerfectDomainStages.frobenius_homology_conductor_bound_oai.{u}
