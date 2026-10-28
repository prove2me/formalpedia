-- Prove2me | solution 1 for OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:27:56.649987+00:00
-- url     : https://prove2.me/submissions/67018509-b0e0-445d-a724-10f662b3684b

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L023
import Theorems.Thm_OAI_Lech_FrobeniusGrowth_frobenius_error_tendstoENNReal
import Theorems.Thm_OAI_Lech_PerfectDomainStages_normalizedLength_actual_stage_quotient
import Theorems.Thm_OAI_Lech_PerfectDomainStages_normalizedLength_scalar_stage_quotient
import Theorems.Thm_OAI_Lech_TensorConductor_length_tendsto
import Theorems.Thm_OAI_Lech_TensorGenerator_length_le
import Theorems.Thm_OAI_Lech_TensorGenerator_scalar_cokernel_le
import Theorems.Thm_OAI_Lech_finiteLength_primary_annihilator

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulTensorSingle
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex

open scoped BigOperators
namespace Lech

variable {R : Type*} [CommRing R]

 
lemma sup_pow_add_pred_le (I J : Ideal R) (n m : ℕ) :
    (I ⊔ J) ^ (n + m - 1) ≤ I ^ n ⊔ J ^ m := by
  rw [← Ideal.add_eq_sup, ← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n ≤ i
  · exact Ideal.mul_le_left.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right hn).trans le_sup_left))
  · refine Ideal.mul_le_left.trans (Ideal.mul_le_right.trans
      ((Ideal.pow_le_pow_right ?_).trans le_sup_right))
    omega

 
lemma finset_sup_pow_le {ι : Type*} (s : Finset ι) (I : ι → Ideal R)
    (a : ℕ) (ha : 1 ≤ a) :
    s.sup I ^ (s.card * (a - 1) + 1) ≤ s.sup (fun j => I j ^ a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj hs =>
    rw [Finset.sup_insert, Finset.sup_insert, Finset.card_insert_of_notMem hj]
    have he : (s.card + 1) * (a - 1) + 1 = a + (s.card * (a - 1) + 1) - 1 := by
      rw [add_mul, one_mul]
      omega
    rw [he]
    exact (sup_pow_add_pred_le (I j) (s.sup I) a _).trans (sup_le_sup_left hs _)

 

lemma parameter_power_cofinality (h a : ℕ) (ha : 1 ≤ a) (z : Fin h → R) :
    (Ideal.span (Set.range z)) ^ (h * (a - 1) + 1) ≤
      Ideal.span (Set.range fun j => z j ^ a) ∧
    Ideal.span (Set.range fun j => z j ^ a) ≤ (Ideal.span (Set.range z)) ^ a := by
  constructor
  · have H := finset_sup_pow_le Finset.univ (fun j : Fin h => Ideal.span {z j}) a ha
    simpa only [Finset.card_univ, Fintype.card_fin, Finset.sup_univ_eq_iSup,
      Ideal.span_singleton_pow, ← Ideal.span_range_eq_iSup] using H
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self j)) a

end Lech


end
end

end OAI
end

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

omit [IsDomain A] in
lemma stage_mono : Monotone (stage A D p) := by
  intro n m h
  apply Algebra.adjoin_le
  rintro _ ⟨d,rfl⟩
  rw [← rootMap_transition D p n m h d]
  exact Algebra.subset_adjoin ⟨iterateFrobenius D p (m-n) d,rfl⟩

omit [IsDomain A] in
lemma stage_exhaustive (c : PerfectClosure D p) : ∃ n, c ∈ stage A D p n := by
  obtain ⟨⟨n,d⟩,rfl⟩ := PerfectClosure.mk_surjective D p c
  exact ⟨n,Algebra.subset_adjoin ⟨d,rfl⟩⟩

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


namespace Lech.PowerSeries
open MvPowerSeries
variable (σ k : Type*) [Fintype σ] [Field k]

lemma dimension_le_variables : ringKrullDim (MvPowerSeries σ k) ≤ Fintype.card σ := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
  rw [maximalIdeal_eq_variables]
  have h := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := MvPowerSeries σ k) (Set.finite_range (X : σ → MvPowerSeries σ k))
  have hcard : (Set.range (X : σ → MvPowerSeries σ k)).ncard ≤ Fintype.card σ := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le (Set.finite_univ)).trans (by simp)
  exact_mod_cast h.trans hcard

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
open scoped nonZeroDivisors
variable (k : Type*) [Field k]

lemma fin_le_dimension (h : ℕ) : (h : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin h) k) := by
  induction h with
  | zero => exact Order.krullDim_nonneg
  | succ h ih =>
    let e : Fin h ↪ Fin (h+1) := Fin.succEmb h
    let f := (killCompl (R := k) e).toRingHom
    have hf : Function.Surjective f := fun x => ⟨rename e x,killCompl_rename_app x⟩
    have hx : (X 0 : MvPowerSeries (Fin (h+1)) k) ∈ (MvPowerSeries (Fin (h+1)) k)⁰ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro hz
        have hc := congrArg (coeff (Finsupp.single 0 1)) hz
        simp at hc)
    have hz : f (X 0) = 0 := by
      apply killCompl_X_eq_zero
      rintro ⟨i,hi⟩
      exact Fin.succ_ne_zero i hi
    have hb := ringKrullDim_succ_le_of_surjective f hf hx hz
    calc
      (↑(h+1) : WithBot ℕ∞) = (h : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (MvPowerSeries (Fin h) k) + 1 := add_le_add ih le_rfl
      _ ≤ _ := hb

lemma fin_dimension (h : ℕ) : ringKrullDim (MvPowerSeries (Fin h) k) = h := by
  apply le_antisymm _ (fin_le_dimension k h)
  simpa using dimension_le_variables (Fin h) k

end Lech.PowerSeries


namespace Lech
variable {R S : Type*} [CommRing R] [CommRing S]
lemma ringKrullDim_eq_of_integral_injective (f : R →+* S)
    (hint : f.IsIntegral) (hf : Function.Injective f) : ringKrullDim S = ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hint⟩
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
    intro p q hpq
    exact Ideal.IsIntegral.comap_lt_comap hpq
  · apply iSup_le
    intro l
    obtain ⟨P,_,hP,hPP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal S)
      (by rw [← RingHom.ker_eq_comap_bot]
          change RingHom.ker f ≤ _
          rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
          exact bot_le)
    have : P.LiesOver l.head.asIdeal := (Ideal.liesOver_iff _ _).mpr hPP.symm
    obtain ⟨L,hL,_,_⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    simpa only [hL,ringKrullDim] using Order.LTSeries.length_le_krullDim L
end Lech


namespace Lech



theorem dimension_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : (dimension A : WithBot ℕ∞) = ringKrullDim A := by
  have hb := ringKrullDim_ne_bot (R := A)
  have ht := ringKrullDim_ne_top (R := A)
  unfold dimension
  generalize he : ringKrullDim A = d at *
  cases d with
  | bot => exact (hb rfl).elim
  | coe d =>
    simp only [WithBot.unbotD_coe]
    exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
      (ENat.natCast_toNat (fun h => ht (by simp [h])))

 

theorem quotient_length_ne_top (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (N : ℕ) :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ N) ≠ ⊤ := by
  by_cases hN : N = 0
  · subst N
    simp
  · let I := (IsLocalRing.maximalIdeal A) ^ N
    have hp : IsLocalRing.maximalIdeal A ∈ I.minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow _ hN,
        Ideal.IsPrime.radical inferInstance, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    let : IsArtinianRing (A ⧸ I) :=
      IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hp
    rw [Module.length_eq_of_surjective (R := A ⧸ I)
      (by simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I)))]
    exact Module.length_ne_top


end Lech
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


namespace Lech
variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma length_quotient_le {I J : Ideal R} (h : I ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ I) := by
  let f := I.mapQ J LinearMap.id h
  apply Module.length_le_of_surjective f
  intro q
  obtain ⟨r, rfl⟩ := J.mkQ_surjective q
  exact ⟨I.mkQ r, rfl⟩

end Lech

open scoped BigOperators


namespace Lech.FrobeniusGrowth
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R]


lemma pow_mem_powerIdeal (H : Ideal R) (q : ℕ) {x : R} (hx : x ∈ H) :
    x^q ∈ powerIdeal H q := Ideal.subset_span ⟨x,hx,rfl⟩

lemma powerIdeal_eq_map (H : Ideal R) (p n : ℕ) [Fact p.Prime] [CharP R p] :
    powerIdeal H (p^n) = H.map (iterateFrobenius R p n) := by
  rw [← Ideal.span_eq H, Ideal.map_span, Ideal.span_eq]
  rfl

lemma pigeonhole (H : Ideal R) (hH : H.FG) :
    ∃ t : ℕ, ∀ q : ℕ, 1 ≤ q → H^(t*(q-1)+1) ≤ powerIdeal H q := by
  classical
  obtain ⟨s,hs⟩ := hH
  let z : Fin s.card → R := fun i => ((s.equivFin).symm i).val
  have hz : Set.range z = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i,rfl⟩
      exact ((s.equivFin).symm i).property
    · intro hr
      exact ⟨s.equivFin ⟨r,hr⟩,congrArg Subtype.val ((s.equivFin).symm_apply_apply _)⟩
  refine ⟨s.card,fun q hq => ?_⟩
  have h := (Lech.parameter_power_cofinality s.card q hq z).1
  rw [hz,hs] at h
  refine h.trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨i,rfl⟩
  apply pow_mem_powerIdeal
  rw [← hs]
  exact Ideal.subset_span (by rw [← hz]; exact Set.mem_range_self i)

lemma linear_power_containment [IsNoetherianRing R] [IsLocalRing R]
    (H : Ideal R) (hH : H.radical = IsLocalRing.maximalIdeal R) :
    ∃ c : ℕ, ∀ q : ℕ, 1 ≤ q → (IsLocalRing.maximalIdeal R)^(c*q) ≤ powerIdeal H q := by
  obtain ⟨a,ha⟩ := H.exists_radical_pow_le_of_fg H.radical.fg_of_isNoetherianRing
  rw [hH] at ha
  obtain ⟨t,ht⟩ := pigeonhole H H.fg_of_isNoetherianRing
  refine ⟨a*(t+1),fun q hq => ?_⟩
  have he : t*(q-1)+1 ≤ (t+1)*q := by
    calc
      _ ≤ t*q+q := Nat.add_le_add (Nat.mul_le_mul_left t (Nat.sub_le q 1)) hq
      _ = _ := by ring
  calc
    _ = ((IsLocalRing.maximalIdeal R)^a)^((t+1)*q) := by rw [← pow_mul]; congr 1; ring
    _ ≤ H^((t+1)*q) := pow_le_pow_left' ha _
    _ ≤ H^(t*(q-1)+1) := Ideal.pow_le_pow_right he
    _ ≤ powerIdeal H q := ht q hq

open Filter
open scoped Topology


end Lech.FrobeniusGrowth


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
-- module Solutions.OAIQ032_LECH.Multiplicity_PerfectTensorLimit
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal nonZeroDivisors Topology
open Filter
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]
local instance perfectTensorLimitPowerSeriesIsDomain : IsDomain (MvPowerSeries (Fin h) k) :=
  NoZeroDivisors.to_isDomain _

include K L in
 

theorem stage_tensor_length_tendsto_oai
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (M : ModuleCat.{u} D) (hM : IsFiniteLength D M) :
    letI : ∀ n, Algebra D (stage (MvPowerSeries (Fin h) k) D p n) :=
      fun n => (originalToStage (MvPowerSeries (Fin h) k) D p n).toAlgebra
    Tendsto (fun n => normalizedLength (Fin h) k p
      ((stage (MvPowerSeries (Fin h) k) D p n) ⊗[D] M)) atTop
      (𝓝 (normalizedLength (Fin h) k p ((PerfectClosure D p) ⊗[D] M))) := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let : ∀ n, Algebra D (stage A D p n) := fun n => (originalToStage A D p n).toAlgebra
  let : ∀ n, IsScalarTower D (stage A D p n) (PerfectClosure D p) := fun n =>
    IsScalarTower.of_algebraMap_eq fun d => rfl
  obtain ⟨hno,hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  let := hno
  let := hart
  obtain ⟨b,f,hfgen⟩ := Module.Finite.exists_fin' D M
  obtain ⟨H,hH,hHM⟩ := Lech.finiteLength_primary_annihilator hM
  have hflat := perfectClosure_flat (Fin h) k p
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_flat_frobenius A p
    (fun n => iterateFrobenius_flat (σ := Fin h) (R := k) p n)
  have hi (n : ℕ) := tensorMap_injective A D p L K hflat n
  have hdim : Lech.dimension D = h := by
    have hd := Lech.ringKrullDim_eq_of_integral_injective (algebraMap A D)
      (Algebra.IsIntegral.isIntegral : (algebraMap A D).IsIntegral) hf
    rw [Lech.PowerSeries.fin_dimension k h] at hd
    have hh := Lech.dimension_cast D
    rw [hd] at hh
    exact_mod_cast hh
  obtain ⟨g,hg,hgc⟩ := exists_conductor A D p L K
  have hgn : algebraMap A D g ∈ D⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr
    (fun hz => hg (hf (by simpa using hz)))
  have herr := Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal H hH hgn p
  rw [hdim] at herr
  have hfiniteQuot (n : ℕ) :
      normalizedLength (Fin h) k p ((stage A D p n) ⧸ H.map (originalToStage A D p n)) ≠ ⊤ := by
    rw [normalizedLength_actual_stage_quotient (Fin h) k D p hres H n (hi n)]
    obtain ⟨c,hc⟩ := Lech.FrobeniusGrowth.linear_power_containment H hH
    have hl := Lech.length_quotient_le D (hc (p^n) (Nat.one_le_pow n p (Fact.out : p.Prime).pos))
    have hlfin := ne_top_of_le_ne_top (Lech.quotient_length_ne_top D (c*p^n)) hl
    rw [Lech.FrobeniusGrowth.powerIdeal_eq_map H p n] at hlfin
    apply ENNReal.mul_ne_top
    · apply ENNReal.inv_ne_top.mpr
      exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    · simpa using hlfin
  have hfinite (n : ℕ) : normalizedLength (Fin h) k p ((stage A D p n) ⊗[D] M) ≠ ⊤ := by
    have hb : (b : ℝ≥0∞) ≠ ⊤ := by simp
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hb (hfiniteQuot n))
      (Lech.TensorGenerator.length_le f (stage A D p n) (regularTower (Fin h) k p)
        hfgen H hHM)
  apply Lech.TensorConductor.length_tendsto (D := D) (stage A D p) M
    (regularTower (Fin h) k p) (stage_mono A D p) (stage_exhaustive A D p)
    (fun n => rootMap A p n g) hgc hfinite
  have ht : Tendsto (fun n => (b : ℝ≥0∞) * normalizedLength (Fin h) k p
      ((stage A D p n) ⧸ (H.map (originalToStage A D p n) ⊔
        Ideal.span {algebraMap P (stage A D p n) (rootMap A p n g)}))) atTop (𝓝 0) := by
    have hb := ENNReal.Tendsto.const_mul herr (a := (b : ℝ≥0∞)) (Or.inr (by simp))
    simp only [mul_zero] at hb
    apply hb.congr
    intro n
    congr 1
    symm
    simpa only [Fintype.card_fin] using
      normalizedLength_scalar_stage_quotient (Fin h) k D p hres H n (hi n) g
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro n
    exact zero_le
  · intro n
    exact Lech.TensorGenerator.scalar_cokernel_le f (stage A D p n)
      (regularTower (Fin h) k p) hfgen H hHM (rootMap A p n g)

end Lech.PerfectDomainStages

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto_oai.{u} := @OAI.Lech.PerfectDomainStages.stage_tensor_length_tendsto_oai.{u}
