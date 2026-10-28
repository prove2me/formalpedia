-- Prove2me | solution 1 for OAI.Lech.MinimalReduction.exists_reduction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:12:15.493635+00:00
-- url     : https://prove2.me/submissions/bd5a2073-2734-4b3e-b54c-385e2d038bc7

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L021
import Theorems.Thm_OAI_Lech_LinearNormalization_exists_linear_normalization
import Theorems.Thm_OAI_Lech_LinearNormalization_generator_number_le_dimension

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.IdealGraded.reesGradedAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.SourceGraded.target_graded _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)

lemma exists_generators [IsNoetherianRing R] :
    ∃ (n : ℕ) (x : Fin n → Ring I),
      Algebra.adjoin (R ⧸ I) (Set.range x) = ⊤ ∧ ∀ j, x j ∈ grade I 1 := by
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  have hamem (j : Fin n) : a j ∈ I ^ 1 := by
    rw [pow_one, ← ha]
    exact Submodule.subset_span (Set.mem_range_self j)
  let u : Fin n → reesAlgebra I := fun j => monomial I 1 ⟨a j, hamem j⟩
  have hupoly : Algebra.adjoin R (Set.range (fun j => Polynomial.monomial 1 (a j))) =
      reesAlgebra I := by
    rw [← adjoin_monomial_eq_reesAlgebra, ← ha, Submodule.map_span, Algebra.adjoin_span,
      ← Set.range_comp]
    rfl
  have hu : Algebra.adjoin R (Set.range u) = ⊤ := by
    apply Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, ← Set.range_comp]
    change Algebra.adjoin R (Set.range (fun j => Polynomial.monomial 1 (a j))) = _
    rw [hupoly]
    exact (Subalgebra.range_val _).symm
  let q := Ideal.Quotient.mkₐ R (shifted I)
  let x : Fin n → Ring I := fun j => q (u j)
  have hxR : Algebra.adjoin R (Set.range x) = ⊤ := by
    have h := congrArg (Subalgebra.map q) hu
    rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top,
      (AlgHom.range_eq_top q).mpr Ideal.Quotient.mk_surjective] at h
    exact h
  have hx : Algebra.adjoin (R ⧸ I) (Set.range x) = ⊤ := by
    apply Subalgebra.restrictScalars_injective R
    rw [Algebra.Subalgebra.restrictScalars_adjoin, hxR, sup_top_eq, Subalgebra.restrictScalars_top]
  refine ⟨n, x, hx, ?_⟩
  intro j
  exact ⟨u j, ⟨⟨a j, hamem j⟩, rfl⟩, rfl⟩

end Lech.IdealGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteGradedQuotient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPolynomial DirectSum
namespace Lech.LinearNormalization
universe u v w
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

lemma integral_image_of_generators_zero {Q : Type w} [CommRing Q] [Algebra k Q]
    (q : A →ₐ[k] Q) {s : ℕ} (z : Fin s → A) (hz : ∀ i,q (z i) = 0)
    {x : A} (hx : IsIntegral (Algebra.adjoin k (Set.range z)) x) :
    IsIntegral k (q x) := by
  let B := Algebra.adjoin k (Set.range z)
  let C := integralClosure k Q
  have hB : B ≤ C.comap q := by
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    change IsIntegral k (q (z i))
    rw [hz i]
    exact isIntegral_zero
  let φ : B →ₐ[k] C := (q.comp B.val).codRestrict C (fun b => hB b.property)
  have h : (algebraMap C Q).comp φ.toRingHom = q.toRingHom.comp (algebraMap B A) := rfl
  exact isIntegral_trans (q x) (hx.map_of_comp_eq φ.toRingHom q.toRingHom h)

lemma finite_quotient_of_integral_generators {N s : ℕ} (x : Fin N → A) (z : Fin s → A)
    (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (hi : ∀ i,IsIntegral (Algebra.adjoin k (Set.range z)) (x i)) :
    Module.Finite k (A ⧸ Ideal.span (Set.range z)) := by
  let J := Ideal.span (Set.range z)
  let q : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J
  have hqz (i) : q (z i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  have hgen : Algebra.adjoin k (Set.range (fun i => q (x i))) = ⊤ := by
    simpa only [AlgHom.map_adjoin,← Set.range_comp,Function.comp_def,Algebra.map_top,
      (AlgHom.range_eq_top q).mpr Ideal.Quotient.mk_surjective] using
      congrArg (Subalgebra.map q) hx
  let := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range (fun i => q (x i)))
    (by rintro _ ⟨i,rfl⟩; exact integral_image_of_generators_zero q z hqz (hi i))
  exact Module.Finite.of_surjective
    (Algebra.adjoin k (Set.range (fun i => q (x i)))).val.toLinearMap
    (by intro a; exact ⟨⟨a,by rw [hgen]; trivial⟩,rfl⟩)

 

lemma finite_grading_bounded {M : Type v} [AddCommGroup M] [Module k M]
    [Module.Finite k M] (G : ℕ → Submodule k M) [Decomposition G] :
    ∃ c : ℕ, ∀ n, c ≤ n → G n = ⊥ := by
  classical
  obtain ⟨r,x,hx⟩ := Module.Finite.exists_fin (R:=k) (M:=M)
  let c := (Finset.univ : Finset (Fin r)).sup
    (fun i => ((decompose G (x i)).support.sup id)+1)
  refine ⟨c,?_⟩
  intro n hn
  let π : M →ₗ[k] G n := (DFinsupp.lapply n).comp (decomposeLinearEquiv G).toLinearMap
  have hπx (i : Fin r) : π (x i) = 0 := by
    apply DFinsupp.notMem_support_iff.mp
    intro hm
    change n ∈ (decompose G (x i)).support at hm
    have hle : n ≤ (decompose G (x i)).support.sup id := Finset.le_sup (f:=id) hm
    have hlt : ((decompose G (x i)).support.sup id)+1 ≤ c :=
      Finset.le_sup (f:=fun i => ((decompose G (x i)).support.sup id)+1) (Finset.mem_univ i)
    omega
  have hπ : LinearMap.ker π = ⊤ := by
    apply top_unique
    rw [← hx]
    exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hπx i)
  apply eq_bot_iff.mpr
  intro a ha
  have hz : π a = 0 := by
    change a ∈ LinearMap.ker π
    rw [hπ]; trivial
  have he : (π a : M) = a := decompose_of_mem_same G ha
  rw [← he,hz]
  exact Submodule.zero_mem _

lemma high_grades_in_span {N s : ℕ} (G : ℕ → Submodule k A) [GradedAlgebra G]
    (x : Fin N → A) (z : Fin s → A)
    (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (hz : ∀ i,z i ∈ G 1)
    (hi : ∀ i,IsIntegral (Algebra.adjoin k (Set.range z)) (x i)) :
    ∃ c : ℕ, ∀ n,c ≤ n → ∀ a ∈ G n,a ∈ Ideal.span (Set.range z) := by
  let J := Ideal.span (Set.range z)
  let q : A →ₗ[k] A ⧸ J := J.mkQ.restrictScalars k
  have hJ : J.IsHomogeneous G := Ideal.homogeneous_span G _
    (by rintro _ ⟨i,rfl⟩; exact ⟨1,hz i⟩)
  have hker : q.ker.IsHomogeneous G := by
    rw [LinearMap.ker_restrictScalars,Submodule.ker_mkQ]
    exact hJ
  let H := Grading.imagePiece G q
  let : Decomposition H := Grading.imageDecomposition G q J.mkQ_surjective hker
  let : Module.Finite k (A ⧸ J) := finite_quotient_of_integral_generators x z hx hi
  obtain ⟨c,hc⟩ := finite_grading_bounded H
  refine ⟨c,fun n hn a ha => ?_⟩
  have hqa : q a ∈ H n := ⟨a,ha,rfl⟩
  rw [hc n hn] at hqa
  change a ∈ J
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q a = 0
  simpa using hqa
end Lech.LinearNormalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AssociatedGradedReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.IdealGraded.reesGradedAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.SourceGraded.target_graded _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open DirectSum
namespace Lech.LinearNormalization
universe u v
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

lemma homogeneous_span_coefficients (G : ℕ → Submodule k A) [GradedAlgebra G]
    {s n : ℕ} (z : Fin s → A) (hz : ∀ i,z i ∈ G 1)
    {a : A} (ha : a ∈ G (n+1)) (hi : a ∈ Ideal.span (Set.range z)) :
    ∃ c : Fin s → A,(∀ i,c i ∈ G n) ∧ ∑ i,c i*z i = a := by
  obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hi
  let π : A →ₗ[k] A := (G (n+1)).subtype.comp
    ((DFinsupp.lapply (n+1)).comp (decomposeLinearEquiv G).toLinearMap)
  have hπ : π a = a := decompose_of_mem_same G ha
  have hsum := congrArg π hc
  rw [map_sum,hπ] at hsum
  refine ⟨fun i => (decompose G (c i) n : A),fun i => (decompose G (c i) n).property,?_⟩
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  exact (coe_decompose_mul_add_of_right_mem G (hz i)).symm
end Lech.LinearNormalization

namespace Lech.IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma initialForm_mem (n : ℕ) (a : ↥(I^n)) : initialForm I n a ∈ grade I n :=
  ⟨monomial I n a,⟨a,rfl⟩,rfl⟩

lemma exists_initialForm {n : ℕ} {a : Ring I} (ha : a ∈ grade I n) :
    ∃ b : ↥(I^n),initialForm I n b = a := by
  obtain ⟨_,⟨b,rfl⟩,rfl⟩ := ha
  exact ⟨b,rfl⟩

lemma initialForm_mul {n m : ℕ} (a : ↥(I^n)) (b : ↥(I^m)) :
    initialForm I (n+m) ⟨(a:R)*(b:R),by rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2⟩ =
      initialForm I n a * initialForm I m b := by
  change Ideal.Quotient.mk (shifted I) _ =
    Ideal.Quotient.mk (shifted I) (monomial I n a) *
    Ideal.Quotient.mk (shifted I) (monomial I m b)
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  exact (Polynomial.monomial_mul_monomial _ _ _ _).symm

lemma initialForm_eq_zero_iff (n : ℕ) (a : ↥(I^n)) :
    initialForm I n a = 0 ↔ (a:R) ∈ I^(n+1) :=
  Ideal.Quotient.eq_zero_iff_mem.trans (monomial_mem_shifted_iff I n a)

lemma initialForm_eq_iff (n : ℕ) (a b : ↥(I^n)) :
    initialForm I n a = initialForm I n b ↔ (a:R)-(b:R) ∈ I^(n+1) := by
  rw [← sub_eq_zero,← map_sub,initialForm_eq_zero_iff]
  rfl

lemma power_le_reduction_sup {s n : ℕ} (z : Fin s → ↥I)
    (h : ∀ a ∈ grade I (n+1),a ∈ Ideal.span (Set.range
      (fun i => initialForm I 1 ⟨(z i:R),by simp⟩)))
    [I.IsMaximal] :
    I^(n+1) ≤ (Ideal.span (Set.range (fun i => (z i:R)))) * I^n ⊔ I^(n+2) := by
  let k := R ⧸ I
  let : Field k := Ideal.Quotient.field I
  let Z : Fin s → Ring I := fun i => initialForm I 1 ⟨(z i:R),by simp⟩
  have hZ (i) : Z i ∈ grade I 1 := initialForm_mem I 1 _
  intro a ha
  let a' : ↥(I^(n+1)) := ⟨a,ha⟩
  obtain ⟨c,hc,hce⟩ := LinearNormalization.homogeneous_span_coefficients
    (grade I) Z hZ (initialForm_mem I (n+1) a') (h _ (initialForm_mem I (n+1) a'))
  choose b hb using fun i => exists_initialForm I (hc i)
  let t : Fin s → ↥(I^(n+1)) := fun i => ⟨(b i:R)*(z i:R),by
    rw [pow_add]
    exact Ideal.mul_mem_mul (b i).2 (by simp)⟩
  have he : initialForm I (n+1) (∑ i,t i) = initialForm I (n+1) a' := by
    rw [map_sum]
    convert hce using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    exact (initialForm_mul I (b i) ⟨(z i:R),by simp⟩).trans
      (congrArg (·*Z i) (hb i))
  have hdiff : a - ∑ i,(b i:R)*(z i:R) ∈ I^(n+2) := by
    have hh := (initialForm_eq_iff I (n+1) a' (∑ i,t i)).mp he.symm
    simpa [a',t,Submodule.coe_sum,Nat.add_assoc] using hh
  have ht : ∑ i,(b i:R)*(z i:R) ∈
      (Ideal.span (Set.range (fun i => (z i:R)))) * I^n := by
    apply Ideal.sum_mem
    intro i _
    rw [mul_comm (b i:R) (z i:R)]
    exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_range_self i)) (b i).2
  rw [← sub_add_cancel a (∑ i,(b i:R)*(z i:R))]
  exact Ideal.add_mem _
    ((show I^(n+2) ≤ _ ⊔ I^(n+2) from le_sup_right) hdiff)
    ((show (Ideal.span (Set.range (fun i => (z i:R)))) * I^n ≤
      (Ideal.span (Set.range (fun i => (z i:R)))) * I^n ⊔ I^(n+2) from le_sup_left) ht)

lemma reduction_of_high_grades [IsLocalRing R] [IsNoetherianRing R]
    {s c : ℕ} (z : Fin s → ↥(IsLocalRing.maximalIdeal R))
    (h : ∀ a ∈ grade (IsLocalRing.maximalIdeal R) (c+1),a ∈ Ideal.span (Set.range
      (fun i => initialForm (IsLocalRing.maximalIdeal R) 1
        ⟨(z i:R),by simp⟩))) :
    (IsLocalRing.maximalIdeal R)^(c+1) =
      Ideal.span (Set.range (fun i => (z i:R))) * (IsLocalRing.maximalIdeal R)^c := by
  let m := IsLocalRing.maximalIdeal R
  let J := Ideal.span (Set.range (fun i => (z i:R)))
  have hJ : J ≤ m := Ideal.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact (z i).2)
  apply le_antisymm
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian (m^(c+1))) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    have H := power_le_reduction_sup m z h
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    change J*m^c ⊔ m*m^(c+1) = J*m^c ⊔ m^(c+2)
    rw [← pow_succ']
  · exact (Ideal.mul_mono hJ le_rfl).trans_eq (pow_succ' m c).symm
end Lech.IdealGraded

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_MinimalReduction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing MvPolynomial
namespace Lech.MinimalReduction
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma associatedGraded_nontrivial [IsNoetherianRing R] [IsLocalRing R] :
    Nontrivial (IdealGraded.Ring (maximalIdeal R)) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  have h1 : (1 : reesAlgebra (maximalIdeal R)) ∈ IdealGraded.shifted (maximalIdeal R) := by
    rw [h]; trivial
  have hm := h1 0
  change (1 : Polynomial R).coeff 0 ∈ (maximalIdeal R)^(0+1) at hm
  simp at hm

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma pad_generators [IsNoetherianRing R] [IsLocalRing R]
    {s d : ℕ} (hs : s≤d) (z : Fin s → ↥(maximalIdeal R)) :
    ∃ w : Fin d → ↥(maximalIdeal R),
      Ideal.span (Set.range (fun i => (w i:R))) =
        Ideal.span (Set.range (fun i => (z i:R))) := by
  classical
  let w : Fin d → ↥(maximalIdeal R) := fun i => if hi : i.val < s then z ⟨i.val,hi⟩ else 0
  refine ⟨w,le_antisymm ?_ ?_⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : i.val < s
    · simpa only [w,dite_eq_left hi] using
        (Ideal.subset_span (Set.mem_range_self (⟨i.val,hi⟩ : Fin s)) :
          (z ⟨i.val,hi⟩:R) ∈ Ideal.span (Set.range (fun j => (z j:R))))
    · simp only [w,dite_eq_right hi,ZeroMemClass.coe_zero]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    let j : Fin d := ⟨i.val,i.isLt.trans_le hs⟩
    have he : w j = z i := by simp [w,j,i.isLt]
    have H := Ideal.subset_span (s:=Set.range (fun i => (w i:R))) (Set.mem_range_self j)
    simpa only [he] using H

 

theorem exists_reduction_oai [Infinite (ResidueField R)] :
    ∃ z : Fin (dimension R) → R, (∀ i,z i ∈ maximalIdeal R) ∧
      ∃ c : ℕ,(maximalIdeal R)^(c+1) =
        Ideal.span (Set.range z) * (maximalIdeal R)^c := by
  let m := maximalIdeal R
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let : Infinite (R ⧸ m) := inferInstanceAs (Infinite (ResidueField R))
  let : Nontrivial (IdealGraded.Ring m) := associatedGraded_nontrivial
  obtain ⟨N,x,hx,hxG⟩ := IdealGraded.exists_generators m
  obtain ⟨s,_,Z,hZspan,hZi,hxI⟩ :=
    @LinearNormalization.exists_linear_normalization (R ⧸ m) (Ideal.Quotient.field m)
      (IdealGraded.Ring m) inferInstance (IdealGraded.gradedAlgebra m) inferInstance
      inferInstance (IdealGraded.grade m) (IdealGraded.gradeGradedAlgebra m) N x hxG
  have hZG (i) : Z i ∈ IdealGraded.grade m 1 := by
    apply (show Submodule.span (R ⧸ m) (Set.range x) ≤ IdealGraded.grade m 1 from
      Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hxG j))
    exact hZspan i
  have hs : s ≤ dimension R := LinearNormalization.generator_number_le_dimension Z hZG hZi
  obtain ⟨c,hc⟩ := @LinearNormalization.high_grades_in_span (R ⧸ m) (Ideal.Quotient.field m)
    (IdealGraded.Ring m) inferInstance (IdealGraded.gradedAlgebra m) N s
    (IdealGraded.grade m) (IdealGraded.gradeGradedAlgebra m) x Z hx hZG hxI
  choose z hz using fun i => IdealGraded.exists_initialForm m (hZG i)
  let zr : Fin s → ↥m := fun i => ⟨(z i:R),by simpa using (z i).2⟩
  have hr : m^(c+1) = Ideal.span (Set.range (fun i => (zr i:R))) * m^c := by
    apply IdealGraded.reduction_of_high_grades zr
    intro a ha
    have he : (fun i => IdealGraded.initialForm m 1
        ⟨(zr i:R),by simp⟩) = Z := by
      funext i
      exact hz i
    rw [he]
    exact hc (c+1) (Nat.le_succ c) a ha
  obtain ⟨w,hw⟩ := pad_generators hs zr
  refine ⟨fun i => (w i:R),fun i => (w i).2,c,?_⟩
  rw [hw]
  exact hr

end Lech.MinimalReduction

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.MinimalReduction.exists_reduction_oai.{u} := @OAI.Lech.MinimalReduction.exists_reduction_oai.{u}
