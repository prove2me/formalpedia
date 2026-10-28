-- Prove2me | solution 1 for OAI.Lech.LinearNormalization.generator_number_le_dimension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:20:11.917679+00:00
-- url     : https://prove2.me/submissions/243ac2c4-1b9f-4574-a4d2-a39422d6a620

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L025

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechBoundedEquiv
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech
namespace IdealGraded

variable {A : Type*} [CommRing A]

lemma inclusion_injective (I : Ideal A) (n : ℕ) :
    Function.Injective (inclusion I n) := by
  rw [← LinearMap.ker_eq_bot, inclusion, Submodule.ker_liftQ_eq_bot]
  simpa only [LinearMap.ker_comp, Submodule.ker_mkQ, nextPower] using (le_refl (nextPower I n))

lemma transition_surjective (I : Ideal A) (n : ℕ) :
    Function.Surjective (transition I n) := by
  intro x
  obtain ⟨a, rfl⟩ := (I ^ n).mkQ_surjective x
  exact ⟨(I ^ (n + 1)).mkQ a, rfl⟩

lemma piece_exact (I : Ideal A) (n : ℕ) :
    Function.Exact (inclusion I n) (transition I n) := by
  rw [LinearMap.exact_iff]
  simp only [inclusion, transition, Submodule.ker_mapQ, Submodule.range_liftQ,
    LinearMap.range_comp, Submodule.range_subtype, Submodule.comap_id]

lemma length_successor (I : Ideal A) (n : ℕ) :
    Module.length A (A ⧸ I ^ (n + 1)) =
      Module.length A (Piece I n) + Module.length A (A ⧸ I ^ n) :=
  Module.length_eq_add_of_exact (inclusion I n) (transition I n)
    (inclusion_injective I n) (transition_surjective I n) (piece_exact I n)

lemma length_eq_sum (I : Ideal A) (N : ℕ) :
    Module.length A (A ⧸ I ^ N) =
      ∑ n ∈ Finset.range N, Module.length A (Piece I n) := by
  induction N with
  | zero => simp
  | succ N ih => rw [length_successor, ih, Finset.sum_range_succ, add_comm]

lemma length_piece_eq_finrank [IsNoetherianRing A] (I : Ideal A) [I.IsMaximal] (n : ℕ) :
    Module.length A (Piece I n) = (Module.finrank (A ⧸ I) (Piece I n) : ℕ∞) := by
  let := Ideal.Quotient.field I
  rw [Module.length_eq_of_surjective (R := A ⧸ I)
    (by simpa only [Ideal.Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective),
    Module.length_eq_finrank]

end IdealGraded
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.Grading
open MvPolynomial
variable (S : Type*) [CommRing S]
lemma index_card (h n : ℕ) : Fintype.card (MonomialIndex h n) = h.multichoose n :=
  (Fintype.card_congr (indexEquiv h n)).trans (Sym.card_sym_fin_eq_multichoose h n)

end Lech.Grading

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
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

 
theorem colength_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (N : ℕ) :
    (colength A N : ℕ∞) = Module.length A (A ⧸ (IsLocalRing.maximalIdeal A)^N) :=
  ENat.natCast_toNat (quotient_length_ne_top A N)

end Lech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLengthLe
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
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

lemma length_le_add_of_exact {R M N P : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hg : Function.Surjective g)
    (he : Function.Exact f g) :
    Module.length R M ≤ Module.length R N + Module.length R P := by
  let f' : N →ₗ[R] g.ker := f.codRestrict g.ker (fun n => by
    rw [LinearMap.exact_iff.mp he]
    exact ⟨n, rfl⟩)
  have hf' : Function.Surjective f' := by
    rintro ⟨m, hm⟩
    rw [LinearMap.exact_iff.mp he] at hm
    obtain ⟨n, rfl⟩ := hm
    exact ⟨n, rfl⟩
  rw [Module.length_eq_add_of_exact g.ker.subtype g g.ker.subtype_injective hg
    (LinearMap.exact_subtype_ker_map g)]
  exact add_le_add (Module.length_le_of_surjective f' hf') le_rfl

namespace ParameterBound
variable {R : Type*} [CommRing R]

lemma length_mul_le (J : Ideal R) (x y : R) :
    Module.length R (R ⧸ (J ⊔ Ideal.span {x * y})) ≤
      Module.length R (R ⧸ (J ⊔ Ideal.span {x})) +
        Module.length R (R ⧸ (J ⊔ Ideal.span {y})) := by
  let A := J ⊔ Ideal.span {x}
  let B := J ⊔ Ideal.span {x * y}
  let C := J ⊔ Ideal.span {y}
  have hmul : ∀ z ∈ A, y * z ∈ B := by
    intro z hz
    obtain ⟨j, hj, t, ht, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    rw [mul_add]
    apply B.add_mem
    · exact Submodule.mem_sup_left (J.mul_mem_left y hj)
    · apply Submodule.mem_sup_right
      apply Ideal.mem_span_singleton'.mpr
      exact ⟨a, by ring⟩
  let f : (R ⧸ A) →ₗ[R] R ⧸ B :=
    A.liftQ (B.mkQ.comp (LinearMap.lsmul R R y)) (by
      intro z hz
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hmul z hz))
  have hBC : B ≤ C := by
    apply sup_le le_sup_left
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩)
  let g : (R ⧸ B) →ₗ[R] R ⧸ C := B.mapQ C LinearMap.id hBC
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨r, rfl⟩ := C.mkQ_surjective q
    exact ⟨B.mkQ r, rfl⟩
  apply length_le_add_of_exact f g hg
  rw [LinearMap.exact_iff]
  ext q
  obtain ⟨r, rfl⟩ := B.mkQ_surjective q
  constructor
  · intro hr
    change C.mkQ r = 0 at hr
    have hrC := (Submodule.Quotient.mk_eq_zero _).mp hr
    obtain ⟨j, hj, t, ht, he⟩ := Submodule.mem_sup.mp hrC
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    refine ⟨A.mkQ a, ?_⟩
    change B.mkQ (y * a) = B.mkQ r
    apply (Submodule.Quotient.eq _).mpr
    rw [← he]
    have he' : y * a - (j + a * y) = -j := by ring
    rw [he']
    exact B.neg_mem (Submodule.mem_sup_left hj)
  · rintro ⟨a, ha⟩
    obtain ⟨a, rfl⟩ := A.mkQ_surjective a
    change B.mkQ (y * a) = B.mkQ r at ha
    change g (B.mkQ r) = 0
    rw [← ha]
    change C.mkQ (y * a) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨a, mul_comm _ _⟩)

lemma length_pow_le (J : Ideal R) (x : R) (n : ℕ) :
    Module.length R (R ⧸ (J ⊔ Ideal.span {x ^ n})) ≤
      n * Module.length R (R ⧸ (J ⊔ Ideal.span {x})) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (length_mul_le J (x ^ n) x).trans (add_le_add ih le_rfl)

lemma length_parameter_powers_le (n : ℕ) (x : Fin n → R) (J : Ideal R) (N : ℕ) :
    Module.length R (R ⧸ (J ⊔ Ideal.span (Set.range (fun i => x i ^ N)))) ≤
      (N : ℕ∞) ^ n * Module.length R (R ⧸ (J ⊔ Ideal.span (Set.range x))) := by
  induction n generalizing J with
  | zero =>
      have he : (fun i : Fin 0 => x i ^ N) = x := funext (fun i => Fin.elim0 i)
      rw [he, pow_zero, one_mul]
  | succ n ih =>
      rw [Fin.range_fin_succ, Ideal.span_insert, Fin.range_fin_succ, Ideal.span_insert]
      have h1 := length_pow_le (J ⊔ Ideal.span (Set.range (fun i : Fin n => x i.succ ^ N)))
         (x 0) N
      have h2 := ih (fun i => x i.succ) (J ⊔ Ideal.span {x 0})
      have h2' := mul_le_mul_right h2 (N : ℕ∞)
      rw [sup_right_comm J] at h2'
      have h := h1.trans h2'
      change Module.length R (R ⧸ (J ⊔ (Ideal.span {x 0 ^ N} ⊔
        Ideal.span (Set.range (fun i : Fin n => x i.succ ^ N))))) ≤
        (N : ℕ∞) ^ (n + 1) * Module.length R (R ⧸ (J ⊔
          (Ideal.span {x 0} ⊔ Ideal.span (Set.range (fun i : Fin n => x i.succ)))))
      rw [← sup_assoc, sup_right_comm J, ← sup_assoc, pow_succ', mul_assoc]
      exact h

end ParameterBound
end Lech


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

lemma colength_polynomial_bound :
    ∃ C : ℕ, ∀ N : ℕ, colength R N ≤ N ^ dimension R * C := by
  classical
  let m := IsLocalRing.maximalIdeal R
  obtain ⟨s, hp, hc⟩ := m.exists_finset_card_eq_height_of_isNoetherianRing
  let I := Ideal.span (s : Set R)
  let x : Fin s.card → R := fun i => ((s.equivFin).symm i).val
  have hx : Set.range x = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact ((s.equivFin).symm i).property
    · intro hr
      exact ⟨s.equivFin ⟨r, hr⟩, congrArg Subtype.val ((s.equivFin).symm_apply_apply _)⟩
  have hxm (i : Fin s.card) : x i ∈ m :=
    hp.le (Ideal.subset_span (by rw [← hx]; exact Set.mem_range_self i))
  have hcard : s.card = dimension R := by
    have h := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hc
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← dimension_cast R] at h
    exact Nat.cast_injective (WithBot.coe_injective h)
  let : IsArtinianRing (R ⧸ I) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hp
  have hfinite : Module.length R (R ⧸ I) ≠ ⊤ := by
    rw [Module.length_eq_of_surjective (R := R ⧸ I)
      (by simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I)))]
    exact Module.length_ne_top
  let C := (Module.length R (R ⧸ I)).toNat
  have hC : (C : ℕ∞) = Module.length R (R ⧸ I) := ENat.natCast_toNat hfinite
  refine ⟨C, fun N => ?_⟩
  have hpow : Ideal.span (Set.range (fun i => x i ^ N)) ≤ m ^ N := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.pow_mem_pow (hxm i) N
  have h1 := length_quotient_le R hpow
  have h2 := ParameterBound.length_parameter_powers_le s.card x (⊥ : Ideal R) N
  rw [bot_sup_eq, bot_sup_eq, hx] at h2
  have h := h1.trans h2
  rw [hcard, ← hC, ← Nat.cast_pow, ← Nat.cast_mul] at h
  rw [← colength_cast R] at h
  exact ENat.natCast_le_natCast.mp h
end Lech

open scoped BigOperators
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LinearNormalizationDimension
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open DirectSum MvPolynomial
namespace Lech.LinearNormalization
universe u v
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

lemma degree_finrank_lower (G : ℕ → Submodule k A) [GradedAlgebra G]
    {s : ℕ} (z : Fin s → A) (hz : ∀ i,z i ∈ G 1)
    (hi : Function.Injective (aeval (R:=k) z)) (n : ℕ) [Module.Finite k (G n)] :
    s.multichoose n ≤ Module.finrank k (G n) := by
  let f : homogeneousSubmodule (Fin s) k n →ₗ[k] G n :=
    (aeval (R:=k) z).toLinearMap.domRestrict
      (homogeneousSubmodule (Fin s) k n) |>.codRestrict (G n)
        (fun p => Grading.aeval_mem G z hz p.property)
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply hi
    exact congrArg Subtype.val he
  have H := f.finrank_le_finrank_of_injective hf
  have he : Module.finrank k (homogeneousSubmodule (Fin s) k n) = s.multichoose n := by
    rw [(Grading.homogeneousEquiv k s n).finrank_eq,Module.finrank_pi,Grading.index_card]
  rwa [he] at H

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma polynomial_rank_le_colength {s : ℕ}
    (z : Fin s → IdealGraded.Ring (IsLocalRing.maximalIdeal R))
    (hz : ∀ i,z i ∈ IdealGraded.grade (IsLocalRing.maximalIdeal R) 1)
    (hi : Function.Injective (aeval (R:=R ⧸ IsLocalRing.maximalIdeal R) z)) (N : ℕ) :
    ∑ n ∈ Finset.range N,s.multichoose n ≤ colength R N := by
  let m := IsLocalRing.maximalIdeal R
  have H : (∑ n ∈ Finset.range N,(s.multichoose n : ℕ∞)) ≤
      Module.length R (R ⧸ m^N) := by
    rw [IdealGraded.length_eq_sum]
    apply Finset.sum_le_sum
    intro n _
    rw [IdealGraded.length_piece_eq_finrank]
    have hdeg : s.multichoose n ≤ Module.finrank (R ⧸ m) (IdealGraded.grade m n) :=
      @degree_finrank_lower (R ⧸ m) (Ideal.Quotient.field m)
        (IdealGraded.Ring m) inferInstance (IdealGraded.gradedAlgebra m)
        (IdealGraded.grade m) (IdealGraded.gradeGradedAlgebra m)
        s z hz hi n (IdealGraded.gradeFinite m n)
    have hp : Module.finrank (R ⧸ m) (IdealGraded.Piece m n) =
        Module.finrank (R ⧸ m) (IdealGraded.grade m n) :=
      (IdealGraded.pieceEquiv m n).finrank_eq
    exact ENat.natCast_le_natCast.mpr (hdeg.trans_eq hp.symm)
  rw [← colength_cast R N,← Nat.cast_sum] at H
  exact_mod_cast H

lemma generator_number_le_dimension_oai {s : ℕ}
    (z : Fin s → IdealGraded.Ring (IsLocalRing.maximalIdeal R))
    (hz : ∀ i,z i ∈ IdealGraded.grade (IsLocalRing.maximalIdeal R) 1)
    (hi : Function.Injective (aeval (R:=R ⧸ IsLocalRing.maximalIdeal R) z)) :
    s ≤ dimension R := by
  obtain ⟨C,hC⟩ := colength_polynomial_bound R
  by_contra hs
  have hsd : dimension R+1 ≤ s := by omega
  let N := s.factorial*C+1
  have hN : 0<N := by dsimp [N]; omega
  have hchoose : (N+s-1).choose s ≤ colength R N := by
    have H := polynomial_rank_le_colength z hz hi N
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [ht,Nat.sum_range_multichoose] at H
    simpa only [ht,Nat.add_right_comm t 1 s,Nat.add_sub_cancel] using H
  have hpow : N^s ≤ s.factorial*colength R N :=
    (Nat.pow_succ_le_ascFactorial N s).trans (by
      rw [Nat.ascFactorial_eq_factorial_mul_choose']
      exact Nat.mul_le_mul_left _ hchoose)
  have htotal : N^(dimension R+1) ≤ N^dimension R*(s.factorial*C) := by
    calc
      N^(dimension R+1) ≤ N^s := Nat.pow_le_pow_right hN hsd
      _ ≤ s.factorial*colength R N := hpow
      _ ≤ s.factorial*(N^dimension R*C) := Nat.mul_le_mul_left _ (hC N)
      _ = N^dimension R*(s.factorial*C) := by ac_rfl
  rw [pow_succ] at htotal
  have hbad : N ≤ s.factorial*C := Nat.le_of_mul_le_mul_left htotal (Nat.pow_pos hN)
  dsimp [N] at hbad
  omega
end Lech.LinearNormalization

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.LinearNormalization.generator_number_le_dimension_oai.{u} := @OAI.Lech.LinearNormalization.generator_number_le_dimension_oai.{u}
