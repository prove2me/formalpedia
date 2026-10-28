-- Prove2me | solution 1 for OAI.Lech.Normalization.parameter_frobenius_multiplicity_enn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:22:24.98221+00:00
-- url     : https://prove2.me/submissions/8fa91d87-9a92-4bac-9aad-dd5273732582

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L009
import Definitions.Def_OAIQ032L025
import Theorems.Thm_OAI_Lech_PowerSeries_finite_module_two_limits

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

end IdealGraded
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.IdealGraded.reesGradedAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.SourceGraded.target_graded _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.Normalization
variable {R S : Type*} [CommRing R] [CommRing S]

 
lemma dimension_le_of_integral (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro p q hpq
  exact Ideal.IsIntegral.comap_lt_comap hpq

 
lemma injective_of_integral_dimension [IsDomain R] (f : R →+* S) (hf : f.IsIntegral)
    {h : ℕ} (hS : (h : WithBot ℕ∞) ≤ ringKrullDim S) (hR : ringKrullDim R ≤ h) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro r hr
  by_contra hn
  have hd := dimension_le_of_integral f.kerLift hf.kerLift
  have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (RingHom.ker f))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hh : (h : WithBot ℕ∞) + 1 ≤ h :=
    (add_le_add (hS.trans hd) le_rfl).trans (hdrop.trans hR)
  norm_cast at hh
  omega

end Lech.Normalization


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
-- module Solutions.OAIQ032_LECH.Multiplicity_SeparableOrderNormalizedLength
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.Grading
open DirectSum
variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
  [Decomposition G] [Decomposition H]

lemma proj_of_mem {i j : ℕ} {x : M} (hx : x ∈ G i) :
    projection G j x = if i = j then x else 0 := by
  by_cases hij : i = j
  · subst j
    simp [DirectSum.decompose_of_mem_same G hx]
  · simp [hij, DirectSum.decompose_of_mem_ne G hx hij]

variable (f : M →ₗ[R] N)
variable (hf : ∀ i, (G i).map f ≤ H (i + 1))
include hf

lemma projection_succ_comp (i : ℕ) :
    (projection H (i + 1)).comp f = f.comp (projection G i) := by
  apply DirectSum.decompose_lhom_ext G
  intro j
  apply LinearMap.ext
  intro x
  have hfx : f (x : M) ∈ H (j + 1) := hf j (Submodule.mem_map_of_mem x.property)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [proj_of_mem H hfx, proj_of_mem G x.property]
  by_cases hi : j = i <;> simp [hi]

lemma projection_zero_comp : (projection H 0).comp f = 0 := by
  apply DirectSum.decompose_lhom_ext G
  intro j
  apply LinearMap.ext
  intro x
  have hfx : f (x : M) ∈ H (j + 1) := hf j (Submodule.mem_map_of_mem x.property)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply]
  rw [proj_of_mem H hfx]
  simp

lemma ker_homogeneous : f.ker.IsHomogeneous G := by
  intro i x hx
  change f (projection G i x) = 0
  rw [← LinearMap.comp_apply, ← projection_succ_comp G H f hf,
    LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]

lemma range_homogeneous : f.range.IsHomogeneous H := by
  intro i y hy
  obtain ⟨x, rfl⟩ := hy
  cases i with
  | zero =>
      have h := DFunLike.congr_fun (projection_zero_comp G H f hf) x
      change projection H 0 (f x) ∈ f.range
      rw [show projection H 0 (f x) = 0 from h]
      exact f.range.zero_mem
  | succ i =>
      refine ⟨projection G i x, ?_⟩
      exact (DFunLike.congr_fun (projection_succ_comp G H f hf i) x).symm

omit [Decomposition G] [Decomposition H] in
lemma step_ker (i : ℕ) : (step G H f hf i).ker = f.ker.comap (G i).subtype := by
  ext x
  simp [LinearMap.mem_ker, Subtype.ext_iff]

lemma step_range (i : ℕ) :
    (step G H f hf i).range = f.range.comap (H (i + 1)).subtype := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    change f x = (y : N) at hx
    refine ⟨decompose G x i, ?_⟩
    apply Subtype.ext
    change f (projection G i x) = (y : N)
    have he := DFunLike.congr_fun (projection_succ_comp G H f hf i) x
    rw [LinearMap.comp_apply, hx, proj_of_mem H y.property, ite_eq_left rfl] at he
    exact he.symm

end Lech.Grading


namespace Lech
open Polynomial Filter
open scoped BigOperators

lemma sumPolynomial_eval (p : ℚ[X]) (n : ℕ) :
    (sumPolynomial p).eval (n : ℚ) = ∑ k ∈ Finset.range n, p.eval (k : ℚ) := by
  simp only [sumPolynomial, eval_finsetSum, eval_mul, eval_C, eval_sub]
  have h (j : ℕ) :
      Polynomial.eval (n : ℚ) (Polynomial.bernoulli (j + 1)) - _root_.bernoulli (j + 1) =
        (j + 1 : ℚ) * ∑ k ∈ Finset.range n, (k : ℚ) ^ j :=
    (Polynomial.sum_range_pow_eq_bernoulli_sub n j).symm
  simp_rw [h]
  have hn (j : ℕ) : (j + 1 : ℚ) ≠ 0 := by positivity
  simp_rw [← mul_assoc, div_mul_cancel₀ _ (hn _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  exact (Polynomial.eval_eq_sum (p := p) (x := (k : ℚ))).symm

lemma EventuallyPolynomial.sub {f g : ℕ → ℚ}
    (hf : EventuallyPolynomial f) (hg : EventuallyPolynomial g) :
    EventuallyPolynomial (fun n => f n - g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, by filter_upwards [hp, hq] with n hn hm; simp [hn, hm]⟩

lemma EventuallyPolynomial.succ {f : ℕ → ℚ} (hf : EventuallyPolynomial f) :
    EventuallyPolynomial (fun n => f (n + 1)) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨p.comp (Polynomial.X + 1), ?_⟩
  have ht := (Filter.tendsto_add_atTop_nat 1).eventually hp
  filter_upwards [ht] with n hn
  simpa using hn

lemma EventuallyPolynomial.of_sub_succ {f : ℕ → ℚ}
    (hf : EventuallyPolynomial (fun n => f (n + 1) - f n)) :
    EventuallyPolynomial f := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hp
  let q := sumPolynomial p
  have hq (n : ℕ) : q.eval (n + 1 : ℚ) - q.eval (n : ℚ) = p.eval (n : ℚ) := by
    have he := sumPolynomial_eval p (n + 1)
    rw [Finset.sum_range_succ, ← sumPolynomial_eval p n] at he
    dsimp [q]
    push_cast at he
    linarith
  refine ⟨q + Polynomial.C (f N - q.eval (N : ℚ)), Filter.eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hstep := hN n hn
      have hqstep := hq n
      simp only [eval_add, eval_C] at ih ⊢
      push_cast
      linarith

lemma EventuallyPolynomial.of_recurrence {f k c : ℕ → ℚ}
    (hk : EventuallyPolynomial k) (hc : EventuallyPolynomial c)
    (hrec : ∀ n, f (n + 1) + k n = f n + c (n + 1)) : EventuallyPolynomial f := by
  apply EventuallyPolynomial.of_sub_succ
  have h := hc.succ.sub hk
  have he : (fun n => f (n + 1) - f n) = (fun n => c (n + 1) - k n) := by
    funext n
    linarith [hrec n]
  rwa [he]

end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHilbertSerre
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
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


namespace Lech
open Filter Polynomial
open scoped Topology

lemma degree_le_of_nat_bound (P : ℝ[X]) (d : ℕ) (C : ℝ)
    (hb : ∀ᶠ n : ℕ in atTop, |P.eval (n : ℝ)| ≤ C * (n : ℝ) ^ d) :
    P.degree ≤ d := by
  by_contra hn
  have hd : (Polynomial.X ^ d : ℝ[X]).degree < P.degree := by
    simpa only [degree_X_pow] using lt_of_not_ge hn
  have ht := (P.abs_div_tendsto_atTop_atTop_of_degree_gt (Polynomial.X ^ d) hd
    (pow_ne_zero d X_ne_zero)).comp tendsto_natCast_atTop_atTop
  have hh : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hb, ht.eventually (eventually_gt_atTop C), eventually_gt_atTop 0]
      with n hn hlarge hnpos
    have hpos : 0 < (n : ℝ) ^ d := pow_pos (by exact_mod_cast hnpos) _
    have hle : |P.eval (n : ℝ) / (n : ℝ) ^ d| ≤ C := by
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      exact hn
    simp only [Function.comp_apply, eval_pow, eval_X] at hlarge
    exact (not_lt_of_ge hle) hlarge
  obtain ⟨n, hn⟩ := hh.exists
  exact hn

lemma exists_polynomial_div_limit (P : ℝ[X]) (d : ℕ) (hd : P.degree ≤ d) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => P.eval (n : ℝ) / (n : ℝ) ^ d) atTop (𝓝 L) := by
  have hd' : P.degree ≤ (Polynomial.X ^ d : ℝ[X]).degree := by
    simpa only [degree_X_pow] using hd
  rcases lt_or_eq_of_le hd' with hlt | heq
  · refine ⟨0, ?_⟩
    simpa only [Function.comp_def, eval_pow, eval_X] using
      (P.div_tendsto_atTop_zero_of_degree_lt (Polynomial.X ^ d) hlt).comp
        tendsto_natCast_atTop_atTop
  · refine ⟨P.leadingCoeff / (Polynomial.X ^ d : ℝ[X]).leadingCoeff, ?_⟩
    simpa only [Function.comp_def, eval_pow, eval_X] using
      (P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq (Polynomial.X ^ d) heq).comp
        tendsto_natCast_atTop_atTop

lemma exists_div_limit_of_eventually_polynomial (f : ℕ → ℕ) (d : ℕ)
    (hp : ∃ p : ℚ[X], ∀ᶠ n in atTop, (f n : ℚ) = p.eval (n : ℚ))
    (hb : ∃ C : ℕ, ∀ n, f n ≤ n ^ d * C) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ) ^ d) atTop (𝓝 L) := by
  obtain ⟨p, hp⟩ := hp
  obtain ⟨C, hC⟩ := hb
  let P := p.map (algebraMap ℚ ℝ)
  have he : ∀ᶠ n in atTop, (f n : ℝ) = P.eval (n : ℝ) := by
    filter_upwards [hp] with n hn
    have h := congrArg (algebraMap ℚ ℝ) hn
    simpa only [map_natCast, ← eval₂_at_apply, ← Polynomial.eval_map] using h
  have hbd : ∀ᶠ n : ℕ in atTop, |P.eval (n : ℝ)| ≤ (C : ℝ) * (n : ℝ) ^ d := by
    filter_upwards [he] with n hn
    rw [← hn, abs_of_nonneg (Nat.cast_nonneg _), mul_comm]
    exact_mod_cast hC n
  obtain ⟨L, hL⟩ := exists_polynomial_div_limit P d (degree_le_of_nat_bound P d C hbd)
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [he] with n hn
  rw [hn]
end Lech


namespace Lech.LengthHilbert
open Lech.Grading DirectSum Filter
variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
variable (G : ℕ → Submodule K M) [Decomposition G]

lemma eventually_eq_bot [Module.Finite K M] : ∀ᶠ n in atTop, G n = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := M)
  let t := s.biUnion (fun x => (decompose G x).support)
  refine Filter.eventually_atTop.mpr ⟨t.sup id + 1, fun n hn => ?_⟩
  have hp : projection G n = 0 := by
    apply (Submodule.linearMap_eq_zero_iff_of_span_eq_top _ hs).mpr
    intro x
    have hnot : n ∉ (decompose G x.val).support := by
      intro hx
      have hnt : n ∈ t := Finset.mem_biUnion.mpr ⟨x.val, x.property, hx⟩
      have ht := Finset.le_sup (f := id) hnt
      dsimp at ht
      omega
    have hz : decompose G x.val n = 0 := DFinsupp.notMem_support_iff.mp hnot
    exact congrArg (fun z : G n => (z : M)) hz
  apply eq_bot_iff.mpr
  intro x hx
  rw [Submodule.mem_bot]
  have he := DFunLike.congr_fun hp x
  simpa [proj_of_mem G hx] using he

omit [Decomposition G] in
lemma subPiece_length (P : Submodule K M) (i : ℕ) :
    Module.length K (subPiece G P i) = Module.length K (P.comap (G i).subtype) := by
  let e : subPiece G P i ≃ₗ[K] P.comap (G i).subtype :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.length_eq

variable {N : Type*} [AddCommGroup N] [Module K N]
omit [Decomposition G] in
lemma pieceMap_surjective (q : M →ₗ[K] N) (i : ℕ) :
    Function.Surjective (pieceMap G q i) := by
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

omit [Decomposition G] in
lemma pieceMap_ker (q : M →ₗ[K] N) (i : ℕ) :
    (pieceMap G q i).ker = q.ker.comap (G i).subtype := by
  ext x
  simp [LinearMap.mem_ker, Subtype.ext_iff]

lemma length_range_add_length_ker {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] (g : V →ₗ[K] W) :
    Module.length K g.range + Module.length K g.ker = Module.length K V := by
  have he := Module.length_eq_add_of_exact (LinearMap.ker g.rangeRestrict).subtype
    g.rangeRestrict (Submodule.subtype_injective _) g.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map g.rangeRestrict)
  rw [LinearMap.ker_rangeRestrict] at he
  simpa only [add_comm] using he.symm

lemma length_recurrence [IsArtinianRing K] [IsNoetherianRing K]
    [∀ i, Module.Finite K (G i)]
    (f : M →ₗ[K] M) (hf : ∀ i, (G i).map f ≤ G (i + 1))
    (q : M →ₗ[K] N) (hq : q.ker = f.range) (i : ℕ) :
    (Module.length K (G (i + 1))).toNat + (Module.length K (subPiece G f.ker i)).toNat =
      (Module.length K (G i)).toNat + (Module.length K (imagePiece G q (i + 1))).toNat := by
  have h1 := length_range_add_length_ker (step G G f hf i)
  have h2 := length_range_add_length_ker (pieceMap G q (i + 1))
  have he : Module.length K (pieceMap G q (i + 1)).range =
      Module.length K (imagePiece G q (i + 1)) := by
    rw [LinearMap.range_eq_top.mpr (pieceMap_surjective G q (i + 1))]
    simp
  have h1' := congrArg ENat.toNat h1
  have h2' := congrArg ENat.toNat h2
  rw [ENat.toNat_add Module.length_ne_top Module.length_ne_top] at h1' h2'
  rw [he, pieceMap_ker, hq, ← step_range G G f hf i] at h2'
  rw [step_ker] at h1'
  rw [subPiece_length]
  omega

end Lech.LengthHilbert


namespace Lech.LengthHilbert

variable {K S M : Type*} [CommRing K] [CommRing S] [Algebra K S]
  [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]

lemma quotient_generators {n : ℕ} (x : Fin (n + 1) → S)
    (hx : Algebra.adjoin K (Set.range x) = ⊤) :
    Algebra.adjoin K (Set.range (fun i : Fin n =>
      Ideal.Quotient.mk (Ideal.span {x 0}) (x i.succ))) = ⊤ := by
  let q := Ideal.Quotient.mkₐ K (Ideal.span {x 0})
  have he := congrArg (Subalgebra.map q) hx
  rw [AlgHom.map_adjoin, Algebra.map_top,
    (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mk_surjective)] at he
  rw [Fin.range_fin_succ, Set.image_insert_eq, ← Set.range_comp] at he
  have hzero : q (x 0) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hzero, Algebra.adjoin_insert_zero] at he
  exact he

lemma finite_of_no_generators [Module.Finite S M]
    (hx : Algebra.adjoin K (∅ : Set S) = ⊤) : Module.Finite K M := by
  have hs : Function.Surjective (algebraMap K S) := by
    apply Algebra.surjective_algebraMap_iff.mpr
    simpa only [Algebra.adjoin_empty] using hx.symm
  exact ⟨by simpa using (Module.Finite.fg_top (R := S) (M := M)).restrictScalars_of_surjective hs⟩

variable (x : S)

lemma ker_smul_killed : Module.IsTorsionBy S (LinearMap.lsmul S M x).ker x := by
  intro m
  apply Subtype.ext
  exact LinearMap.mem_ker.mp m.property

lemma coker_smul_killed : Module.IsTorsionBy S (M ⧸ (LinearMap.lsmul S M x).range) x := by
  apply (Module.isTorsionBy_quotient_iff _ _).mpr
  intro m
  exact ⟨m, rfl⟩

end Lech.LengthHilbert


namespace Lech.LengthHilbert
open DirectSum
universe u v w
variable (K : Type u) [CommRing K] [IsArtinianRing K] [IsNoetherianRing K]

theorem hilbertSerre (n : ℕ) (S : Type v) (M : Type w)
    [CommRing S] [Algebra K S] [IsNoetherianRing S]
    [AddCommGroup M] [Module S M] [Module K M] [IsScalarTower K S M]
    [Module.Finite S M]
    (x : Fin n → S) (hx : Algebra.adjoin K (Set.range x) = ⊤)
    (G : ℕ → Submodule K M) [Decomposition G]
    [∀ i, Module.Finite K (G i)]
    (hG : ∀ j i (m : M), m ∈ G i → x j • m ∈ G (i + 1)) :
    EventuallyPolynomial (fun i => ((Module.length K (G i)).toNat : ℚ)) := by
  induction n generalizing S M with
  | zero =>
      have hx0 : Algebra.adjoin K (∅ : Set S) = ⊤ := by simpa using hx
      let : Module.Finite K M := finite_of_no_generators hx0
      refine ⟨0, ?_⟩
      filter_upwards [LengthHilbert.eventually_eq_bot G] with i hi
      rw [hi, Module.length_bot]
      simp
  | succ n ih =>
      let fS : M →ₗ[S] M := LinearMap.lsmul S M (x 0)
      let f : M →ₗ[K] M := fS.restrictScalars K
      have hf : ∀ i, (G i).map f ≤ G (i + 1) := by
        rintro i _ ⟨m, hm, rfl⟩
        exact hG 0 i m hm
      let P : Submodule S M := fS.ker
      let Q : Submodule S M := fS.range
      let V := M ⧸ Q
      let q : M →ₗ[K] V := Q.mkQ.restrictScalars K
      let S' := S ⧸ Ideal.span {x 0}
      let x' : Fin n → S' := fun j => Ideal.Quotient.mk _ (x j.succ)
      have hx' : Algebra.adjoin K (Set.range x') = ⊤ := quotient_generators x hx
      let hPkill : Module.IsTorsionBy S P (x 0) := ker_smul_killed (M := M) (x 0)
      let hVkill : Module.IsTorsionBy S V (x 0) := coker_smul_killed (M := M) (x 0)
      let : Module S' P := hPkill.module
      let : Module S' V := hVkill.module
      have : IsScalarTower K S' P := inferInstance
      have : IsScalarTower K S' V := inferInstance
      have : IsScalarTower S S' P := inferInstance
      have : IsScalarTower S S' V := inferInstance
      have : Module.Finite S' P := Module.Finite.of_restrictScalars_finite S S' P
      have : Module.Finite S' V := Module.Finite.of_restrictScalars_finite S S' V
      let GP : ℕ → Submodule K P := fun i => (G i).comap (P.subtype.restrictScalars K)
      let GV : ℕ → Submodule K V := Grading.imagePiece G q
      have hPhom : (P.restrictScalars K).IsHomogeneous G := by
        exact Grading.ker_homogeneous G G f hf
      have hQhom : q.ker.IsHomogeneous G := by
        have hker : q.ker = f.range := by
          change (Q.mkQ.restrictScalars K).ker = f.range
          rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
          rfl
        rw [hker]
        exact Grading.range_homogeneous G G f hf
      let : Decomposition GP := Grading.subDecomposition G (P.restrictScalars K) hPhom
      let : Decomposition GV := Grading.imageDecomposition G q Q.mkQ_surjective hQhom
      have (i : ℕ) : Module.Finite K (GP i) := by
        exact Module.Finite.of_injective (Grading.subPieceMap G (P.restrictScalars K) i)
          (by
            intro a b h
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z : G i => (z : M)) h)
      have (i : ℕ) : Module.Finite K (GV i) := by
        exact Module.Finite.of_surjective (Grading.pieceMap G q i)
          (LengthHilbert.pieceMap_surjective G q i)
      have hGP : ∀ j i (m : P), m ∈ GP i → x' j • m ∈ GP (i + 1) := by
        intro j i m hm
        change x j.succ • (m : M) ∈ G (i + 1)
        exact hG j.succ i m hm
      have hGV : ∀ j i (m : V), m ∈ GV i → x' j • m ∈ GV (i + 1) := by
        rintro j i _ ⟨m, hm, rfl⟩
        refine ⟨x j.succ • m, hG j.succ i m hm, ?_⟩
        exact Q.mkQ.map_smul _ _
      have hpolP := ih S' P x' hx' GP hGP
      have hpolV := ih S' V x' hx' GV hGV
      apply EventuallyPolynomial.of_recurrence hpolP hpolV
      intro i
      have hker : q.ker = f.range := by
        rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
        rfl
      have he := LengthHilbert.length_recurrence G f hf q hker i
      exact_mod_cast he

end Lech.LengthHilbert
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
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
namespace Lech.IdealGraded
open Filter
variable {R : Type*} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
lemma length_piece_eq_length (I : Ideal R) (n : ℕ) :
    Module.length R (Piece I n) = Module.length (R ⧸ I) (Piece I n) := by
  apply Module.length_eq_of_surjective
  simpa only [Ideal.Quotient.algebraMap_eq] using
    (Ideal.Quotient.mk_surjective (I := I))

lemma eventuallyPolynomial_piece_length (I : Ideal R) [IsArtinianRing (R ⧸ I)] :
    Lech.EventuallyPolynomial (fun n => ((Module.length R (Piece I n)).toNat : ℚ)) := by
  obtain ⟨n, x, hx, hxmem⟩ := exists_generators I
  have h := Lech.LengthHilbert.hilbertSerre (R ⧸ I) n (Ring I) (Ring I) x hx
    (grade I) (by
      intro j i m hm
      simpa only [smul_eq_mul, add_comm] using grade_mul I (hxmem j) hm)
  have he (n : ℕ) : Module.length R (Piece I n) = Module.length (R ⧸ I) (grade I n) := by
    rw [length_piece_eq_length]
    exact (pieceEquiv I n).length_eq
  simpa only [he] using h

lemma eventuallyPolynomial_length_of_artinian (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] :
    Lech.EventuallyPolynomial (fun n => ((Module.length R (R ⧸ I ^ n)).toNat : ℚ)) := by
  have hfin (n : ℕ) : Module.length R (Piece I n) ≠ ⊤ := by
    rw [length_piece_eq_length]
    exact Module.length_ne_top
  have hsum (N : ℕ) : Module.length R (R ⧸ I ^ N) ≠ ⊤ := by
    rw [length_eq_sum]
    exact ENat.sum_ne_top.mpr (fun n _ => hfin n)
  apply Lech.EventuallyPolynomial.of_sub_succ
  have he : (fun n => ((Module.length R (R ⧸ I ^ (n + 1))).toNat : ℚ) -
      ((Module.length R (R ⧸ I ^ n)).toNat : ℚ)) =
      (fun n => ((Module.length R (Piece I n)).toNat : ℚ)) := by
    funext n
    rw [length_successor, ENat.toNat_add (hfin n) (hsum n), Nat.cast_add,
      add_sub_cancel_right]
  rw [he]
  exact eventuallyPolynomial_piece_length I
end Lech.IdealGraded


namespace Lech.Primary
open Filter
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma artinian_quotient (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    IsArtinianRing (R ⧸ I) := by
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I
  rw [← Ideal.radical_minimalPrimes, hI, Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

lemma exists_maximal_pow_le (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∃ a : ℕ, (IsLocalRing.maximalIdeal R) ^ a ≤ I := by
  simpa only [hI] using I.exists_radical_pow_le_of_fg I.radical.fg_of_isNoetherianRing

lemma length_ne_top (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (N : ℕ) :
    Module.length R (R ⧸ I ^ N) ≠ ⊤ := by
  obtain ⟨a, ha⟩ := exists_maximal_pow_le I hI
  have hle := Lech.length_quotient_le R (show
    (IsLocalRing.maximalIdeal R) ^ (a * N) ≤ I ^ N by
      rw [pow_mul]
      exact pow_le_pow_left' ha N)
  exact ne_top_of_le_ne_top (Lech.quotient_length_ne_top R (a * N)) hle

lemma colength_cast (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (N : ℕ) :
    (colength I N : ℕ∞) = Module.length R (R ⧸ I ^ N) :=
  ENat.natCast_toNat (length_ne_top I hI N)

lemma polynomial_bound (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∃ C : ℕ, ∀ N : ℕ, colength I N ≤ N ^ Lech.dimension R * C := by
  obtain ⟨a, ha⟩ := exists_maximal_pow_le I hI
  obtain ⟨C, hC⟩ := Lech.colength_polynomial_bound R
  refine ⟨a ^ Lech.dimension R * C, fun N => ?_⟩
  have hle := Lech.length_quotient_le R (show
    (IsLocalRing.maximalIdeal R) ^ (a * N) ≤ I ^ N by
      rw [pow_mul]
      exact pow_le_pow_left' ha N)
  rw [← colength_cast I hI N, ← Lech.colength_cast R (a * N)] at hle
  apply (ENat.natCast_le_natCast.mp hle).trans
  simpa only [mul_pow, mul_assoc, mul_left_comm] using hC (a * N)

theorem multiplicity_is_limit (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    Tendsto (normalizedColength I) atTop (𝓝 (multiplicity I)) := by
  let := artinian_quotient I hI
  obtain ⟨L, hL⟩ := Lech.exists_div_limit_of_eventually_polynomial (colength I)
    (Lech.dimension R) (IdealGraded.eventuallyPolynomial_length_of_artinian I)
    (polynomial_bound I hI)
  have ht : Tendsto (normalizedColength I) atTop
      (𝓝 ((Nat.factorial (Lech.dimension R) : ℝ) * L)) := by
    change Tendsto (fun N => (Nat.factorial (Lech.dimension R) : ℝ) *
      (colength I N : ℝ) / (N : ℝ) ^ Lech.dimension R) atTop
        (𝓝 ((Nat.factorial (Lech.dimension R) : ℝ) * L))
    simpa only [mul_div_assoc] using
      hL.const_mul (Nat.factorial (Lech.dimension R) : ℝ)
  rw [show multiplicity I = (Nat.factorial (Lech.dimension R) : ℝ) * L from ht.limUnder_eq]
  exact ht

end Lech.Primary


open CategoryTheory
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFinDimension
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
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
open CategoryTheory


namespace Lech.LocalAlgebra
open IsLocalRing
variable (A D : Type*) [CommRing A] [CommRing D] [IsLocalRing A] [IsLocalRing D]
  [Algebra A D] [IsLocalHom (algebraMap A D)]

lemma quotient_length_eq (I : Ideal A)
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField D))) :
    Module.length A (D ⧸ I • (⊤ : Submodule A D)) =
      Module.length D (D ⧸ I.map (algebraMap A D)) := by
  rw [Ideal.smul_top_eq_map]
  rw [(Submodule.Quotient.restrictScalarsEquiv A (I.map (algebraMap A D))).length_eq]
  rw [IsLocalRing.length_restrictScalars A D _,
    Module.length_eq_of_surjective (R := ResidueField D) hres]
  simp

end Lech.LocalAlgebra


namespace Lech.PowerSeries
open MvPowerSeries IsLocalRing Filter
open scoped Topology
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  (h : ℕ) [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]

 

theorem parameter_powers_limit (hh : 0 < h) (hdim : Lech.dimension D = h)
    (hres : Function.Surjective (algebraMap (ResidueField (MvPowerSeries (Fin h) k))
      (ResidueField D)))
    (hprim : ((maximalIdeal (MvPowerSeries (Fin h) k)).map
      (algebraMap (MvPowerSeries (Fin h) k) D)).radical = maximalIdeal D) :
    Tendsto (fun q : ℕ => ((Module.length D (D ⧸
      (Ideal.span (Set.range fun i : Fin h => (X i : MvPowerSeries (Fin h) k)^q)).map
        (algebraMap (MvPowerSeries (Fin h) k) D))).toNat : ℝ) / (q : ℝ)^h)
      atTop (𝓝 (Lech.Primary.multiplicity ((maximalIdeal (MvPowerSeries (Fin h) k)).map
        (algebraMap (MvPowerSeries (Fin h) k) D)))) := by
  obtain ⟨r,hrm,hrp⟩ := finite_module_two_limits (k := k) h hh D
  have hm : Tendsto (Lech.Primary.normalizedColength ((maximalIdeal (MvPowerSeries (Fin h) k)).map
      (algebraMap (MvPowerSeries (Fin h) k) D))) atTop (𝓝 (r : ℝ)) := by
    apply hrm.congr
    intro q
    rw [Lech.LocalAlgebra.quotient_length_eq _ _ _ hres,Ideal.map_pow]
    simp only [Lech.Primary.normalizedColength,Lech.Primary.colength,hdim]
  have he : Lech.Primary.multiplicity ((maximalIdeal (MvPowerSeries (Fin h) k)).map
      (algebraMap (MvPowerSeries (Fin h) k) D)) = (r : ℝ) := tendsto_nhds_unique (Lech.Primary.multiplicity_is_limit _ hprim) hm
  rw [he]
  apply hrp.congr
  intro q
  rw [Lech.LocalAlgebra.quotient_length_eq _ _ _ hres]

end Lech.PowerSeries


namespace Lech.Normalization
open IsLocalRing
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [Algebra k D]

lemma finite_primary_quotient (I : Ideal D) (hI : I.radical = maximalIdeal D)
    (hres : Function.Surjective (algebraMap k (ResidueField D))) : Module.Finite k (D ⧸ I) := by
  let : IsArtinianRing (D ⧸ I) := by
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I
    rw [← Ideal.radical_minimalPrimes,hI,Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  let : IsArtinian D (D ⧸ I) := isArtinian_of_surjective_algebraMap (R := D ⧸ I) (M := D ⧸ I)
    (S := D) Ideal.Quotient.mk_surjective
  have hs : Function.Surjective (algebraMap (ResidueField k) (ResidueField D)) := by
    intro y
    obtain ⟨x,hx⟩ := hres y
    exact ⟨residue k x,hx⟩
  have hl : Module.length k (D ⧸ I) = Module.length D (D ⧸ I) := by
    rw [IsLocalRing.length_restrictScalars k D (D ⧸ I),Module.length_eq_of_surjective hs]
    simp
  have hfin : IsFiniteLength k (D ⧸ I) := Module.length_ne_top_iff.mp (by
    rw [hl]; exact Module.length_ne_top)
  let : IsNoetherian k (D ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  infer_instance

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable {σ k D : Type*} [Fintype σ] [Field k] [CommRing D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
  (z : σ → D) (hz : ∀ i, z i ∈ maximalIdeal D)

include hφ in
 

theorem finite_parameter_algebra
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    let : Algebra (MvPowerSeries σ k) D :=
      (Lech.PowerSeries.eval φ (maximalIdeal D) z hz).toAlgebra
    Module.Finite (MvPowerSeries σ k) D := by
  let A := MvPowerSeries σ k
  let I := Lech.PowerSeries.variablesIdeal σ k
  let J : Ideal D := Ideal.span (Set.range z)
  let : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra k D := φ.toAlgebra
  let : Algebra A D := ψ.toAlgebra
  let : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (Lech.PowerSeries.eval_C φ (maximalIdeal D) z hz a).symm)
  have hmap : I.map (algebraMap A D) = J := by
    change (Ideal.span (Set.range (X : σ → A))).map (algebraMap A D) = J
    rw [Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    exact congrArg Set.range (funext (fun i => Lech.PowerSeries.eval_X φ (maximalIdeal D) z hz i))
  have hJ : J ≤ maximalIdeal D := Ideal.span_le.mpr (Set.range_subset_iff.mpr hz)
  let : IsHausdorff I D := IsHausdorff.of_map (I := I) (J := maximalIdeal D) (by rw [hmap]; exact hJ)
  let : IsPrecomplete I A := (Lech.PowerSeries.complete_variables σ k).toIsPrecomplete
  let : Module.Finite k (D ⧸ J) := finite_primary_quotient J hprim hφ
  let : Module.Finite A (D ⧸ J) := Module.Finite.of_restrictScalars_finite k A (D ⧸ J)
  have hsub : I • (⊤ : Submodule A D) = J.restrictScalars A := by
    rw [← hmap]
    symm
    simpa only [smul_eq_mul,Ideal.mul_top,Submodule.restrictScalars_top] using
      Submodule.restrictScalars_map_smul_eq I (⊤ : Submodule D D)
  let e := (Submodule.quotEquivOfEq _ _ hsub).trans (Submodule.Quotient.restrictScalarsEquiv A J)
  let : Module.Finite A (D ⧸ (I • (⊤ : Submodule A D))) := Module.Finite.equiv e.symm
  exact Lech.AdicNakayama.finite_of_quotient I

end Lech.Normalization


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CoefficientFieldLocalSection
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
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
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory


namespace Lech.Normalization
open IsLocalRing MvPowerSeries
variable {σ k D : Type*} [Fintype σ] [Field k] [CommRing D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (φ : k →+* D) (hφ : Function.Surjective ((residue D).comp φ))
  (z : σ → D) (hz : ∀ i, z i ∈ maximalIdeal D)

include hφ in
lemma parameter_eval_finite (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    (Lech.PowerSeries.eval φ (maximalIdeal D) z hz).Finite :=
  finite_parameter_algebra φ hφ z hz hprim

include hφ in
lemma parameter_eval_injective (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D)
    (hdim : (Fintype.card σ : WithBot ℕ∞) ≤ ringKrullDim D) :
    Function.Injective (Lech.PowerSeries.eval φ (maximalIdeal D) z hz) := by
  let : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra (MvPowerSeries σ k) D := ψ.toAlgebra
  let : Module.Finite (MvPowerSeries σ k) D := finite_parameter_algebra φ hφ z hz hprim
  exact injective_of_integral_dimension ψ (Algebra.IsIntegral.isIntegral)
    hdim (Lech.PowerSeries.dimension_le_variables σ k)

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing MvPowerSeries Filter
open scoped Topology
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D]

 

theorem parameter_powers_multiplicity (h : ℕ) (hh : 0 < h)
    (hdim : Lech.dimension D = h) (φ : k →+* D)
    (hφ : Function.Surjective ((residue D).comp φ)) (z : Fin h → D)
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    Tendsto (fun q : ℕ => ((Module.length D
      (D ⧸ Ideal.span (Set.range fun i : Fin h => z i^q))).toNat : ℝ) / (q : ℝ)^h)
      atTop (𝓝 (Lech.Primary.multiplicity (Ideal.span (Set.range z)))) := by
  have hz : ∀ i, z i ∈ maximalIdeal D := fun i => by
    rw [← hprim]
    exact Ideal.le_radical (Ideal.subset_span ⟨i,rfl⟩)
  let A := MvPowerSeries (Fin h) k
  let ψ := Lech.PowerSeries.eval φ (maximalIdeal D) z hz
  let : Algebra A D := ψ.toAlgebra
  let : Module.Finite A D := parameter_eval_finite φ hφ z hz hprim
  have hinj : Function.Injective ψ := parameter_eval_injective φ hφ z hz hprim (by
    rw [Fintype.card_fin,← hdim,Lech.dimension_cast])
  let : IsLocalHom (algebraMap A D) :=
    RingHom.IsIntegral.isLocalHom (f := ψ) Algebra.IsIntegral.isIntegral hinj
  have hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField D)) := by
    intro b
    obtain ⟨a,ha⟩ := hφ b
    refine ⟨residue A (C a),?_⟩
    rw [ResidueField.algebraMap_residue]
    change residue D (ψ (C a)) = b
    rw [Lech.PowerSeries.eval_C]
    exact ha
  have hm : (maximalIdeal A).map (algebraMap A D) = Ideal.span (Set.range z) := by
    rw [Lech.PowerSeries.maximalIdeal_eq_variables,Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact Lech.PowerSeries.eval_X φ (maximalIdeal D) z hz i
  have hp (q : ℕ) : (Ideal.span (Set.range fun i : Fin h => (X i : A)^q)).map
      (algebraMap A D) = Ideal.span (Set.range fun i => z i^q) := by
    rw [Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    change ψ ((MvPowerSeries.X i)^q) = z i^q
    rw [map_pow,Lech.PowerSeries.eval_X]
  have ht := Lech.PowerSeries.parameter_powers_limit (k := k) (D := D) h hh hdim hres
    (by rwa [hm])
  change Tendsto (fun q : ℕ => ((Module.length D
    (D ⧸ (Ideal.span (Set.range fun i : Fin h => (X i : A)^q)).map
      (algebraMap A D))).toNat : ℝ) / (q : ℝ)^h) atTop
    (𝓝 (Lech.Primary.multiplicity ((maximalIdeal A).map (algebraMap A D)))) at ht
  rw [hm] at ht
  apply ht.congr
  intro q
  rw [hp q]

end Lech.Normalization


namespace Lech.Normalization
open IsLocalRing Filter
open scoped Topology ENNReal
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D]

omit [Field k] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D] in
lemma radical_span_powers {ι : Type*} (z : ι → D) (q : ℕ) (hq : q ≠ 0) :
    (Ideal.span (Set.range fun i => z i^q)).radical =
      (Ideal.span (Set.range z)).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self i)) q (Nat.pos_of_ne_zero hq)
  · apply Ideal.radical_le_radical_iff.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨q,Ideal.subset_span ⟨i,rfl⟩⟩

theorem parameter_powers_multiplicity_enn (h : ℕ) (hh : 0 < h)
    (hdim : Lech.dimension D = h) (φ : k →+* D)
    (hφ : Function.Surjective ((residue D).comp φ)) (z : Fin h → D)
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D) :
    Tendsto (fun q : ℕ => ((q : ℝ≥0∞)^h)⁻¹ * (Module.length D
      (D ⧸ Ideal.span (Set.range fun i : Fin h => z i^q))).toENNReal)
      atTop (𝓝 (ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z))))) := by
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (parameter_powers_multiplicity h hh hdim φ hφ z hprim)
  simp only [Function.comp_def] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hf : Module.length D (D ⧸ Ideal.span (Set.range fun i => z i^q)) ≠ ⊤ := by
    have hf := Lech.Primary.length_ne_top
      (Ideal.span (Set.range fun i => z i^q))
      ((radical_span_powers z q (by omega)).trans hprim) 1
    rw [pow_one] at hf
    exact hf
  rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast,ENNReal.ofReal_natCast,div_eq_mul_inv,mul_comm]
  congr 1
  exact congrArg ENat.toENNReal (ENat.natCast_toNat hf)

 

theorem parameter_frobenius_multiplicity_enn_oai (h : ℕ) (hh : 0 < h)
    (hdim : Lech.dimension D = h) (φ : k →+* D)
    (hφ : Function.Surjective ((residue D).comp φ)) (z : Fin h → D)
    (hprim : (Ideal.span (Set.range z)).radical = maximalIdeal D)
    (a : ℕ) (ha : 0 < a) (p : ℕ) [Fact p.Prime] [CharP D p] :
    Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ * (Module.length D
      (D ⧸ (Ideal.span (Set.range fun i : Fin h => z i^a)).map
        (iterateFrobenius D p n))).toENNReal) atTop
      (𝓝 ((a : ℝ≥0∞)^h * ENNReal.ofReal
        (Lech.Primary.multiplicity (Ideal.span (Set.range z))))) := by
  have hp : Tendsto (fun n : ℕ => a*p^n) atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop' ha
    exact tendsto_pow_atTop_atTop_of_one_lt (Fact.out : p.Prime).one_lt
  have ht := ENNReal.Tendsto.const_mul (a := (a : ℝ≥0∞)^h)
    ((parameter_powers_multiplicity_enn h hh hdim φ hφ z hprim).comp hp)
    (Or.inr (by finiteness))
  apply ht.congr
  intro n
  dsimp only [Function.comp_def]
  have he : (Ideal.span (Set.range fun i : Fin h => z i^a)).map
      (iterateFrobenius D p n) = Ideal.span (Set.range fun i : Fin h => z i^(a*p^n)) := by
    rw [Ideal.map_span,← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact (pow_mul (z i) a (p^n)).symm
  rw [he,Nat.cast_mul,Nat.cast_pow,mul_pow,ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness)),← pow_mul]
  rw [← mul_assoc,← mul_assoc,ENNReal.mul_inv_cancel (by positivity) (by finiteness),one_mul]

end Lech.Normalization


end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Lech.Normalization.parameter_frobenius_multiplicity_enn_oai.{u_1, u_2} := @OAI.Lech.Normalization.parameter_frobenius_multiplicity_enn_oai.{u_1, u_2}
