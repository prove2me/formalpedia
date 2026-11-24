-- Prove2me | solution 1 for GlobalTheory.dvr_finite_over_complete_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:00.654245+00:00
-- url     : https://prove2.me/submissions/494d7eec-7673-4a2a-8c24-3dc5742658f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_InjectiveAlgebraMapOfDvrOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
open IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (O V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing V] [IsDomain V]
      [IsDiscreteValuationRing V] [Algebra O V] [Module.Finite O V],
      Function.Injective (algebraMap O V) ∧ IsLocalHom (algebraMap O V) ∧
        IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ CharZero V ∧
          (Finite (IsLocalRing.ResidueField O) → Finite (IsLocalRing.ResidueField V)) := by
  intro O V _ _ _ _ _ _ _ _ _ _
  haveI : Algebra.IsIntegral O V := Algebra.IsIntegral.of_finite O V
  have hinj : Function.Injective (algebraMap O V) := by
    rw [injective_iff_map_eq_zero]
    by_contra h
    push_neg at h
    obtain ⟨a, ha, ha0⟩ := h
    have hker : (RingHom.ker (algebraMap O V)).IsMaximal := by
      refine Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) ?_
      intro hb
      apply ha0
      have hmem : a ∈ RingHom.ker (algebraMap O V) := ha
      rw [hb] at hmem
      exact (Ideal.mem_bot).1 hmem
    have hbot : (⊥ : Ideal V).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) ⊥
        (by rwa [← RingHom.ker_eq_comap_bot])
    exact IsDiscreteValuationRing.not_a_field V (IsLocalRing.eq_maximalIdeal hbot).symm
  have hloc : IsLocalHom (algebraMap O V) :=
    RingHom.IsIntegral.isLocalHom (fun x => Algebra.IsIntegral.isIntegral x) hinj
  haveI := hloc
  refine ⟨hinj, hloc, ?_, charZero_of_injective_algebraMap hinj, fun h => ?_⟩
  swap
  · exact Module.finite_of_finite (ResidueField O)
  haveI : Module.IsTorsionFree O V := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.Free O V := Module.free_of_finite_type_torsion_free'
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hπm : π ∈ maximalIdeal O := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hπ.not_isUnit)
  have hp0 : algebraMap O V π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have hpm : algebraMap O V π ∈ maximalIdeal V :=
    (mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => hπ.not_isUnit ((isUnit_map_iff _ _).1 hu))
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {algebraMap O V π}) (by simpa using hp0) hq
  have hpow : ∀ k, maximalIdeal V ^ (e * k) = Ideal.span {algebraMap O V π ^ k} := by
    intro k
    rw [hq.maximalIdeal_eq, Ideal.span_singleton_pow, pow_mul, ← Ideal.span_singleton_pow, ← he,
      Ideal.span_singleton_pow]
  refine
    { toIsHausdorff := IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal V).ne_top
      toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  have hf' : ∀ m n, m ≤ n → f m - f n ∈ maximalIdeal V ^ m := fun m n h => by
    simpa using SModEq.sub_mem.1 (hf h)
  have hg : ∀ m n, m ≤ n →
      ∃ y, f (e * m + m) - f (e * n + n) = algebraMap O V π ^ m * y := by
    intro m n h
    have h1 := hf' _ _ (Nat.add_le_add (Nat.mul_le_mul_left e h) h)
    have h2 : f (e * m + m) - f (e * n + n) ∈ Ideal.span {algebraMap O V π ^ m} := by
      rw [← hpow]
      exact Ideal.pow_le_pow_right (Nat.le_add_right _ _) h1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
    exact ⟨y, by rw [← hy, mul_comm]⟩
  let b := Module.Free.chooseBasis O V
  have hc : ∀ i, ∀ {m n : ℕ}, m ≤ n →
      b.repr (f (e * m + m)) i ≡ b.repr (f (e * n + n)) i
        [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O O)] := by
    intro i m n h
    obtain ⟨y, hy⟩ := hg m n h
    have hdiff : b.repr (f (e * m + m)) i - b.repr (f (e * n + n)) i = π ^ m * b.repr y i := by
      rw [← Finsupp.sub_apply, ← map_sub, hy, ← map_pow, ← Algebra.smul_def, map_smul,
        Finsupp.smul_apply, smul_eq_mul]
    have hmem : π ^ m * b.repr y i ∈ maximalIdeal O ^ m :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm m)
    rw [SModEq.sub_mem, hdiff]
    simpa using hmem
  choose l hl using fun i =>
    (inferInstance : IsPrecomplete (maximalIdeal O) O).prec
      (f := fun k => b.repr (f (e * k + k)) i) (hc i)
  refine ⟨∑ i, l i • b i, fun n => ?_⟩
  have hgn : f (e * n + n) - ∑ i, l i • b i ∈ maximalIdeal V ^ n := by
    have hex : ∀ i, ∃ t, b.repr (f (e * n + n)) i - l i = π ^ n * t := fun i => by
      have hmem := SModEq.sub_mem.1 (hl i n)
      simp only [smul_eq_mul, Ideal.mul_top] at hmem
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
      obtain ⟨t, ht⟩ := hmem
      exact ⟨t, by rw [← ht, mul_comm]⟩
    choose t ht using hex
    have hsum : f (e * n + n) - ∑ i, l i • b i =
        algebraMap O V π ^ n * ∑ i, t i • b i := by
      conv_lhs => rw [← b.sum_repr (f (e * n + n))]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, ht, mul_smul, Algebra.smul_def, map_pow]
    rw [hsum]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpm n)
  have hfg : f n - f (e * n + n) ∈ maximalIdeal V ^ n := hf' n (e * n + n) (Nat.le_add_left _ _)
  have hsum := Ideal.add_mem _ hfg hgn
  rw [sub_add_sub_cancel] at hsum
  rw [SModEq.sub_mem]
  simpa using hsum
end _root_.GlobalTheory
end GlobalTheory
