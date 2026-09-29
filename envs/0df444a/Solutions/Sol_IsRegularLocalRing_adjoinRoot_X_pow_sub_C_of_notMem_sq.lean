-- Prove2me | solution 1 for IsRegularLocalRing.adjoinRoot_X_pow_sub_C_of_notMem_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/316f5bc5-b085-51a8-927b-0b6bf348467f

import Mathlib
import Theorems.Thm_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_AlgebraicGeometry_RegularLocalRingQuotientNonZeroDivisorAscent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_adjoinRoot_X_pow_sub_C_of_notMem_sq

open IsLocalRing Polynomial

namespace KummerRegSol

section K2

variable {R : Type*} [CommRing R]

theorem monic_kummer (t : R) {n : ℕ} (hn : 0 < n) : (X ^ n - C t : R[X]).Monic :=
  monic_X_pow_sub_C t hn.ne'

theorem root_pow_eq (t : R) (n : ℕ) :
    AdjoinRoot.root (X ^ n - C t : R[X]) ^ n = AdjoinRoot.of (X ^ n - C t : R[X]) t := by
  have h := AdjoinRoot.eval₂_root (X ^ n - C t : R[X])
  rw [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem exists_eq_of_add_root_mul (t : R) (n : ℕ) (s : AdjoinRoot (X ^ n - C t : R[X])) :
    ∃ (a : R) (q : AdjoinRoot (X ^ n - C t : R[X])),
      s = AdjoinRoot.of _ a + AdjoinRoot.root _ * q ∧
        ∀ (S : Type*) [CommRing S] (i : R →+* S) (x : S) (h : (X ^ n - C t : R[X]).eval₂ i x = 0),
          AdjoinRoot.lift i x h s = i a + x * AdjoinRoot.lift i x h q := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective s
  refine ⟨p.coeff 0, AdjoinRoot.mk _ (divX p), ?_, ?_⟩
  · conv_lhs => rw [← X_mul_divX_add p]
    rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, add_comm]
  · intro S _ i x h
    conv_lhs => rw [← X_mul_divX_add p]
    simp only [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.lift_root,
      AdjoinRoot.lift_of]
    rw [add_comm]

variable [IsRegularLocalRing R]

theorem main {t : R} (ht : t ∈ maximalIdeal R) (ht2 : t ∉ maximalIdeal R ^ 2) {n : ℕ} (hn : 0 < n) :
    IsRegularLocalRing (AdjoinRoot (X ^ n - C t : R[X])) ∧
    ringKrullDim (AdjoinRoot (X ^ n - C t : R[X])) = ringKrullDim R ∧
    (∀ N : Ideal (AdjoinRoot (X ^ n - C t : R[X])), N.IsMaximal →
      N = Ideal.span {AdjoinRoot.root (X ^ n - C t : R[X])} ⊔
        (maximalIdeal R).map (AdjoinRoot.of (X ^ n - C t : R[X]))) ∧
    IsSMulRegular (AdjoinRoot (X ^ n - C t : R[X])) (AdjoinRoot.root (X ^ n - C t : R[X])) := by

  set f : R[X] := X ^ n - C t with hf_def
  haveI : IsDomain R := IsRegularLocalRing.isDomain R
  have hf : f.Monic := monic_kummer t hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht2 (Ideal.zero_mem _)
  set S := AdjoinRoot f with hS_def
  let pb : PowerBasis R S := AdjoinRoot.powerBasis' hf
  haveI : Module.Finite R S := hf.finite_adjoinRoot
  haveI : Module.Free R S := .of_basis pb.basis
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have hroot : AdjoinRoot.root f ^ n = AdjoinRoot.of f t := root_pow_eq t n

  have hψ0 : f.eval₂ (residue R) 0 = 0 := by
    rw [hf_def, eval₂_sub, eval₂_X_pow, eval₂_C, zero_pow hn.ne', zero_sub, neg_eq_zero,
      IsLocalRing.residue_eq_zero_iff]
    exact ht
  let ψ : S →+* ResidueField R := AdjoinRoot.lift (residue R) 0 hψ0
  have hψsurj : Function.Surjective ψ := by
    intro k
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective k
    exact ⟨AdjoinRoot.of f a, AdjoinRoot.lift_of hψ0⟩
  set J : Ideal S := Ideal.span {AdjoinRoot.root f} ⊔ (maximalIdeal R).map (AdjoinRoot.of f) with hJ_def
  have hkerψ : RingHom.ker ψ = J := by
    apply le_antisymm
    · intro s hs
      rw [RingHom.mem_ker] at hs
      obtain ⟨a, q, hsq, hlift⟩ := exists_eq_of_add_root_mul t n s
      have hψs : ψ s = residue R a + 0 * ψ q := hlift _ (residue R) 0 hψ0
      rw [zero_mul, add_zero, hs] at hψs
      have ha : a ∈ maximalIdeal R := (IsLocalRing.residue_eq_zero_iff a).mp hψs.symm
      rw [hsq]
      refine Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha))
        (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    · rw [hJ_def, sup_le_iff]
      constructor
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
        exact AdjoinRoot.lift_root hψ0
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker]
        change ψ (AdjoinRoot.of f a) = 0
        rw [AdjoinRoot.lift_of hψ0, IsLocalRing.residue_eq_zero_iff]
        exact ha
  have hJmax : J.IsMaximal := by
    rw [← hkerψ]
    exact RingHom.ker_isMaximal_of_surjective ψ hψsurj

  have hall : ∀ N : Ideal S, N.IsMaximal → N = J := by
    intro N hN
    have hcomap : (N.comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal N
    have hcomap' : N.comap (algebraMap R S) = maximalIdeal R := IsLocalRing.eq_maximalIdeal hcomap
    have hJN : J ≤ N := by
      rw [hJ_def, sup_le_iff]
      constructor
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
        apply hN.isPrime.mem_of_pow_mem n
        rw [hroot]
        have : t ∈ N.comap (algebraMap R S) := hcomap' ▸ ht
        exact this
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        have : a ∈ N.comap (algebraMap R S) := hcomap' ▸ ha
        exact this
    exact (hJmax.eq_of_le hN.ne_top hJN).symm
  haveI hloc : IsLocalRing S := IsLocalRing.of_unique_max_ideal ⟨J, hJmax, fun N hN => hall N hN⟩
  have hmax : maximalIdeal S = J := hall _ (IsLocalRing.maximalIdeal.isMaximal S)

  have htreg : IsSMulRegular S (algebraMap R S t) := by
    have h1 : IsSMulRegular S t :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht0)
    intro a b hab
    apply h1
    simp only [Algebra.smul_def]
    exact hab
  have hroot' : AdjoinRoot.root f ^ (n - 1) * AdjoinRoot.root f = AdjoinRoot.of f t := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
    exact hroot
  have hrootmem_span : AdjoinRoot.of f t ∈ Ideal.span {AdjoinRoot.root f} := by
    rw [← hroot']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hrootreg : IsSMulRegular S (AdjoinRoot.root f) := by
    intro a b hab
    apply htreg
    change algebraMap R S t * a = algebraMap R S t * b
    change AdjoinRoot.root f * a = AdjoinRoot.root f * b at hab
    have : AdjoinRoot.of f t = algebraMap R S t := rfl
    rw [← this, ← hroot', mul_assoc, mul_assoc, hab]

  have hφ0 : f.eval₂ (Ideal.Quotient.mk (Ideal.span {t})) 0 = 0 := by
    rw [hf_def, eval₂_sub, eval₂_X_pow, eval₂_C, zero_pow hn.ne', zero_sub, neg_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  let φ : S →+* R ⧸ Ideal.span {t} := AdjoinRoot.lift (Ideal.Quotient.mk _) 0 hφ0
  have hφsurj : Function.Surjective φ := by
    intro k
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective k
    exact ⟨AdjoinRoot.of f a, AdjoinRoot.lift_of hφ0⟩
  have hkerφ : RingHom.ker φ = Ideal.span {AdjoinRoot.root f} := by
    apply le_antisymm
    · intro s hs
      rw [RingHom.mem_ker] at hs
      obtain ⟨a, q, hsq, hlift⟩ := exists_eq_of_add_root_mul t n s
      have hφs : φ s = Ideal.Quotient.mk _ a + 0 * φ q := hlift _ (Ideal.Quotient.mk _) 0 hφ0
      rw [zero_mul, add_zero, hs] at hφs
      have ha : a ∈ Ideal.span {t} := Ideal.Quotient.eq_zero_iff_mem.mp hφs.symm
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [hsq, map_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hrootmem_span)
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      exact AdjoinRoot.lift_root hφ0
  let e : S ⧸ Ideal.span {AdjoinRoot.root f} ≃+* R ⧸ Ideal.span {t} :=
    (Ideal.quotEquivOfEq hkerφ.symm).trans (RingHom.quotientKerEquivOfSurjective hφsurj)

  haveI : Nontrivial (R ⧸ Ideal.span {t}) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun hu => (IsLocalRing.mem_maximalIdeal _).mp ht hu
  haveI : IsLocalRing (R ⧸ Ideal.span {t}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hRt : IsRegularLocalRing (R ⧸ Ideal.span {t}) :=
    (IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem R ht ht2
      (by
        intro p hp
        rw [IsDomain.minimalPrimes_eq_singleton_bot] at hp
        rw [Set.mem_singleton_iff.mp hp]
        simpa using ht0)).1
  haveI hSroot : IsRegularLocalRing (S ⧸ Ideal.span {AdjoinRoot.root f}) :=
    IsRegularLocalRing.of_ringEquiv e.symm

  have hrootmem : AdjoinRoot.root f ∈ maximalIdeal S := by
    rw [hmax, hJ_def]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hrootnzd : AdjoinRoot.root f ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    apply hrootreg
    change AdjoinRoot.root f * a = AdjoinRoot.root f * 0
    rw [mul_zero, mul_comm, ha]
  have hSreg : IsRegularLocalRing S :=
    RegularLocalRingQuotientAscent.isRegularLocalRing_of_isRegularLocalRing_quotient hrootmem hrootnzd hSroot
  have hSdim : ringKrullDim (S ⧸ Ideal.span {AdjoinRoot.root f}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hrootreg hrootmem
  refine ⟨hSreg, ?_, hall, hrootreg⟩

  have hRdim : ringKrullDim (R ⧸ Ideal.span {t}) + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ht0) ht
  rw [← hSdim, ← hRdim, ringKrullDim_eq_of_ringEquiv e]

end K2

end KummerRegSol

theorem solution
    {R : Type*} [CommRing R] [IsRegularLocalRing R] {t : R}
    (ht : t ∈ maximalIdeal R) (ht2 : t ∉ maximalIdeal R ^ 2) {n : ℕ} (hn : 0 < n) :
    IsRegularLocalRing (AdjoinRoot (X ^ n - C t : R[X])) ∧
    ringKrullDim (AdjoinRoot (X ^ n - C t : R[X])) = ringKrullDim R ∧
    (∀ N : Ideal (AdjoinRoot (X ^ n - C t : R[X])), N.IsMaximal →
      N = Ideal.span {AdjoinRoot.root (X ^ n - C t : R[X])} ⊔
        (maximalIdeal R).map (AdjoinRoot.of (X ^ n - C t : R[X]))) ∧
    IsSMulRegular (AdjoinRoot (X ^ n - C t : R[X])) (AdjoinRoot.root (X ^ n - C t : R[X])) :=
  KummerRegSol.main ht ht2 hn

end S_IsRegularLocalRing_adjoinRoot_X_pow_sub_C_of_notMem_sq
end P2MW
export P2MW.S_IsRegularLocalRing_adjoinRoot_X_pow_sub_C_of_notMem_sq (solution)
