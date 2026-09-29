-- Prove2me | solution 1 for HopfAlgebra.rational_separating_dense_algHom_algebraicClosure_of_forall_ringEquiv_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6e3d5ffc-916c-5ff4-b465-dcfecbb99eb5

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_rational_separating_dense_algHom_algebraicClosure_of_forall_ringEquiv_apply_eq

open scoped TensorProduct

namespace P2mOddConstGeneric

noncomputable section

def intAlgHom {R S : Type*} [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] (g : R →+* S) :
    R →ₐ[ℤ] S :=
  { g with
    commutes' := fun r => by
      rw [Subsingleton.elim (algebraMap ℤ R) (Int.castRingHom R),
        Subsingleton.elim (algebraMap ℤ S) (Int.castRingHom S)]
      simp }

@[scoped simp] theorem intAlgHom_apply {R S : Type*} [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S]
    (g : R →+* S) (x : R) : intAlgHom g x = g x := rfl

section Engine

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

abbrev L : Type := AlgebraicClosure ℚ

abbrev Pt : Type := K →ₐ[ℤ] L

abbrev KQ : Type :=
  @TensorProduct ℤ _ ℚ K _ _ (Algebra.toModule (R := ℤ) (A := ℚ)) (Algebra.toModule (R := ℤ) (A := K))

example : HopfAlgebra ℚ (KQ K) := inferInstance
example : CommRing (KQ K) := inferInstance

variable {K} in

abbrev tmulQ (r : ℚ) (k : K) : KQ K :=
  @TensorProduct.tmul ℤ _ ℚ K _ _ (Algebra.toModule (R := ℤ) (A := ℚ))
    (Algebra.toModule (R := ℤ) (A := K)) r k

def extendQ (φ : Pt K) : KQ K →ₐ[ℚ] L :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ L) φ (fun _ _ => Commute.all _ _)

@[scoped simp] theorem extendQ_tmul (φ : Pt K) (r : ℚ) (k : K) :
    extendQ K φ (tmulQ r k) = algebraMap ℚ L r * φ k := by
  simp [extendQ, tmulQ]

def restrictQ (Φ : KQ K →ₐ[ℚ] L) : Pt K :=
  intAlgHom ((Φ : KQ K →+* L).comp
    ((Algebra.TensorProduct.includeRight : K →ₐ[ℤ] KQ K) : K →+* KQ K))

@[scoped simp] theorem restrictQ_apply (Φ : KQ K →ₐ[ℚ] L) (k : K) :
    restrictQ K Φ k = Φ (tmulQ 1 k) := rfl

theorem restrictQ_extendQ (φ : Pt K) : restrictQ K (extendQ K φ) = φ := by
  ext k; simp

variable {K} in
theorem tmul_eq_smul_one_tmul (r : ℚ) (k : K) : tmulQ r k = r • tmulQ (1 : ℚ) k := by
  change _ = @TensorProduct.tmul ℤ _ ℚ K _ _ (Algebra.toModule (R := ℤ) (A := ℚ))
    (Algebra.toModule (R := ℤ) (A := K)) (r • 1) k
  rw [smul_eq_mul, mul_one]

theorem extendQ_restrictQ (Φ : KQ K →ₐ[ℚ] L) : extendQ K (restrictQ K Φ) = Φ := by
  apply Algebra.TensorProduct.ext'
  intro r k
  change extendQ K (restrictQ K Φ) (tmulQ r k) = Φ (tmulQ r k)
  rw [tmul_eq_smul_one_tmul r k, map_smul, map_smul, extendQ_tmul, restrictQ_apply, map_one,
    one_mul]

def pointsEquiv : Pt K ≃ (KQ K →ₐ[ℚ] L) where
  toFun := extendQ K
  invFun := restrictQ K
  left_inv := restrictQ_extendQ K
  right_inv := extendQ_restrictQ K

variable {K}

theorem finite_KQ (ℓ : ℕ)
    (hℓ : letI : Module ℤ K := AddCommGroup.toIntModule K;
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K)) :
    Module.Finite ℚ (KQ K) := by
  letI : Module ℤ K := AddCommGroup.toIntModule K
  haveI := hℓ
  have h := Module.Finite.equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ (GaloisRep.ratLocalizedAt ℓ) ℚ ℚ K)
  convert h <;> first | rfl | exact Subsingleton.elim _ _

theorem finite_KQ_of_hff (p : ℕ)
    (hff : letI : Module ℤ K := AddCommGroup.toIntModule K;
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K)) :
    Module.Finite ℚ (KQ K) := by
  by_cases hp : p = 2
  · exact finite_KQ 3 (hff 3 Nat.prime_three (by omega))
  · exact finite_KQ 2 (hff 2 Nat.prime_two (Ne.symm hp))

theorem finrank_KQ [Module.Finite ℚ (KQ K)] :
    Module.finrank ℚ (KQ K) = Nat.card (Pt K) := by
  rw [← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ℚ (KQ K) L]
  exact (Nat.card_congr (pointsEquiv K)).symm

variable (K) in

def toKQ : K →ₐ[ℤ] KQ K := Algebra.TensorProduct.includeRight

theorem toKQ_apply (k : K) : toKQ K k = tmulQ 1 k := rfl

theorem toKQ_injective (hflat : letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Flat ℤ K) :
    Function.Injective (toKQ K) := by
  haveI : @Module.Flat ℤ K _ _ (Algebra.toModule (R := ℤ) (A := K)) := by
    convert hflat <;> exact Subsingleton.elim _ _
  exact Algebra.TensorProduct.includeRight_injective (R := ℤ) (A := ℚ) (B := K)
    (fun a b h => by simpa using h)

theorem tmulQ_intCast_left (n : ℤ) (k : K) : tmulQ (n : ℚ) k = toKQ K ((n : K) * k) := by
  rw [tmul_eq_smul_one_tmul, ← toKQ_apply, map_mul, map_intCast, Algebra.smul_def]
  congr 1

theorem exists_nsmul_eq_toKQ (x : KQ K) : ∃ (N : ℕ) (k : K), 0 < N ∧ (N : ℚ) • x = toKQ K k := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, Nat.one_pos, by simp⟩
  | tmul r k =>
    refine ⟨r.den, (r.num : K) * k, r.den_pos, ?_⟩
    change (r.den : ℚ) • tmulQ r k = tmulQ 1 ((r.num : K) * k)
    rw [← toKQ_apply, tmul_eq_smul_one_tmul r k, smul_smul, Rat.den_mul_eq_num,
      ← tmul_eq_smul_one_tmul, tmulQ_intCast_left]
  | add x y hx hy =>
    obtain ⟨N, k, hN, hk⟩ := hx
    obtain ⟨M, k', hM, hk'⟩ := hy
    refine ⟨N * M, (M : K) * k + (N : K) * k', Nat.mul_pos hN hM, ?_⟩
    rw [smul_add, Nat.cast_mul, mul_comm, ← smul_smul, hk, mul_comm, ← smul_smul, hk', map_add,
      map_mul, map_mul, map_natCast, map_natCast]
    simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem exists_rat_of_fixed (φ : Pt K)
    (hgal : ∀ (σ : L ≃+* L) (k : K), σ (φ k) = φ k) (k : K) :
    ∃ r : ℚ, φ k = algebraMap ℚ L r := by
  haveI : IsAlgClosure ℚ L :=
    ⟨inferInstance, by convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _⟩
  haveI : IsGalois ℚ L := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hfix : ∀ f : L ≃ₐ[ℚ] L, f (φ k) = φ k := fun f => hgal f.toRingEquiv k
  obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (K := L) (φ k)).mpr hfix
  exact ⟨r, hr.symm⟩

section Rational

variable (hrat : ∀ (ψ : Pt K) (k : K), ∃ r : ℚ, ψ k = algebraMap ℚ L r)

def ψ₀ (ψ : Pt K) : K →+* ℚ where
  toFun k := (hrat ψ k).choose
  map_one' := (algebraMap ℚ L).injective (by rw [← (hrat ψ 1).choose_spec, map_one, map_one])
  map_mul' a b := (algebraMap ℚ L).injective (by
    rw [← (hrat ψ (a * b)).choose_spec, map_mul, map_mul, ← (hrat ψ a).choose_spec,
      ← (hrat ψ b).choose_spec])
  map_zero' := (algebraMap ℚ L).injective (by rw [← (hrat ψ 0).choose_spec, map_zero, map_zero])
  map_add' a b := (algebraMap ℚ L).injective (by
    rw [← (hrat ψ (a + b)).choose_spec, map_add, map_add, ← (hrat ψ a).choose_spec,
      ← (hrat ψ b).choose_spec])

theorem algebraMap_ψ₀ (ψ : Pt K) (k : K) : algebraMap ℚ L (ψ₀ hrat ψ k) = ψ k :=
  (hrat ψ k).choose_spec.symm

def ΨQ (ψ : Pt K) : KQ K →ₐ[ℚ] ℚ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ ℚ) (intAlgHom (ψ₀ hrat ψ)) (fun _ _ => Commute.all _ _)

theorem ΨQ_tmul (ψ : Pt K) (r : ℚ) (k : K) : ΨQ hrat ψ (tmulQ r k) = r * ψ₀ hrat ψ k := by
  simp [ΨQ, tmulQ]

theorem ΨQ_toKQ (ψ : Pt K) (k : K) : ΨQ hrat ψ (toKQ K k) = ψ₀ hrat ψ k := by
  rw [toKQ_apply, ΨQ_tmul, one_mul]

theorem algebraMap_ΨQ (ψ : Pt K) (x : KQ K) : algebraMap ℚ L (ΨQ hrat ψ x) = extendQ K ψ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r k =>
    change algebraMap ℚ L (ΨQ hrat ψ (tmulQ r k)) = extendQ K ψ (tmulQ r k)
    rw [ΨQ_tmul, extendQ_tmul, map_mul, algebraMap_ψ₀]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

def evQ : KQ K →ₐ[ℚ] (Pt K → ℚ) :=
  Pi.algHom ℚ _ (fun ψ => ΨQ hrat ψ)

@[scoped simp] theorem evQ_apply (x : KQ K) (ψ : Pt K) : evQ hrat x ψ = ΨQ hrat ψ x := rfl

theorem exists_apply_eq_zero_and_ne (ψ ψ' : Pt K) (hne : ψ ≠ ψ') :
    ∃ y : KQ K, ΨQ hrat ψ' y = 0 ∧ ΨQ hrat ψ y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hne

  have hΨ : ∀ x, ΨQ hrat ψ x = ΨQ hrat ψ' x := by
    intro x
    have hx : ΨQ hrat ψ' (x - algebraMap ℚ (KQ K) (ΨQ hrat ψ' x)) = 0 := by
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    have := hcon _ hx
    rwa [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] at this
  have hext : extendQ K ψ = extendQ K ψ' := by
    refine AlgHom.ext fun x => ?_
    rw [← algebraMap_ΨQ hrat, ← algebraMap_ΨQ hrat, hΨ]
  have := congrArg (restrictQ K) hext
  rwa [restrictQ_extendQ, restrictQ_extendQ] at this

variable [Finite (Pt K)]

open Classical in

theorem exists_evQ_eq_single (ψ : Pt K) : ∃ z : KQ K, evQ hrat z = Pi.single ψ 1 := by
  haveI := Fintype.ofFinite (Pt K)
  choose y hy0 hy1 using fun ψ' (h : ψ ≠ ψ') => exists_apply_eq_zero_and_ne hrat ψ ψ' h

  let x : KQ K := ∏ ψ' ∈ (Finset.univ.erase ψ), if h : ψ ≠ ψ' then y ψ' h else 1
  have hx0 : ∀ ψ', ψ' ≠ ψ → ΨQ hrat ψ' x = 0 := by
    intro ψ' hψ'
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hψ', Finset.mem_univ _⟩)
    rw [dif_pos (Ne.symm hψ')]
    exact hy0 ψ' (Ne.symm hψ')
  have hx1 : ΨQ hrat ψ x ≠ 0 := by
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun ψ' hψ' => ?_
    have hne : ψ ≠ ψ' := Ne.symm (Finset.mem_erase.mp hψ').1
    rw [dif_pos hne]
    exact hy1 ψ' hne
  refine ⟨(ΨQ hrat ψ x)⁻¹ • x, funext fun ψ' => ?_⟩
  rw [evQ_apply, map_smul, smul_eq_mul]
  by_cases h : ψ' = ψ
  · subst h
    rw [Pi.single_eq_same, inv_mul_cancel₀ hx1]
  · rw [Pi.single_eq_of_ne h, hx0 ψ' h, mul_zero]

theorem evQ_surjective : Function.Surjective (evQ hrat (K := K)) := by
  classical
  haveI := Fintype.ofFinite (Pt K)
  intro c
  choose z hz using exists_evQ_eq_single hrat (K := K)
  refine ⟨∑ ψ, c ψ • z ψ, ?_⟩
  rw [map_sum]
  simp_rw [map_smul, hz]
  ext ψ
  simp [Finset.sum_apply, Pi.single_apply]

theorem evQ_bijective [Module.Finite ℚ (KQ K)] : Function.Bijective (evQ hrat (K := K)) := by
  haveI := Fintype.ofFinite (Pt K)
  refine ⟨?_, evQ_surjective hrat⟩
  have hfr : Module.finrank ℚ (KQ K) = Module.finrank ℚ (Pt K → ℚ) := by
    rw [finrank_KQ, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
    (f := (evQ hrat).toLinearMap)).mpr (evQ_surjective hrat)

include hrat in

theorem eq_of_forall_apply_eq [Module.Finite ℚ (KQ K)]
    (hflat : letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Flat ℤ K)
    (k k' : K) (h : ∀ ψ : Pt K, ψ k = ψ k') : k = k' := by
  apply toKQ_injective hflat
  apply (evQ_bijective hrat).1
  funext ψ
  rw [evQ_apply, evQ_apply, ΨQ_toKQ, ΨQ_toKQ]
  apply (algebraMap ℚ L).injective
  rw [algebraMap_ψ₀, algebraMap_ψ₀, h]

include hrat in

theorem exists_forall_apply_eq_mul [Module.Finite ℚ (KQ K)] (c : Pt K → ℤ) :
    ∃ (k : K) (N : ℕ), 0 < N ∧ ∀ ψ : Pt K, ψ k = ((N : ℤ) * c ψ : ℤ) := by
  obtain ⟨x, hx⟩ := (evQ_bijective hrat).2 (fun ψ => (c ψ : ℚ))
  obtain ⟨N, k, hN, hk⟩ := exists_nsmul_eq_toKQ x
  refine ⟨k, N, hN, fun ψ => ?_⟩
  have h1 : ΨQ hrat ψ (toKQ K k) = (N : ℚ) * c ψ := by
    rw [← hk, map_smul, smul_eq_mul, ← evQ_apply, hx]
  rw [ΨQ_toKQ] at h1
  rw [← algebraMap_ψ₀ hrat, h1, map_mul, map_natCast, Int.cast_mul, Int.cast_natCast]
  congr 1

end Rational

end Engine

end

end P2mOddConstGeneric
p2m_reactivate "P2MW.S_HopfAlgebra_rational_separating_dense_algHom_algebraicClosure_of_forall_ringEquiv_apply_eq.P2mOddConstGeneric"

open P2mOddConstGeneric in
theorem solution
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Module.Flat ℤ K]
    (ℓ : ℕ) (hfin : Module.Finite (GaloisRep.ratLocalizedAt ℓ)
      (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    [Finite (K →ₐ[ℤ] AlgebraicClosure ℚ)]
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k) :
    (∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K), ∃ r : ℚ, ψ k = algebraMap ℚ _ r) ∧
    (∀ k k' : K, (∀ ψ : K →ₐ[ℤ] AlgebraicClosure ℚ, ψ k = ψ k') → k = k') ∧
    (∀ c : (K →ₐ[ℤ] AlgebraicClosure ℚ) → ℤ, ∃ (k : K) (N : ℕ), 0 < N ∧
      ∀ ψ : K →ₐ[ℤ] AlgebraicClosure ℚ, ψ k = ((N : ℤ) * c ψ : ℤ)) := by
  have hrat : ∀ (ψ : Pt K) (k : K), ∃ r : ℚ, ψ k = algebraMap ℚ L r :=
    fun ψ k => exists_rat_of_fixed ψ (fun σ k => hgal σ ψ k) k
  haveI : Module.Finite ℚ (KQ K) := finite_KQ ℓ hfin
  exact ⟨hrat, eq_of_forall_apply_eq hrat ‹_›, exists_forall_apply_eq_mul hrat⟩

end S_HopfAlgebra_rational_separating_dense_algHom_algebraicClosure_of_forall_ringEquiv_apply_eq
end P2MW
export P2MW.S_HopfAlgebra_rational_separating_dense_algHom_algebraicClosure_of_forall_ringEquiv_apply_eq (solution)
