-- Prove2me | solution 1 for HopfAlgebra.prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/06fa46cf-63e7-5648-a0fd-220c1e670c0f

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_HopfAlgebra_exists_basis_tateOort_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two

open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace P2mTwoPointHopf

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

theorem prime_of_forall_mem_ratLocalizedAt {p : ℕ} {q : ℚ}
    (hq : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → q ∈ GaloisRep.ratLocalizedAt ℓ) (hqZ : q.den ≠ 1) :
    p.Prime ∧ p ∣ q.den := by
  obtain ⟨ℓ₀, hℓ₀, hdvd⟩ := Nat.exists_prime_and_dvd hqZ
  by_cases hℓp : ℓ₀ = p
  · subst hℓp; exact ⟨hℓ₀, hdvd⟩
  · exfalso
    have hmem : q.den.Coprime ℓ₀ := hq ℓ₀ hℓ₀ hℓp
    have h1 : ℓ₀ ∣ Nat.gcd q.den ℓ₀ := Nat.dvd_gcd hdvd (dvd_refl _)
    rw [hmem] at h1
    exact hℓ₀.one_lt.ne' (Nat.dvd_one.mp h1)

theorem den_eq_prime_pow {p : ℕ} (hp : p.Prime) {q : ℚ}
    (hq : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → q ∈ GaloisRep.ratLocalizedAt ℓ) :
    ∃ n : ℕ, q.den = p ^ n := by
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz ?_⟩
  intro d hd hdd
  by_contra hne
  have hmem : q.den.Coprime d := hq d hd hne
  have h1 : d ∣ Nat.gcd q.den d := Nat.dvd_gcd hdd (dvd_refl _)
  rw [hmem] at h1
  exact hd.one_lt.ne' (Nat.dvd_one.mp h1)

theorem eq_num_div_pow {p : ℕ} {q : ℚ} {n : ℕ} (h : q.den = p ^ n) :
    q = (q.num : ℚ) / (p : ℚ) ^ n := by
  have h1 : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
  rw [h] at h1
  push_cast at h1
  exact h1.symm

theorem inv_mem_of_prime_dvd_den (S : Subring ℚ) {q : ℚ} (hqS : q ∈ S) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q.den) : ((ℓ : ℚ)⁻¹) ∈ S := by
  obtain ⟨d, hd⟩ := hℓq
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hd0 : (d : ℚ) ≠ 0 := by
    have : q.den ≠ 0 := q.den_nz
    rw [hd] at this
    exact_mod_cast (mul_ne_zero_iff.mp this).2

  have hqd : q * d = (q.num : ℚ) / ℓ := by
    have hq : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
    rw [hd] at hq
    push_cast at hq
    have hq' : q * d = (q.num : ℚ) / ((ℓ : ℚ) * d) * d := by rw [hq]
    rw [hq']
    field_simp

  have hcop : Int.gcd q.num ℓ = 1 := by
    have h1 : Nat.Coprime q.num.natAbs q.den := q.reduced
    have h2 : Nat.Coprime q.num.natAbs ℓ :=
      Nat.Coprime.coprime_dvd_right (by rw [hd]; exact dvd_mul_right ℓ d) h1
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact h2
  have hbez : (q.num : ℚ) * (Int.gcdA q.num ℓ) + (ℓ : ℚ) * (Int.gcdB q.num ℓ) = 1 := by
    have h := Int.gcd_eq_gcd_ab q.num ℓ
    rw [hcop] at h
    have h' : ((1 : ℕ) : ℤ) = q.num * Int.gcdA q.num ℓ + (ℓ : ℤ) * Int.gcdB q.num ℓ := h
    have h'' := congrArg (fun z : ℤ => (z : ℚ)) h'
    push_cast at h''
    exact h''.symm
  have key : ((ℓ : ℚ)⁻¹) = (Int.gcdA q.num ℓ : ℚ) * (q * d) + (Int.gcdB q.num ℓ : ℚ) := by
    rw [hqd]
    apply inv_eq_of_mul_eq_one_right
    rw [mul_add, ← mul_assoc, mul_comm (ℓ : ℚ) (Int.gcdA q.num ℓ : ℚ), mul_assoc,
      mul_div_cancel₀ _ hℓ0]
    linear_combination hbez
  rw [key]
  exact add_mem (mul_mem (intCast_mem S _) (mul_mem hqS (natCast_mem S _))) (intCast_mem S _)

theorem div_pow_mem_of_inv_mem (S : Subring ℚ) {p : ℕ} (hpS : ((p : ℚ)⁻¹) ∈ S) (n : ℤ) (i : ℕ) :
    (n : ℚ) / (p : ℚ) ^ i ∈ S := by
  rw [div_eq_mul_inv, ← inv_pow]
  exact mul_mem (intCast_mem S n) (pow_mem hpS i)

section GenericFibre

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

abbrev L : Type := AlgebraicClosure ℚ

abbrev KQ : Type :=
  @TensorProduct ℤ _ ℚ K _ _ (Algebra.toModule (R := ℤ) (A := ℚ))
    (Algebra.toModule (R := ℤ) (A := K))

variable {K} in

abbrev tmulQ (q : ℚ) (k : K) : KQ K :=
  @TensorProduct.tmul ℤ _ ℚ K _ _ (Algebra.toModule (R := ℤ) (A := ℚ))
    (Algebra.toModule (R := ℤ) (A := K)) q k

def extendQ (φ : K →ₐ[ℤ] L) : KQ K →ₐ[ℚ] L :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ L) φ (fun _ _ => Commute.all _ _)

@[scoped simp] theorem extendQ_tmul (φ : K →ₐ[ℤ] L) (q : ℚ) (k : K) :
    extendQ K φ (tmulQ q k) = algebraMap ℚ L q * φ k := by
  simp [extendQ, tmulQ]

def restrictQ (Φ : KQ K →ₐ[ℚ] L) : K →ₐ[ℤ] L :=
  intAlgHom ((Φ : KQ K →+* L).comp
    ((Algebra.TensorProduct.includeRight : K →ₐ[ℤ] KQ K) : K →+* KQ K))

@[scoped simp] theorem restrictQ_apply (Φ : KQ K →ₐ[ℚ] L) (k : K) :
    restrictQ K Φ k = Φ (tmulQ 1 k) := rfl

theorem restrictQ_extendQ (φ : K →ₐ[ℤ] L) : restrictQ K (extendQ K φ) = φ := by
  ext k; simp

variable {K} in
theorem tmul_eq_smul_one_tmul (q : ℚ) (k : K) : tmulQ q k = q • tmulQ (1 : ℚ) k := by
  change _ = @TensorProduct.tmul ℤ _ ℚ K _ _ (Algebra.toModule (R := ℤ) (A := ℚ))
    (Algebra.toModule (R := ℤ) (A := K)) (q • 1) k
  rw [smul_eq_mul, mul_one]

theorem extendQ_restrictQ (Φ : KQ K →ₐ[ℚ] L) : extendQ K (restrictQ K Φ) = Φ := by
  apply Algebra.TensorProduct.ext'
  intro q k
  change extendQ K (restrictQ K Φ) (tmulQ q k) = Φ (tmulQ q k)
  rw [tmul_eq_smul_one_tmul q k, map_smul, map_smul, extendQ_tmul, restrictQ_apply, map_one,
    one_mul]

def pointsEquiv : (K →ₐ[ℤ] L) ≃ (KQ K →ₐ[ℚ] L) where
  toFun := extendQ K
  invFun := restrictQ K
  left_inv := restrictQ_extendQ K
  right_inv := extendQ_restrictQ K

abbrev εQ : KQ K →ₐ[ℚ] ℚ := Bialgebra.counitAlgHom ℚ (KQ K)

theorem counit_tmul (q : ℚ) (k : K) :
    εQ K (tmulQ q k) = (Bialgebra.counitAlgHom ℤ K k : ℚ) * q := by
  change (Bialgebra.counitAlgHom ℤ K k : ℤ) • (q : ℚ) = _
  exact zsmul_eq_mul _ _

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

theorem finrank_KQ [Module.Finite ℚ (KQ K)] (hgen : Nat.card (K →ₐ[ℤ] L) = 2) :
    Module.finrank ℚ (KQ K) = 2 := by
  rw [← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ℚ (KQ K) L, ← hgen]
  exact (Nat.card_congr (pointsEquiv K)).symm

variable (K) in

def toKQ : K →ₐ[ℤ] KQ K := Algebra.TensorProduct.includeRight

theorem toKQ_apply (k : K) : toKQ K k = tmulQ 1 k := rfl

theorem toKQ_injective (hflat : letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Flat ℤ K) :
    Function.Injective (toKQ K) := by
  haveI : @Module.Flat ℤ K _ _ (Algebra.toModule (R := ℤ) (A := K)) := by
    convert hflat <;> first | rfl | exact Subsingleton.elim _ _
  exact Algebra.TensorProduct.includeRight_injective (R := ℤ) (A := ℚ) (B := K)
    (fun a b h => by simpa using h)

theorem counit_toKQ (k : K) : εQ K (toKQ K k) = (Bialgebra.counitAlgHom ℤ K k : ℚ) := by
  rw [toKQ_apply, counit_tmul, mul_one]

end GenericFibre

section TensorSquare

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

abbrev KK : Type :=
  @TensorProduct ℤ _ K K _ _ (Algebra.toModule (R := ℤ) (A := K)) (Algebra.toModule (R := ℤ) (A := K))

variable {K} in

abbrev tmulK (x y : K) : KK K :=
  @TensorProduct.tmul ℤ _ K K _ _ (Algebra.toModule (R := ℤ) (A := K))
    (Algebra.toModule (R := ℤ) (A := K)) x y

abbrev modKK : Module ℤ (KK K) :=
  @TensorProduct.leftModule ℤ ℤ _ _ K K _ _ (Algebra.toModule (R := ℤ) (A := K))
    (Algebra.toModule (R := ℤ) (A := K)) (Algebra.toModule (R := ℤ) (A := K)) _

theorem flat_KK (h : @Module.Flat ℤ K _ _ (Algebra.toModule (R := ℤ) (A := K))) :
    @Module.Flat ℤ (KK K) _ _ (modKK K) :=
  @Module.Flat.instTensorProduct ℤ K K _ _ (Algebra.toModule (R := ℤ) (A := K)) _
    (Algebra.toModule (R := ℤ) (A := K)) ℤ _ _ (Algebra.toModule (R := ℤ) (A := K))
    (@IsScalarTower.left ℤ K _ (@DistribMulAction.toMulAction ℤ K _ _
      (@Module.toDistribMulAction ℤ K _ _ (Algebra.toModule (R := ℤ) (A := K))))) h h

abbrev QKK : Type :=
  @TensorProduct ℤ _ ℚ (KK K) _ _ (Algebra.toModule (R := ℤ) (A := ℚ)) (modKK K)

variable {K} in

abbrev tmulQKK (q : ℚ) (t : KK K) : QKK K :=
  @TensorProduct.tmul ℤ _ ℚ (KK K) _ _ (Algebra.toModule (R := ℤ) (A := ℚ)) (modKK K) q t

def dBC : QKK K ≃ₗ[ℚ] KQ K ⊗[ℚ] KQ K :=
  @TensorProduct.AlgebraTensorModule.distribBaseChange ℤ ℚ K K _ _ _ _
    (Algebra.toModule (R := ℤ) (A := K)) _ (Algebra.toModule (R := ℤ) (A := K))

def Theta (t : KK K) : KQ K ⊗[ℚ] KQ K := dBC K (tmulQKK 1 t)

theorem Theta_add (s t : KK K) : Theta K (s + t) = Theta K s + Theta K t := by
  simp only [Theta, tmulQKK, TensorProduct.tmul_add, map_add]

theorem Theta_zero : Theta K 0 = 0 := by
  simp only [Theta, tmulQKK, TensorProduct.tmul_zero, map_zero]

theorem Theta_tmul (x y : K) : Theta K (tmulK x y) = toKQ K x ⊗ₜ[ℚ] toKQ K y :=
  @TensorProduct.AlgebraTensorModule.distribBaseChange_tmul ℤ ℚ K K _ _ _ _
    (Algebra.toModule (R := ℤ) (A := K)) _ (Algebra.toModule (R := ℤ) (A := K)) x y 1

theorem tmulQKK_one_injective
    (hflat : letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Flat ℤ K) :
    Function.Injective (fun t : KK K => tmulQKK (1 : ℚ) t) := by
  haveI : @Module.Flat ℤ K _ _ (Algebra.toModule (R := ℤ) (A := K)) := by
    convert hflat <;> first | rfl | exact Subsingleton.elim _ _
  have hF : @Module.Flat ℤ (KK K) _ _ (modKK K) := flat_KK K inferInstance
  have h1 := @Module.Flat.rTensor_preserves_injective_linearMap ℤ (KK K) ℤ ℚ _ _ (modKK K) _ _ _
    (Algebra.toModule (R := ℤ) (A := ℚ)) hF (Algebra.linearMap ℤ ℚ)
    (fun a b h => by simpa using h)
  have h2 := h1.comp (@TensorProduct.lid ℤ _ (KK K) _ (modKK K)).symm.injective
  convert h2 using 1
  rfl

theorem Theta_injective
    (hflat : letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Flat ℤ K) :
    Function.Injective (Theta K) :=
  (dBC K).injective.comp (tmulQKK_one_injective K hflat)

theorem Theta_comul (k : K) :
    Theta K (Bialgebra.comulAlgHom ℤ K k) = Coalgebra.comul (R := ℚ) (toKQ K k) := by
  rw [toKQ_apply, tmulQ,
    @TensorProduct.comul_tmul ℤ ℚ ℚ K _ _ _ _ _ _ _ (Algebra.toModule (R := ℤ) (A := K)) _ _ _ 1 k,
    CommSemiring.comul_apply, ← Bialgebra.comulAlgHom_apply]
  induction Bialgebra.comulAlgHom ℤ K k using TensorProduct.induction_on with
  | zero => rw [Theta_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero]
  | tmul x y =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    exact Theta_tmul K x y
  | add x y hx hy =>
    rw [Theta_add, @TensorProduct.tmul_add ℤ _ _ _ _ _ _ (modKK K) _ x y, LinearEquiv.map_add,
      hx, hy]

end TensorSquare

section TateOort

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

structure TOData where

  x : KQ K

  a : ℚ

  b : ℚ

  c₁ : KQ K →ₗ[ℚ] ℚ
  hab : a * b = 2
  hεx : εQ K x = 0
  hxx : x * x = a • x
  hΔ : Coalgebra.comul (R := ℚ) x = x ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] x - b • (x ⊗ₜ[ℚ] x)
  c₁_one : c₁ 1 = 0
  c₁_x : c₁ x = 1
  decomp : ∀ w : KQ K, w = (εQ K w) • (1 : KQ K) + (c₁ w) • x

theorem nonempty_TOData [Module.Finite ℚ (KQ K)] (h2 : Module.finrank ℚ (KQ K) = 2) :
    Nonempty (TOData K) := by
  obtain ⟨e, a, b, he0, hab, hε, hxx, hΔ, -⟩ :=
    HopfAlgebra.exists_basis_tateOort_two (R := ℚ) (H := KQ K) h2
  have hc0 : e.coord 1 (e 0) = 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  have hc1 : e.coord 1 (e 1) = 1 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self]
  have hε1 : εQ K (e 1) = 0 := hε
  refine ⟨⟨e 1, a, b, e.coord 1, hab, hε1, hxx, hΔ, by rw [← he0]; exact hc0, hc1, fun w => ?_⟩⟩
  have hw := (e.sum_repr w).symm
  rw [Fin.sum_univ_two, he0] at hw
  have hεw : εQ K w = e.repr w 0 := by
    have := congrArg (εQ K) hw
    rw [map_add, map_smul, map_smul, map_one, hε1, smul_zero, add_zero, smul_eq_mul, mul_one] at this
    exact this
  rw [hεw, Module.Basis.coord_apply]
  exact hw

variable {K}
variable (T : TOData K)

theorem TOData.a_ne_zero : T.a ≠ 0 := by
  intro h; have := T.hab; rw [h, zero_mul] at this; norm_num at this

theorem TOData.b_eq : T.b = 2 / T.a := by
  rw [eq_div_iff T.a_ne_zero, mul_comm]; exact T.hab

theorem TOData.mul_eq (α β γ δ : ℚ) :
    (α • (1 : KQ K) + β • T.x) * (γ • (1 : KQ K) + δ • T.x) =
      (α * γ) • (1 : KQ K) + (α * δ + β * γ + T.a * β * δ) • T.x := by
  have hxx := T.hxx
  simp only [Algebra.smul_def, mul_one] at hxx ⊢
  simp only [map_add, map_mul]
  linear_combination (algebraMap ℚ (KQ K) β * algebraMap ℚ (KQ K) δ) * hxx

theorem TOData.εQ_combo (α β : ℚ) : εQ K (α • (1 : KQ K) + β • T.x) = α := by
  rw [map_add, map_smul, map_smul, map_one, T.hεx, smul_zero, add_zero, smul_eq_mul, mul_one]

theorem TOData.c₁_combo (α β : ℚ) : T.c₁ (α • (1 : KQ K) + β • T.x) = β := by
  rw [map_add, map_smul, map_smul, T.c₁_one, T.c₁_x, smul_zero, zero_add, smul_eq_mul, mul_one]

def TOData.χQ : KQ K →+* ℚ where
  toFun w := εQ K w + T.a * T.c₁ w
  map_one' := by rw [map_one, T.c₁_one, mul_zero, add_zero]
  map_mul' w v := by
    have hw := T.decomp w
    have hv := T.decomp v
    set α := εQ K w
    set β := T.c₁ w
    set γ := εQ K v
    set δ := T.c₁ v
    rw [hw, hv, T.mul_eq, T.εQ_combo, T.c₁_combo]
    ring
  map_zero' := by rw [map_zero, map_zero, mul_zero, add_zero]
  map_add' w v := by rw [map_add, map_add]; ring

theorem TOData.χQ_apply (w : KQ K) : T.χQ w = εQ K w + T.a * T.c₁ w := rfl

def TOData.χ₀ : K →+* ℚ := T.χQ.comp ((toKQ K : K →ₐ[ℤ] KQ K) : K →+* KQ K)

def TOData.lam0 (k : K) : ℚ := T.c₁ (toKQ K k)

theorem TOData.χ₀_eq (k : K) : T.χ₀ k = (Bialgebra.counitAlgHom ℤ K k : ℚ) + T.a * T.lam0 k := by
  change T.χQ (toKQ K k) = _
  rw [T.χQ_apply, counit_toKQ]
  rfl

theorem TOData.toKQ_eq (k : K) :
    toKQ K k = ((Bialgebra.counitAlgHom ℤ K k : ℚ)) • (1 : KQ K) + (T.lam0 k) • T.x := by
  have h := T.decomp (toKQ K k)
  rwa [counit_toKQ] at h

theorem TOData.a_lam0_eq (k : K) : T.a * T.lam0 k = T.χ₀ k - (Bialgebra.counitAlgHom ℤ K k : ℚ) := by
  rw [T.χ₀_eq]; ring

theorem TOData.eq_zero_of (hflat : letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Flat ℤ K)
    (k : K) (hε : Bialgebra.counitAlgHom ℤ K k = 0) (hχ : T.χ₀ k = 0) : k = 0 := by
  have hl : T.lam0 k = 0 := by
    have h := T.χ₀_eq k
    rw [hχ, hε, Int.cast_zero, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_left T.a_ne_zero
  apply toKQ_injective hflat
  rw [T.toKQ_eq, hε, hl, Int.cast_zero, zero_smul, zero_smul, add_zero, map_zero]

theorem TOData.eq_of (hflat : letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Flat ℤ K)
    {k k' : K} (hε : Bialgebra.counitAlgHom ℤ K k = Bialgebra.counitAlgHom ℤ K k')
    (hχ : T.χ₀ k = T.χ₀ k') : k = k' := by
  rw [← sub_eq_zero]
  exact T.eq_zero_of hflat _ (by rw [map_sub, hε, sub_self]) (by rw [map_sub, hχ, sub_self])

end TateOort

section AwayFromP

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K]

abbrev KL (ℓ : ℕ) : Type :=
  @TensorProduct ℤ _ (GaloisRep.ratLocalizedAt ℓ) K _ _
    (Algebra.toModule (R := ℤ) (A := GaloisRep.ratLocalizedAt ℓ))
    (Algebra.toModule (R := ℤ) (A := K))

abbrev tmulL (ℓ : ℕ) (z : GaloisRep.ratLocalizedAt ℓ) (k : K) : KL (K := K) ℓ :=
  @TensorProduct.tmul ℤ _ (GaloisRep.ratLocalizedAt ℓ) K _ _
    (Algebra.toModule (R := ℤ) (A := GaloisRep.ratLocalizedAt ℓ))
    (Algebra.toModule (R := ℤ) (A := K)) z k

theorem mem_ratLocalizedAt_of_finite (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hfin : letI : Module ℤ K := AddCommGroup.toIntModule K;
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (χ' : K →+* ℚ) (k : K) : χ' k ∈ GaloisRep.ratLocalizedAt ℓ := by
  haveI : Module.Finite (GaloisRep.ratLocalizedAt ℓ) (KL (K := K) ℓ) := by
    convert hfin <;> exact Subsingleton.elim _ _
  haveI : Algebra.IsIntegral (GaloisRep.ratLocalizedAt ℓ) (KL (K := K) ℓ) := inferInstance
  let θ : KL (K := K) ℓ →ₐ[GaloisRep.ratLocalizedAt ℓ] ℚ :=
    Algebra.TensorProduct.lift (Algebra.ofId _ ℚ) (intAlgHom χ') (fun _ _ => Commute.all _ _)
  have hint : IsIntegral (GaloisRep.ratLocalizedAt ℓ) (χ' k) := by
    have h1 : IsIntegral (GaloisRep.ratLocalizedAt ℓ) (tmulL ℓ 1 k) :=
      Algebra.IsIntegral.isIntegral _
    have h2 := h1.map θ
    have hθ : θ (tmulL ℓ 1 k) = χ' k := by
      change Algebra.TensorProduct.lift _ _ _ (tmulL ℓ 1 k) = _
      rw [tmulL, Algebra.TensorProduct.lift_tmul]
      simp
    rwa [hθ] at h2
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt ℓ hℓ
  haveI := GaloisRep.isFractionRing_ratLocalizedAt ℓ
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← hy]
  exact y.2

theorem finite_of_forall_den_eq_one (χ' : K →+* ℚ) (hχ' : ∀ k, (χ' k).den = 1)
    (hinj : ∀ k, Bialgebra.counitAlgHom ℤ K k = 0 → χ' k = 0 → k = 0) :
    letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Finite ℤ K := by
  letI : Module ℤ K := AddCommGroup.toIntModule K
  let f : K →+ ℤ × ℤ :=
    { toFun := fun k => (Bialgebra.counitAlgHom ℤ K k, (χ' k).num)
      map_zero' := by simp
      map_add' := fun a b => by
        ext
        · simp
        · change (χ' (a + b)).num = (χ' a).num + (χ' b).num
          have ha : χ' a = (χ' a).num := (Rat.den_eq_one_iff _).mp (hχ' a) |>.symm
          have hb : χ' b = (χ' b).num := (Rat.den_eq_one_iff _).mp (hχ' b) |>.symm
          have hab : χ' (a + b) = (χ' (a + b)).num := (Rat.den_eq_one_iff _).mp (hχ' _) |>.symm
          have := map_add χ' a b
          rw [hab, ha, hb, ← Int.cast_add] at this
          exact_mod_cast this }
  refine Module.Finite.of_injective f.toIntLinearMap fun a b hab => ?_
  have h := congrArg (fun x => x) hab
  simp only [AddMonoidHom.coe_toIntLinearMap] at h
  have h1 : Bialgebra.counitAlgHom ℤ K a = Bialgebra.counitAlgHom ℤ K b := congrArg Prod.fst h
  have h2 : (χ' a).num = (χ' b).num := congrArg Prod.snd h
  have h2' : χ' a = χ' b := by
    rw [← (Rat.den_eq_one_iff _).mp (hχ' a), ← (Rat.den_eq_one_iff _).mp (hχ' b), h2]
  have := hinj (a - b) (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2', sub_self])
  exact sub_eq_zero.mp this

end AwayFromP

section Situation

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K] (T : TOData K) (p : ℕ)

structure Sit : Prop where
  hp : p.Prime
  hflat : letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Flat ℤ K
  hval : ∀ k : K, ∃ n : ℕ, (T.χ₀ k).den = p ^ n
  hinv : ((p : ℚ)⁻¹) ∈ T.χ₀.range

theorem sit_of
    (hflat : letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      letI : Module ℤ K := AddCommGroup.toIntModule K;
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hK : ¬ (letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Finite ℤ K)) :
    Sit T p := by
  have hmem : ∀ k : K, ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → T.χ₀ k ∈ GaloisRep.ratLocalizedAt ℓ :=
    fun k ℓ hℓ hℓp => mem_ratLocalizedAt_of_finite ℓ hℓ (hff ℓ hℓ hℓp) T.χ₀ k

  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : K, (T.χ₀ k₁).den ≠ 1 := by
    by_contra h
    push Not at h
    exact hK (finite_of_forall_den_eq_one T.χ₀ h (T.eq_zero_of hflat))
  obtain ⟨hp, hpk₁⟩ := prime_of_forall_mem_ratLocalizedAt (hmem k₁) hk₁
  exact
    { hp := hp
      hflat := hflat
      hval := fun k => den_eq_prime_pow hp (hmem k)
      hinv := inv_mem_of_prime_dvd_den T.χ₀.range (RingHom.mem_range_self _ _) hp hpk₁ }

variable {T p}

theorem Sit.p_ne_zero (S : Sit T p) : (p : ℚ) ≠ 0 := by exact_mod_cast S.hp.ne_zero

theorem Sit.exists_eq_div (S : Sit T p) (k : K) : ∃ (n : ℤ) (i : ℕ), T.χ₀ k = n / (p : ℚ) ^ i := by
  obtain ⟨i, hi⟩ := S.hval k
  exact ⟨_, i, eq_num_div_pow hi⟩

theorem Sit.exists_apply_eq (S : Sit T p) (n : ℤ) (i : ℕ) : ∃ k : K, T.χ₀ k = n / (p : ℚ) ^ i := by
  have h := div_pow_mem_of_inv_mem T.χ₀.range S.hinv n i
  obtain ⟨k, hk⟩ := RingHom.mem_range.mp h
  exact ⟨k, hk⟩

variable (T)

def idealM : Ideal ℤ where
  carrier := {n : ℤ | ∃ j : K, Bialgebra.counitAlgHom ℤ K j = 0 ∧ T.χ₀ j = n}
  add_mem' := by
    rintro a b ⟨j, hj, hja⟩ ⟨j', hj', hjb⟩
    exact ⟨j + j', by rw [map_add, hj, hj', add_zero], by rw [map_add, hja, hjb, Int.cast_add]⟩
  zero_mem' := ⟨0, map_zero _, by rw [map_zero, Int.cast_zero]⟩
  smul_mem' := by
    rintro c n ⟨j, hj, hjn⟩
    refine ⟨(c : K) * j, by rw [map_mul, hj, mul_zero], ?_⟩
    rw [map_mul, map_intCast, hjn, smul_eq_mul, Int.cast_mul]

def mgen : ℕ := (Submodule.IsPrincipal.generator (idealM T)).natAbs

theorem mem_idealM_iff (n : ℤ) : n ∈ idealM T ↔ (mgen T : ℤ) ∣ n := by
  rw [mgen, Int.natAbs_dvd]
  constructor
  · intro hn
    rw [← Ideal.span_singleton_generator (idealM T)] at hn
    exact Ideal.mem_span_singleton.mp hn
  · intro hn
    rw [← Ideal.span_singleton_generator (idealM T)]
    exact Ideal.mem_span_singleton.mpr hn

theorem exists_w0 : ∃ w₀ : K, Bialgebra.counitAlgHom ℤ K w₀ = 0 ∧ T.χ₀ w₀ = mgen T := by
  obtain ⟨j, hj, hjm⟩ := (mem_idealM_iff T (mgen T : ℤ)).mpr dvd_rfl
  exact ⟨j, hj, by rw [hjm, Int.cast_natCast]⟩

variable {T}

theorem Sit.J_val (S : Sit T p) (j : K) (hj : Bialgebra.counitAlgHom ℤ K j = 0) :
    ∃ (c : ℤ) (i : ℕ), T.χ₀ j = (mgen T : ℚ) * c / (p : ℚ) ^ i := by
  obtain ⟨n, i, hn⟩ := S.exists_eq_div j
  have hmem : n ∈ idealM T := by
    refine ⟨((p : K) ^ i) * j, by rw [map_mul, hj, mul_zero], ?_⟩
    rw [map_mul, map_pow, map_natCast, hn, mul_div_cancel₀ _ (pow_ne_zero i S.p_ne_zero)]
  obtain ⟨c, hc⟩ := (mem_idealM_iff T n).mp hmem
  refine ⟨c, i, ?_⟩
  rw [hn, hc, Int.cast_mul, Int.cast_natCast]

theorem Sit.k_val (S : Sit T p) (k : K) :
    ∃ (c : ℤ) (i : ℕ), T.χ₀ k - (Bialgebra.counitAlgHom ℤ K k : ℚ) = (mgen T : ℚ) * c / (p : ℚ) ^ i := by
  obtain ⟨c, i, hc⟩ := S.J_val (k - (Bialgebra.counitAlgHom ℤ K k : K))
    (by rw [map_sub, map_intCast, Int.cast_id, sub_self])
  refine ⟨c, i, ?_⟩
  rw [← hc, map_sub, map_intCast]

theorem Sit.a_lam0 (S : Sit T p) (k : K) :
    ∃ (c : ℤ) (i : ℕ), T.a * T.lam0 k = (mgen T : ℚ) * c / (p : ℚ) ^ i := by
  obtain ⟨c, i, hc⟩ := S.k_val k
  exact ⟨c, i, by rw [T.a_lam0_eq, hc]⟩

theorem Sit.mgen_ne_zero (S : Sit T p)
    (hK : ¬ (letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Finite ℤ K)) : mgen T ≠ 0 := by
  intro h0
  apply hK
  apply finite_of_forall_den_eq_one T.χ₀ _ (T.eq_zero_of S.hflat)
  intro k
  obtain ⟨c, i, hc⟩ := S.k_val k
  rw [h0, Nat.cast_zero, zero_mul, zero_div, sub_eq_zero] at hc
  rw [hc]
  exact Rat.den_intCast _

theorem Sit.not_dvd (S : Sit T p)
    (hK : ¬ (letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Finite ℤ K)) : ¬ p ∣ mgen T := by
  rintro ⟨m', hm'⟩
  obtain ⟨w₀, hw₀, hw₀m⟩ := exists_w0 T
  obtain ⟨k₁, hk₁⟩ := S.exists_apply_eq 1 1
  have hmem : (m' : ℤ) ∈ idealM T := by
    refine ⟨k₁ * w₀, by rw [map_mul, hw₀, mul_zero], ?_⟩
    rw [map_mul, hk₁, hw₀m, hm', Int.cast_one, pow_one, Nat.cast_mul, Int.cast_natCast,
      one_div, inv_mul_cancel_left₀ S.p_ne_zero]
  have hdvd : mgen T ∣ m' := Int.natCast_dvd_natCast.mp ((mem_idealM_iff T _).mp hmem)
  have hm'0 : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · exact absurd (by rw [hm', h, mul_zero]) (S.mgen_ne_zero hK)
    · exact h
  have hle : p * m' ≤ 1 * m' := by rw [← hm', one_mul]; exact Nat.le_of_dvd hm'0 hdvd
  have hp1 : p ≤ 1 := Nat.le_of_mul_le_mul_right hle hm'0
  exact absurd hp1 (not_le.mpr S.hp.one_lt)

theorem Sit.lift (S : Sit T p) (α c : ℤ) (i : ℕ) :
    ∃ k : K, Bialgebra.counitAlgHom ℤ K k = α ∧ T.χ₀ k = α + (mgen T : ℚ) * c / (p : ℚ) ^ i := by
  obtain ⟨kc, hkc⟩ := S.exists_apply_eq c i
  obtain ⟨w₀, hw₀, hw₀m⟩ := exists_w0 T
  refine ⟨(α : K) + kc * w₀, ?_, ?_⟩
  · rw [map_add, map_intCast, map_mul, hw₀, mul_zero, add_zero, Int.cast_id]
  · rw [map_add, map_intCast, map_mul, hkc, hw₀m]
    ring

variable (T)

def Λ : KQ K ⊗[ℚ] KQ K →ₗ[ℚ] ℚ := LinearMap.mul' ℚ ℚ ∘ₗ TensorProduct.map T.c₁ T.c₁

theorem Λ_tmul (u v : KQ K) : Λ T (u ⊗ₜ[ℚ] v) = T.c₁ u * T.c₁ v := by
  simp [Λ]

def Pm (p : ℕ) (q : ℚ) : Prop := ∃ (c : ℤ) (i : ℕ), q = (mgen T : ℚ) ^ 2 * c / (p : ℚ) ^ i

theorem Pm_zero : Pm T p 0 := ⟨0, 0, by simp⟩

variable {T}

theorem Sit.Pm_add (S : Sit T p) {q r : ℚ} (hq : Pm T p q) (hr : Pm T p r) : Pm T p (q + r) := by
  obtain ⟨c, i, hc⟩ := hq
  obtain ⟨c', i', hc'⟩ := hr
  refine ⟨c * p ^ i' + c' * p ^ i, i + i', ?_⟩
  rw [hc, hc']
  have := S.p_ne_zero
  field_simp
  push_cast
  ring

theorem Sit.Pm_Theta (S : Sit T p) (t : KK K) : Pm T p (T.a ^ 2 * Λ T (Theta K t)) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [Theta_zero, map_zero, mul_zero]; exact Pm_zero T
  | tmul x y =>
    rw [Theta_tmul, Λ_tmul]
    obtain ⟨c, i, hc⟩ := S.a_lam0 x
    obtain ⟨c', i', hc'⟩ := S.a_lam0 y
    refine ⟨c * c', i + i', ?_⟩
    calc T.a ^ 2 * (T.c₁ (toKQ K x) * T.c₁ (toKQ K y))
        = (T.a * T.lam0 x) * (T.a * T.lam0 y) := by simp only [TOData.lam0]; ring
      _ = (mgen T : ℚ) ^ 2 * ((c * c' : ℤ) : ℚ) / (p : ℚ) ^ (i + i') := by
        rw [hc, hc']
        have := S.p_ne_zero
        field_simp
        push_cast
        ring
  | add s t hs ht => rw [Theta_add, map_add, mul_add]; exact S.Pm_add hs ht

theorem Sit.mgen_dvd_two (S : Sit T p)
    (hK : ¬ (letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Finite ℤ K)) : mgen T ∣ 2 := by
  obtain ⟨w₀, hw₀, hw₀m⟩ := exists_w0 T
  have hP := S.Pm_Theta (Bialgebra.comulAlgHom ℤ K w₀)
  rw [Theta_comul] at hP
  have hμ : T.a * T.lam0 w₀ = mgen T := by
    rw [T.a_lam0_eq, hw₀m, hw₀, Int.cast_zero, sub_zero]
  have htoKQ : toKQ K w₀ = (T.lam0 w₀) • T.x := by
    rw [T.toKQ_eq, hw₀, Int.cast_zero, zero_smul, zero_add]
  rw [htoKQ, map_smul, T.hΔ] at hP
  have hΛ : Λ T (T.lam0 w₀ • (T.x ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] T.x - T.b • (T.x ⊗ₜ[ℚ] T.x))) =
      -(T.lam0 w₀ * T.b) := by
    rw [map_smul, map_sub, map_add, map_smul, Λ_tmul, Λ_tmul, Λ_tmul, T.c₁_one, T.c₁_x,
      smul_eq_mul, smul_eq_mul]
    ring
  rw [hΛ] at hP
  have hval : T.a ^ 2 * -(T.lam0 w₀ * T.b) = -2 * mgen T := by
    calc T.a ^ 2 * -(T.lam0 w₀ * T.b) = -((T.a * T.lam0 w₀) * (T.a * T.b)) := by ring
      _ = -2 * mgen T := by rw [hμ, T.hab]; ring
  rw [hval] at hP
  obtain ⟨c, i, hc⟩ := hP
  have hp0 := S.p_ne_zero
  have h1 : (-2 * (mgen T : ℚ)) * (p : ℚ) ^ i = (mgen T : ℚ) ^ 2 * c := by
    rw [hc, div_mul_cancel₀ _ (pow_ne_zero i hp0)]
  have hZ : (-2 * (mgen T : ℤ)) * (p : ℤ) ^ i = (mgen T : ℤ) ^ 2 * c := by exact_mod_cast h1
  have hm0 : (mgen T : ℤ) ≠ 0 := by exact_mod_cast S.mgen_ne_zero hK
  have hZ' : (mgen T : ℤ) * c = -2 * (p : ℤ) ^ i := by
    have : (mgen T : ℤ) * ((mgen T : ℤ) * c) = (mgen T : ℤ) * (-2 * (p : ℤ) ^ i) := by
      rw [← mul_assoc, ← sq, ← hZ]; ring
    exact mul_left_cancel₀ hm0 this
  have hdvd : mgen T ∣ 2 * p ^ i := by
    have : (mgen T : ℤ) ∣ ((2 * p ^ i : ℕ) : ℤ) := ⟨-c, by push_cast; linear_combination hZ'⟩
    exact Int.natCast_dvd_natCast.mp this
  have hcop : Nat.Coprime (mgen T) (p ^ i) :=
    Nat.Coprime.pow_right i ((Nat.Prime.coprime_iff_not_dvd S.hp).mpr (S.not_dvd hK)).symm
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem Sit.mgen_cases (S : Sit T p)
    (hK : ¬ (letI : Module ℤ K := AddCommGroup.toIntModule K; Module.Finite ℤ K)) :
    mgen T = 1 ∨ (mgen T = 2 ∧ p ≠ 2) := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (S.mgen_dvd_two hK) with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    rintro rfl
    exact S.not_dvd hK (by rw [h])

end Situation

namespace Const

section Const

variable (R : Type) [CommRing R] (ι : Type) [AddCommGroup ι] [Fintype ι] [DecidableEq ι]

abbrev e (i : ι) : ι → R := Pi.single i 1

lemma e_apply (i j : ι) : e R ι i j = if j = i then 1 else 0 := by
  simp [Pi.single_apply]

lemma e_mul_e (i j : ι) : e R ι i * e R ι j = if i = j then e R ι i else 0 := by
  ext k
  by_cases h : i = j
  · subst h
    by_cases hk : k = i <;> simp [hk]
  · simp only [Pi.mul_apply, Pi.single_apply, if_neg h, Pi.zero_apply]
    by_cases hk : k = i
    · subst hk; simp [h]
    · simp [hk]

lemma sum_e : ∑ i, e R ι i = 1 := by
  have := Finset.univ_sum_single (fun _ : ι => (1 : R))
  simp only [e] at this ⊢
  exact this

noncomputable def comulLin : (ι → R) →ₗ[R] (ι → R) ⊗[R] (ι → R) :=
  (Pi.basisFun R ι).constr R fun g => ∑ a, e R ι a ⊗ₜ[R] e R ι (g - a)

lemma comulLin_e (g : ι) :
    comulLin R ι (e R ι g) = ∑ a, e R ι a ⊗ₜ[R] e R ι (g - a) := by
  have h := (Pi.basisFun R ι).constr_basis R (fun g => ∑ a, e R ι a ⊗ₜ[R] e R ι (g - a)) g
  rw [Pi.basisFun_apply] at h
  exact h

lemma comulLin_one : comulLin R ι 1 = 1 := by
  rw [← sum_e R ι, map_sum]
  simp_rw [comulLin_e]
  rw [Finset.sum_comm]
  have : ∀ a : ι, ∑ g, e R ι a ⊗ₜ[R] e R ι (g - a) = e R ι a ⊗ₜ[R] 1 := by
    intro a
    rw [← TensorProduct.tmul_sum, ← sum_e R ι]
    congr 1
    exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
  simp_rw [this, ← TensorProduct.sum_tmul, sum_e]
  rfl

lemma comulLin_mul_e (a b : ι) :
    comulLin R ι (e R ι a * e R ι b) = comulLin R ι (e R ι a) * comulLin R ι (e R ι b) := by
  rw [comulLin_e, comulLin_e, Finset.sum_mul_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul, e_mul_e, TensorProduct.ite_tmul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_left_inj, TensorProduct.tmul_ite]
  by_cases h : a = b
  · subst h; simp [comulLin_e]
  · simp [h]

lemma comulLin_mul (f g : ι → R) :
    comulLin R ι (f * g) = comulLin R ι f * comulLin R ι g := by
  have key : (LinearMap.mul R (ι → R)).compr₂ (comulLin R ι)
      = (LinearMap.mul R ((ι → R) ⊗[R] (ι → R))).compl₁₂ (comulLin R ι) (comulLin R ι) := by
    refine (Pi.basisFun R ι).ext fun a => (Pi.basisFun R ι).ext fun b => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
      Pi.basisFun_apply]
    exact comulLin_mul_e R ι a b
  exact congr($key f g)

private noncomputable def _root_.P2mTwoPointHopf.Const.comulAlgHom : (ι → R) →ₐ[R] (ι → R) ⊗[R] (ι → R) :=
  AlgHom.ofLinearMap (comulLin R ι) (comulLin_one R ι) (comulLin_mul R ι)

p2m_export "P2mTwoPointHopf.Const" "comulAlgHom"
@[scoped simp] private lemma _root_.P2mTwoPointHopf.Const.comulAlgHom_apply (f : ι → R) : comulAlgHom R ι f = comulLin R ι f := rfl

p2m_export "P2mTwoPointHopf.Const" "comulAlgHom_apply"

private noncomputable def _root_.P2mTwoPointHopf.Const.counitAlgHom : (ι → R) →ₐ[R] R := Pi.evalAlgHom R (fun _ : ι => R) 0

p2m_export "P2mTwoPointHopf.Const" "counitAlgHom"
@[scoped simp] private lemma _root_.P2mTwoPointHopf.Const.counitAlgHom_apply (f : ι → R) : counitAlgHom R ι f = f 0 := rfl

p2m_export "P2mTwoPointHopf.Const" "counitAlgHom_apply"
lemma counit_e (a : ι) : counitAlgHom R ι (e R ι a) = if a = 0 then 1 else 0 := by
  simp [Pi.single_apply, eq_comm]

lemma coassoc_e (g : ι) :
    (Algebra.TensorProduct.assoc R R R (ι → R) (ι → R) (ι → R))
        (Algebra.TensorProduct.map (comulAlgHom R ι) (AlgHom.id R (ι → R))
          (comulAlgHom R ι (e R ι g)))
      = Algebra.TensorProduct.map (AlgHom.id R (ι → R)) (comulAlgHom R ι)
          (comulAlgHom R ι (e R ι g)) := by
  simp only [comulAlgHom_apply, comulLin_e, map_sum, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, TensorProduct.sum_tmul, Algebra.TensorProduct.assoc_tmul,
    TensorProduct.tmul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight c) _ _ (fun a => ?_)
  simp only [Equiv.subRight_apply]
  congr 3
  abel

lemma rTensor_counit_e (g : ι) :
    Algebra.TensorProduct.map (counitAlgHom R ι) (AlgHom.id R (ι → R)) (comulAlgHom R ι (e R ι g))
      = (Algebra.TensorProduct.lid R (ι → R)).symm (e R ι g) := by
  simp only [comulAlgHom_apply, comulLin_e, map_sum, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, counit_e, TensorProduct.ite_tmul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, sub_zero, Algebra.TensorProduct.lid_symm_apply]

lemma lTensor_counit_e (g : ι) :
    Algebra.TensorProduct.map (AlgHom.id R (ι → R)) (counitAlgHom R ι) (comulAlgHom R ι (e R ι g))
      = (Algebra.TensorProduct.rid R R (ι → R)).symm (e R ι g) := by
  simp only [comulAlgHom_apply, comulLin_e, map_sum, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, counit_e, sub_eq_zero, TensorProduct.tmul_ite]
  simp_rw [show ∀ a : ι, (g = a) = (a = g) from fun a => propext eq_comm]
  rw [Finset.sum_ite_eq' Finset.univ g, if_pos (Finset.mem_univ _)]
  simp [Algebra.TensorProduct.rid_symm_apply]

lemma algHom_ext_e {B : Type*} [Semiring B] [Algebra R B] {φ ψ : (ι → R) →ₐ[R] B}
    (h : ∀ g, φ (e R ι g) = ψ (e R ι g)) : φ = ψ := by
  apply AlgHom.toLinearMap_injective
  refine (Pi.basisFun R ι).ext fun g => ?_
  simpa [Pi.basisFun_apply] using h g

@[reducible] noncomputable def constBialgebra : Bialgebra R (ι → R) :=
  Bialgebra.ofAlgHom (comulAlgHom R ι) (counitAlgHom R ι)
    (algHom_ext_e R ι fun g => by simpa using coassoc_e R ι g)
    (algHom_ext_e R ι fun g => by simpa using rTensor_counit_e R ι g)
    (algHom_ext_e R ι fun g => by simpa using lTensor_counit_e R ι g)

noncomputable def antipodeLin : (ι → R) →ₗ[R] (ι → R) := LinearMap.funLeft R R fun i : ι => -i

lemma antipodeLin_e (a : ι) : antipodeLin R ι (e R ι a) = e R ι (-a) := by
  ext i
  simp [antipodeLin, LinearMap.funLeft_apply, Pi.single_apply, neg_eq_iff_eq_neg]

lemma sum_e_neg : ∑ a, e R ι (-a) = 1 := by
  rw [← sum_e R ι]
  exact Fintype.sum_equiv (Equiv.neg ι) _ _ (fun _ => rfl)

lemma antipode_rTensor :
    LinearMap.mul' R (ι → R) ∘ₗ (antipodeLin R ι).rTensor (ι → R) ∘ₗ (comulAlgHom R ι).toLinearMap
      = Algebra.linearMap R (ι → R) ∘ₗ (counitAlgHom R ι).toLinearMap := by
  refine (Pi.basisFun R ι).ext fun g => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Pi.basisFun_apply,
    comulAlgHom_apply, comulLin_e, map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
    antipodeLin_e, e_mul_e, counit_e, Algebra.linearMap_apply]
  simp_rw [show ∀ a : ι, (-a = g - a) = (g = 0) from fun a => propext
    ⟨fun h => by have := congrArg (· + a) h; simpa using this.symm, fun h => by simp [h]⟩]
  by_cases hg : g = 0
  · simp [hg, sum_e_neg]
  · simp [hg]

lemma antipode_lTensor :
    LinearMap.mul' R (ι → R) ∘ₗ (antipodeLin R ι).lTensor (ι → R) ∘ₗ (comulAlgHom R ι).toLinearMap
      = Algebra.linearMap R (ι → R) ∘ₗ (counitAlgHom R ι).toLinearMap := by
  refine (Pi.basisFun R ι).ext fun g => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Pi.basisFun_apply,
    comulAlgHom_apply, comulLin_e, map_sum, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
    antipodeLin_e, e_mul_e, counit_e, neg_sub, Algebra.linearMap_apply]
  simp_rw [show ∀ a : ι, (a = a - g) = (g = 0) from fun a => propext
    ⟨fun h => by have := congrArg (fun x => a - x) h; simpa using this.symm, fun h => by simp [h]⟩]
  by_cases hg : g = 0
  · simp [hg, sum_e]
  · simp [hg]

@[reducible] noncomputable def constHopf : HopfAlgebra R (ι → R) :=
  letI := constBialgebra R ι
  { antipode := antipodeLin R ι
    mul_antipode_rTensor_comul := antipode_rTensor R ι
    mul_antipode_lTensor_comul := antipode_lTensor R ι }

end Const

end Const
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.P2mTwoPointHopf.Const"

section ScalarTower

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K]

theorem isScalarTower_int :
    @IsScalarTower ℤ ℤ K Algebra.toSMul (Algebra.toSMul (R := ℤ) (A := K))
      (Algebra.toSMul (R := ℤ) (A := K)) :=
  @IsScalarTower.mk ℤ ℤ K Algebra.toSMul (Algebra.toSMul (R := ℤ) (A := K))
    (Algebra.toSMul (R := ℤ) (A := K)) fun x y z => by
      simp only [Algebra.smul_def, map_mul, mul_assoc, Algebra.algebraMap_self, RingHom.id_apply]

end ScalarTower
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.P2mTwoPointHopf.Const"

section CaseA

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K]

attribute [local instance] isScalarTower_int

abbrev P2 : Type := Fin 2 → ℤ

@[reducible] def instHopfP2 : HopfAlgebra ℤ P2 := Const.constHopf ℤ (Fin 2)

attribute [local instance] instHopfP2

theorem comul_P2 (v : P2) : Bialgebra.comulAlgHom ℤ P2 v = Const.comulLin ℤ (Fin 2) v := rfl

theorem counit_P2 (v : P2) : Bialgebra.counitAlgHom ℤ P2 v = v 0 := rfl

theorem comul_P2_e (g : Fin 2) :
    Bialgebra.comulAlgHom ℤ P2 (Const.e ℤ (Fin 2) g) =
      Const.e ℤ (Fin 2) 0 ⊗ₜ[ℤ] Const.e ℤ (Fin 2) g + Const.e ℤ (Fin 2) 1 ⊗ₜ[ℤ] Const.e ℤ (Fin 2) (g - 1) := by
  rw [comul_P2, Const.comulLin_e, Fin.sum_univ_two, sub_zero]

section psiA

variable (w : K) (hw : w * w = w)

def psiARingHom : P2 →+* K where
  toFun v := (v 0 : K) * (1 - w) + (v 1 : K) * w
  map_one' := by simp
  map_mul' v v' := by
    simp only [Pi.mul_apply, Int.cast_mul]
    linear_combination (-(((v 0 : K) - v 1) * ((v' 0 : K) - v' 1))) * hw
  map_zero' := by simp
  map_add' v v' := by
    simp only [Pi.add_apply, Int.cast_add]
    ring

def psiA : P2 →ₐ[ℤ] K := intAlgHom (psiARingHom w hw)

theorem psiA_apply (v : P2) : psiA w hw v = (v 0 : K) * (1 - w) + (v 1 : K) * w := rfl

theorem psiA_e0 : psiA w hw (Const.e ℤ (Fin 2) 0) = 1 - w := by
  rw [psiA_apply]; simp

theorem psiA_e1 : psiA w hw (Const.e ℤ (Fin 2) 1) = w := by
  rw [psiA_apply]; simp

end psiA
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.P2mTwoPointHopf.Const"

variable {T : TOData K} {p : ℕ}

structure DatA (T : TOData K) where
  w : K
  hε : Bialgebra.counitAlgHom ℤ K w = 0
  hχ : T.χ₀ w = 1
  hww : w * w = w
  htoKQ : toKQ K w = T.a⁻¹ • T.x

theorem Sit.nonempty_datA (S : Sit T p) (hm : mgen T = 1) : Nonempty (DatA T) := by
  obtain ⟨w, hwε, hwχ⟩ := exists_w0 T
  rw [hm, Nat.cast_one] at hwχ
  have hww : w * w = w := T.eq_of S.hflat (by rw [map_mul, hwε, mul_zero]) (by rw [map_mul, hwχ, mul_one])
  have hν : T.lam0 w = T.a⁻¹ := by
    have h := T.a_lam0_eq w
    rw [hwχ, hwε, Int.cast_zero, sub_zero] at h
    exact (eq_inv_of_mul_eq_one_right h)
  refine ⟨⟨w, hwε, hwχ, hww, ?_⟩⟩
  rw [T.toKQ_eq, hwε, Int.cast_zero, zero_smul, zero_add, hν]

variable (D : DatA T)

theorem DatA.counit_psiA (v : P2) : Bialgebra.counitAlgHom ℤ K (psiA D.w D.hww v) = v 0 := by
  rw [psiA_apply, map_add, map_mul, map_mul, map_sub, map_one, map_intCast, map_intCast, D.hε,
    Int.cast_id, Int.cast_id]
  ring

theorem DatA.χ₀_psiA (v : P2) : T.χ₀ (psiA D.w D.hww v) = v 1 := by
  rw [psiA_apply, map_add, map_mul, map_mul, map_sub, map_one, map_intCast, map_intCast, D.hχ]
  ring

theorem DatA.toKQ_one_sub : toKQ K (1 - D.w) = 1 - T.a⁻¹ • T.x := by
  rw [map_sub, map_one, D.htoKQ]

theorem DatA.comul_one_sub :
    Coalgebra.comul (R := ℚ) (toKQ K (1 - D.w)) =
      (1 : KQ K) ⊗ₜ[ℚ] (1 : KQ K) - T.a⁻¹ • (T.x ⊗ₜ[ℚ] 1) - T.a⁻¹ • (1 ⊗ₜ[ℚ] T.x)
        + (T.a⁻¹ * T.b) • (T.x ⊗ₜ[ℚ] T.x) := by
  rw [D.toKQ_one_sub, map_sub, Bialgebra.comul_one, Algebra.TensorProduct.one_def, map_smul, T.hΔ,
    smul_sub, smul_add, smul_smul]
  abel

theorem DatA.comul_w :
    Coalgebra.comul (R := ℚ) (toKQ K D.w) =
      T.a⁻¹ • (T.x ⊗ₜ[ℚ] 1) + T.a⁻¹ • (1 ⊗ₜ[ℚ] T.x) - (T.a⁻¹ * T.b) • (T.x ⊗ₜ[ℚ] T.x) := by
  rw [D.htoKQ, map_smul, T.hΔ, smul_sub, smul_add, smul_smul]

def DatA.psiBialg (S : Sit T p) :=
  BialgHom.ofAlgHom (psiA D.w D.hww)
    (by
      refine Const.algHom_ext_e ℤ (Fin 2) fun g => ?_
      rw [AlgHom.comp_apply, counit_P2, D.counit_psiA])
    (by
      refine Const.algHom_ext_e ℤ (Fin 2) fun g => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, comul_P2_e, map_add, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul]
      apply Theta_injective K S.hflat
      rw [Theta_comul, Theta_add, Theta_tmul, Theta_tmul]
      have hcoef : T.a⁻¹ * T.b = T.a⁻¹ * T.a⁻¹ + T.a⁻¹ * T.a⁻¹ := by rw [T.b_eq]; ring
      fin_cases g
      · simp only [Fin.zero_eta, Fin.isValue, show (0 : Fin 2) - 1 = 1 from by decide]
        rw [psiA_e0, psiA_e1, D.comul_one_sub, D.toKQ_one_sub, D.htoKQ, hcoef, add_smul]
        simp only [TensorProduct.tmul_sub, TensorProduct.sub_tmul, TensorProduct.smul_tmul,
          TensorProduct.tmul_smul, smul_sub, smul_smul]
        abel
      · simp only [Fin.mk_one, Fin.isValue, show (1 : Fin 2) - 1 = 0 from by decide]
        rw [psiA_e0, psiA_e1, D.comul_w, D.toKQ_one_sub, D.htoKQ, hcoef, add_smul]
        simp only [TensorProduct.tmul_sub, TensorProduct.sub_tmul, TensorProduct.smul_tmul,
          TensorProduct.tmul_smul, smul_sub, smul_smul]
        abel)

def fA (p : ℕ) : P2 := ![1, (p : ℤ)]

theorem DatA.isLocalization (S : Sit T p) (hm : mgen T = 1) :
    letI : Algebra P2 K := ((D.psiBialg S) : P2 →+* K).toAlgebra
    IsLocalization.Away (fA p) K := by
  letI : Algebra P2 K := ((D.psiBialg S) : P2 →+* K).toAlgebra
  have halg : ∀ v : P2, algebraMap P2 K v = psiA D.w D.hww v := fun v => rfl
  have hεF : Bialgebra.counitAlgHom ℤ K (psiA D.w D.hww (fA p)) = 1 := by
    rw [D.counit_psiA]; rfl
  have hχF : T.χ₀ (psiA D.w D.hww (fA p)) = p := by
    rw [D.χ₀_psiA]; simp [fA]

  obtain ⟨G, hGε, hGχ⟩ := S.lift 1 (1 - p) 1
  rw [hm, Nat.cast_one, one_mul, pow_one] at hGχ
  have hGχ' : T.χ₀ G = (p : ℚ)⁻¹ := by
    rw [hGχ]; have := S.p_ne_zero; field_simp; push_cast; ring
  have hFG : psiA D.w D.hww (fA p) * G = 1 :=
    T.eq_of S.hflat (by rw [map_mul, hεF, hGε, map_one, one_mul])
      (by rw [map_mul, hχF, hGχ', map_one, mul_inv_cancel₀ S.p_ne_zero])
  have hunit : IsUnit (psiA D.w D.hww (fA p)) := isUnit_iff_exists_inv.mpr ⟨G, hFG⟩
  refine (isLocalization_iff (Submonoid.powers (fA p)) K).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    rw [halg, map_pow]
    exact hunit.pow n
  · intro z
    obtain ⟨n, i, hn⟩ := S.exists_eq_div z
    refine ⟨(![Bialgebra.counitAlgHom ℤ K z, n], ⟨fA p ^ i, i, rfl⟩), ?_⟩
    change z * algebraMap P2 K (fA p ^ i) = algebraMap P2 K ![Bialgebra.counitAlgHom ℤ K z, n]
    rw [halg, halg, map_pow]
    refine T.eq_of S.hflat ?_ ?_
    · rw [map_mul, map_pow, hεF, one_pow, mul_one, D.counit_psiA]; rfl
    · rw [map_mul, map_pow, hχF, hn, D.χ₀_psiA, div_mul_cancel₀ _ (pow_ne_zero i S.p_ne_zero)]
      rfl
  · intro v v' h
    refine ⟨1, ?_⟩
    rw [halg, halg] at h
    have h0 : v 0 = v' 0 := by
      have := congrArg (Bialgebra.counitAlgHom ℤ K) h
      rwa [D.counit_psiA, D.counit_psiA] at this
    have h1 : v 1 = v' 1 := by
      have := congrArg T.χ₀ h
      rw [D.χ₀_psiA, D.χ₀_psiA] at this
      exact_mod_cast this
    have hv : v = v' := by
      funext i; fin_cases i
      · exact h0
      · exact h1
    rw [hv]

theorem Sit.caseA (S : Sit T p) (hm : mgen T = 1) :
    ∃ (K₀ : Type) (_ : CommRing K₀) (_ : HopfAlgebra ℤ K₀) (ψ : K₀ →ₐc[ℤ] K) (f : K₀),
      (letI : Algebra K₀ K := (ψ : K₀ →+* K).toAlgebra; IsLocalization.Away f K) ∧
      ((∃ e : K₀ ≃ₐ[ℤ] (Fin 2 → ℤ), e f = ![1, (p : ℤ)] ∧
          ∀ x : K₀, Bialgebra.counitAlgHom ℤ K₀ x = e x 0) ∨
       (p ≠ 2 ∧ ∃ e : K₀ ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod 2)),
          e f = MonoidAlgebra.single 1 (((p : ℤ) + 1) / 2) +
            MonoidAlgebra.single (Multiplicative.ofAdd 1) ((1 - (p : ℤ)) / 2))) := by
  obtain ⟨D⟩ := S.nonempty_datA hm
  exact ⟨P2, inferInstance, instHopfP2, D.psiBialg S, fA p, D.isLocalization S hm,
    Or.inl ⟨AlgEquiv.refl, rfl, fun x => rfl⟩⟩

end CaseA
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.P2mTwoPointHopf.Const"

section CaseB

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K]

attribute [local instance] isScalarTower_int

abbrev G2 : Type := Multiplicative (ZMod 2)

abbrev ZG : Type := MonoidAlgebra ℤ G2

abbrev gg : G2 := Multiplicative.ofAdd 1

theorem G2_cases : ∀ h : G2, h = 1 ∨ h = gg := by decide

theorem gg_mul_gg : gg * gg = 1 := by decide

section chi

variable (u : K) (hu : u * u = 1)

def chiU : G2 →* K where
  toFun h := if h = 1 then 1 else u
  map_one' := by simp
  map_mul' a b := by
    rcases G2_cases a with rfl | rfl <;> rcases G2_cases b with rfl | rfl <;>
      simp [gg_mul_gg, hu]

theorem chiU_one : chiU u hu 1 = 1 := by simp [chiU]

theorem chiU_gg : chiU u hu gg = u := by simp [chiU]

def psiB : ZG →ₐ[ℤ] K := MonoidAlgebra.lift ℤ K G2 (chiU u hu)

theorem psiB_single (h : G2) (r : ℤ) : psiB u hu (MonoidAlgebra.single h r) = (r : K) * chiU u hu h := by
  rw [psiB, MonoidAlgebra.lift_single, Algebra.smul_def, eq_intCast]

theorem psiB_pair (c d : ℤ) :
    psiB u hu (MonoidAlgebra.single 1 c + MonoidAlgebra.single gg d) = (c : K) + (d : K) * u := by
  rw [map_add, psiB_single, psiB_single, chiU_one, chiU_gg, mul_one]

end chi
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.P2mTwoPointHopf.Const"

theorem ZG_decomp (y : ZG) : ∃ c d : ℤ, y = MonoidAlgebra.single 1 c + MonoidAlgebra.single gg d := by
  induction y using MonoidAlgebra.induction_on with
  | of h =>
    rcases G2_cases h with rfl | rfl
    · exact ⟨1, 0, by rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_zero, add_zero]⟩
    · exact ⟨0, 1, by rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_zero, zero_add]⟩
  | add x y hx hy =>
    obtain ⟨c, d, rfl⟩ := hx
    obtain ⟨c', d', rfl⟩ := hy
    exact ⟨c + c', d + d', by simp only [MonoidAlgebra.single_add]; abel⟩
  | smul r y hy =>
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨r * c, r * d, by
      rw [smul_add, MonoidAlgebra.smul_single, MonoidAlgebra.smul_single, smul_eq_mul, smul_eq_mul]⟩

variable {T : TOData K} {p : ℕ}

structure DatB (T : TOData K) where
  u : K
  hε : Bialgebra.counitAlgHom ℤ K u = 1
  hχ : T.χ₀ u = -1
  huu : u * u = 1
  htoKQ : toKQ K u = 1 - (2 * T.a⁻¹) • T.x

theorem Sit.nonempty_datB (S : Sit T p) (hm : mgen T = 2) : Nonempty (DatB T) := by
  obtain ⟨u, huε, huχ⟩ := S.lift 1 (-1) 0
  rw [hm] at huχ
  have huχ' : T.χ₀ u = -1 := by rw [huχ]; norm_num
  have huu : u * u = 1 := T.eq_of S.hflat (by rw [map_mul, huε, map_one, mul_one])
    (by rw [map_mul, huχ', map_one]; norm_num)
  have hν : T.lam0 u = -(2 * T.a⁻¹) := by
    have h := T.a_lam0_eq u
    rw [huχ', huε, Int.cast_one] at h
    have h' : T.lam0 u = (-1 - 1) / T.a := by rw [eq_div_iff T.a_ne_zero, mul_comm]; exact h
    rw [h']; ring
  refine ⟨⟨u, huε, huχ', huu, ?_⟩⟩
  rw [T.toKQ_eq, huε, Int.cast_one, one_smul, hν, neg_smul, sub_eq_add_neg]

variable (D : DatB T)

theorem DatB.counit_psiB (c d : ℤ) :
    Bialgebra.counitAlgHom ℤ K (psiB D.u D.huu (MonoidAlgebra.single 1 c + MonoidAlgebra.single gg d)) = c + d := by
  rw [psiB_pair, map_add, map_mul, map_intCast, map_intCast, D.hε, Int.cast_id, Int.cast_id, mul_one]

theorem DatB.χ₀_psiB (c d : ℤ) :
    T.χ₀ (psiB D.u D.huu (MonoidAlgebra.single 1 c + MonoidAlgebra.single gg d)) = c - d := by
  rw [psiB_pair, map_add, map_mul, map_intCast, map_intCast, D.hχ, mul_neg_one, sub_eq_add_neg]

theorem DatB.psiB_injective {y y' : ZG} (h : psiB D.u D.huu y = psiB D.u D.huu y') : y = y' := by
  obtain ⟨c, d, rfl⟩ := ZG_decomp y
  obtain ⟨c', d', rfl⟩ := ZG_decomp y'
  have h1 : c + d = c' + d' := by
    have := congrArg (Bialgebra.counitAlgHom ℤ K) h
    rwa [D.counit_psiB, D.counit_psiB] at this
  have h2 : c - d = c' - d' := by
    have := congrArg T.χ₀ h
    rw [D.χ₀_psiB, D.χ₀_psiB] at this
    exact_mod_cast this
  obtain rfl : c = c' := by omega
  obtain rfl : d = d' := by omega
  rfl

theorem DatB.comul_u :
    Coalgebra.comul (R := ℚ) (toKQ K D.u) =
      (1 : KQ K) ⊗ₜ[ℚ] (1 : KQ K) - (2 * T.a⁻¹) • (T.x ⊗ₜ[ℚ] 1) - (2 * T.a⁻¹) • (1 ⊗ₜ[ℚ] T.x)
        + ((2 * T.a⁻¹) * T.b) • (T.x ⊗ₜ[ℚ] T.x) := by
  rw [D.htoKQ, map_sub, Bialgebra.comul_one, Algebra.TensorProduct.one_def, map_smul, T.hΔ,
    smul_sub, smul_add, smul_smul]
  abel

def DatB.psiBialg (S : Sit T p) :=
  BialgHom.ofAlgHom (psiB D.u D.huu)
    (by
      refine MonoidAlgebra.algHom_ext (fun h => ?_) (Subsingleton.elim _ _)
      rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply (R := ℤ) (A := ZG), MonoidAlgebra.counit_single,
        CommSemiring.counit_apply, psiB_single, Int.cast_one, one_mul]
      rcases G2_cases h with rfl | rfl
      · rw [chiU_one, map_one]
      · rw [chiU_gg]; exact D.hε)
    (by
      refine MonoidAlgebra.algHom_ext (fun h => ?_) (Subsingleton.elim _ _)
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply (R := ℤ) (A := ZG),
        MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
        MonoidAlgebra.lsingle_apply, Algebra.TensorProduct.map_tmul, psiB_single, Int.cast_one, one_mul]
      rcases G2_cases h with rfl | rfl
      · rw [chiU_one, map_one]; rfl
      · rw [chiU_gg]
        apply Theta_injective K S.hflat
        rw [Theta_comul, Theta_tmul, D.comul_u, D.htoKQ]
        have hcoef : 2 * T.a⁻¹ * T.b = (2 * T.a⁻¹) * (2 * T.a⁻¹) := by rw [T.b_eq]; ring
        rw [hcoef]
        simp only [TensorProduct.tmul_sub, TensorProduct.sub_tmul, TensorProduct.smul_tmul,
          TensorProduct.tmul_smul, smul_sub, smul_smul]
        abel)

def fB (p : ℕ) : ZG :=
  MonoidAlgebra.single 1 (((p : ℤ) + 1) / 2) + MonoidAlgebra.single (Multiplicative.ofAdd 1) ((1 - (p : ℤ)) / 2)

theorem DatB.isLocalization (S : Sit T p) (hm : mgen T = 2) (hp2 : p ≠ 2) :
    letI : Algebra ZG K := ((D.psiBialg S) : ZG →+* K).toAlgebra
    IsLocalization.Away (fB p) K := by
  letI : Algebra ZG K := ((D.psiBialg S) : ZG →+* K).toAlgebra
  have halg : ∀ y : ZG, algebraMap ZG K y = psiB D.u D.huu y := fun y => rfl

  obtain ⟨k, hk⟩ := S.hp.odd_of_ne_two hp2
  have hd1 : ((p : ℤ) + 1) / 2 = k + 1 := by rw [hk]; push_cast; omega
  have hd2 : (1 - (p : ℤ)) / 2 = -(k : ℤ) := by rw [hk]; push_cast; omega
  have hfB : fB p = MonoidAlgebra.single 1 ((k : ℤ) + 1) + MonoidAlgebra.single gg (-(k : ℤ)) := by
    rw [fB, hd1, hd2]
  have hεF : Bialgebra.counitAlgHom ℤ K (psiB D.u D.huu (fB p)) = 1 := by
    rw [hfB, D.counit_psiB]; ring
  have hχF : T.χ₀ (psiB D.u D.huu (fB p)) = p := by
    rw [hfB, D.χ₀_psiB, hk]; push_cast; ring
  have hp0 := S.p_ne_zero

  obtain ⟨G, hGε, hGχ⟩ := S.lift 1 (-(k : ℤ)) 1
  rw [hm, pow_one] at hGχ
  have hGχ' : T.χ₀ G = (p : ℚ)⁻¹ := by
    rw [hGχ, hk]
    have : ((2 * k + 1 : ℕ) : ℚ) ≠ 0 := by rw [← hk]; exact hp0
    field_simp
    push_cast
    ring
  have hFG : psiB D.u D.huu (fB p) * G = 1 :=
    T.eq_of S.hflat (by rw [map_mul, hεF, hGε, map_one, one_mul])
      (by rw [map_mul, hχF, hGχ', map_one, mul_inv_cancel₀ hp0])
  have hunit : IsUnit (psiB D.u D.huu (fB p)) := isUnit_iff_exists_inv.mpr ⟨G, hFG⟩
  have hoddZ : Odd (p : ℤ) := ⟨k, by rw [hk]; push_cast; ring⟩
  refine (isLocalization_iff (Submonoid.powers (fB p)) K).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    rw [halg, map_pow]
    exact hunit.pow n
  · intro z
    obtain ⟨n, i, hn⟩ := S.exists_eq_div z
    obtain ⟨c, j, hc⟩ := S.k_val z
    rw [hm, Nat.cast_ofNat] at hc

    have hpi : (p : ℚ) ^ i ≠ 0 := pow_ne_zero _ hp0
    have hpj : (p : ℚ) ^ j ≠ 0 := pow_ne_zero _ hp0
    have h1 : ((n : ℚ) - (Bialgebra.counitAlgHom ℤ K z : ℚ) * (p : ℚ) ^ i) * (p : ℚ) ^ j =
        2 * (c : ℚ) * (p : ℚ) ^ i := by
      rw [hn, div_sub' hpi, div_eq_div_iff hpi hpj] at hc
      linear_combination hc
    have hZ : ((n : ℤ) - (Bialgebra.counitAlgHom ℤ K z) * (p : ℤ) ^ i) * (p : ℤ) ^ j =
        2 * c * (p : ℤ) ^ i := by exact_mod_cast h1
    have hev : Even (((n : ℤ) - (Bialgebra.counitAlgHom ℤ K z) * (p : ℤ) ^ i) * (p : ℤ) ^ j) :=
      ⟨c * (p : ℤ) ^ i, by rw [hZ]; ring⟩
    have hnpj : ¬ Even ((p : ℤ) ^ j) := Int.not_even_iff_odd.mpr (hoddZ.pow)
    have hnpi : ¬ Even ((p : ℤ) ^ i) := Int.not_even_iff_odd.mpr (hoddZ.pow)
    have hev' : Even ((n : ℤ) - (Bialgebra.counitAlgHom ℤ K z) * (p : ℤ) ^ i) := by
      rcases Int.even_mul.mp hev with h | h
      · exact h
      · exact absurd h hnpj
    have hev'' : Even ((Bialgebra.counitAlgHom ℤ K z : ℤ) - n) := by
      rw [Int.even_sub] at hev' ⊢
      rw [Int.even_mul] at hev'
      constructor
      · intro he; exact hev'.mpr (Or.inl he)
      · intro hn'; rcases hev'.mp hn' with h | h
        · exact h
        · exact absurd h hnpi
    obtain ⟨t, ht⟩ := hev''
    refine ⟨(MonoidAlgebra.single 1 ((Bialgebra.counitAlgHom ℤ K z : ℤ) - t) + MonoidAlgebra.single gg t,
      ⟨fB p ^ i, i, rfl⟩), ?_⟩
    change z * algebraMap ZG K (fB p ^ i) =
      algebraMap ZG K (MonoidAlgebra.single 1 ((Bialgebra.counitAlgHom ℤ K z : ℤ) - t) + MonoidAlgebra.single gg t)
    rw [halg, halg, map_pow]
    refine T.eq_of S.hflat ?_ ?_
    · rw [map_mul, map_pow, hεF, one_pow, mul_one, D.counit_psiB]; ring
    · rw [map_mul, map_pow, hχF, hn, D.χ₀_psiB, div_mul_cancel₀ _ hpi]
      have ht' : (n : ℤ) = Bialgebra.counitAlgHom ℤ K z - t - t := by omega
      rw [ht']
      push_cast
      ring
  · intro y y' h
    refine ⟨1, ?_⟩
    rw [halg, halg] at h
    rw [D.psiB_injective h]

theorem Sit.caseB (S : Sit T p) (hm : mgen T = 2) (hp2 : p ≠ 2) :
    ∃ (K₀ : Type) (_ : CommRing K₀) (_ : HopfAlgebra ℤ K₀) (ψ : K₀ →ₐc[ℤ] K) (f : K₀),
      (letI : Algebra K₀ K := (ψ : K₀ →+* K).toAlgebra; IsLocalization.Away f K) ∧
      ((∃ e : K₀ ≃ₐ[ℤ] (Fin 2 → ℤ), e f = ![1, (p : ℤ)] ∧
          ∀ x : K₀, Bialgebra.counitAlgHom ℤ K₀ x = e x 0) ∨
       (p ≠ 2 ∧ ∃ e : K₀ ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod 2)),
          e f = MonoidAlgebra.single 1 (((p : ℤ) + 1) / 2) +
            MonoidAlgebra.single (Multiplicative.ofAdd 1) ((1 - (p : ℤ)) / 2))) := by
  obtain ⟨D⟩ := S.nonempty_datB hm
  exact ⟨ZG, inferInstance, inferInstance, D.psiBialg S, fB p, D.isLocalization S hm hp2,
    Or.inr ⟨hp2, BialgEquiv.refl ℤ ZG, rfl⟩⟩

end CaseB
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.P2mTwoPointHopf.Const"

end
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.P2mTwoPointHopf.Const"

end P2mTwoPointHopf
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.P2mTwoPointHopf.Const P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.P2mTwoPointHopf"

open P2mTwoPointHopf in
theorem solution
    (p : ℕ) (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2)
    (hK : ¬ Module.Finite ℤ K) :
    p.Prime ∧
    ∃ (K₀ : Type) (_ : CommRing K₀) (_ : HopfAlgebra ℤ K₀) (ψ : K₀ →ₐc[ℤ] K) (f : K₀),
      (letI : Algebra K₀ K := (ψ : K₀ →+* K).toAlgebra; IsLocalization.Away f K) ∧
      ((∃ e : K₀ ≃ₐ[ℤ] (Fin 2 → ℤ), e f = ![1, (p : ℤ)] ∧
          ∀ x : K₀, Bialgebra.counitAlgHom ℤ K₀ x = e x 0) ∨
       (p ≠ 2 ∧ ∃ e : K₀ ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod 2)),
          e f = MonoidAlgebra.single 1 (((p : ℤ) + 1) / 2) +
            MonoidAlgebra.single (Multiplicative.ofAdd 1) ((1 - (p : ℤ)) / 2))) := by

  obtain ⟨ℓ₀, hℓ₀, hℓ₀p⟩ : ∃ ℓ₀ : ℕ, ℓ₀.Prime ∧ ℓ₀ ≠ p := by
    by_cases h : p = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun h' => h h'.symm⟩
  haveI : Module.Finite ℚ (KQ K) := finite_KQ ℓ₀ (hff ℓ₀ hℓ₀ hℓ₀p)
  have h2 : Module.finrank ℚ (KQ K) = 2 := finrank_KQ hgen
  obtain ⟨T⟩ := nonempty_TOData K h2
  have S : Sit T p := sit_of T p inferInstance hff hK
  refine ⟨S.hp, ?_⟩
  rcases S.mgen_cases hK with hm | ⟨hm, hp2⟩
  · exact S.caseA hm
  · exact S.caseB hm hp2

end S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two
end P2MW
export P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two (solution)
