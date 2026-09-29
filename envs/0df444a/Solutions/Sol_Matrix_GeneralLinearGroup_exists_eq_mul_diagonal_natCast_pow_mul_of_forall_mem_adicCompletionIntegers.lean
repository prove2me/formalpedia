-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b4819fea-3ce8-5117-be68-1934bee4aaab

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_GeneralLinearGroup_exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra IsDedekindDomain NumberField

namespace LocalType

section Generic
variable {K : Type*} [Field K] (O : ValuationSubring K)

def IsInt (M : Matrix (Fin 2) (Fin 2) K) : Prop := ∀ i j, M i j ∈ O

theorem IsInt.mul {M N : Matrix (Fin 2) (Fin 2) K} (hM : IsInt O M) (hN : IsInt O N) : IsInt O (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact O.toSubring.sum_mem fun k _ => O.toSubring.mul_mem (hM i k) (hN k j)

theorem IsInt.one : IsInt O (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [O.one_mem, O.zero_mem]

theorem isInt_conj_iff (k : GL (Fin 2) K) (hk : IsInt O (k : Matrix (Fin 2) (Fin 2) K))
    (hki : IsInt O ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) (Y : Matrix (Fin 2) (Fin 2) K) :
    IsInt O (((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y * (k : Matrix (Fin 2) (Fin 2) K)) ↔ IsInt O Y := by
  constructor
  · intro h
    have e : Y = (k : Matrix (Fin 2) (Fin 2) K) *
        ((((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y * (k : Matrix (Fin 2) (Fin 2) K))) *
        ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [e]
    exact IsInt.mul O (IsInt.mul O hk h) hki
  · intro h
    exact IsInt.mul O (IsInt.mul O hki h) hk

theorem isInt_conj_iff' (k : GL (Fin 2) K) (hk : IsInt O (k : Matrix (Fin 2) (Fin 2) K))
    (hki : IsInt O ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) (Y : Matrix (Fin 2) (Fin 2) K) :
    IsInt O ((k : Matrix (Fin 2) (Fin 2) K) * Y * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) ↔ IsInt O Y := by
  have h := isInt_conj_iff O k⁻¹ hki (by rw [inv_inv]; exact hk) Y
  rw [inv_inv] at h
  exact h

def mkGL (M M' : Matrix (Fin 2) (Fin 2) K) (h1 : M * M' = 1) (h2 : M' * M = 1) : GL (Fin 2) K := ⟨M, M', h1, h2⟩

theorem exists_GL (M M' : Matrix (Fin 2) (Fin 2) K) (h1 : M * M' = 1) (h2 : M' * M = 1) :
    ∃ g : GL (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) = M ∧ ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = M' :=
  ⟨mkGL M M' h1 h2, rfl, rfl⟩

theorem assoc4 (S A B C : Matrix (Fin 2) (Fin 2) K) : S * (A * B * C) = S * A * B * C := by noncomm_ring

theorem conj_decomp (s : K) (hs : s ≠ 0) (A A' B B' C C' Y : Matrix (Fin 2) (Fin 2) K) :
    C' * (B' * (A' * Matrix.scalar (Fin 2) s⁻¹)) * Y * (Matrix.scalar (Fin 2) s * A * B * C) =
      C' * (B' * A' * Y * (A * B)) * C := by
  have ecomm : Matrix.scalar (Fin 2) s⁻¹ * Y = Y * Matrix.scalar (Fin 2) s⁻¹ :=
    (Matrix.scalar_commute s⁻¹ (Commute.all s⁻¹) Y).eq
  have hS2 : Matrix.scalar (Fin 2) s⁻¹ * Matrix.scalar (Fin 2) s = (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← map_mul, inv_mul_cancel₀ hs, map_one]
  calc C' * (B' * (A' * Matrix.scalar (Fin 2) s⁻¹)) * Y * (Matrix.scalar (Fin 2) s * A * B * C)
      = C' * B' * A' * (Matrix.scalar (Fin 2) s⁻¹ * Y) * (Matrix.scalar (Fin 2) s * A * B * C) := by noncomm_ring
    _ = C' * B' * A' * (Y * Matrix.scalar (Fin 2) s⁻¹) * (Matrix.scalar (Fin 2) s * A * B * C) := by rw [ecomm]
    _ = C' * B' * A' * Y * (Matrix.scalar (Fin 2) s⁻¹ * Matrix.scalar (Fin 2) s) * A * B * C := by noncomm_ring
    _ = C' * (B' * A' * Y * (A * B)) * C := by rw [hS2]; noncomm_ring

theorem smul_eq_scalar_mul (s : K) (X : Matrix (Fin 2) (Fin 2) K) : s • X = Matrix.scalar (Fin 2) s * X := by
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]

theorem scalar_mul_eq_mul_scalar (s : K) (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix.scalar (Fin 2) s * X = X * Matrix.scalar (Fin 2) s :=
  (Matrix.scalar_commute s (Commute.all s) X).eq

theorem scalar_conj (r : K) (P X Q : Matrix (Fin 2) (Fin 2) K) :
    P * (Matrix.scalar (Fin 2) r * X) * Q = Matrix.scalar (Fin 2) r * (P * X * Q) := by
  have e : Matrix.scalar (Fin 2) r * P = P * Matrix.scalar (Fin 2) r := (Matrix.scalar_commute r (Commute.all r) P).eq
  calc P * (Matrix.scalar (Fin 2) r * X) * Q = (P * Matrix.scalar (Fin 2) r) * X * Q := by noncomm_ring
    _ = (Matrix.scalar (Fin 2) r * P) * X * Q := by rw [e]
    _ = Matrix.scalar (Fin 2) r * (P * X * Q) := by noncomm_ring

theorem scalar_mul_apply (r : K) (A : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (Matrix.scalar (Fin 2) r * A) i j = r * A i j := by
  rw [Matrix.scalar_apply, Matrix.diagonal_mul]

theorem smul_one_eq_scalar (r : K) : r • (1 : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) r := by
  rw [smul_eq_scalar_mul, Matrix.mul_one]

theorem isInt_scalar {r : K} (hr : r ∈ O) : IsInt O (Matrix.scalar (Fin 2) r) := by
  intro i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hr
  · exact O.zero_mem

theorem isInt_diagonal {x y : K} (hx : x ∈ O) (hy : y ∈ O) : IsInt O (Matrix.diagonal ![x, y]) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hx, hy, O.zero_mem]

theorem diag_mul_diag (x y : K) :
    Matrix.diagonal ![(1 : K), x] * Matrix.diagonal ![(1 : K), y] = Matrix.diagonal ![(1 : K), x * y] := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i; fin_cases i <;> simp

def conjEquiv (g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K ≃+* Matrix (Fin 2) (Fin 2) K where
  toFun x := ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (g : Matrix (Fin 2) (Fin 2) K)
  invFun x := (g : Matrix (Fin 2) (Fin 2) K) * x * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  left_inv x := by
    show (g : Matrix (Fin 2) (Fin 2) K) * (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x *
      (g : Matrix (Fin 2) (Fin 2) K)) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = x
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv x := by
    show ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((g : Matrix (Fin 2) (Fin 2) K) * x *
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * (g : Matrix (Fin 2) (Fin 2) K) = x
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  map_mul' x y := by
    show ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (x * y) * (g : Matrix (Fin 2) (Fin 2) K) =
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (g : Matrix (Fin 2) (Fin 2) K) *
        (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * y * (g : Matrix (Fin 2) (Fin 2) K))
    have hg : (g : Matrix (Fin 2) (Fin 2) K) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (x * y) * (g : Matrix (Fin 2) (Fin 2) K)
        = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * 1 * y * (g : Matrix (Fin 2) (Fin 2) K) := by noncomm_ring
      _ = _ := by rw [← hg]; noncomm_ring
  map_add' x y := by
    show ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (x + y) * (g : Matrix (Fin 2) (Fin 2) K) =
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (g : Matrix (Fin 2) (Fin 2) K) +
        ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * y * (g : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.mul_add, Matrix.add_mul]

theorem conjEquiv_apply (g : GL (Fin 2) K) (x : Matrix (Fin 2) (Fin 2) K) :
    conjEquiv g x = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x * (g : Matrix (Fin 2) (Fin 2) K) := rfl

end Generic

theorem natGenerator_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = ℓ := by
  show Rat.HeightOneSpectrum.natGenerator v = ℓ
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ ℓ := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
    rwa [map_natCast] at this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hdvd

theorem exists_unit_mul_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (t₀ : v.adicCompletion ℚ) (ht₀ : t₀ ∈ v.adicCompletionIntegers ℚ) (ht₀0 : t₀ ≠ 0) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers ℚ)ˣ),
      t₀ = ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) * ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n := by
  set t : v.adicCompletionIntegers ℚ := ⟨t₀, ht₀⟩ with htdef
  have ht : t ≠ 0 := fun h => ht₀0 (by rw [htdef] at h; exact congrArg Subtype.val h)
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  set ψ := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v with hψ
  have ht' : ψ t ≠ 0 := fun h => ht (by simpa using congrArg ψ.symm h)
  refine ⟨(ψ t).valuation, Units.map ψ.symm.toRingEquiv.toRingHom.toMonoidHom (PadicInt.unitCoeff ht'), ?_⟩
  show (t : v.adicCompletion ℚ) = _
  have key : t = ψ.symm ((PadicInt.unitCoeff ht' : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) *
      ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) ^ (ψ t).valuation) := by
    rw [← PadicInt.unitCoeff_spec ht']; simp
  have hp : (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
      ((ℓ : ℕ) : v.adicCompletion ℚ) := by
    rw [← natGenerator_eq hℓ v hv]; exact map_natCast (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) _
  have e1 : (t : v.adicCompletion ℚ) =
      ((ψ.symm (PadicInt.unitCoeff ht' : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) *
        (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ^ (ψ t).valuation := by
    conv_lhs => rw [key]
    rw [map_mul, map_pow, map_natCast]
    push_cast
    rfl
  rw [e1, hp]
  rfl

end LocalType

namespace LocalType
section Generic2
variable {K : Type*} [Field K] (O : ValuationSubring K)

theorem cancel_conj (s : K) (A A' B W W' : Matrix (Fin 2) (Fin 2) K) (hA : A' * A = 1) (hW : W * W' = 1) :
    A' * (Matrix.scalar (Fin 2) s * (A * B * W)) * W' = Matrix.scalar (Fin 2) s * B := by
  rw [scalar_conj]
  congr 1
  calc A' * (A * B * W) * W' = (A' * A) * B * (W * W') := by noncomm_ring
    _ = B := by rw [hA, hW, Matrix.one_mul, Matrix.mul_one]

theorem diag_entry_00 (x : K) : (Matrix.diagonal ![(1 : K), x]) 0 0 = 1 := by simp
theorem diag_entry_11 (x : K) : (Matrix.diagonal ![(1 : K), x]) 1 1 = x := by simp

end Generic2
end LocalType

namespace LocalType
section Generic3
variable {K : Type*} [Field K] (O : ValuationSubring K)

theorem assoc5 (S A D U C : Matrix (Fin 2) (Fin 2) K) : S * (A * (D * U) * C) = S * A * D * (U * C) := by noncomm_ring

theorem assoc_conj (B' A' Y A B : Matrix (Fin 2) (Fin 2) K) : B' * A' * Y * (A * B) = B' * A' * Y * A * B := by noncomm_ring

theorem entry00_scalar_diag (s x : K) : (Matrix.scalar (Fin 2) s * Matrix.diagonal ![(1 : K), x]) 0 0 = s := by
  rw [scalar_mul_apply]; simp

theorem entry11_scalar_diag_scalar (r x s : K) :
    (Matrix.scalar (Fin 2) r * Matrix.diagonal ![(1 : K), x] * Matrix.scalar (Fin 2) s) 1 1 = r * x * s := by
  rw [Matrix.mul_assoc, scalar_mul_apply, ← scalar_mul_eq_mul_scalar, scalar_mul_apply]; simp; ring

theorem scalar_mul_scalar_inv (s : K) (hs : s ≠ 0) :
    Matrix.scalar (Fin 2) s * Matrix.scalar (Fin 2) s⁻¹ = (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [← map_mul, mul_inv_cancel₀ hs, map_one]

theorem scalar_inv_mul_scalar (s : K) (hs : s ≠ 0) :
    Matrix.scalar (Fin 2) s⁻¹ * Matrix.scalar (Fin 2) s = (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [← map_mul, inv_mul_cancel₀ hs, map_one]

theorem diag_mul_diag_inv' (x : K) (hx : x ≠ 0) :
    Matrix.diagonal ![(1 : K), x] * Matrix.diagonal ![(1 : K), x⁻¹] = 1 := by
  rw [diag_mul_diag, mul_inv_cancel₀ hx]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem diag_inv_mul_diag' (x : K) (hx : x ≠ 0) :
    Matrix.diagonal ![(1 : K), x⁻¹] * Matrix.diagonal ![(1 : K), x] = 1 := by
  rw [diag_mul_diag, inv_mul_cancel₀ hx]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem comm_of_val_eq_scalar (S g : GL (Fin 2) K) (s : K) (hS : (S : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) s) :
    S * g = g * S := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hS, scalar_mul_eq_mul_scalar]

end Generic3
end LocalType

namespace Y3Cartan

open LocalType

theorem inv_natCast_not_mem (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    (((ℓ : ℕ) : v.adicCompletion ℚ))⁻¹ ∉ v.adicCompletionIntegers ℚ := by
  have hcast : ((ℓ : ℕ) : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ) := by rw [map_natCast]
  rw [hcast, ← map_inv₀, HeightOneSpectrum.mem_adicCompletionIntegers,
    show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) = v.valuation ℚ ((ℓ : ℚ)⁻¹) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _, map_inv₀]
  have hlt : v.valuation ℚ (ℓ : ℚ) < 1 := by
    have : (ℓ : ℚ) = algebraMap (𝓞 ℚ) ℚ ((ℓ : ℕ) : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact hv
  have hne : v.valuation ℚ (ℓ : ℚ) ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact_mod_cast hℓ.ne_zero
  intro hle
  have := (one_lt_inv₀ (zero_lt_iff.mpr hne)).mpr hlt
  exact absurd hle (not_le.mpr this)

end Y3Cartan

open scoped Quaternion TensorProduct NumberField Pointwise in
open QuaternionAlgebra IsDedekindDomain NumberField LocalType Y3Cartan in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Y : GL (Fin 2) (v.adicCompletion ℚ))
    (hY : ∀ i j, (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ (e₁ e₂ : ℕ) (k₁ k₂ : GL (Fin 2) (v.adicCompletion ℚ)), e₁ ≤ e₂ ∧
      (∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ i j, ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ) ∧
      (∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ i j, ((k₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ) ∧
      (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        Matrix.diagonal ![((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₁, ((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₂] * (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∧
      ((∀ i j, ((((ℓ : ℕ) : v.adicCompletion ℚ)⁻¹ • (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)) ↔ 1 ≤ e₁) := by
  classical
  set K := v.adicCompletion ℚ with hKdef
  set O := v.adicCompletionIntegers ℚ with hOdef
  have hℓK : ((ℓ : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) ℓ]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  have hℓO : ((ℓ : ℕ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := natCast_mem _ ℓ

  obtain ⟨s, t, k₁, k₂, hs0, ht0, htO, hk₁, hk₁i, hk₂, hk₂i, hYeq⟩ :=
    Matrix.GeneralLinearGroup.exists_eq_smul_mul_diagonal_mul_of_valuationSubring (v.adicCompletionIntegers ℚ) Y

  set A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hA
  set A' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
    ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hA'
  set B : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hB
  set B' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
    ((k₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hB'
  have hAA : A' * A = 1 := by rw [hA, hA']; exact Units.inv_mul k₁
  have hAA' : A * A' = 1 := by rw [hA, hA']; exact Units.mul_inv k₁
  have hBB : B * B' = 1 := by rw [hB, hB']; exact Units.mul_inv k₂
  have hBB' : B' * B = 1 := by rw [hB, hB']; exact Units.inv_mul k₂
  set D : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![(1 : v.adicCompletion ℚ), t] with hD
  have hY1 : (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = Matrix.scalar (Fin 2) s * (A * D * B) := by
    rw [hYeq, smul_eq_scalar_mul]

  have hsO : s ∈ v.adicCompletionIntegers ℚ := by
    have hint : IsInt (v.adicCompletionIntegers ℚ) (A' * (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * B') :=
      IsInt.mul _ (IsInt.mul _ hk₁i hY) hk₂i
    rw [hY1, cancel_conj s A A' D B B' hAA hBB] at hint
    have := hint 0 0
    rwa [hD, entry00_scalar_diag] at this

  obtain ⟨e₁, u, hsu⟩ := exists_unit_mul_pow hℓ v hv s hsO hs0
  obtain ⟨f, u', htu⟩ := exists_unit_mul_pow hℓ v hv t htO ht0
  set e₂ := e₁ + f with he₂

  set uK : v.adicCompletion ℚ := ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) with huK
  set u'K : v.adicCompletion ℚ := ((u' : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) with hu'K
  set uiK : v.adicCompletion ℚ := (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) with huiK
  set u'iK : v.adicCompletion ℚ := (((u'⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) with hu'iK
  have huu : uK * uiK = 1 := by
    rw [huK, huiK, ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
  have hu'u' : u'K * u'iK = 1 := by
    rw [hu'K, hu'iK, ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
  set U : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![uK, uK * u'K] with hU
  set U' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![uiK, uiK * u'iK] with hU'
  have hUU' : U * U' = 1 := by
    rw [hU, hU', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.one_apply]; exact huu
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Pi.one_apply]
      calc uK * u'K * (uiK * u'iK) = (uK * uiK) * (u'K * u'iK) := by ring
        _ = 1 := by rw [huu, hu'u', one_mul]
  have hU'U : U' * U = 1 := mul_eq_one_comm.mp hUU'
  have hUint : IsInt (v.adicCompletionIntegers ℚ) U :=
    isInt_diagonal _ (u : v.adicCompletionIntegers ℚ).2 (mul_mem (u : v.adicCompletionIntegers ℚ).2 (u' : v.adicCompletionIntegers ℚ).2)
  have hU'int : IsInt (v.adicCompletionIntegers ℚ) U' :=
    isInt_diagonal _ ((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ).2
      (mul_mem ((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ).2
        ((u'⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ).2)
  obtain ⟨gU, hgU, hgU'⟩ := exists_GL U U' hUU' hU'U
  set Dℓ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
    Matrix.diagonal ![((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₁, ((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₂] with hDℓ

  have hdiag : Matrix.scalar (Fin 2) s * D = U * Dℓ := by
    rw [hD, hU, hDℓ, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, mul_one]
      exact hsu
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
      rw [hsu, htu, he₂, pow_add]
      ring

  have hYmain : (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      ((k₁ * gU : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Dℓ * B := by
    rw [hY1, Units.val_mul, hgU, ← hA]
    calc Matrix.scalar (Fin 2) s * (A * D * B) = A * (Matrix.scalar (Fin 2) s * D) * B := by
          rw [scalar_conj]
      _ = A * (U * Dℓ) * B := by rw [hdiag]
      _ = A * U * Dℓ * B := by noncomm_ring

  have hcancel : ∀ r : v.adicCompletion ℚ,
      ((gU⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * A' *
        (r • (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) * B' = r • Dℓ := by
    intro r
    rw [hYmain, Units.val_mul, hgU, hgU', ← hA, smul_eq_scalar_mul, smul_eq_scalar_mul]
    calc U' * A' * (Matrix.scalar (Fin 2) r * (A * U * Dℓ * B)) * B'
        = Matrix.scalar (Fin 2) r * ((U' * (A' * A) * U) * Dℓ * (B * B')) := by
          rw [show U' * A' * (Matrix.scalar (Fin 2) r * (A * U * Dℓ * B)) * B' =
            (U' * A') * (Matrix.scalar (Fin 2) r * (A * U * Dℓ * B)) * B' from rfl, scalar_conj]
          noncomm_ring
      _ = Matrix.scalar (Fin 2) r * Dℓ := by rw [hAA, hBB]; simp only [Matrix.mul_one, Matrix.one_mul, hU'U]
  refine ⟨e₁, e₂, k₁ * gU, k₂, Nat.le_add_right e₁ f, ?_, ?_, hk₂, hk₂i, hYmain, ?_⟩
  · rw [Units.val_mul, hgU]; exact IsInt.mul _ hk₁ hUint
  · rw [mul_inv_rev, Units.val_mul, hgU']; exact IsInt.mul _ hU'int hk₁i
  · constructor
    · intro hint
      by_contra hlt
      have he0 : e₁ = 0 := by omega
      have hconj : IsInt (v.adicCompletionIntegers ℚ)
          (((gU⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * A' *
            ((((ℓ : ℕ) : v.adicCompletion ℚ))⁻¹ • (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) * B') := by
        refine IsInt.mul _ (IsInt.mul _ (IsInt.mul _ (by rw [hgU']; exact hU'int) hk₁i) ?_) hk₂i
        exact hint
      rw [hcancel] at hconj
      have h00 := hconj 0 0
      rw [Matrix.smul_apply, hDℓ, he0, smul_eq_mul] at h00
      simp only [Fin.isValue, Matrix.diagonal_apply_eq, Matrix.cons_val_zero, pow_zero, mul_one] at h00
      exact inv_natCast_not_mem v hℓ hv h00
    · intro he i j

      have hsmulD : IsInt (v.adicCompletionIntegers ℚ) ((((ℓ : ℕ) : v.adicCompletion ℚ))⁻¹ • Dℓ) := by
        have h1 : (((ℓ : ℕ) : v.adicCompletion ℚ))⁻¹ * ((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₁ =
            ((ℓ : ℕ) : v.adicCompletion ℚ) ^ (e₁ - 1) := by
          conv_lhs => rw [show e₁ = (e₁ - 1) + 1 by omega, pow_succ]
          rw [mul_comm, mul_assoc, mul_inv_cancel₀ hℓK, mul_one]
        have h2 : (((ℓ : ℕ) : v.adicCompletion ℚ))⁻¹ * ((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₂ =
            ((ℓ : ℕ) : v.adicCompletion ℚ) ^ (e₂ - 1) := by
          conv_lhs => rw [show e₂ = (e₂ - 1) + 1 by omega, pow_succ]
          rw [mul_comm, mul_assoc, mul_inv_cancel₀ hℓK, mul_one]
        rw [hDℓ, Matrix.smul_eq_diagonal_mul, Matrix.diagonal_mul_diagonal]
        have : (fun i => (((ℓ : ℕ) : v.adicCompletion ℚ))⁻¹ *
            ![((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₁, ((ℓ : ℕ) : v.adicCompletion ℚ) ^ e₂] i) =
            ![((ℓ : ℕ) : v.adicCompletion ℚ) ^ (e₁ - 1), ((ℓ : ℕ) : v.adicCompletion ℚ) ^ (e₂ - 1)] := by
          funext i; fin_cases i
          · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; exact h1
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]; exact h2
        rw [this]
        exact isInt_diagonal _ (pow_mem hℓO _) (pow_mem hℓO _)
      have heq : (((ℓ : ℕ) : v.adicCompletion ℚ))⁻¹ • (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
          ((k₁ * gU : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
            ((((ℓ : ℕ) : v.adicCompletion ℚ))⁻¹ • Dℓ) * B := by
        rw [smul_eq_scalar_mul, smul_eq_scalar_mul, hYmain, scalar_conj]
      rw [heq]
      exact IsInt.mul _ (IsInt.mul _ (by rw [Units.val_mul, hgU]; exact IsInt.mul _ hk₁ hUint) hsmulD) hk₂ i j

end S_Matrix_GeneralLinearGroup_exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers
end P2MW
export P2MW.S_Matrix_GeneralLinearGroup_exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers (solution)
