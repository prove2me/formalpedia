-- Prove2me | solution 1 for Matrix.relIndex_inf_conj_diagonal_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7754b398-8ed5-559d-8606-2434d8fcd2c6

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_relIndex_inf_conj_diagonal_pow_eq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace W4p

def unitsConjAddEquiv {M : Type*} [Ring M] (h : Mˣ) : M ≃+ M where
  toFun m := (↑h⁻¹ : M) * m * ↑h
  invFun m := (↑h : M) * m * ↑h⁻¹
  left_inv m := by
    show (↑h : M) * ((↑h⁻¹ : M) * m * ↑h) * ↑h⁻¹ = m
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, Units.mul_inv_cancel_right]
  right_inv m := by
    show (↑h⁻¹ : M) * ((↑h : M) * m * ↑h⁻¹) * ↑h = m
    rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]
  map_add' m m' := by
    show (↑h⁻¹ : M) * (m + m') * ↑h = (↑h⁻¹ : M) * m * ↑h + (↑h⁻¹ : M) * m' * ↑h
    rw [mul_add, add_mul]

variable (v : HeightOneSpectrum (𝓞 ℚ))

def intMat : AddSubgroup (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) where
  carrier := {m | ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ}
  zero_mem' := fun i j => by simp only [Matrix.zero_apply]; exact zero_mem _
  add_mem' := fun {m m'} hm hm' i j => by simp only [Matrix.add_apply]; exact add_mem (hm i j) (hm' i j)
  neg_mem' := fun {m} hm i j => by simp only [Matrix.neg_apply]; exact neg_mem (hm i j)

theorem mem_intMat_iff (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    m ∈ intMat v ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ := Iff.rfl

theorem conj_diagonal_mem_intMat_iff {n : v.adicCompletion ℚ} (hn : n ≠ 0)
    (hnR : n ∈ v.adicCompletionIntegers ℚ)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)} (hm : m ∈ intMat v) :
    Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹] * m * Matrix.diagonal ![(1 : v.adicCompletion ℚ), n]
        ∈ intMat v ↔ n⁻¹ * m 1 0 ∈ v.adicCompletionIntegers ℚ := by
  rw [mem_intMat_iff] at hm ⊢
  constructor
  · intro H
    have h10 := H 1 0
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h10
    simpa using h10
  · intro H i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j
    · simpa using hm 0 0
    · simpa using mul_mem (hm 0 1) hnR
    · simpa using H
    · have : n⁻¹ * m 1 1 * n = m 1 1 := by
        rw [mul_comm n⁻¹, mul_assoc, inv_mul_cancel₀ hn, mul_one]
      simpa [this] using hm 1 1

theorem mem_span_iff {n : v.adicCompletion ℚ} (hn : n ≠ 0) (nR : v.adicCompletionIntegers ℚ)
    (hnR : (nR : v.adicCompletion ℚ) = n) (r : v.adicCompletionIntegers ℚ) :
    r ∈ Ideal.span {nR} ↔ n⁻¹ * (r : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    have : n⁻¹ * ((a * nR : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = a := by
      push_cast
      rw [hnR, mul_comm (a : v.adicCompletion ℚ) n, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    rw [this]
    exact a.2
  · intro H
    refine ⟨⟨n⁻¹ * (r : v.adicCompletion ℚ), H⟩, Subtype.ext ?_⟩
    push_cast
    rw [hnR, mul_comm n⁻¹, inv_mul_cancel_right₀ hn]

theorem main {A : Type*} [Ring A] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : A ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (h : GL (Fin 2) (v.adicCompletion ℚ)) (e : ℕ)
    (O O' : AddSubgroup A)
    (hO : ∀ x, x ∈ O ↔ ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)
    (hO' : ∀ x, x ∈ O' ↔ ∀ i j,
      (Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : v.adicCompletion ℚ) ^ e)⁻¹] *
        ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), (ℓ : v.adicCompletion ℚ) ^ e]) i j
          ∈ v.adicCompletionIntegers ℚ) :
    (O ⊓ O').relIndex O = ℓ ^ e := by
  classical
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective

  set n : v.adicCompletion ℚ := (ℓ : v.adicCompletion ℚ) ^ e with hn_def
  have hn : n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  have hnR : n ∈ v.adicCompletionIntegers ℚ := pow_mem (natCast_mem _ ℓ) e
  let nR : v.adicCompletionIntegers ℚ := ((ℓ ^ e : ℕ) : v.adicCompletionIntegers ℚ)
  have hnR' : (nR : v.adicCompletion ℚ) = n := by push_cast [nR]; rfl
  let d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![(1 : v.adicCompletion ℚ), n]
  let d' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![(1 : v.adicCompletion ℚ), n⁻¹]

  let ψ : A ≃+ Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := φ.toAddEquiv.trans (unitsConjAddEquiv h)
  have hψ : ∀ x, ψ x =
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) := fun _ => rfl
  let M := intMat v
  let Md := M.comap ((AddMonoidHom.mulRight d).comp (AddMonoidHom.mulLeft d'))
  have hOeq : O = M.comap ψ.toAddMonoidHom := by
    ext x; rw [AddSubgroup.mem_comap, hO]; rfl
  have hO'eq : O' = Md.comap ψ.toAddMonoidHom := by
    ext x
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_comap, hO', AddMonoidHom.comp_apply,
      AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight, AddEquiv.coe_toAddMonoidHom, hψ,
      ← mul_assoc, ← mul_assoc]
    rfl
  rw [hOeq, hO'eq, ← AddSubgroup.comap_inf, AddSubgroup.relIndex_comap,
    AddSubgroup.map_comap_eq_self_of_surjective ψ.surjective]

  let I : Ideal (v.adicCompletionIntegers ℚ) := Ideal.span {nR}
  let g₀ : M →+ v.adicCompletionIntegers ℚ :=
    { toFun := fun m => ⟨(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0, m.2 1 0⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let g : M →+ v.adicCompletionIntegers ℚ ⧸ I := (Ideal.Quotient.mk I).toAddMonoidHom.comp g₀
  have hg : ∀ m : M, g m = Ideal.Quotient.mk I (g₀ m) := fun _ => rfl
  have hker : g.ker = (M ⊓ Md).addSubgroupOf M := by
    ext m
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf, hg,
      Ideal.Quotient.eq_zero_iff_mem, mem_span_iff v hn nR hnR', AddSubgroup.mem_comap,
      AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    show n⁻¹ * (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 ∈ v.adicCompletionIntegers ℚ ↔
      (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) ∈ M ∧ d' * m * d ∈ intMat v
    rw [conj_diagonal_mem_intMat_iff v hn hnR m.2]
    exact ⟨fun H => ⟨m.2, H⟩, fun H => H.2⟩
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨⟨Matrix.single 1 0 (r : v.adicCompletion ℚ), fun i j => ?_⟩, ?_⟩
    · by_cases hij : (1 : Fin 2) = i ∧ (0 : Fin 2) = j
      · obtain ⟨rfl, rfl⟩ := hij
        rw [Matrix.single_apply_same]; exact r.2
      · rw [Matrix.single_apply_of_ne _ _ _ _ _ hij]; exact zero_mem _
    · rw [hg]
      congr 1
  calc (M ⊓ Md).relIndex M = ((M ⊓ Md).addSubgroupOf M).index := rfl
    _ = g.ker.index := by rw [hker]
    _ = Nat.card g.range := AddSubgroup.index_ker g
    _ = Nat.card (v.adicCompletionIntegers ℚ ⧸ I) := by
        rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top]
    _ = ℓ ^ (ℓ ^ e).factorization ℓ :=
        IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
          v ℓ hℓ hℓv (ℓ ^ e) (pow_ne_zero e hℓ.ne_zero)
    _ = ℓ ^ e := by rw [Nat.factorization_pow_self hℓ]

end W4p

theorem solution
    {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (h : GL (Fin 2) (v.adicCompletion ℚ)) (e : ℕ)
    (O O' : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hO : ∀ x, x ∈ O ↔ ∀ i j,
      (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)
    (hO' : ∀ x, x ∈ O' ↔ ∀ i j,
      (Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : v.adicCompletion ℚ) ^ e)⁻¹] *
        ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), (ℓ : v.adicCompletion ℚ) ^ e]) i j
          ∈ v.adicCompletionIntegers ℚ) :
    (O ⊓ O').relIndex O = ℓ ^ e := by
  exact W4p.main v ℓ hℓ hℓv φ h e O O' hO hO'

end S_Matrix_relIndex_inf_conj_diagonal_pow_eq
end P2MW
export P2MW.S_Matrix_relIndex_inf_conj_diagonal_pow_eq (solution)
