-- Prove2me | solution 1 for ModularCurve.not_isEventuallyEisenstein_of_repClauses
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/39adcf77-6f74-5f50-aca9-abf885302479

import Mathlib
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Theorems.Thm_Representation_exists_trace_ne_one_add_det_of_irreducible
import Theorems.Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_not_isEventuallyEisenstein_of_repClauses
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace P2mWs11E1

open ModularCurve

section TwoByTwo

variable {R : Type*} [CommRing R]

theorem mul_self_eq_trace_smul_sub_det_smul (M : Matrix (Fin 2) (Fin 2) R) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply] <;> ring

theorem pow_add_two_eq (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    M ^ (n + 2) = M.trace • M ^ (n + 1) - M.det • M ^ n := by
  rw [pow_succ, pow_succ, mul_assoc, mul_self_eq_trace_smul_sub_det_smul, mul_sub,
    Matrix.mul_smul, Matrix.mul_smul, mul_one, ← pow_succ]

theorem trace_pow_add_two (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    (M ^ (n + 2)).trace = M.trace * (M ^ (n + 1)).trace - M.det * (M ^ n).trace := by
  rw [pow_add_two_eq, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

theorem trace_pow_eq_one_add_det_pow {M : Matrix (Fin 2) (Fin 2) R}
    (hM : M.trace = 1 + M.det) : ∀ n : ℕ, (M ^ n).trace = 1 + (M ^ n).det := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [Matrix.trace_one]; norm_num
    | 1, _ => simpa using hM
    | (m + 2), ih =>
      rw [trace_pow_add_two, ih (m + 1) (by omega), ih m (by omega), hM, Matrix.det_pow,
        Matrix.det_pow, Matrix.det_pow]
      ring

end TwoByTwo

section MatrixRep

variable {k G : Type*} [CommRing k] [Monoid G]

def matrixRep {n : ℕ} (ρmat : G →* Matrix (Fin n) (Fin n) k) :
    Representation k G (Fin n → k) :=
  (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.toRingHom.toMonoidHom.comp ρmat

@[scoped simp] theorem matrixRep_apply {n : ℕ} (ρmat : G →* Matrix (Fin n) (Fin n) k) (g : G)
    (v : Fin n → k) :
    matrixRep ρmat g v = (ρmat g).mulVec v := by
  simp [matrixRep, Matrix.toLinAlgEquiv'_apply]

theorem trace_matrixRep {n : ℕ} (ρmat : G →* Matrix (Fin n) (Fin n) k) (g : G) :
    LinearMap.trace k (Fin n → k) (matrixRep ρmat g) = (ρmat g).trace := by
  have : (matrixRep ρmat g : (Fin n → k) →ₗ[k] (Fin n → k))
      = Matrix.toLin (Pi.basisFun k (Fin n)) (Pi.basisFun k (Fin n)) (ρmat g) := by
    rw [Matrix.toLin_eq_toLin']
    rfl
  rw [this, Matrix.trace_toLin_eq]

theorem det_matrixRep {n : ℕ} (ρmat : G →* Matrix (Fin n) (Fin n) k) (g : G) :
    LinearMap.det (matrixRep ρmat g) = (ρmat g).det := by
  have : (matrixRep ρmat g : (Fin n → k) →ₗ[k] (Fin n → k)) = Matrix.toLin' (ρmat g) := rfl
  rw [this]
  simp

end MatrixRep

end P2mWs11E1
p2m_reactivate "P2MW.S_ModularCurve_not_isEventuallyEisenstein_of_repClauses.P2mWs11E1"

open P2mWs11E1 ModularCurve in
theorem solution
    (𝔪 : Ideal ModularCurve.HeckeAlg) (hmax : 𝔪.IsMaximal)
    (ρmat : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ModularCurve.HeckeAlg ⧸ 𝔪))
    (hirr : ∀ Wsub : Submodule (ModularCurve.HeckeAlg ⧸ 𝔪) (Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪),
      (∀ g, ∀ v ∈ Wsub, (ρmat g).mulVec v ∈ Wsub) → Wsub = ⊥ ∨ Wsub = ⊤)
    (Sρ : Finset ℕ)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ Sρ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          (ρmat σ).trace = Ideal.Quotient.mk 𝔪 (ModularCurve.heckeGen ⟨ℓ, hℓ⟩))
    (hdet : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ Sρ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          (ρmat σ).det = ((ℓ : ℕ) : ModularCurve.HeckeAlg ⧸ 𝔪))
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρmat.ker) :
    ¬ ModularCurve.IsEventuallyEisenstein 𝔪 := by
  classical
  rintro ⟨S₀, hS₀⟩
  haveI : 𝔪.IsMaximal := hmax
  letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪

  set S' : Finset ℕ := Sρ ∪ S₀.image (fun ℓ : Nat.Primes => (ℓ : ℕ)) with hS'
  have hdense := FrobeniusDensity.frobeniusPowerDense_of_le_ker F hker S'

  have hall : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (ρmat σ).trace = 1 + (ρmat σ).det := by
    intro σ
    obtain ⟨ℓ, A, τ, g, n, hℓ, hℓS', hA, hτ, hmem⟩ := hdense σ
    have hℓSρ : ℓ ∉ Sρ := fun h => hℓS' (Finset.mem_union_left _ h)
    have hℓS₀ : (⟨ℓ, hℓ⟩ : Nat.Primes) ∉ S₀ := fun h =>
      hℓS' (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨ℓ, hℓ⟩, h, rfl⟩))

    have hE : Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = ((ℓ : ℕ) : HeckeAlg ⧸ 𝔪) + 1 := by
      have h0 := (Ideal.Quotient.eq (I := 𝔪)).mpr (hS₀ ⟨ℓ, hℓ⟩ hℓS₀)
      rw [h0, map_add, map_natCast, map_one]

    have hτid : (ρmat τ).trace = 1 + (ρmat τ).det := by
      rw [htr ℓ hℓ hℓSρ A hA τ hτ, hdet ℓ hℓ hℓSρ A hA τ hτ, hE, add_comm]
    have hpow : (ρmat τ ^ n).trace = 1 + (ρmat τ ^ n).det := trace_pow_eq_one_add_det_pow hτid n

    have hσ : ρmat σ = ρmat g * ρmat τ ^ n * ρmat g⁻¹ := by
      have h1 : ρmat (g * τ ^ n * g⁻¹ * σ⁻¹) = 1 := (MonoidHom.mem_ker).mp hmem
      have h2 : g * τ ^ n * g⁻¹ = (g * τ ^ n * g⁻¹ * σ⁻¹) * σ := by group
      calc ρmat σ = ρmat ((g * τ ^ n * g⁻¹ * σ⁻¹) * σ) := by rw [map_mul, h1, one_mul]
        _ = ρmat (g * τ ^ n * g⁻¹) := by rw [← h2]
        _ = ρmat g * ρmat τ ^ n * ρmat g⁻¹ := by rw [map_mul, map_mul, map_pow]
    have hinv1 : ρmat g⁻¹ * ρmat g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have htrσ : (ρmat σ).trace = (ρmat τ ^ n).trace := by
      rw [hσ, Matrix.trace_mul_cycle, hinv1, one_mul]
    have hdetσ : (ρmat σ).det = (ρmat τ ^ n).det := by
      rw [hσ, Matrix.det_mul, Matrix.det_mul, mul_comm (ρmat g).det, mul_assoc, ← Matrix.det_mul,
        ← map_mul, mul_inv_cancel, map_one, Matrix.det_one, mul_one]
    rw [htrσ, hdetσ, hpow]

  obtain ⟨g, hg⟩ := Representation.exists_trace_ne_one_add_det_of_irreducible (matrixRep ρmat)
    (Module.finrank_fin_fun (R := HeckeAlg ⧸ 𝔪)) (fun W hW => hirr W fun g v hv => by
      simpa only [matrixRep_apply] using hW g v hv)
  exact hg (by rw [trace_matrixRep, det_matrixRep]; exact hall g)

end
end S_ModularCurve_not_isEventuallyEisenstein_of_repClauses
end P2MW
export P2MW.S_ModularCurve_not_isEventuallyEisenstein_of_repClauses (solution)
