-- Prove2me | solution 1 for ModularCurve.mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6977559c-c75f-5aca-8cf2-97d02a70aa92

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense

set_option Elab.async false

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "HeckeAlg heckeGen heckeTorsion mTorsionGaloisRep coe_mTorsionGaloisRep_apply FrobeniusQuadratic"
p2m_open "ModularCurve"
namespace I2Push

variable {k : Type} [CommRing k]

def lucasU (t d : k) : ℕ → k
  | 0 => 0
  | 1 => 1
  | (n + 2) => t * lucasU t d (n + 1) - d * lucasU t d n

private theorem lucasU_zero (t d : k) : lucasU t d 0 = 0 := rfl
private theorem lucasU_one (t d : k) : lucasU t d 1 = 1 := rfl
private theorem lucasU_add_two (t d : k) (n : ℕ) :
    lucasU t d (n + 2) = t * lucasU t d (n + 1) - d * lucasU t d n := rfl

private theorem lucasU_norm (t d : k) (n : ℕ) :
    lucasU t d (n + 1) ^ 2 - t * lucasU t d (n + 1) * lucasU t d n + d * lucasU t d n ^ 2 = d ^ n := by
  induction n with
  | zero => simp [lucasU_zero, lucasU_one]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 from rfl, lucasU_add_two, pow_succ]
    linear_combination d * ih

variable {W : Type} [AddCommGroup W] [Module k W]

local notation "E" => Module.End k W

private theorem pow_succ_eq_of_quadratic (A : E) (t d : k) (hA : A ^ 2 - t • A + d • (1 : E) = 0) (n : ℕ) :
    A ^ (n + 1) = lucasU t d (n + 1) • A - (d * lucasU t d n) • (1 : E) := by
  have hA2 : A ^ 2 = t • A - d • (1 : E) :=
    eq_of_sub_eq_zero (((by abel) : A ^ 2 - (t • A - d • (1 : E)) = A ^ 2 - t • A + d • 1).trans hA)
  induction n with
  | zero => simp [lucasU_zero, lucasU_one]
  | succ n ih =>
    rw [pow_succ', ih, show n + 1 + 1 = n + 2 from rfl, lucasU_add_two, mul_sub, Algebra.mul_smul_comm,
      Algebra.mul_smul_comm, mul_one, ← sq, hA2]
    module

private theorem quadratic_pow_succ_of_quadratic (A : E) (t d : k) (hA : A ^ 2 - t • A + d • (1 : E) = 0) (n : ℕ) :
    (A ^ (n + 1)) ^ 2 - (t * lucasU t d (n + 1) - 2 * d * lucasU t d n) • A ^ (n + 1)
      + d ^ (n + 1) • (1 : E) = 0 := by
  have hA2 : A * A = t • A - d • (1 : E) := by
    rw [← sq]
    exact eq_of_sub_eq_zero (((by abel) : A ^ 2 - (t • A - d • (1 : E)) = A ^ 2 - t • A + d • 1).trans hA)
  have hn := lucasU_norm t d n
  rw [pow_succ_eq_of_quadratic A t d hA n]
  simp only [sq, sub_mul, mul_sub, smul_mul_smul_comm, mul_one, one_mul, hA2, smul_sub, smul_smul]
  match_scalars <;> first | ring1 | linear_combination (-d) * hn

private theorem matrix_fin_two_quadratic (B : Matrix (Fin 2) (Fin 2) k) :
    B ^ 2 - B.trace • B + B.det • (1 : Matrix (Fin 2) (Fin 2) k) = 0 := by
  ext i j
  rw [sq, Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem matrix_pow_succ_eq (B : Matrix (Fin 2) (Fin 2) k) (n : ℕ) :
    B ^ (n + 1) = lucasU B.trace B.det (n + 1) • B - (B.det * lucasU B.trace B.det n) • (1 : Matrix (Fin 2) (Fin 2) k) := by
  have hB2 : B ^ 2 = B.trace • B - B.det • (1 : Matrix (Fin 2) (Fin 2) k) :=
    eq_of_sub_eq_zero (((by abel) : B ^ 2 - (B.trace • B - B.det • (1 : Matrix (Fin 2) (Fin 2) k))
      = B ^ 2 - B.trace • B + B.det • 1).trans (matrix_fin_two_quadratic B))
  induction n with
  | zero => simp [lucasU_zero, lucasU_one]
  | succ n ih =>
    rw [pow_succ', ih, show n + 1 + 1 = n + 2 from rfl, lucasU_add_two, mul_sub, Algebra.mul_smul_comm,
      Algebra.mul_smul_comm, mul_one, ← sq, hB2]
    module

private theorem trace_pow_succ (B : Matrix (Fin 2) (Fin 2) k) (n : ℕ) :
    (B ^ (n + 1)).trace = B.trace * lucasU B.trace B.det (n + 1) - 2 * B.det * lucasU B.trace B.det n := by
  rw [matrix_pow_succ_eq B n, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

private theorem conj_quadratic (P X Q : E) (t d : k) (hQP : Q * P = 1) (hPQ : P * Q = 1) :
    (P * X * Q) ^ 2 - t • (P * X * Q) + d • (1 : E) = P * (X ^ 2 - t • X + d • (1 : E)) * Q := by
  have hQP' : ∀ y : E, Q * (P * y) = y := fun y => by rw [← mul_assoc, hQP, one_mul]
  simp only [sq, mul_add, mul_sub, add_mul, sub_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_one,
    hPQ, hQP', mul_assoc]

private theorem one_quadratic :
    (1 : E) ^ 2 - (1 : Matrix (Fin 2) (Fin 2) k).trace • (1 : E) + (1 : k) • (1 : E) = 0 := by
  rw [Matrix.trace_one, Fintype.card_fin, Nat.cast_smul_eq_nsmul, one_smul, one_pow, two_nsmul]
  abel

end I2Push
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "HeckeAlg heckeGen heckeTorsion mTorsionGaloisRep coe_mTorsionGaloisRep_apply FrobeniusQuadratic"
p2m_open "ModularCurve"

private theorem mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense
    {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal HeckeAlg) (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧ Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (heckeTorsion J 𝔪 : Set J))) :
    ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      mTorsionGaloisRep J 𝔪 g ^ 2 - (ρ g).trace • mTorsionGaloisRep J 𝔪 g + (ρ g).det • 1 = 0 := by
  classical

  set σ := mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J 𝔪 with hσdef
  intro g
  obtain ⟨ℓ, A, τ, g₀, n, hℓ, hℓS, hA, hτ, hH⟩ := hdense g
  obtain ⟨hHker, hHfix⟩ := Subgroup.mem_inf.mp hH
  set h := g₀ * τ ^ n * g₀⁻¹ * g⁻¹ with hhdef

  have hρh : ρ h = 1 := (MonoidHom.mem_ker).mp hHker
  have hσh : σ h = 1 := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    have := (mem_fixingSubgroup_iff (M := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).mp hHfix (y : J) y.2
    simpa [hσdef] using this
  have hρh' : ρ h⁻¹ = 1 := by
    have e := map_mul ρ h⁻¹ h
    rw [inv_mul_cancel, map_one, hρh, mul_one] at e
    exact e.symm
  have hσh' : σ h⁻¹ = 1 := by
    have e := map_mul σ h⁻¹ h
    rw [inv_mul_cancel, map_one, hσh, mul_one] at e
    exact e.symm
  have hg : g = h⁻¹ * (g₀ * τ ^ n * g₀⁻¹) := by rw [hhdef]; group

  obtain ⟨htr, hdet⟩ := hatt ℓ hℓ hℓS A hA τ hτ
  have hfrob : σ τ ^ 2 - (ρ τ).trace • σ τ + (ρ τ).det • (1 : Module.End (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪))
      = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx : ∃ m : ℕ, p ^ m • (x : J) = 0 :=
      ⟨1, by
        rw [pow_one, ← Nat.cast_smul_eq_nsmul HeckeAlg]
        exact (Submodule.mem_torsionBySet_iff _ _).mp x.2 ⟨_, hp⟩⟩
    have hq := hES ℓ hℓ (hS ℓ hℓ hℓS) A hA τ hτ x hx
    rw [← htr, ← hdet]
    simp only [hσdef, sq, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, LinearMap.zero_apply, Submodule.torsionBySet.mk_smul, Submodule.coe_sub,
      Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero, coe_mTorsionGaloisRep_apply, Nat.cast_smul_eq_nsmul]
    exact hq

  have hρinv : ρ g₀⁻¹ * ρ g₀ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hρinv' : ρ g₀ * ρ g₀⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hσinv : σ g₀⁻¹ * σ g₀ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hσinv' : σ g₀ * σ g₀⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]

  have hσg : σ g = σ g₀ * σ τ ^ n * σ g₀⁻¹ := by rw [hg, map_mul, hσh', one_mul, map_mul, map_mul, map_pow]
  have hρg : ρ g = ρ g₀ * ρ τ ^ n * ρ g₀⁻¹ := by rw [hg, map_mul, hρh', one_mul, map_mul, map_mul, map_pow]
  have htrg : (ρ g).trace = (ρ τ ^ n).trace := by
    rw [hρg, Matrix.trace_mul_cycle, hρinv, one_mul]
  have hdetg : (ρ g).det = (ρ τ).det ^ n := by
    rw [hρg, Matrix.det_mul, Matrix.det_mul, mul_comm (ρ g₀).det, mul_assoc, ← Matrix.det_mul, hρinv',
      Matrix.det_one, mul_one, Matrix.det_pow]
  show σ g ^ 2 - (ρ g).trace • σ g + (ρ g).det • 1 = 0
  rw [hσg, htrg, hdetg, I2Push.conj_quadratic _ _ _ _ _ hσinv hσinv']
  cases n with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero, I2Push.one_quadratic, mul_zero, zero_mul]
  | succ m =>
    rw [I2Push.trace_pow_succ, I2Push.quadratic_pow_succ_of_quadratic (σ τ) (ρ τ).trace (ρ τ).det hfrob m,
      mul_zero, zero_mul]

end ModularCurve

#check @ModularCurve.mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense

set_option autoImplicit false
p2m_open "ModularCurve P2MW.S_ModularCurve_mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense.ModularCurve"

theorem solution
    {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal HeckeAlg) (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧ Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (heckeTorsion J 𝔪 : Set J))) :
    ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      mTorsionGaloisRep J 𝔪 g ^ 2 - (ρ g).trace • mTorsionGaloisRep J 𝔪 g + (ρ g).det • 1 = 0 := by
  exact ModularCurve.mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense N p 𝔪 hp ρ hES hS hatt hdense

end S_ModularCurve_mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense
end P2MW
export P2MW.S_ModularCurve_mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense (solution)
